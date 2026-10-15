-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4455
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:40:33.466482+00:00
-- url     : https://prove2.me/submissions/0e19cc68-f93d-460b-973d-f6c94fd16f3d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 801079136 ≤ n < 801258992 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 801080386 1250 801079136 801079157
    0x312042f060d0f060305071a040e01090504031b0506061207081b0d0602031504050604020705060c0c0a1403041e0b07120e0607060e010c0516020d030207030f120207140102060403 78
    0x302d000b514a01c81202055441c00c0303000001e0140000d6140221012820154080c3c1e08040800c003c0c2d03c81d0b802842c1c0ba414004004000854481e0300460703106010b440d02100e9007000e0310354684148005541030341c40c2e071320400521106103050818581c50226100003000b2807480c00003055120100c40035103800300c1a40180c485241c2e241c0e2683c000040d540014119580e1810101c164240045d062410b401a864880058a0740c20240300301c0d100c080e0020010039295884444907829503020280303402c5903008154010f4000340400c1e03021804103a82d40c0c0610f4403103060140703d02d00c2d00c5040340a41a0702da280ea00c00c03c00b00e443c0100b282c0c1c030a504440412744900c8802002e907001e0300401982600312034000340c00c4082c003196a0140d002d001201e0002c1c442402030410444150152000301032038403010b200440b00501e41046c0c0300581300c1c424010388400c03603aa6259040204211102942c01c8160035540b001c45580c14454440900301d400705d00d030200344803003000075964000100024180000b0811 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 801081636 1250 801080386 801080407
    0x2109190209070309170a090e0f06041d0a060e0606191208131d012c1e040c080105010f26070f180b09040f021509030312042f06 56
    0x200c0000c0e504001722900c100c00b40100d11100c0d911042c441c000040c40454081002c0081d800c000b8080c8002d10b26031f20251301d03040200001000c011502042d141000c0d2001d60403a031041c8403449545000e03860004050402810326410920001c1c841ea20440400b03058401c10c1a00703044410507100040c4080d008400e06280c004914401c40c082e01038524401c040018149400c5401c0d0149040036446d0054981d07a942000704010b11501a070908000710600b642c06010100444164030040c0310110b210b0b14100e0f140010105041618160703501071b515002405001d034240605070050030038094a100311850220039001c1072244500c03002d0b0980c2030a42294070040f003040140301900e4001c040068290b0350b14001031807481020000c8804a04000b203040d0545002c44a140c03042c1d401444128940c4080c2c1c1c00c00010b2411814a002822010301410410f51800c102410b040030590070140041d050a04100000700c916001c1118400628101c501d08004c105135901e1080d00191030785a01c5060b4502d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 801082886 1250 801081636 801081641
    0x503030711211b0105062d04060605190c0203031c0905060f09070501030912050307200c010306150c0b0606040302041103070f0c080304110a0b21091902090703 70
    0x41d244480e28000041030500035800100610612860b00148001401c0d010649805c0c0c9100b210225401411407403881c0d80541d22942000b90b507101650024900c2d4003083c000307401ca0b10700741c0020b00090008512002e050700d05002000c0c1c16062802e2044c0103015a0340002d80d46d10510704100000c104240c0364a8049000b074101072981d82c2c2c00815581c8910f0070304207080214400f110290441c0c8240140000d03554000c0c802c505410b500074644600f03480c180f0304240c3c0c090f071016005208020030307003001440d521035108992070305c0080034004c2c1241c010141c0005041c0d44c555006210075100080403400d481c2e800800300c80c84154040c088055682d10100040e00a006030751004c0d4006003881902c83c00d0610b04c10080d4810146901d90420b07000d10b03504c1c111001c080d084d0008017031040c00c1020802103102e46c0c184185002c002050f0cc521191204a03403010f0341c02101c3c0045d4403400b0000c41011448080400e280c2c406e84850050401c207003104140d6030480b1101c20007038017603a03c1c840800c004502c00e8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 801084136 1250 801082886 801082903
    0x604080703060f0f0c0305040c050f0a030807170a021f05190e1e070305190c03061503080a02031306110c060c0a0605130c09290307051203091c0503030711 68
    0x130325082000e084000b0026000e402d0071181164900481c23440440d20385062400c02400c4080078001400184c21965980c050354001842600c445180806100490b06458010000340031a40d001d0020050002c9001401c0144421262800c42c2010104404071055007284000c4032a413030000702e00f85890301511410711140003c14842c2d1842900012a140800501c030b03422a032080086a100301c03c0c081d02003c410403441d600030302c511480e01c1d080011503c2c0c3d41145405100c0300c159811800e40c0d90ba55244180e00034403080025810101d550b014044506030100000c1c81d050900942e00d485d80d25000d80c0350004002207510940b0045010980c09004200303c1403102d501040c100f040b42410f9540c610085c4c15400c04896100780c1510215181003a03025074460b40014075003000140290f8800c070848442c10401e0706800d8850703050005207540c0c40e40c0f82d0400411080010350340e10b070300120074006413419003c44070000c01c10000c00b9500291000080342e0703001d516443c0c50019110340c908a141019030b171 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 801085386 1250 801084136 801084161
    0x1a12040206220f0e060a05030a0f050c091e0a0e1c050d05040c030506071707080408091008090106080a08070308130f0c0e0601020a020d08091203030c0a0e0604080703060f 75
    0x440010a51000480803503054904d0401e001619a80d1103040101e54001c900546415030170070000c101c0010561810300782c0311840354080c1c41e4880701c80c20114152242c1140c0c0442c140e0700701c0c0b0138000d03d00080d603052034124102c0c05080c84011103000c40c00f5a51481c0509ca130444250b545440c50845100e03d0927100001c9003440203005500381070911603642c0e6450f002c256118052440401c0300203000e0b40d480621640701c8003641115a03581d0f401a0b4185000034030683c2c01030f504000285459844020741221811070b51a450540e04041c134100f800c40340c0c030383c210381101d51002240710003092100c01520b02c81039051520ba11250750308241ca94071121091030041020a0b030680520400a400074684242c40702a064850310303030766590049903035070f0b400000650440e0740d864103240440d050000420350642d029100c1104202c510f0740040c5550320440b980395103401c01151804078168011900302e09003000300c035000c0c01d107410001e840e0b44a650314807004100036903a0364500c0c46000aa044a086000c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 801086636 1250 801085386 801085447
    0x30f031009330e0c0d0507050403031409150d061a0f0f03090a02100305040209070503040b06040506120706020f0717070608130209040812090601122009101a12040206 73
    0xc003103044c90755541001001c0040c0078100350009a52510500989041b00d80580c2c400128602e10b10058041d03a1040200980012400701c141240009000040510f40200400002d138140f4041c100b00c60604840802d0820010070072080722015000350684040d621003e4000d507503a01c2c1d1441c03041c500b10603000f00940002000203039040d150f8055101ca841507000340c2d2000916074070030710100d503940300446005190341d04510100d901801e16911056101740040e003580c20007000d00300050b00c2c00c00281d002100507803041e00b0b0b9240400307040c40500e0040003000403860160f8100c504483d107460341d0b4041e1904100c010300002e030542e00c00c08481d084840c1c01414854103030509050030003107907110040010203180002d02059081d500001c1c018100c8200d03250b04c01e070b8480709540d604140c4050300501490384240d1011405c0f10742e1020619805001c0480c0c40200e05454070f4040000b00e1448074103130700c1005017030020a240c011b803200c4161740503a048581e25a0782030b01c03020001e00c5048112807920481c1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 801087886 1250 801086636 801086641
    0x503030c1518060c0c19030c151d0718020a09051e100801050316030c1e030204060f061e090e061305010f0f050a1203030e0f030f031009330e 62
    0x1d080d0b00102015016141940c001c4621180080445451b07013400400103044c1003001c9000c0b40e0a201310840091001c2c02c0803030b80344400c412650907031081814100441c2c0012400b006480c685910800114800352015414130607c0c01009c0c054074031f03c1c4540750041030500c0651210589c80c40303841080c8a0009d2005410144e041401820840c090046c2800b900c58030114440762610f2a154404407940010840c09090030100c5118120084514550b00301e01d0110010005a465010343c0e0050411400c1ca000c902c2d1801c8001401c08030b500c8006492116580800d520407940722403042e0a4401b042401042a12600003140c05038660b10040c806d82440c1800100d84620503101c0740c000c4079040201444401d85610402038590f0041c49580c0c030f060401449240003034041e800580c41025070b40241d940c403400785030b80b443c210360055010501b510b1002003003100c0c4c54090078611000c1c060b84002046144e00060803110100358002c0890540060203054144440b203100e8260003910000003c40c40c0d60 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 801089136 1250 801087886 801087901
    0xb0c071406091e060402090c0f0f1c2427020c0c0a0b18040e030912070e0a0c080714090307060206091e030304140a0204050415060503030c151806 64
    0x5443c12820344078084400341c0825107100000a805004640040c80070f9103075210b8820070038031644410b2041e40020f100f0f01600c450940f4500181003103103100c03882c1c00d12004011303c40c0130844071165090f5800001c00b01e4000d5918090702840c8060720810b0b030074102c1c4036a000c1c0030740880c2540c8440e50b90f081400044ca0b115604030200b61200c03500002e179000165251070706000b06041c010340e680d845ca42c11522401c00214585500440782805034081034924001780200800d03150745143d01c51104560100030204640d144840302143d00060703074102040054000380000700281409081c0700200054519040c466504110450b16502c200034100c95050f40d507250040d40b2082c0885004100c0c5c0990308840c500003094241c2d02d148000900041c52641c1c0c0c8035a980300050054283c20341c214414102880b0050f16244500350069015050300e022600101280308152842030f004240a0f80050010035900513000074100c0c1f9400e1100c10b42c240b145d68914900000c50307605039080c0500d124000c10322008 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 801090386 1250 801089136 801089143
    0x3070f080910021b04091b0602060f100608280507020c03100209030c091f09021b0d0203180f0306070302210f010b070519050706020f06040b0c07140609 67
    0x244071090354241c1d54404800b5050741c9980f4078002c034240c400c03200c02c207500c010b207007681c81308200b1803040754025003c7c1c00101080e0b06420035504a180540c0c020380c203001c42090244099079101a606082c084081e007002402062030402a00d401000380002c048440e100d442d000e0369100c10039200404010304c2c54049402503503001c070032080340d001c2c1c003030409444803008a074000c45002800103030041542e4505402401401035000301319402200800700380040da10704c1507036080001e2409000c0545c07203091201d1002128518526000800c1c0d014890030724031560044103440070704a460304014641200103000c00d0500c4440c00706181d06014007010000361300d0305039000c1d00c0d07001d500720031100703003100d14100d180700c951026541024006622401080048900d50003040e40500c201d0540384080c20400400100380d5010030100c44542002e50700f40001d6904104184c40c5c0340c003460003481541401d846081c0c4d0307c60301800c8080840350005810040c801540c0901c4014003111044800c1341c0f804c1c8132160784 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 801091636 1250 801090386 801090397
    0x60503092113090905120a120c0807111c050a020a08040e0708061c0b040309030f0b090609010c08010b0a110a0f06050705091e04150f150201020a0212090303070f08 72
    0x2000d1103200d00443e20311158800c2c0c909041c2e00500a202c49150407940035080d0300b02c01000000c005035040700e18622841400303803000711091030b07c0f0450203041050300942004c1480c050701e5000c0c0e101c05400d820141d00e4408998070100c3c581403090b80c0700090a000c904103014240080c0c69031a00080c0040d00b01d9102801c18800c041d103a44102507512203000f04195500384a031100080500c40c0d40010204042c0703055580c00502c2070038184a280d5a075034a145280117907590030740f00d01905204104508105001c075a600100c0c0c80f00070803070200b100030090310a50040c0102000e0300c3d008030b001440309000d5103900700d0351418034085409660300c5280c45003c188040b1002c6480c1400c0c8401b041c0486d0007081074864901c4014000ea00c1501c4005465060054450020350b00c5519100070203a03840740950f0840190029004101d500d42c01e00c2413000040b00b0403054007046a10403c544030807594003007090b0306480c6010b0110390b0f55800503000286140142c80d800707480c0540c04c580702420003128200410307 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 801092886 1250 801091636 801091657
    0xc040213081204120305030c0d110d0509011811150301230103060b0d2f07050106050d050304030b1005030706030e0f1f0207051c03060e1602070605030921 68
    0x40d40d4100039030b4048180d001d42d100d01e10040c02c0c040320100019025401456201d00c2e05520182000a008000d4064892005214074880000a154140d040e12070140a600c004514001c0c000c1d070386481d159620308003503a0305c0a072269502e0496941503030341d110280a4100e00c22142c035a2607586642c0d13030500e03c0340c030080c01c919550711100d0400050350280c01000c3c01c07900b004900a0030074640f4100c0328003802101d1920b07034004e03448110501d0802000480f0041c0888000c02c840c0e1107507a2850894211042078000c28462102102d1460000d6000800c44060b80c1e800194503241c0e072506942000348440c80c1c0c000960600031070002050641d4190f100c10310f400302c000c0480d4041d034102109182c0300d010101c40c0384c0042c000480420b03140b03c0990000d0001521030030845800c04003051030107001c02540c00d10303d80025290346c0104010407071090328035004004190415400440004040e580325400d1041c1018004080001411008180b0001c00460300c010320341d01c050429440e1419107a80f12451a0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 801094136 1250 801092886 801092893
    0x91c0c03050c2805090c07051203060112060b030703090206041a09040606030515040c0e0402030a150803030705190e06070f0c06091202130b060d020327031b0c04021308 74
    0x300024140b64280026100c0e1248a403d020300f808244041800001d002c189079101c100714034000141c0412015141c034040c4103040e0303128100000010003905040403080440c1d400c0520a100503075103142141c0c1c120f81d050500052015140c4086400c034015a0310122002e801072041c4c446401c8110014001360b40c08660802070302d604e0311800d500b00c030010384243c141d012243c01c04078110b041607842002040041d040007121191440000782c141d070303c00c58440080c1074032180b0341d0788006d40d508405406056140091f5007980b0301003a004010b4064042901c81200d4601068490309015520001c05c00c14081c00a581c3d0303510504089054035a95a400c44e0703041c140c2c8100040c0140b2551801e010f9883c1e10342c00b0720a03041c15030204078020782000f010050166030f9414100150f5036040003014191040000940ca0345802140011a0129007891605405e0010660200c80d1004401c607030018041c12040c000030040f000046140030581d00042e0380262001401842c03e4050440c050f080b00c0800049 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 801095386 1250 801094136 801094159
    0x7060606021002070b1801061503150909030219080f0301060309110f0f120f060403090e0c030601050d2c101d060f07020f12032703091c0c03050c 64
    0x81d50413481010005031400c10301402180e149018600300402400f80c1e8000400c6040e11480002d6404500d040c034503001c6990742174208803040c0301000300070040c05032000c1040280b000f910007035118038100d0201180c47c1c0c031042c149820080300c1c40950304040c04245c415600c0b0741c0c440d03002500074a5106c00903079070010310503a21000b9280007501072440200290080000722620310a1020102c078640d0719402034050b020480c0040b1200f006a1403043d400303036072440341c092720300401c03010420000f410940c00c1c4a400c0007040766a90b0454101c801072042844009031703d0b803100344200b905101d082c21002503402c20380c96450030588002402058603c894008100700300c034158810014480e007078808251900a480000c010424598011781c1c01441801943c252202007184a170a0041086611180003400303c1401100010881c1c0f900c9401c0e10758000110500d601c9a2803503581c0101d903450340c80b4504a000c40060024060040284181d00c454803601c55500ca1420769200e40e4141d10050060000030075 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 801096636 1250 801095386 801095413
    0x2090f0a05030304150c050105132006070807050f010501030b15011d010f17070224060d060b0d020d0501020309150c0a0810030807032001060e1306110706060602 71
    0x10318500701e50004000758075142c0340c004101c140059001502090124a500e03203008038201780a1280304100070851404407007038518040036101c18a0a08040d940c2d404d00d443c2c2880e8545400301c1d00c4141c2c00c4414152150100d2814078a0404810715030101075082c68000000c11001800765406490310b504848008030700c03003004451203c01c58100d00502c5581c03000e01111940030386c03600e140c20700b01d034549031105c51f00410b100c0003050019690500103074001d00c02c1c00b5101e150203050701100c0c2100c080c40d9206042c900c000400c240150b02010345420758030704004449a460306800005140d0140c07080c0c0748040d8a080090007034000315940fa449000b0018182d80c4c5044030301086101e6482107101c542050004003013110340c070f0f6004040c819855403035480800802d0000001e009101d2195a03a0581c80d10b0600316119001140040040c0d00c0e03041c41014460184681c1e0b9895214240220010703041c2101c0c1000c0c0c015100c080307400c00b4000c100080000503c90140c100e80706030303030803902290380b040c40605 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 801097886 1250 801096636 801096649
    0x520e010201090b010b090a0e18190209070f1b0f0210030b090f09011808070515092119051210210312050108010c0e0301060f050621070302090f 63
    0xa4004103809200f000500c210100c45000d001c2040f0050138002e0384030f0311106c02921180007a680c3d0129003a0148050042180400a8000040c01c400328450302c19000c2d0b02081801802828190600141d000d104201c248900c0c00412955200440d04040c1d2186d420710b0789414941500907400350380e0301c1c031520b030764503000303004408019034090721242590f80e0340c03005400c440002a01c107032881c3d500e5a90fa0921016800540d40c0c2160040110350b0f40c40c10300b450101c2c40c041003030f680d4103c944000401c1180300703800410a40d00f0f01040d00402100b140201e040f08481c0d11076001e9402c0c4c0110700c205180c001d16808000b400d000000101d058002d6121403c10141c0808588a031180e003800d108000070729409081c2c040400907219060130441d8543c4e0580c1c2d54260b0b10700b40c018581c140e643e00034001501d0b40c460044a403000d400c0e0000c10a8a04040300c0b1104100103008481c080c000018003080500e00e001064840351856400381402410107250040281d8001e0044620507001c40342d8451440c602030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 801099136 1250 801097886 801097901
    0x200c060c131e08030a030e01181101030c02070e0a02070b0109090f030e06120a0c1b0b010302010c140106090507271404020d0e06041406520e010201 65
    0xe00304042251810500c00716011800e02003400c00212a0800030f02d545041000d4010410300e9200840c3e0000d481211344c0c219a810004c0a0740e22405072a10408200c1c0030f403941c5480d810a20303000c5080d4140c41420b926080e2150f0140c45248401c1c0c0800c000d420b00d0746d000d041355030701c12140c00e81c059a0340c1c1d20320005c0d240c01c0034015004152803010403000902943e500daa808802070011814040ba08038100d040c07602c1100e41602d45622940805c0da46603025000120612003001d04801d54249912015048001400001c0c1401101c0641c2800d1164290500d005110254001d1010740c0e1120f0a85001c2c01068601e01c01044004010001001e10a000f20044107002c5107403210241c5001e40d407607032407200d0109598000e5803c10010f00d094020b0f01441400c10180001088070f810a4600306a00360009250700306c894102e9000d01a8802c094184804603c41d41c218120a0748150400319445c0c80c0c103480c00248500404030341e0000894010780d02c0540819030344568160321080401a400c0e40c524 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 801100386 1250 801099136 801099157
    0x30b041406091c0e0603131101090b09040c030902030303040302030403050c06030c07060b010e060706090224041514042d06020304180207080a02100b04090c18200c060c 74
    0x440652100b950189680083c000d081e1501d0701c00c195814000c00e401e81c2c416070f040c20304282000d813101d00717103c0c00500c0507807885801e00e808a05949041c42550241c0100e179481449180c44e203107000855442500400d02213600107056907070324201890069500d0b0301921040f60b05d4041d41e813800b0398a241600c1900e02c100790160000b440c14800d40d50314001041c8482216050290384001031190f40c0782c0030054040e55209040005a40200f4010000c0740180206104086031000070000107035120441503030200c3d42e0100031000520141c2c802600d03503028007555942946408a0009604170003803012a09100b9812075000c6c0c03041d0b520412340740404040c003580001da0704c1004108585038181c8820394095000100060038000c1d160f0303031900280e1011003100c3c0143d000c414505241c1c2c2d003c0c41020621001100d0402c09200941d803a00808a0b41c4d1082601d0481600962182c03408203401811104030280340c2400701034501c00003568a03400c41c00c0c1600d154490311001800440312803089a030381400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 801101636 1250 801100386 801100393
    0xe0105011503051314240702120c01090f060c030b010c0b1b120c09030601061724040c0206090d1805211219030209010c2a030b04140609 60
    0x1c1e41c24240d02800c0c02600d40b0b0146109031003040003042044005078170503130041e000b800c2e0b421020251031403a0359100d41c0300c1c82c3c01102c510074030040c5c64000030301c00b0290b90040102d0f0344907401e0f0b2031203d0040c925500003500d80c4008054000410610b94841200f41c4165101080707802058001120800c81001004001c843c460001c40c450450310307990111454115240c1c103241031403495a076414900113492a40f886240401d68807000e2030140302d40c60141400740b80411118402102d456403a000180141c1d4141c0080422800500200e010303900000001400500c46100c045c080295560700450342c0d4141401041c0c402c240c1e8030b10404606400700b90310300c06681054107110812007a441c90a440f20400c0c603881b1101c00078580706201035003a45180420b031545883c01e0594541211000c0c64050041600c10440e401071361b038001d0011600142c2040d070340050403548080280c0b0140720072044c0c540303030401d10030b0010400142e130705464400c81c8940005560800380c0302580da030b00c0307009544110f150341 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 801102886 1250 801101636 801101669
    0x9154506021b0f0f060708130b100b0a080405011d0c10021f05040b060a270f06080a110901051012020909040302031b1603140f1f0e010501 61
    0x300c80d50090702e041d008054481190894601c141e9103059680c010810307064008a55070501041d06000440c0c1c85401400c2c40c86a03440d02d51413201c40d680e0700d01e8000300701e400390001048944101401c114040c108240000d0303910940050040d207911030454007140c6540c00e02458004400201203607241403102e45000f40641040e000c2044080700b01455110114071036181c145142c420384585482c423080016000040034101b5060604103503100030702c80ca00908609400b003050300309413404004903940034030390a0300c0991003a4985010b00041040383e0030060030000e0104081c0350205108060511502c400103a10082000b8004038070030074424150f2044014200d01017a9000c3d40002000d0030410400516041955002440300b040940b401d81c010703400490001c50081c5940012200070b03050034001c01c0107504190b4003140d036660701e00004040403042c05001d14100800c118441d008c0600e00300f41c1c1c01400120040340081403040c110584144d00b41f002a075012901841118140c0300c1d070b5100380c1d8900 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 801104136 1250 801102886 801102893
    0x21b161202030a02220b010302030f01030b180102180301150506040612230708090109210507060204141315060c05031324090e0a091545 60
    0x803184400c0c1e8140c01100e201600584d01c004035018900741e0410280300303164224180d10201c0f41c501c2211410b0510400500c88201d01c0020400e0440e5406040340f180ca5580c088803960320140c2c0006000198008150a000b0400b00c0c2020455030409030000c0010400c081c1020009005902c11036410800420092142e80c1c8158888017141c5001d000100711855030080d04121001c0700350030414020400c000f4081e10b00d6000800f5174200300030000034004800b29440f8021502d80b4001b00180b00c40d100070410300c2c554011400e842100d41c00100c2151620303a91400803e8010b111500d0038411070817804802903c0c0c0043c450000070201d0642c40d2005036060801c196200351503490280d81d50f110a0003205086a03c12003500041c00030445001f0107400c0300c2c1107080c18803902c1560074050022101c1c09019260806805950102d402c12001c2242c1880707040ca00c040700056201c0e042418149506081b9010a101e1003110784a4102c08000b404041400c1180804400c8110001454003030401074020 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 801105386 1250 801104136 801104159
    0x60304030f020a080c010609240b03090a050f0714010c1e020a0b130311030a05060f0c0c0d09080d030b0105090f120703061b0e0d0308100302090406021b16 68
    0x1e01c0e45900458806841e0b0ba2281080d0f40c2152201400aa442d2082442881514055200801d2440340250203030720076821105d00c01c040f80c0c02105180f50380031000a01c2094100404c000c100d03000000d4440980445810300e458a5041c0206058844491460251755103d03000540b05c0582145100040e049516070a80100d227400100b6a80409646c03008903001a034503000704030031800a02020700d100e00d1840d0907100c4050010500d13100b60444500c90700882d00100d0a41c2d4050300821031080165200c03041078850707000e00e04848049224841c0525139050300180c0c80d00036201c401d0100c41d4030350520030048050b03071225000c0500082003401b00b60804c4c01e00c032110700054034001b00030070007404610081900d40221584181e034035980b5101e508030250707072128104241e403015142c40e03000b1421110208125100844000707040200020000d216440350003451006907074001c2c40c0d02c0c030300d0030141004030294021040c000c101101c07501c0104910b800001e00d4101c1001d8103411081482e10b00f01d81c8511 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 801106636 1250 801105386 801105407
    0x406051b07110d080d02130911070611070804080307060e010b0a0e070c1e0c0914010612020702030618151506130506300f01030f02010e040c0909140606030403 70
    0x402210f6048a03000141d0503801400c458200c4810058984090a00614043e506540f00d62181d03450302040312400004801180c01c401d80103807001c501220301001400e40340c495501c1c040c040d0440480d010038010f10100060000e01d000700d20a001465000c21940d01300d904d0300c00510b90103040b10204002c46030030107256507030000c0d550403d6a000306540e10b40c030810011504545c22001c204082203400c100c4001c5c4400c001c0c00e0030f43c00401403081403036080c845428040c01968140305600c620350013194025011a03840581c0a401e903001c504115400d10301611000484007050300810390464070404107000c140c0c0c45181e1684e00c514106003040148122136000303038812006192005d0020405c1d413038000007808070001010302c40d00e08200550102180720009507021040040d40301c10701c002c454441c0090b5054a4125401401410b400d20060314981d043d081c000340c1260801d15000344c07107a0040c010504440400d03006000d101802030007505e054ac0120f80c2e0300d5011034140041400b0a1103082c0c80309 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 801107886 1250 801106636 801106639
    0x9120201110c4b0108100b07050a06050108030306030c0613030611030612060f010501200136050a0f14070f180204140d060f060801050406051b0711 65
    0xc2d403000d60480403034590039003890400b03105000b00d202c41e04100e001c801d440780c1c182041d165451150302c0500e2502050403400b01c10b203040100c4240403a80e0241e855a5503002031505800b20b55036003020303162080e21490405000d480e02d0b07161400000d503132100401100e205080050103009144641c8007042040d4000f03500c441c40b03144015002000041c951702c9050041c0440380356541d100e140082c1040b807280c1c55480d43c05107942088060200f0102103c1c2107a041d02d109080000615030300c40c414128200152840034100d60038208070081c02c818102d00c1d00441101e01140d40008101c04003c50f005001c049001041a03009542002c0401e00402c0412500c0e0320580074610b1101c40303144601d14140310f580054048e14a000d404110a40e0b10201d0700074001074076001542130605c0c3c00c1042140000418030725000d203401026200400a1079400076100c1c00e203032a020030205855100550090200711000c50710989002e01081030725001d0300344200c183d00030b10485840d151240e904c0900c022122038185 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 801109136 1250 801107886 801107893
    0x6010908151801110c1b0d0807031e1d04050c07030e0d121e084507050909120f0d140c030916030305180619080402100912020111 57
    0x90b42c80c01020701661022840e482041500e60840d031080c0f60411190350020a13203d03410100720303241c0b034845100f401c2149030000491a00d402c2141400d540c1c1d00e0b101290440380b04400c1b8101144107410622220075242419090316103c2940828002100c10940d2400c01400c0705000c07180000f813164003442104032024001c446c030780c034456448030025041d030004100821b90a160140e400c0070700040f01d51009919203070020342800c1070708408259010516a940b0f0520b1a1708444014840300e0030f240c80c20171042c03250b10600b82c0b421030606844070218082e10f4854030b00900484c4440c14001060012a000c4070445454140840903008455209408185445803100031035241301c41030030000f0307220307021650f000d51760ba180001100e41440b07151031030021860306503001440480c3d406819105d003844a07450b00004c19665600040f0540180c00464149849a860700c1f80c1083d4054060350249109a40c541588400c0e0748007912101d240c0d014075880c080c880e0b24540701561040c2c04150075203d0100c140c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 801110386 1250 801109136 801109171
    0x1f02090405010e0f100b1602060903060702030901140306060d150905070309110402120705090a03080403060603140d1704020f0415150507020609040c0509060d0f050601090815 77
    0x41010341e04268000b0350788907094010442c5001c41d48484640c84004140b4030080a030078103529001a000b01d100300c00c540b0040d4440d14017151103d40845500c0340c0c00400b200c000c1e1904200003583d030703403003a298103000803079840c0e04503101014101500d01616004000a08160300881c02c0740c001c0144451066104140c6100085c03c1402403051038021120fa64000c80d40c00b0703181c2041046100d084184601440c81008400c00311120000e007140c0052542c42c0c07041d41d03098a1400a6a070015580001d0100c50001400208020341a4030810449201e9031280b1106680070024035200d41d030340c40071100441d281b18500801c20718800065644035100400605c0d210212a0104e000c445200208105240c002070060041c0307488039509184186c441c1c94038525105c0d041e40450440e009110031207029981302c0e5201001c0302e00401c00d070b806008010380038035210b000c02000c80011700503100303080607143c3ca8a0701140140d40b02d0f24200b000c1d43e44160013440f510f81b41106090340902d004101601c0c0070f181034003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 801111636 1250 801110386 801110389
    0x316030203062223010b01050403031d0a0503030406030209090106020c150a0207150c0209010e101a040515030106030e0c1f120c0f080c0717181903150903021f0209 72
    0x18015141c3c540d0944c100c104601e20101c5085a88100425051010501c01040002d506c0300d2162000d08680015036858003031080411405252904956450b00002c9000b09949516901a1a40720300c120742c080303a1640d8555041e6190402561815000700441c6103141420b2032030320080250160a104403041c80e039803410005810a0b0031580c001c002030224a8050661919406450242c11030590002003402c10721255035600740e40d4800c07105110b0111034000782d01110071003500d004200c06051003038000d098110703000240d4404d0140c03070046403400000310981c907030005a02ca0340e0362003e070001a2107004401c0300c001c61200425040300f0031910400c003040c5035140b4010380400706884e840c0d001d90b100c4900e1b0050a031600040c107801c074a0301c0502101c0041121076042200c4c0c410f00d0003900313659013034040001041b2044241c5194000d408030001c0c03940c501c0c8140720502180d002d14030300e030002d0469860700030588540c44c00140040e4000040342c100780840c9048040801c21049006141210100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 801112886 1250 801111636 801111653
    0x212030909040f030314070816021203130c091b030b0301150303021e06040f021516120807080609060411071403090109173c010b03160302030622 64
    0x30350403200c03111488010020140c0600a4912000c031404106c102403902d540300034100c07078000780f00e270090300803500310720046074000d015a0340c0e80415100344581e20716201c42e56010300242c0380030071a100e862000d40001c402583d44109032100460882c8050301d09401c0c08114090032454040c41d9041d5a01c0440c041c081d50103000040c0190311a80103002075584000305040310112064500d01d054200744100400100391010075880913504440082d2502020b901c0084140640c110004050b00c0c0840c09009012203142e41c0007400701584e40f042c00d40c1e03980c0f0004407080c1c9016102280c10030b02d0347c80411303494501500004614200c28006a003461100d40f26940410091011480190130000c0c00300c242d540c0c400042c0d0040d00c480c203104081c1e0002420300e81c2e61200640002001c085a48158cc43ca02c290501c3c2255445014840d15400c18800010180203107030b0616002d01c2407044074610f044100b01d80c1900c0d0102c0380c00801904c400e9480c8a00401e00314000c02a0340703244002410f039600000c1002 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 801114136 1250 801112886 801112891
    0xd02070212061f050d020d080703020c03250f0b030402131e0f1107020907140f0a0f0f1812060e0a0506010f0e2205010f020a1205010510020a0212030909 67
    0x100c005141c400c2c102c122a141443c1c03540c008902503800d400c0900702684800644602c21903006003d00d544400500b401c0b800d140000040c81d616004030340d54400c1c02c0002045031030850301a8a030811540d992861039000e4848103100c0d1032000e071020320005000d480c003101600e60001e031403035011580d81c0f5001c0401c000308003580e50b1040070700e565400c500d0710f10f41c0a1080c00c013111204000145404410f030006008800d000704080300300b00c401c0c1c58000a40c200002615024000110815215800c4803000390801e26807915440000c4c000c0b11403101c0403840380c15920a80380d50903109803c0da904040d06d910064000c41d500f519000c1e100d2000201c0c10b40c08006651096025101401465051407010310700303807246500c9402c0b1000390601b030040001290007901500b203000d02800e007180c1403c1c50715501605050300340503605440410076645050701b100c44c101c80d02c007603c00200079907038031801000210481014410700507400305040400605014200300307408014441128100007815000a87d00c1070304 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 801115386 1250 801114136 801114151
    0x102403060f0603020c060105040c020a0b1506030c0c0d030903140708040e0a0203011d04031e1707051804020c0703060914060411041a030c060f070b10050111030c030d0207021206 78
    0x1789800e071880e400d0040380d01411048400f4041400f04d260005d6807140e160303802914429014000c0f4184145441240707100c07910207450b080e02d034900700c0c030b1002d40383e04411910407071401040820005140320740300d001c078619072549500c1c4c0c40c4018a030789160382d0b401440302180e003024200402b0a0f840c0766072540c248039010042016070f072913040402800d00080c5880303141d280c3c44400003c0c000020742004a0f80300c0c15103e818034507404041c0300004c031000240c2060141c0711600490902000075880001089080c01c80d0745140142d01010083c04200c2c82908000707400303904080d40c144005a8290000302005004016210350b21002c405200c2c00c0040607101200c2c014205123002c21715040c0b50046a1411205070102c8400c02c2c1030740f020a0b11415040400c91044000044c407007001801901610092900800c8c10b451507d001004410461114000c4902092061003403015242002044451207800c034009076013001801c01011010790014a000c0340d2103212000340d5582d9860801c40e1038400e0302c2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 801116636 1250 801115386 801115391
    0x9040f0b1906051e090d03020f011b0915020f030a05221212050d0c0207050316150807120513060b0f0d020d0501020d14010806102403060f0603 63
    0x8405040041d09210803810740e840d400110303810824260840107070f998043da01e01550070303045444108101e052048043c40b40e80800003c524406055000881440c1002c90700b008004e40c000c0388031320a00000001442a002480e01e4409200030314000360810300302c074054011030384a0410320107031703504582015040c0786c0011400318402450750300071201002d503040c80300c542103074150070700c3c40104600540081c090021001038480307458941c86801101d0b200c03d0130520070003000c25400d01c000d4813442103116661082c802c00003680d40500d568080b241c21502414410030080038031303080036159464010042002d019141c0d05c1410320f4119405814400e0326950072080d0840b0841ca00442101c050150044c0079030341c4142104020380b51038005006d019011100011034003403038504030340079104030310b0380b100840e05080401001e00000c40d000d6050792103100a440143d507491039012550300c0188901b0743c500d4110003030a4000e103854a80103038000c24030718004c100315071640101c003620b1681c0e5102d000043d6 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 801117886 1250 801116636 801116651
    0x8030301060c030210060605070305090f0a150306080c03280b070504060f0c111c0206070b0402270103030509010315060e120c060315190303030f050924090309040f 72
    0x103038184082c0017a440240300c100b0541d81040c1000f07055008543e80201485000615a04103607540003c0803020080206880080703a00c802c800661458100100c0c0040303410148013280310b10f004030b2030324201e0001500034015201d44138031601c40c9151810702902c0b0841c89101c410f000c290120a80b5104542ca5102c0c40e030f40b50300d04040100b9080700c4041003000c000000b001200040e4107450b03098070b5003800311071011100d5840c1d4009010300c042140b0080d88242d00192400811040d041002c1c420360003190070b948440c201500903406024810800784155520b0401800000c1c00348004e0a1407510614002854400080043c11180c4260b00424082483c5c01849402481e00300074000303407628580d0150034170072903801c00304000380400b030101d64141c2001426584c0e6500c4800001c01444a07580703008a81e541d503414054014013000034600181410100002d00310f100004030030081c0c01440c4865200d150707074080c018420160180c007690340d5000c10000c0c6c0303510350340e02d00450f10703401440c140010382e46 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 801119136 1250 801117886 801117893
    0x1809060a0e2a0a090e060613030507030c0e010308030c0a0e040905060402030606180c03041b0f0504050c0301080a0b190e030c060114150901030204180e15060f01050c010608030301060c 81
    0xb0740d10100112048404008070200a6406855141101c072603407030007003075916058002282030146000c94109001d441400100b4480c002601000b140e02403121501c2c603684400061712001c2c007d01000d4100c0c102000840d01c600300716001412407868601e0a44000c2807420005070540b41e42100980b03503035000d0410302095240620415402070411a91200707461904102d88161480c01404090104c0001c00010300340030503151641c0d40c0c1c0c40700070b1400c2c1d090358aa60881c403040181d401030600a82c40c04c0001002c400403482100d068230b04020007000e42c204181c0c0c540b201058010107503680d446544500c02503060b150b02a61f182691103401450310350b10f402540d01c1c6000c0e030507840268140f6070b240654110303846d0903070260300404005400039640c80c18000103030043c0c412a0b020320708071003524610080c070b100380c0c0c0d01c84040e03016074074191502c0090440441103d12020754000781c0c4000038524101e4190b0244004214075003c0c100007181c00380e514080b00c0d0560b00b090f401640410401d440d101d041 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 801120386 1250 801119136 801119191
    0x70c080c0c1003020c0d111c1d03071a280207060e10171b030a020304030e0406030c0b09040908160b0f0702030d0e16180f021809060a0e 60
    0x820690303c0d0440c01d000182280a54030150200c400d0103000a000f0800402d11090144051040d501c0300c01c52410700145070000c0c24404944140c103000509424600101e00d00030075484207c3c0d02180010400c135200c0702c8101c0c91640b040d4503150303803485200344508000031090840c440384d00c050717001303040b5042c680480580281042c4d009244240c603044000544550405013407a03000d101208407074566540e11070414001003d80c0501005041c001c01001081d07103580e001103114610903900c0c141d44100b220280070a4038414000181041c419074024458244490041c0c04441401000030030b000702d00b901c0380b880951042c04904c15035008603440c502441451100103410100a10a0160038941194020344178016421403041040c0c032a44000e488400810200c80010600341907500b1060f0345007040a03414a0358100d0000d0b1900f828180b000034650352080e40d20105100044510780d0000401708075203083d00801480c2e12003410b80020031124900325500e0701c64543c94100000c10800007030031401 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 801121636 1250 801120386 801120409
    0x503182809060504050105030730111f0e15041206020703030b120307080d06030b0f0703050106110c0d05071208040302030c060412020f150d06030b090d0207060503070c080c0c 77
    0x140c2d05140c010001c940b4002080400c484a188c014041d140c0c41044440c0502030ac06000d0142d008aa00384d1400c0c01701d0b02030501100f40c0e003100d07128009101c1d500d440000070b5000314040003042c0301151002032070074035054854101c20460361080c85c2a84803004c0d5080000c007031009403041e0f640401d411080642510a111210703100311900c07110040035446041c1c3d01d00c10101c005001900c003188003204180d8075000200510340c070030031400d0f80e4580859002060074040ba0703000002400e0100000310702e4041c2c001c0b584d4a05c400c5c00580405110705061001340900000d003158207102d9042d0010300f400d40d84101d6002e00c0c1c81501ca60396201d02e0350042601d000e170f40345442c901c00c0c18200000c201034142960b02e2070880764166040d0b4100c200d10740000d5041c0014a5040b10074000c002001c02d04403800d544481d064a04c00c04014655071507040da107954640b152000b10001d80d1004100707004150060014507031015513880c28030426605555581000d402c0800b200f06254080090041c3e00c0c54840c58181 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 801122886 1250 801121636 801121639
    0x3070f090506030a0f0f081c0f0b041a09180d02071d06061c060503030f09091b04121401090303020a17040201080123100f0f08010305031828090605 65
    0x101210241c0c617000709941c55054020182e18051071040e0030132000c0d1040c0d600585000100c61102c48120503e8006003080c0250520307482d1520300310108519003403041441d40700000c41d07218401c1200c5410b0142001010706840010644c1c005078001c508020440388920035190303805407405902d09501456440700c80c00c1140310300d20a0400b0007507180c403140c041c1c1d01d40040801c8042e82c034400d170720310302da000304882c1c1c00094042c08005200038092100400800d141c0703400380d03403c0901c0c0d520603940011034880748503103e071802c40401040003014500e00e104c01c0c050740580c01d1851000000c3e0005401c5074111007080b070100c1d40114940700a90781000c54103a52491004044449286c990300003031102c001402198401c0150030540340d504080b50031300500f0780801a0102283c2202d800c0c001e0096070841340541c00084d501018103600710b210b01155412a54001c0040d41040100f1105007180000c0185141d00035003c000c02c503000e08902c102a01400802007003e00300b9500f003940c0f50f002c1c0c4450390041c9 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 801124136 1250 801122886 801122893
    0x71701231215100b1611121f05091207032a03030507050a02070303030e0f070e01030605070c0b040809150a080901060b0a090e040c03150b01090611060703051503070f09050603 77
    0xc0080384c1c0d019007160340c0c5c14508801030941d40040d15016503c81485614240c001401c0c030788080303050f000010310002020384400f40600d203906e182148000e9030800c40d1420402d03001001011940d19115028104a510a09201c4186003c0344040c00720600b042c2c1c21b140c1701e41300c00380314101415018807079190020b1030351511520b050344010020b5560076062000070700b010342d195034513030b20030100388414003503c40d214059920503540c4c0c0d15a1801e5007028081910440d00d0400171407142d5000340000501940d11004100c4c1a40c2d9a13100c060042d04806456600810b98418194650320100c00612600300c941d21385110b00d08100c4e407568211a403507042040e10031010400710303922a0300200004121086000c90100e40c1c0d80d81c0c50003100b0b118442e8002403100c0c2c28507034405101c184680001c280c92600303076611040140e4510080b10b03107011281c003443c2c00740c0015001c200421b1203a0001e039030048440c1c0c0701d0b10b000c95600c00401d01d49005035120003040c4c420100103120740d4a6a00405802030b0049004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 801125386 1250 801124136 801124139
    0x50406050703020414090703150e060f010503010e0c0d0906050906070f0807120e01022808090111030c0901090b0c0a1b1d0709030618020907170123121510 68
    0x204580d103014200e0582c8600804800100036501c40d810131074501c00045d41e250703510780e40d849540ac01d45ca019075802d80702d0740c80b10b80c19036055403045054904a070051404010140c44030400d20070f1a0384000c0d5034000e40303034581d50898080b400a01405010b0b0300c4900050030325141103000140149441b1694404000386141400032440d0300100c1144c81d03940903400000c04618451400780284500c0c20800914020508028003a000c12243d403024641c550301c0b080c0440e030b203440b61076081700e440b441c0c2c6a18080082c030210701030200781d002038150645e0604080160944881504803260820003a0b440c59901110114003000100b05c41940d010450380240b00382d503820a10707039100441c004043c00592903183c0d8000340e0390500c2032401c54025a0030000410030121144020f211f051609034083e40513000700c0c0b0100305203a200e1650382c0d813158802d1801ca100f503402d1440c0401c0190400505170351302403443e036035500c1940c0c50099560000e4000c00050000b005030901d11001800001e09081035288200070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 801126636 1250 801125386 801125399
    0x9010e0c010f050702040e07031208010f060e0409020a0e06032e05130c0816050d1a062106010e0f0f0a200d1d0309010507020f010e130504060507030204 67
    0x40e5a200c00900342008044070b00c4411040360203000b040006035000c0d00b0541c0c02d20f8404404034a88060703c0c051041c803400f001c00340c0d4040c8d410103000e2140c0303010068103400810409102e10043e00f15280010400b24002c03043c1c0e00045d5094031070b0b80081c4100e01004c428044140307010014207403001500d000d03421039100006a80055051040c041a0712940c84600081c10036061340c2002c0c4280fa84110088034641e00c032186580d450310031601c0140e0807080c40d400428035103010252815442c7d48581c0b0070f00d4100081ca40003200c4c100161901b504094140103220780751107403203008401c020100000b8900b641c03410103d05403203600a807074031240101801c1840420071030504000c0d4408814140803070340f524940014001103054442c5c2242484000c144103900c41403d41004210070443c140100c8000d060f0301e480350301d078480d00207050301150040100740018204003042c44101e01050600784c840902c0c160102d000c0c800032000c0048141e5a0300204001c001640c415950407141500d021402c082c10a0b0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 801127886 1250 801126636 801126643
    0x10606090b040b0c01061203030912090e040611041205150105090f0c0703020a1a0f0601090f0e0c1303080a021203160c1104022d121b0c070f03020909010e 68
    0x144440c0d0f00700000c07020145070094000a00038003800f0482580010241001030051064800484a4444240584004a20810700702d410760300d602c1c1c8111041e0b1035941c4c03030313100601c918a001080c8070070078040091303a90340c80e421001d8003038001c1d409000051000d0001c002400e20581040c3d00c6040d803c0c0c01c0c017441211005600703a01144c8030b08030f03503070f904c0c05410264981111200001c003864001003a40805080308407100c0d00a07004070071145100c0d2290401034030016140d00072800070300c460b05020010040c0405905400180f22010700d4907000440075016074804583d0410703500a8000901029440c0e410020710b00c01c859102c0a00307041d0300b894000c1d81018401400c80e14100529000c0d110300780250309411a0041400400c00c55603500e402e909080c400100004a40b09025161102112042c0c28802c4440c160305001e04187c0545c0e41600b0500000240c020368450b1410a101c0c0c0e8071106010084400a401e81102540c4080d203144100319005e10010044c06103641042e100c81803402000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 801129136 1250 801127886 801127889
    0x50c150d050a0e0319021c03020702031606051c09140f070618050603071b050c0a080309132315090a020c1c03090b0c19020a0b1f090c02010c02010606090b04 69
    0x1211424918020f92080307240c1883c1c7e414100302d0150140300d42154a40650003003100d1803003602170f9070203c2c042181c520480b40840c400c00021420400c4100c140100d01c00e1682c51907603012600095004540e11000605100034855581d66400b080c0402403e00d0104059401400d2901d0180040030318100b044070820b100f40701b0ac88c002c100100208a000b0b0081881e000c500061910280304c3e0781c11809e107690740717501c40700b142c0f07005a680380c0000c511410b0200480340106805000700100080025500009100c20050581c5007030984032090703500c000c0030756010b02030880c49004440034220701c010000202e0740078184901d150310400500e02c0c0c00340f012524620000350350790100c071b1840580000790060f2180550003400c0c0c14006040298480140018010394601c80b0306c002c86580e8055001c4e0b94503114000c003c1e120b00101400aa04904441c010150500c07609084080a41c3d556807102c09441502c440e45002d42d44070f2241c040304035824441c01e0014901d600d040a103052801c003207060741303200f42e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 801130386 1250 801129136 801129157
    0xc0306020304060228270b030c0c0f0f01050610120e010f090f1106070c0e090109210e091e0414030304030503011d0403050406030504050c150d050a0e03 67
    0x22000034240500c95045e5100308004220300b401740420106003041d8041079407000e0b40491007011104184d481e41c000c00901ca04804100000e1842c188100b00070a600014500341c046103080014010380c00040c403030020018042c02c02440c00c1c08600000500b5140300030300c000c1c0180344900340c081c04184e100141c10020030824000040f00c0111030030b010301601c000b007a0360350b203903080ca40794104100105401100d42c501170941400c1043c554810007005104241c0054295204903009020b1002d01450042c2c100c403038540001182c54080e52840703005030f040e003048000c2c01c64401594080780c0e08121f500d181500c2c1201e42020600d0210074801c0e04800c3c0c0d030380841c0d505060740c000178100000303480020000e6044800b200d49920b018a0001c100394024042c00314a0300c20051500c60b9044207201d032038043e950540f42c1604003810b0035000c170001d05004005440703a200721500c140c4251240203ca91410405c4880c1554403a0285030b60020b541010b852290003c1c03802ca4540050741020041d80d515408 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 801131636 1250 801130386 801130391
    0x60306091f03081306020709050108070512030d06140f011106130218040c170307020102060f06130501090c02011a1f0203040b04060203070c1508010501120f020d0c0215040c0306 78
    0x10445503601403841160002004408005043c400c21510b138844441221aa0307402c0300d014a4031000080103132082841160725a9020351400e111514160032440307000c0581c442264107140d841201c2c0c60a0310490b42c08208001e207405c00307010681c240105880c80c145420f0030401084004000090390320310740100744052201501003540708541d50f881e1a0405110b504001e80c2840c201410b2580d425041c52040c0800701600d841a51800300c80441942c2c607494058000e820541e99200490001d01c07001002298040002404400000c02512815019007040b10000415121041002c1c0c00c551444a4204200e60200099000c903030b11004c00e045098001600c2010003485941d050746140242c0e0841c1059000202d00032900701da0010181c030009020712204121682d450a4140400320640450f0001070782c010014441940035625a8040324020180003405003507007000142280c0244a55000c0e0301d4a4240c0c18034078580c100120328001e0300744224580359042682d20b01245614520004114a4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 801132886 1250 801131636 801131671
    0x507210504151e0207060b040507020601061e0c020d030c020f01030603020a050609060f040306050702160803030a1109030d05040e15090a1112040f0c0e010b0912071a030a050606030609 81
    0x100742d1100b1810500e107201066441d4581703413400c03a01034402c016900d4003444c905000240342d9480010218101c50f403544419a801202d0340341c1c00c84c00d49441c240f010034065160100c40041e25513541a00741c6900980e600810000c0520410107810b44440e070080c10107050810034009651100101021078208070ba481d81e84004010200741c5a0103a081d0114440b10045000030900160303400c8a8410344081e400da0308074103c15901d03449240c40c1406007100d80c1d4001d000080621515a1007800e006100d1719901b81000000740000e881c00f000400c0b00000285d011030304020303564800807d15000004e001282c00350034011004a0105800100400c96080e25007542102d146041c40403518803403204001400c40d0300d400d081c0841d0720800c4140840701d080300c002001038900e0090342c0640c143c0f0b081009952900c8080001c100486081c4016a1210f02480a0024660700b61102c048188220050300d0394681c0b501005246c21110001c0149005d04802c00400c525684c5003440190701c5246000e000c070501 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 801134136 1250 801132886 801132911
    0x105070e03162d080d0318030503060f011e0306080c180c1813060312080609070c0615061e0c03140c030c060108010b19050d080715050721050415 64
    0x45284240f00100384445100124036183c0106840800200d107880c103200300d0300c2c0c00d4041903100713100b810007800180c41800851440c0c03428000c07400001805160803560100c2030071240c05070300f00418094002c00d590351010041c041040c0240c50120404a915944e0349900c800700c0c91403080c0041885002034400200400c45c41ca0302c1c86044100759015205010040b00c019800c0000c02090200b592070a001070008155588514141442910060046405500c9403081603400801254007125030303507198102c4c50003011004031090000c00190b95460140303202e1107182d243e500b050400500400c8030103034440b80400d4012404003070381410310301010b5454001d084500c0c114001c8c1610300d10940120000000c142d035054100c5100c0b95000c07100040505410000d0b600c48840032b124894002c41c072801360b41d01081d83c03e40500708481c003509111090319002ca055804942c070444450004ca03654041c44404440e0803014108091251902000780d070403d170302c80d1200300f514040d40580b140c0c0c45808541d181c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 801135386 1250 801134136 801134189
    0xf060a110c121b0f0102040f0506180f010512240a030b2202090a09030e040b010206130c0f030c060201050a02030903181302070b0910021905070519050105070e0316 72
    0x10b442001c000d580040142034104c6000c1d6019125084910110042c0801e0307915120003225044d401031140020300d61414824060002084000c0d241404010b2007501e1103103000c1e033261841a1040714013410061104e220644042c2041d540d51030180048160031310000d0759822500e60480010381005003400001980103010741e0808a0094104a001c0e081c00454004e40c0c00c0516818402e844203880104184240021111070380403950041c1e00210104040108113420700c4102c900580c1144034280d250f865500e0640c0e440e9004480088440d1b0040040c2b43d07081c0f1a44d9040311528409515504003548060750303902aa0f882044100a40b800035021540e80f030700dc010003c22140c3c0150740741c00840c20311101036141210016182c2c01009580880c1e0354841c42202c001d1141c00384540c901030b60350581100c1d25086500201d88610611f0200c000300340e4100c0011990078030400000c110b902c2c0c89200148000140d440c92400703039100181c841c0e8a80d041c00c0020701641c40d103107100d280c1006007a15a404 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 801136636 1250 801135386 801135427
    0x20f19020a05120c090106030b06270307240302091810090501180e0303010f0b161e0201020f011e09031215081b0f04020a03020c0f060a110c12 63
    0x1030084101d10094401c01c070100c1c20013250841156035040790b0380d8034441581619030300703030425900030001c00c450081b6a404041101c400e5030101c050b042c5410045021038640462078124500382d00110165030300d440702ca1600e440006195203015800e0030f159801140a5050b1010010090040680049e188440c42c6200301c000f0000e0890a12003960345180010108030103162980b816414108200610391000040302e041b00c0b907070714080c1010707458606031140702e40080d8846071200c20ba1201070300101e0070900c0651001d88d0500030b0705030740590500c006803a005c2d11014217803060341006543e545225100700030b00000e462408010580300c4071441c0880b00c500000c1c2109008914092181a110b0718a400c02000d40c0c1015048803412044031000c40780451082940a27807149006906680307a082940103040c02451a040250500b06d2001a0a090034a600819187c40e80088208840c08004d4020010581c1c0b49142c001d15144800070002d4a9201c00f91030007404250009400c2100200e040d8680c8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 801137886 1250 801136636 801136639
    0xa020f01050f06030705090f07030207022206050a050d11130e012a0912080a050c060712050c041406030912030106030c0801090b1e031002071110020f19020a05 70
    0x1c5440c2c400d50b10201040203440300c9000e40316107400030401d0b01300003001c01d0107500841181d904070707624440114040d52250070300300d030803929801d2014124180500d24002508800e0400b00310a810641131004568443e8001403184208407039071000f0032811410b90741e8064050f40d240c02118510100c0741c1c0503044d854404c0d10f0a61038400e103000c03000f0032450140518402d089070300c0341b02c80d00520f084500308060300032500300c03007200b0300711600044003080101034070082c0d03080040c00c1068209109040550407502e030307008901c189000304401c41c880c0c401c00b94414008480c1c41e05007030410803500c0300480060407190280c0000008107000309400c00541042915000c5219500c1da140d08000b4042e00ca4883c0c4080440d8a03000003041e580c280d4050503d05c2c110103232804114440380a107203400c1a40441c03426415002e24081099685064002010024094100d40c01e1006050050090306003200c80d980003150003029943c00f400d41c0100c0c018003000c0b0703400d4a81c00c1c013410b0381c0001080544254041e5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 801139136 1250 801137886 801137891
    0x230910030c0e19030213060608011e0e0c03190606121e020304080d2909071107140306010806010e010308030709080a0b0103021f2f0109080319060b040b0a020f01 71
    0x19054424541522410799100380e60501503004c1801c0600d01f40c0d84c07d4043d4a0120708400018403800901c100410442002d2071072214100307035501e03041e4510400070307a10000000f5000040000c02042c27200201c600c1c00540300d082103098038041000309841c8480519400d01502d400290b0380901c5450b030064502c103d21941196681082e1910942581c0584081a2641c0c2068605003044446420f109940ca9201c10304680380c00d007803401c20044031401070044c410722021010a1344880b2040207010041d0040000038004204400704041c54040c6c140d016007005d17030141c0300602620340320080320340c110703079000041a8690b262400140da60310495003215070781d441551482018001c4070340d1a01e04030383c001c0e00ea900c913a805144041c10780c04494175400012940c0303c110700c8004000c0c00128900b55161b600845010507442c80b246096529600e010355807520048103001600080100d4142d040400b450b0803c90203213842c103540c03854040c901c91903032030318408210440c05600a02071041240e82541c001c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 801140386 1250 801139136 801139159
    0x20a030b120601030c051c0b041b0b18151908061203120402090915040818010513031b0902220801020a02070e0705090a06230910030c0e 60
    0x60080104041403032003210510000107035010040361407810b0b607401c0406074411500305070034007050490480d51030803125000f62803900450a07400d402c40c061480743d20142c00e4868030601e2001e48001c1900404403021040000840ba001c1e896440b11300c8030402c0e00d03d2071400326104121502c0313001e64071405447c5000060721801b807550100d4458802c1108a400e03951404040b07120b9640c0c2c0c001c0809401c118001c0c0e40205000d85000f000c1c642e4419080000c0b40d4000090211004070000203680464102d480840d442032030359450700669004c9c100070318009040410403a000d00c10110140f00c0941b5500d8070289a0000c180c05d8444080641409070003503668051145043c0040078141145100001288101180c032034818022501d007060554001c0044900305240b030070b001d00001c1d29034024050104404c100d951900d001840060071585c88296462030f65580000801c06545a400c0402008011214107a51464074031100500a45070006440d200d00d0015560b40c2e00710107105601c00324190300c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 801141636 1250 801140386 801140407
    0xe1c0819090b010f091401120605040204110a0201230906010605030a0b0901060c0203060a051302040209030109290115360b0c0111030c070803040503090a0603060e1003051b01030f02 80
    0x5046080305c03a444800c0105003d075071000b03406100b00303005007584100b4601c1d42c900840c0041d004150080d00003000090351100c502e0399050554000082000542d4580c0100028108801700c3c0000c0e500c003000c010740051400140158880f50140106001d0200200c0403c0055440d0b40c060568008003520028071541c440401404c800c0306204120b10a211301c00029041140501070f960041c0503402441c01900560340c20031010b90820b6031103d80540d80c80b08d02601040030b0503150301200f040c1424008602100380b00750400520160844040c460000e84414805648280c05d12044507420b04c0701d0340042c0741207180c0e0034a03602082c4441c1100103900340124014403060010400da0700c50708001c000c0700c00c4030072030402680000c40302c45018038818081240864070400065078000d05c10410b40c0e2401c0480000520340b585940c000c04006580d4203828090600032000140e04941c0d0100c040744800d186a4400f5501d41003000c41e01c14203040d62880c004140d009030445072400d8050203065448480450 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 801142886 1250 801141636 801141659
    0xf0403021e03060a0b01020c01030f0b04050f01180203040b07050a0c02030708060106091406040303080603070e0c120a0b090a0b030a022e0f0c03051305030d030e1c0819090b01 77
    0x260900c00e02601010650144e150301c9a07241140068004c0c1c18220010710064008222036900011103d84445600c0d03030a41d11445840d02c40c900080490546506103100c9400428040c0c0308032000520404c103000200c1c419414040d88480b207031415a980d8501c21000b1540e485060800940502c17505a0101d410400403c1080c1030b1421681c6500741c440c0d643c0310340380b8180207105089400810421007400460f10809c44c2c982c4c041d0001d403c98541c21365400d0b03c091610012901d0801444001c030b810040800c01c0407a0359041610420180401621000003c220303d2010f0000d600a80d030b43d0364200f80988041c084490801d800602d02c5540503000114543d28410b1074005103090204000c00c0b10082d40210204110005183d40b4541182169030f002c3c2c845600000d4482d0140f8100c0c98006104da074204202d81c8451202d590100f8040d0b030b030000062410a02d280901070b220716014079044007542c0300c43c000d940248007884031155400b82c4c080c11070040111010203054942c002002140f80310101c0d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 801144136 1250 801142886 801142939
    0xe0403021e0703030831050c1f20100e0c040b01090303020d0806042a090f080a0206030a0e1c0207050d2a050907121119050f040302 58
    0x5040d0290440000c25020b032200040e010050204007940040390400d010700107504c0e00e19800c40e02e50040644109440c029044101004a07010b900000707080c0002d0610b035040c824503044540d603c03050550b01c680d02512180d682c00d920f04104034080104408071a003003107014000c581722201040300751540042d4a0300d03022442900d070b00503401c0080d021f8003035205102c01005c494159010300100038190400f100c500744041c08030350340107446c1c00c600030304211241a0301f0405150b207101c0c044690034100c406070088045a01140090480c202c040041d24804100501d0540e070440c1e4071540c0b6a10015504010304003d49d81200c0b6229850710103501100019200000302215000c03554502c3d03403141004501408640b0003042031400038184003020500c21031107035200d8840c1d080c05010940741c4004c108507010444040707000846402d4002e0302d4010520541c05400307101400b07140340050f00100c550101691040d0141003020019800c442c0075180015100079642c0101200e190403a400002001680351 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 801145386 1250 801144136 801144163
    0x601032307180f090b2a090306060d171306080901050118020a05041815081b010305070c4418010903060f021803010903020703141e0601060f0908060408130e040302 72
    0x31501c0511000301c0e24241c1f5480c03a0000d004165030f96807202409282e4850b0601140c8842c1d24402942c1141d0710600508601e21000e9442d04100d0b103003040060620102400308000340e45044014000c11940404869441d0010100135a503500d41e0b110843d007503c2654031024880825044410500485400288103c3c0c00480281c0c134450300d4044250b199043c00d0800d90242c90040d0380c0d2070f55035000b5001181c0c89040750030300c0c2c00452500d44544e2400c143e40340040b280380f419000d10468000450120b01400207810004201111246c4c1e46000345100d20a00e2030403c215941500e12561f10404140d070240d07900c07103410b20141c203404030444080d4106038410b11070f000704001454540e090521400100e203030035a0041407510310716243e08141c45d01c04105243d05004a41e08082e118910182420010803114020403017980740c03441c024140b0304902080001c0040c48a010070078a240001c540c2c0d000350700080c1486c0d85001814000018640d0395000d0f0381001102000c1209040c1c010404820040c203 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 801146636 1250 801145386 801145441
    0x3141b07180605030d090e0a02070209090c01030c02030406200f1b04050601050c030a0e0105190c0b060306010b041517040b04020f0609061e0702030601032307180f090b 74
    0x3c0b6001095100c401c8040c40d0800110140020894240c1281041d900310140150051500c40d181e0040307024010b04035184665036000845500c103d5904d44184003100d800c0d4800b40d420a81800c00003408001100e0424242907004503a101b40e0000070b2192882d11140c00c0b04898a000509603002094110a61058421031030031300000c520354050011211036420a0000c0c1d45050004801960801e11600703025040203414080c1d40c0d00244c403040150040d04003a103031050741c010685045924208002c004074000e401820041008107400030a82c4c0903141814149090710302071003401c0b00c2c20394040d0f0214207015920400c1c4018002c060194900540c02079401690341c041d240300b40314252045101c03a0b1740000d410003405010700d0003201c007203181c000000d007400d20300401c13500020b01e0480c00fa0400d85081503140b03403445240b880c140008590b5031145000e48001440d003e1400e404480c49420400c5443d100d8100c07a2080010380c1c071020090340d100c0002d2040d404c107400040c590081e0a6004c6d03803401c4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 801147886 1250 801146636 801146639
    0x16081c0810030816060e0102040f050d030e01350708091204050402090f0a03030215160f0e1311130609050307062102040618090903141b071806 63
    0x24030030645103114a600c6a4000e0699245940e03000310f0358411980003001640206030b9000050b418090680d02ca5002d00000d42c4a40c108090490b844000e03502c002d100311104080070000a40182894440079401d0078103515120b401070008a0100e030400c0c2241c81d0340803980c80000d1000290031064016840782c1d803106080d6a03043c8840303071345003e19031000c00d144406010810403880c084d002042240005000c411003c0915070101740d0a044580013180903802614440c0700000c0b15045e6254048a900c00c00b088101c000400581400181d1440c10200000c070034041803652507074031a0005124086008005c800182c0000b410103404c400d102e0344180543c404c00064203845203a000060b80d8009026041462a21509030b4071740e42d90710441c0c0075024010050351543c6045201400c020080c139110b030b000b500c0707c001401c80e0400041d00070154652800320b000300803a520184a01c44d00b140b46203595039440c0203490304982c2c40c10354500c0808501c00c002011651018000b8403807a100f49000f014011756 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 801149136 1250 801147886 801147943
    0x19030b07030603060b0f090a0203090c060c0f190b0f06010c1b030b01092a0201140a2007110f01030e011a0310060b0712050403062910050702040b031608 67
    0x1e400c5040c1d98480d2050001c107055001949c0110781100b5800704450700340c00c07405c000c99160380020710b200e09560000c68181081c0341044c0010910034044406864250941d03a135450a0b640000d404042d030002c88500003080d507401881c0622040b0b402440c19056458140200303a5805140d000807680c040003800002003150450050000c030310075010004403601e05482001d21000845580401199210b21004240c40200303a0883d01034038003500042035006030035405070000e400500600300d11440400c004ac0c04114004600060303a10125016400e0400c66401280940388039a45843e031546000b8a9074030f900d041500c0e403100c8140980031742d80781501901c4c040d4101c84c0c140c0315500303500300c041080c40c00140312400400f21000403410114141502ea403514001c55a0041c88800130031010b01c01c0403001c3e10208105600100111048417030320b0b48008006125000b6403030000d0140707407140c8a2580070364040c800a40340803103c84c9a071600070346c3c036a0181c4e83d444c0c0140034102d09000102000208 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 801150386 1250 801149136 801149149
    0x40f060c020115030f1713080c0a050907030f0617030a17061c03020a08030f0618070212070609020411070309090504050a0f24020d141519030b07030603060b 69
    0x4081c41050f00074000c1e146407120400f05240700e9045806110f40e10304011140901c0000e0f1081000c0c4080d04079806080131481c07450501d02020710380c030407007031700c0d10410003036584285140c0e0084c1c4a10780807034018030f148034490240c12250031028403005911002503000500002901070104582d4408801c10240320018420a900740c0c0d120740c22081902d20305210300480001d44150754840d00c1100e9a19510392507030361403a001900c4240890200c0c1083c060305291400001c80d160048056245480c249900301964440b601100c8a61041c8086442c03c103000d05540328003541c2e50068010311900403008203414482d07214100071004200700c1800070400b401e8a210b0144101d0307000c1e00902c00c1c0401a00ca200c4a0014100c044506900490205800c1030800f4100e08248011000160704c0c4d4140302400b9059546103074507104002405c7c2c040051280348402040000041916002cac09910200129070000800b0b8001038000d075010703c10b0001e0698035601460440f0300038201041f400c4020b0040101 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 801151636 1250 801150386 801150401
    0xc0f0a030b16180620011406040e070f030602090108090a030210020d061e290f070f170301050405060418060b01093f020d0b0406060e040f060c0201 65
    0x8055070401c00103a5050110b80b140e414522142007404800c00c40304400c20441a25401c150f0000f6540d031007094030350036041011006080468028047c038260165000358014005100e10301c901e40750200d01401200501c0620050b141c0d06588101060f140d003405c00c0607501a4507283d002445080004002e50408244030b81d0315581640a0304045105a94903406500b1142a000800d90341d05030000e048a001e1202d01c400c1140c072072110b0542490440c110b600615050f00b0b800354020031402c58070500d07a607541120401c40007c450f1070784610340d50900090144814100a108540c920404c0c100301e4445800386d4100c43c0b045030b040c4299951202808142c54443c0c60341080500401851400900540c1180104141c1850500c040710703555801c00c01e200343c88505080c607141003081c1c2d100070310f06c2e500b0a14840030402c03100e150030a0725030b9002ca80072074901e2101a00c04419400400c2c2046036541011000b0161800101014202418000e50303030100075400302e84081ca001080d0b007600380107000740c04 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 801152886 1250 801151636 801151643
    0xe10091205090103020409020403050f1e0a290f10092309010b361302010c1104020a0504092324060c06010503071a07060b030c030d020c0f0a03 63
    0x3004140c000c08269100d42144080c541455000d010100d240c0741144081c0000310b015000a200f0f4a250b02d015900340304407145083c2c0740f46d124150843c003124000440b001c1965000031112580f4000043c00000403199001c40602500090306106000c0e00b00c0107580d0164040f68800b035000b507510b00381c41c0101d0b51415006c000340082d41404403800a90320106a0340541c1c468004910051804000b550300b580000703480c814000400d8a09488809040d4140740c0c0502c1204000b2950520341c0001c00420240c1000904000b268101c0350100302e03c0155228440318007334000d6480b05c0c100c840c0a09240c04c240549000d81d40340010000d00803900c0c0c850012084048070791046181c03100624909072001d6840181c00e152003100000c111900c0700002041004500300240c070055041c401010305000e001e0340800c003005010151040000541000c540381c03181d2100c00015400380500100341400411560254140507504040c48c00580200711904400e200f150200000c1144c00c0411030401020701014 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 801154136 1250 801152886 801152903
    0xd03060806071b060906051e01030f02150c010c0c12020607080c21011e06050708180411070609031803080904020a091a042c040f0309050301020d0e1009 67
    0x80e8105016210200b06079541808203030010a40741c035100c0544600081c12501b03250b44038204240c0f04d0369208000384c072075605030b147d2100317524503100c104a1010121010344180708510b15078000c040c40700e08603189441404007c0c000d00740050009846959181c500750786074520b0010129000d8404900760b445500140c444003002e880e0300e801802942c104907417a082040c21079a80000c48100403040d54000c02d09109042010681c3e450340004c0c0046c0c650240e014004140000000600040251400e00c40420b81e8294803404001c0003501030711030400032008403031000816109010481d00302c449168040c1d101e6401ca41d8140f14980031401c003038803010300001310078404881c20b480c01da0024040e071600b030b1406416080d15428000c1c0d00101c03100c00f04803000c000040c208886013641502d032494055860500d011072100030038a0050030401000206000f01041c0c1c4502014041c9800101410000c0d000719101c040094111004100e020003440b11803081816070400d190841c0503d4444983c0074168 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 801155386 1250 801154136 801154141
    0x405010501081611120c07080a050a0b040219120311070815100905070903030e100504140a0e150a080f070308030a11120f1003021c060906090605090d03060806 70
    0xc005280309400460302000701071038190408078410172180b40c000741d10f07a1213560f0701c1c440814100e00d031001030760000c02c0c07a0708815100f0000c1900400d1178a81c154019075022400d0381d40380300155544030041000e03050741d2110b0f00041509041c000c049481c99200c0d4031b0f2030740d10808141d0002e07034404d1144541505035100d501c502030700e81c100b40c05643d00148410b1000f81001c0c0c0710940714041c0c4000701c3e64000010102031080040c90f6001c1200482e44506807101c01c81c030011110000c00a200d01e028844810310500041aa540c0349c40c0b91080c000e00d048040320301c0c2c904107050020041100340c4100c51045107404030204035200c02250301d50402400100401003240b445d920017005410042c0715010a550ba6804602d600ea1010000c0c001c071800030b40c0c1030060345480c01e80c0e10f448440181c018020358042c05018001a1190300d0800384e428000aa2900c01d52607500d851005450502c000500c0d50f030512140d0010411142c000030f0154580782c05454501c1ca41703440031011a10317544180041c07a8443c201 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 801156636 1250 801155386 801155401
    0x4050c1b010e250e0105030d140712120e070e1807031a1b0901020a061a0d0f0c051905012f06010801050601050903060f0606070c06020d030b040501050108 68
    0xc081488003010300049911a08409494140b84000c107207100c9210305102c10000c0c5450800200c400740015258080a650500000c65603c59036207030440c0034400c00300162180ca501d0030b426110250781c425601000c0c9081d0000060001c0115000c59420074241051054610008142e80c826070b110071501406640e100404144109a01c0e60706a009006020010002c0b541c03080c0108400c02100c8040340560922940c0c0f4160a07080c0040080349160500264845a90201e110104183c001031f01003511b0154000452400860301001c0d6071120706d51108004005e00125242e423210701500b00c2020103652002401a288680c10340078821181c01d240c24081356006641d40400300c021951002d107654540d01c03c1998030b83ca823050343d03082d541c4071100400c6070003400d00400f1391010082c60518200001e51003c207a44d540c01400f070b52490206000042d045132a000c056903121a00882055a51682c50a0194a07500305044040010b82000340c85101e500302802168101d40c0c2c180e480b10083d42d01c428 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 801157886 1250 801156636 801156667
    0x11509090b04060f0b06040b03071b0201051b01110d0e0f03030f0417090d0f060608030405060409020c0f0304030f03020705180402011d06130e090d020d050f07020402120103060b04050c 81
    0x96020b40c0c80307561401d2918880d00c420001e00080c152456601d40d403404e1040c40030b05a00c502540710340c01101c00307540bd00c0040c0d03484401c1d9402d540d02160a0905100218001c0d40500302c640c2c8407880c00d450101d51300400b03084d02d400603070015070500195150ba01c41d010b040d503140d00c005c03182c02c2c600c0c80c90300700410005011745e06100003150410041c1c6080030000d40001e1410b805000e01a034086d40e01002c10410301c00c1c1b5119040c01020404002e514141c60036002c01c94901681c85408121580440c904200a5092000f0011404803405480d640c580701e01e413003003800681240c2900141300b10400400c01e810921070f0300c1c2034000d04c0400c1818640d035035030044880b0202d0100010920742c1000c1350003010344911011307084415040301c00c15140c82c2070020103059080000c0c004407095000322078104026802103002a000da01c5840d03c1955241d5560300c18113580304e6040004d410501c0084c0c1c4004003180c0c000300b0b44c1640c0c80340304180100c0185904200a550040c0c40500f03401500700024140303107070000d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 801159136 1250 801157886 801157901
    0x160f0f150e06030f01050414161107050d06020406020f030a0516151109040e1204062a050c15090108011520010606111605010804030c0b09011509090b0406 68
    0x81c9404014025010081a01900140e807103105051081005009a14090084110b015000000381160340381c228030031001c0c1e85800201c2d005101030346d14240c0401c6810f018000103448064241401070f8020f103004c01c02136105200f04001409403801e49010f01c0004402c4418030300c010740e98282400400c018038a03030041500340c116850980800101600d041ba400754088400d007589110307488000c1d5405000603601c400d081d000c815000302e40d401f100343c60048166010f503806868013000380307042c0c9042094103408240ca40c02000ca140d200d640100800010340034401b1605513250b6603d5203400c80c180e0300d00c0c0600400c01303000c102c005005014080302c00030448000a10340c905200d404680702e035020205103804440155694603040d09112440d0810251401c4182c138000400a070040c503070740344030402c0d46c50203214100101000480d060601c140010a03140750400946100ea0801c400880e00034842211244416000c030000010110b2851050034082c41d004014020319a4556035000d0080080 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 801160386 1250 801159136 801159179
    0x50706021b0d02070602010e070f090e12130303091706070810050a06020f01060605030c123301020601090218010c0203010207050a0305041806140907020717160f0f 72
    0x119007500c1e1400a0400141c2c029608580240880b01e08000e80282514800340c07001c01d00e54450641003040e0501d25140b9011101040d4000403040c1d01851405d00300803601c11745c10b40c07000000c140c4840410700c02049404892003a12104100340d074030b002e0302d6010a0341e104c404446030013840c0042d49460140385110b1380601a0641030030704540b05d00005011003400e42051005034469201c20b2058142407040501410071746c10302c01d086280075145502c0314812420b01c480084091000329011950f8554245500b0311000204d0003030b201105d8006c501111801c48560040c49410000140190544221240079031a46100102c1c04542001501c24040500b4126010740d820011700c004100b0510404c9200ca00c2540d0f0b05507190700e03020342c404080c81c141d0851080286041c50401103201411010003280740d003aa0410f1356541c4040f01641444c903ea40301864098a031311681e1101440070a003d441d4544001c030011005032210310b03002c1c14100d1800380042c503030100401444030b05800400260400c22 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 801161636 1250 801160386 801160417
    0x30b011409040608061305010b09151003021c0506131109010c0521030601180b0315060d32550c05070f150605150d05070c0305070602 59
    0x1582c0f5801303403410008660411700c90300c00c1c410344410041e00307000741003a010b804c0340c00700e4150921115203034800b500c03811018414070b40d01c0000000706009405032060b0002c99074101c01607124810440000e00021200755120b611105104e101507000b40c0b00d03c15422161001d241c3c1010b2141d8010f540b030a009107425282c520840603129807009191040801400151206648a0070709100261280b8441900d800c00c1c0d2150b6071060103c281e01000356a0300809080d450000700714040045016407040b100d00c0c541003824611800d800d0400c180442018201144080d01e02c3c41c240c0c840c07120b0801080e20001e5020441c604000d0045a291440040400c500c2504070006250180c1045140381c0c407610301403e44401e5003589044c400180f04101a640c540e0806d14a0000740d56114080c0c0d490b0000006c1266900340c090200c0000710364058005010054800e000400b181050070303082d42c20050802c1442404c0c8400145140d10400401d140281d1580b556030134041c03144d54030300103504501c1c40322480c4403 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 801162886 1250 801161636 801161639
    0x3050c161202030903060a06031e051c031b0314010b090a090f110c0a020109060c05060609180129060c120f0d060b0304030306091814070e011d07030b0114090406 71
    0x20f4086c07050340d010701c83e21580003510b1842d6103081000d407680842c40c0c000076156446910081000030811480c03200524182e80220a02420f041e40100b00d52080c4039203840c18801d5002907283c143d446204810140202494142e0b40c8024280440c410184800d4200310000030400845a6031b4108040c59154004049088900703124144100c1d0800443e41d4080d5101543c0384086d5604030000724007401252802c10744603010f646519660b01806408503000700c4801002031022042201c1103018241d011000748461841000c039140e89991541d00015501c6085201c502c151800608030750003c11201c014200342c000000d01c3c0d14203500002c0e0f800e10841070403c00c020840d40355100e217001a00110958503101d06050038010203d0b201034102d460924540720b10001d9200c1000d80c2a44180e41c0145000081c9030311a4a032801e0103000c4c1d00c141e00f10a90040089000034180d80348518421010020f0607459849404c01c406441401070340c0f0b8041200000c42c00e100400c007130003c0c81c1400700a00082070300c9 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 801164136 1250 801162886 801162889
    0x81e0615070c0306110a090e04020f100c02090c0c070906060c0210030b03030703052a1e0a1b05150405061e070f05061e0f0105101206120303050c1612020309 69
    0x43e04000306452a8035000994250b10300c0d01f00d10501d014007044118502d81c2d203003da01041c0030b0418601032a104800c1d42d4200b1a40911441c80010310f9540505450040d003820400840240c210f01c0e06c081b19401032250210351070856101d048104d540e959540710785c01046400b48190f0b441610041b47c00c042d00c810321803d080d24100024980c01344695500307680d5000802954214510711000270850300c00d5080d01c0407903047c00003103507828400d9400145400e0030b0300d4113441e07280000c0100c0080c0b80e240c0410b641c40c40b0988100b4030380b048800986400c80d0490366000442c02d41d10540c00f410380d111000b408102c40310000740820760345444100000d01e160160b030f6142c142190141d02c4046070250b100d041001440304010844904040740707840c108030b0f14141400703034140d85001406150301501a910420902030700c03414002c407481040c3c000c104030340d41c0c0b9810381650340c90301040c06502090810022503070b000960002c548070034254142d103c129202a540368001060300e05105411440705101800e000e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 801165386 1250 801164136 801164141
    0x30304170a0f03020624030c04020a0309020a140f12030301090b040207020301020d0606030e0a0206030609040f020d0506061009120f08040f06030906060b03061005031f06081e0615070c0306 83
    0x180d0081d00200711628202500b840b418240c0d1804490310340f0500c6954011f628000384403a40084111800360b08d07421007100490041c080000041c0d80401f011100060907010002e07070602204040c8c0c0c0d01001a003c250070300100c2d03109001d100c4096841000100300018465000c489074040040c07001d440c02c00280c00013405d9822074400c0003d0603544110422100d901031080548604d0040080d004025160b00003c01ea400010310b81409107100c1c100180404c100311800c442c590b50300512250840f0060700701507640f003104692180c0640703810454506942d020740000002c9401c1c3e02c41062181102d551006400300f0321080c00c45540c4070500010618084529000d000b80c0803da800048007280d03070603c08249c41072071384080301c00c001c01c00078028280c0781c01040259981180c142160303240c5440d084c0794134000f1146400204500200004a416039005a1a0740181c05000580002c1c04401c181c003018580c0c00d0303d04035400420440703000200e000d11805098260f00803078141c000590f494484205 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 801166636 1250 801165386 801165413
    0xc020a060929160e030a030c06060909080a1706100509190b07020a1d011a07020a030b0405151012030207150201020910021501090207062004080d0c02030304170a 71
    0x2610040903081042d02d600da4104030311040058130780303640c4076440751020030380301d074070020300501040400441d10051040ca07401000080c200d0100c108002116801d15010b50340150b83c40b00c0c001100c031380120301a4000300c09a103018400080400c000000303540e105844035404101c2883d00000d103158070005c62071906100b00d00402c09000c4280d5640b0745031040002e000c03500e8001c54040d416090b000c4880e0f4055a8a26040d0f0720384d02c03441141c90505c258440264015901c0095120700010b00100403c0003030b0300f440c1d0280c2e109078202c500c4011640e01920800f142110346101d4840b031001c00700300d1156422076000481e8081d00640d0320b45034841260b00c4084402092000150b900040d5110290804602486601d40d041c4090f00e4109120414610354640621402d110f40d80c0110b0b150082c001c40d540462034080b524081c0c0c203915404a029100e185c2c219103c0d0301c0e40d60003100706030f128841c007030380260003402e038010065807600341440050b90320010030340d00340c41c80341c8160001c4000050301d8501008 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 801167886 1250 801166636 801166703
    0x6010c060b0a0e101d06010c0309030f0510060509040209061323010614040602061311030d08090606010302120a0c030b03060a0e07091e0e16180608010c020a0609 71
    0x1265181c1101d503c2d86a0701c0661001704c6400080c080001d01ca2071900384540c06c035000f403800c080d2851160408540011480d0000303420508481210070030008006903112110760150000d022035035564081040000d4120380103074008903840000341e07083c0b62003002e050a80555000008010000500900a180d0100741107240400003000520034250010300840310041051490343ca8241400d40c006d4589a010380075070240c5140e50541d40c1000580030f41d14518034400781c11a02c1d010b4222500500742a010307203501885002d080007143d0254401d000b00c0b540d00b00d425a0301542c0342c07a1110310a00a000f00c920407000c15540d04248549a9030600c10b150103445803500c00708803d01000800d82c24110640d001d20002c0d46001d507884c0828899071203e4104103440e840c005440d0700e18040032030503d082400b455032440b040ba507021412401251409299074200c40b82002081d8951151508a4140320450400359201c40310400010b03907036801c4070498031f100704050b1004a0201d284000401c4000040301c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 801169136 1250 801167886 801167909
    0x5090f25080105122a0109170a022112070206090a12060606081b0c0106050301110d05090a170a0c05030a0807030e0604031d0a030804060201060602070e0103020906010c060b0a 77
    0x4201e1484c101c1010300250344004064665007004e4603d151301000d54400301c48141d01081c1e402d8030700c0c1c2e0140300324000800c11240d980112a284c886015251700007908124881c02c01e070300c5210a907030100481c107610200c51b07900901c1a081d00b00074003040d41d00890403c81c0c1c801400c1017101555212420450001c014007001c00306e00d40400d2034a1000d42c2c00e560802030401c00c5100c100b040c0301491501580c0400c4014407560b5442d600440340c00c3c05000b4a4001e150150300f012908051083d0304001070031900810402000982c44642c904c54840d100c032407007e0409000c0d003035515580840e5400511100e5154200b0b21020b00e0340303581d214215000b40c51000701248c03643d030800000c0e54142c040c0c540320f803016030060842440c10f42ea001c3c158694001442108440700604601c242d15140c045201841d0441c007102e0f03ca603a1644000d002c0d1069000e6a401809808000120a0101c84080703042e2a402403070780140d582d0719401100e1051582c030003075801a0302c580e0005050b8503400010000b07041040e008 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 801170386 1250 801169136 801169139
    0x604030606031401050c0a03090609050610051201060f1e09090b181c08070e031504051903230d021314030a0507050d0201050705060c040501031505090f250801 70
    0x6048096185103c0d8082e41000104a0170040050840703603540e149041c0041c0c500100d05206006182c04c10000304144213000910075881142038082e800c452084441082220746080d4075402c2c3d4a0320b05c039080c06403030752040601441d0500d0f60b002d040c3c0e200f0303080c00c0500d49944801000a803400983c055a04036458000d1000031100c2041031481c40050318000d00b2140d2501c07001210070302d00034000c03504022520300032481d0f140c86005a8808290010304455445520070500741070904180c030b04072020706c502d0009004446200003030150b880d4250700c0e0081854426031f41814610050304c0c0d216192002041010925103051010b0002e401003800b1040c646402e022407501502c2d001c161213072096011611840000724005843c605441d400d80d044244c5040520051700e89019041000300180036000c10001c070880700d0350242c003c0722001d076418003000d0181a0229001038160145680204180d8001140b800754080c0103a000064007040110459070301041080028003201403100240c4e41400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 801171636 1250 801170386 801170393
    0xa09081903060b091011010e0d022406060f0a1206030501020904050c03060a0b070203030903031b0d0c020a03060c0210020f090f09010503070515090405100602100507021218060403060603 82
    0xa008060150b03a6040c3d4a003420700c20005686099952600c0d0400181240c1c03076002e0704084d004200840000c00440752881030360078006c1d45542c1d14001c028515a40b5440308940445480e02042c042c4001030010303031034202c3d02501c540141d8040c080800500c030500c21884035801007480343c0f400550207400016240d0071400e040106490028003030881101d001d00900030340b940c0b01b10500c1c00b191550240d540d6168803510100381103008064009925001c00b003203012042105c40e024a41b010302c0803044c0c42d440f5401120503542140200c0001e03400c083c0110080c000104541e100300110f41c0c1c1401102c3c000b82218085c20280d911400c46498403081c0441d00da809414810742103130344680e040f01c0c85481e560624010070b1b50b56985108142c80340504103100c0c510301d0648021103500e0305026000b40a1484c04200c5030104c1c03007852140c0c0005200b02405028100454800c0324003a81c20303540030340713140d100141d404100c60300b100981041d4500e6038078028416554500c020002140310301808990f90f0318505 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 801172886 1250 801171636 801171641
    0x102011b0509010c2406051309050604111216150813030305060d0618110d0b150109050301020c0601091503050a0b130b09060a0c03020c07030b0a09081903 68
    0x4a905540346059100140e1098000098850b070071000c0c03809100360b0109080c042c0040d0110100480300002c402c03140c012501c20741d0003200a8820a40e04858080086c544600c00c45511100c00360030b0380c011002040c0001c41031043e10300c0084004182c641b4000001501508248440c0500c012844003624100301050b014800000070a02c1c03400c04100d0342c0b0705404032120040040030003d0402d6954400a010b590342c0240c20004180c0090040000c0c00c5603480b4020081880c01d130684160840844401244c50000c01000c88241e00007092074894544104008400b940024803505200000c000032403252000d00c054080b480d8108010300d41c95240c005a102150011000e42c050700404200c00c0c40800c100040e02d601040d070000311081140d444480c11072031001805170007400d08180c1e10a0000c403080028005000d403000380740400404e000b2210540407032007004580136507a0444074040022030004550158021443d620202d661030300c0d9079990f6035580c0181d40c0c0301c000801c90032480695940c5803 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 801174136 1250 801172886 801172901
    0x2040218041a03191a01150e090408160c1208071205030103020d141029092202120105010303091403070b0405040f09080a0201060e06190e040821010302010201 70
    0x31050b0b03054000d40c00d00801c0c0c41e403540c0108040181241d595500400c03c200b000c07072101c0b01c00080c90b070207156100d01131071450b0a14a070166000896201c0041181d1030515003890050b54880e4038145071252020644207244e04900c0c040ea196860510001035280c9440c0c40d0308e103060300c2820381980c1c690cc2440c0003000c00100c0448003042201c280014001a1a150104d01010f600944001030380e0404140c41d900d0807060141100340e250910700304003000444440d41f466080d121440c0c0040c0d0507045414401ca050017195005c500c502c0010311080001d40f84c84100c210310340090710035000301703401201003400c4d41c10070783c000c070000b030108a8208101d0081013200481000b0840282c04400d2030b01c140f5404074000c0d030282910a650760ba03200c0d0080e4800e94000680b071a4031121107900c600105101a00030401442120760010280c40085e00c5844c1280140c840b4403400000220181c3c10541d0354a03000c2402402152402000c00c8001075400c018810580d040498050070601503046100081c01d65114 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 801175386 1250 801174136 801174161
    0x90c030106050f1b0304060f031b200102090d110108011212030c020f060406020d0f060f120221030304120305070e15070b090102030604060e0f0105040b0604030204021804 75
    0x240014000c0a60090880f0354008044003815190b904444d20304104004c52000c4c20884d101c0010300051b83c503048069039203680c406450800c03001142010030780c0281d190b48800e10020f000e02e00040c0d8001e00c0703400c044004101044c0014241074503000410b1101808079400d490400c0626071910996070f01441303050140041d0115045000708950300c00007030806c10b56072075040c5034440001c844801e02c03c00c09600c1d00358100741119010705050800c00001c4d44841904420903003010881049600140108400c458481c901e49000364904a1003991a0200e60b2040342c2c007149501030041d80200304000040c003030702c1581c05180d403800c4c28502014080c000480d440c0c1803505200400c074800d6008400401502000d4031820480540c1849100140c418100010700c010403072018801c0d0071005501961060000fa1402c015858a401c848203009408407008000002484014802030605400c50303d046d117000703000d65003010303120343c0001c041e604a07000c1c1100005c4480d910345000e190501454680a14 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 801176636 1250 801175386 801175411
    0x5090304060e0d08070b0f01030204110c0a08030c091908010c1403060103200d090b06220e07050a0e04060605090603030a05031003051f050703151509030b011409 71
    0x150501c0502407100d00140341e44107080c034a10003420300035004d00301c440c0d140d400403603080c0516103940c034000715000038081680268a804481106a1501801c40340c5131f401c500020101203d03541e40c4d5649a0f84014055402a002801021416211801e9803500c4c15000345d0911140d60400400a00b1246003000b080b08004143d070011020342c5024044a0300144280b90101d0550000088501185001140102e0881000655001900785540a14132961046402001c0764590b40200b018186a403082c812020b0b4020005079007030301041c0c0c4950300d8031039601c3c2940c1c15556075038001a020a425406480c0a404000c10003080120600c101406842d0407105c40c1c9890805802203640da0040031302c0c140a01c04004089480129850284e07001558003104440d960100d0300d0300d200113400704180d508036040c2403402184525004e40600103070b019060315411555807a0030382035817a0400558291003400720030340010005c0340341101014040d00020790f03203410000180c014451005002001c5800800 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 801177886 1250 801176636 801176639
    0x601050a090902010c170702010905150307200a1a1605030a0903140a0e130b1026070305061504030209060103050c0c101d210f04051207030605090304 66
    0x40c0c0301501001a14044180000c10290510043e50041d0400300c0c080c1a5601c14107a401c0320107050ba000b40320880c400c0e81c0340e681c01a500d40521400002240e41522508401e00c0000c00091140c1d6600e0b5a8003042c245150030000580c80d810b08020201d082070b6810f020320300085a1454140d8041ca80200180b041d41120300d8884000604034040501007402e001d8440b82c1001c203040c880c00b05400707111070200d00c8940e0361101d12409064007201800d0b807402002c444003907440d00400c0d8402c961000700013070010040c4040302c0f003040ba50340b10005140000c15480081403118813003060314142c030901c44da40340000c850910004005a1524240407000e1090041005000686803045caa40d000482802c022807143c03503518040c050340c02030480c2c00429100d080c103182008141c42e0090403d0b1040000c01c0d0540c880c01106060b160040d4031036869122441c1075058026415040042654188103041c5a06250700c0d403000918000c0400a0b514080d817140e2002d00a0200501c55180c0002d1044010362400303 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 801179136 1250 801177886 801177889
    0x2301060f0f050a0201060b0f0915120f0c0c0d0207080709020703052706070c030c091107030806191206060605190f030f05010b07060509070602101515020a05010e060105 74
    0xa89010790908002c0045910408036000b508100068021600b003540c85000c90860740e0f16a400c107100d1103100710301099112584491a00c01c542036115207030003404140e82ca4950842c0c00510141c0101c070b0b0300e00c0400168800781b000380940e00d03d00751640d014040d41840d0680062602c803060304400e215510410035200040e400c4002c544408042034420b001c42039411800c8025407884101681e041080013850108110701c01c0e803a24180e9200f200282106512032140001b01c0302c840910b22079400040011070007282c00f6000c803d0380104010100c1c3c146004141c0c0543d010348407075004140c881a090054010032005029400c068107642c500f0a0608625522075070300314901012400610102c0300341d00008620a030000c14500004c0801403080396907458010800340e0201d0710940e1481d143c40046241c500000c0788910441d0b0140e0b00500b122228240300030005c1c810004280c038855000074000a94500b01051b034000000550082c00340c00c001802c18131701759840b5801c18000c5410460040c40203 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 801180386 1250 801179136 801179147
    0x50309030f0303061e0d0503120f1608130f120207080c0609010c030c05160605220e06120f0a0302011506030504050319110609100c050306060301030f0c092301060f 72
    0x79118a40b6074101c1507503c03170000c03441c0b0506e83c01b030240c4903010002c1e4002d4140204034882d401103005034107552242c0d4540c810340c4a01c444c2c880b030400010301540082121551200300130041c9602400c12554a902181e0f0f50fa001c1c49441010040903800c0741c0d00410071010280b02e440c3c2211410340d015498440d081c13000030304103d0449001030500ca400700c120400c0c00000c000615001000307442c88010315440b800d0280c0b95070130a8039020070700090f80958404401550710603004840490307450764000d0f11124200701c140040e8071003402243c86403031005940762108203d00c0302c855001e03400000b100c2c42c0b01034903d4041c002540100b010b06040805000008000104031421390001b00c10540c01c00800070703000c80756501d45482035209403140800b84041c5440100303d840340e43c2203481c0100100c1381007210548050100301ca15a0380183d0600040011440150825031038510031150a003c2da5210198501103900f2007880c80480e80e4007105180c0586d0102c1403c40c0501010f0078020308410080380000d21 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 801181636 1250 801180386 801180409
    0xc0607051e0f010207060614041a01030b030a0602190e2704060603052b0e06160203150705030a0c030b061803121606051303020d0c0203031204050309030f030306 71
    0x81c044403000c41e5481c0800c1c46418050000d04000355642d520506042010340454058101c040c420521074101d1403415100e0783d55251200c401d00040401c560006400130200c01213007580500400407880c000510900c007c0c440e500680e20392a820b810780704001402904184110340c010080501a200c000c03060081a060b070380000103080342580e4580ca808405888250700080c0709101d42601c02020300d0082c0e0000c0000c19030001c500395540c106250444900408030561600420304001100e043d00114030401d01460020b4120380c051640c15100c500000707401c50300030300081e0010040c008400024011000d5240c214070b03052001c40710810001d030b644c1c030070b02560800c22004c500007101d480e04d00b032284501c8622a41c0c2e0f186c3d261480350008092000892404481480c5440c0c00151185006080312184a41541c010031109a0150003030751078100199050741d1500c81801035190182a219445104504c80d10140d6188e0540c0c2003418900640004078802c0f641060080000b0354542031101d10 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 801182886 1250 801181636 801181663
    0x4030602070807020402040e09060a1a0607020a0e0705070623010b0d06180b1207030309050d0507270b01090308090d0305211807181d07090c020c060705 67
    0x503940c1c0040e18108085203e0210025001400400c5c00120009070703070b01451040805100792a070540e00c20324a80111078245081959003c1090310840b03803030a00a000d40525071014244075031707058070740060082c181d00489020002501c0094040c0410801d030081e8094070301415002e4a501d169580c0b500000341e014040c0946800c804035208412064030b8011a00910f202184000b03808910020480a4250508054056103001501d41c1c0c64140c0015104200d91b0150350704000c807130034030040060300b100301c610654083c0300d81c0202140c41c84c03040302c082607508010400c1d4944464654040c3c801c0e43c9000350901d041c0306510350104040366003941110340490049450385408001c0e450292a0f03030048840da10402080c070b220250310b820314660458090b41403000d0340d030307a00a4140e240c0c6903552618042c82e40c1148641442c03000200e00c076001070034901c4030002a88200d140c4100c0d000e140c00c3c1a50700a05ca0f15442d80f071688007440d0140001e0f0040481660158030b01552519015902c492455150 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 801184136 1250 801182886 801182891
    0x50c06070f120201060f0509040b0703020313050f030406121811010c0b0411090609070219061d0607030501050301060501170606040f0b0c0705010f0c02040c050d02130f0515040306 79
    0x40c410404800c41469509501103010100d080602d44002c1c0200a580601c081c411a0320501080710b140425440b4131566102d0034a01d51565484022030282d000a0041613401c000b4258140c00140c0612605107100540001561103500d890802006082030407200c001c200e1406a801340c01c100681440c406260708200e000360012124001200c65400c000b1024080300d08282c24001000391460080102c0d001c101c800721080d40301c140400c52103800544004016900070304110049102050601e0000c82c0103400014461180103022a80490b1014012003c1c0d00a842040005501403113035070f0141000350002c10801c1c3c2410000792100c240b040c4d032901c00d1510100041d00c40d40e66002250042c200324291021790341c0c0c1c0c0d2518030200350031252010035540640400480d00e0f52180700b1459030003850b43d135075620701c40c615000d000c004c000c0101c0f07460030804d042203560301070401400100846407100c00114aa549000500110301079980c002c50310615000010200c07003042401510144e07501321500 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 801185386 1250 801184136 801184147
    0x506060a0e240c061e10090917070503030405011d03040509180f0d020106080118060b01031b09030209060d081209100c030212070905060417010e070e01031a04050c06 73
    0x3081e140403854050b4996001c00195450b00e5002c040340c0607000340702a00b0745008000d84580c266410210071200b9981c40341c410001004009204e421002c40a402444281c000c1013581c40c1c20303241c980c040101590b09502c004184030800400b40b082410481004c0300e003888a101008031640ca0344198490144624900360224500f00ca12591b07001120f05480216011381009c0c003403480d100c0580201e50700c090b500c0c207000019110410300800e10f945880c0210340d605000741d0740d2408020a00c40003894101035441c01065000495a10b40c00e49040850711000455451841003218400000305007e000b1200e001d44440000c04500907208420502c038080381050307444022003403030b0541c482e240d00040c0e814400c103000e0081e0950300402c0f03404210100c0f5105681c0710101500e800c0b009104881d00318004020400000303420340384080a00c1400d0340081b0311f02006d450254a040b00f183c11010100300b140e0700410403c81540c40300095400d0500c1d000b0910324250322120340790f4a5111801e0b005203400500c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 801186636 1250 801185386 801185419
    0x6010f09080d0206040507060503070804080d0f1a030f0a11010507170f0304110409050718060e0a051006020604120f0c06150602070603110d0f090c0305030901030506060a0e 76
    0x2010241451100b01d41906800d210001c0d912103080d6420398960184107030104500d881101203912661241c0c9600d0b2941c1c07101c2d55101c641d47e0003c41401da09660b6103840004100a13402000104242d802441148140d04410181043d640031000000b55201c2101c40c0d00040c4106604e694506090801030344548640c1460926446201281c24074070078002150b5074010700c2c840203580114002c00070382400c2e1202d1000d01040390045240605649d0094408014aa0350921080d0340f03501d00407404550b8566842c20504803110540340b5980079520b510400c250411121490380003000144010310140c1030548990f60307011151003002d010419010003015646000e0070107041c44c80da202d902042002d02001c5d4030960141e25001c2e0038014020700e41d002414030711038020004401c09182c0c805282031034520340b003c014500b00c41c3d01c0507650b413140702100c0031400c0030300004011800384002c5d50b5689100000101290001003d10348070b20401d00890309030360740c060000b510500d420386011279003050054 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 801187886 1250 801186636 801186647
    0x201151404200d0e010b010e01021e120f18040c1b021512040201030e03040b040905130614010602010f0911040207240b0a0503010e121c060f031b08030306010f 70
    0x3a41082054006100c9904104a0b841100c40c4e55a11000308029610f040044400e01d604407026401640301c0c0d0a2608809840041c3d80d00700200442214558001c96100c207405403c14501d460500e840841c0c40784111000d0741048030b621508a90400c184441c40c84090615501c0c40000311070150082c400008640750318034520b80e034542c490780030b0340c0704c1072001012880c205c8100c4003240002e0074116010415030300041034500380c9a04001450401c1d082844d880002c103c0101040004144c000800d408101203204002d140e949078a00c0e00c440e50705041c0c020f82994070280680c46032034038000c99080401c551601c0d02c4144c00d0304440260750352040d41811000d0280d10602c07070000564401030340108100c0ca41c0042440d03903080c3d854440300c070341c1ca608260032908001501500d40d0001203102c84406001c8004001c0580f01c04920051502040c0104007112425004000042811501881805850341d03005030030307940903080b070360b540c170301b03040320140c4902015007020b0611040071040300c2610b0150 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 801189136 1250 801187886 801187931
    0x307050c0c090a0516030515040f1506090e09060402030a0b13170a1101020c0604030c170d1e0b030a030f0306032001030507050703020a0305030403031e06060201151404 74
    0x30103074010340c10988040c40061605039440b0389500d4805c1c003181c0e2941c3c000e01403240300e0300300310b04101680c00f001020b001c082c0c031a6200c1d4100340ca0341c4809015501c510400c82c0740240441d40c4e1420076032801c109080440010160a580320f65003c0d40030440142c0c0c00050000e41e5950024045d0a20b4541940d00700b07a24030b1481d8000c11580c2c1c0000c004404d40d41c0b04001e002c0580c03459403a0001d4084803150075080788602c0540d60f20f0760700010002404a801281740d10881032140c000c01c0103c5445a216940036000040300e4102d541d110f00550380c046a043c0c030058607104102c0c404010b110100030000799100d142c50f2000381400204040b004d0000e019a100342c0c001c5400854000d8180080f141112442d10f011207503902192030200840d4002c0c3c892070a4a140c83d40c50b400401c0c0350381e1aa01e06441603000140210109500e904103c2e968001c41c0160791074840000201140050821001900b52402c0c0740d40007450503501c0c9010030540d000c00b0102c080c1000d05641c0080c0100e5010101282c681c4003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 801190386 1250 801189136 801189139
    0xa0c0501140c0f010902190f0e0402060906180406140907082a0903010c03230a18030c020f060a020709021e22090c0f08070309240e0d02030307050c0c 66
    0x100c42d06006103402c10740124040b02d2086030714104504600901107c0b80c0c81500074580100c00100c000d001d4000038441340c680041c001000e0508001c2c2210001d00190b200c2d0300b02a80d50407041d251040181400c1c0511000750800389801a120120103010403020740c0e009080344200040407002c5901003080384486610b01684d0380c0a46419420103036414550f80c80f07104554001d6280081070400c89100384100200040d0660300c01c13070780f501c108600308012000640441c4c1c0303150b61030448440c0c411402c180d00c808e1501c2074468050030210360041204101c0300d80d141ca40120000c1040c030f00019070100ba0b12003540d04c8101c0058840b0b1125030658480315440c8610103001800003003c0b900340c1a000c03c02c00080d09002142e42c021500d17400c2410a44400000d0080410410a03c40c0a4103010740d00c2c80d54044c6d083d190008101107543c94a4101c1c1a1414280c00030044130072405a131049103000e0505004042c1008104990411600075a40d11004180300204130300420302e0b400c14031051181c00c072032580 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 801191636 1250 801190386 801190393
    0x24060f0f101112040b0405090a0f14010303020c0d260c010e031b030a17180703060501090f06230607120306181b12060f03060e0c030a0c0501140c 64
    0x10740c005800c1e20085050090039204140c828003c003c1d40a040394151800201c2a07400d10b0f181005014103684040c042c04011501d90115501c4e1404502c01c0f140c0350070212a00c3c402652540c180642880c11051442d8010700d14807500b00c1c0807888140004041d000b241440308011842001c000070303c0c3c021210a21083e500303007d0b1841e4005000400703040c0e54003c2c0c40b4280b0100d1070050043e0341c0da20501e007840d07010414103250b061070f4840c0c0c401032a90154006041798001444501d00c6400c121107608115440d59545006000241d4284500745050b86007440c1081400c3c1400021170103501000100e50b00000c1d540e10003403507500d584003580c881c143e0024140002c07805044014020b0300041c044c599416141c00382c02900e10440c1c0c000c19010714002e14801d5402111803d007281e030f000729032804811765900ea01d130000d5099400a40b45000750b004000c00200400c480405c02d080041e501681c502c2540000c0d0702c10080b420305040b042c211942405c0c807410403591600b04c0811800b5079400001c4600 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 801192886 1250 801191636 801191659
    0xc1e0c03090f0109060212031b1201030c1d0c0702061c1407050301061e020106050d030224040510090c090603080a020d021f0b06040f031424060f0f 65
    0x80c05400714200c40100d5080c40ca0303401110b510002c0d2207000c1c0160301c400c1090564018400066410407080744076003000074001a40803001c0d03131020000681d1141070000400034000b07058015400392012281501c50010020040429018003030301a840c04500060200704540c0c8410840b4101503581d22002c1c1d500300301e03121090040480e80c0340480c6811060000a0203503204030200c0b0305132041516203010400c00e10404090700082d070210314096650390039012800360b842c424190a074910960040c030000100c1c2158401c0c40c82c4402c2e80301d03004d90b844800d10002440215410601e02580d20b00050340303407800d05110140c1c490b01ea21034020341d450100b0100520840384014505040345400b03d8a0f004c81d041800c0340d0707070825116400c44c400c400c1c41084040b48070b10382115520040040c09141070580701c0d08003108000c1c043d403007110b80c21141c5a0358181c00c401803055881c888848104001641810040c0680e2130000a11440c82094100650710540d650640018035541c4061320301005030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 801194136 1250 801192886 801192907
    0xd0b010303030c020309100806300c030d140708070b150315060f2205100510020307021809010e060103290903041208251709090c1e 58
    0x10280800e6001909001514400d20b00000c119146001e001d030855205994080003181c58400c064021030703200e015450040c0c030072882c2041c03243d0742030030004c1d605019002a0040c940340400142e040c03402908001400d00312913403c130904203410b4110015241d5100131904d80f16500344103d01c402040b40001800b4005209000c4440d1101e49134250704441c1e03002c40518941c03c0020048865a50001106001c9551818007540e8400c400d0001121340310403a294820700e00031b4610864050102c0b84440600300021714243e0f0311224001080d0018601e40140e42c0c0214081016140111035a0007214012801741003095003c2c010b480040d0050f13a00704d585a15020301c80305483c0780c51f41d0b403141100c000c0d485070b0b85001a02600650956008501d400d26214245041624180d01903031503010500c89008020000c4601d1402c2c1000c0340c05017000300d000c600d081d80c0b60320b0000c418018040ca00f4000300380203488151080b40c001d103880c12102e4503540d401d604202400301290809044460114680d00c02 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 801195386 1250 801194136 801194153
    0x307030e040c05030f0a0f0216061a010c0302070b03040c0e070806011806090e06030307020a080a06150b0703180f03030915020109081204020a17030c0616050406050906090d 76
    0x40042220280030ba01c0c1540d000b01c40c207001c1565103c602d4203035031010628001140c1c0c0510031703280c90040c0250a01c5503052030159540503900d41a903100e80c40700c42e95601d0b0346421300c5083d100507007420310f0320b5200107a0701c0c020740d60192805986460500000400c090080304c2500c031008001d0182000c4062420704801082d80b00c00b076030510301041c3d81100302e020150442c1418010f8034581c0e586d10241c1450714015860a07070024201c030b41c250008100c4640982c40c1c0346090303005400d06100500c0007004130328040c0308031512080c01a0385160788010520000240702c08441401d81c00d442c0030f82032000010203042c41c00100368454800312240000001c101500187e1100484140c0e060350020404001c1040c0d01f80e070f903000e8005010b22003c00501110110040c04150804c1c009000300780119180d0802c01030004145101c0191035101084c00401100104200c1c0c0d4440903481c10750b440c685281401405500403409040180308010070350180340d88915007510040d20004000ca02c00b10450300f0f00c40744 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 801196636 1250 801195386 801195407
    0x609090a2a0602030a230909040804030b04051c08070c0b070923120d0807110109020306180d020d02030a0c1401151e0e1513090606140a08030703080702030c030703 72
    0x101e4110b4502d2120260626006d103d904444401c191410342c5130020000c0000e0000c00450311104103210100c08201016106403013584203c0040040d02000c8d5401c030751204001012504001618040152440d400000d01c1055a4400c049545940743c10300240d62040b41508031201c1003408000354810242841003c030140801070b64003040480d01c8038142c03500d40c284204050081740d000390118146610481301401001e030044c0c000604011694006400d1010558103058048288103150502403000d05c603c6029002c2400103028000d40444042e440780280ca82035800d100303110301824103100d0301c824800c12200001000700884000784450b4080302c5228050003581c60302c1000d512504070290921034040e06c05600180100707070ba03000001d1541e082d400d080c440c0c11030100c200c0449050021b000d800035061044401007030080c10300c0d02c19001e490065500c24464000500204601030000c8104c40f41d039601880d1426550f590030909920b14030902a800419200004824040c107900030311845 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 801197886 1250 801196636 801196657
    0x1020c040e1b0303071a130b07020102030402090c0a090315270317280f050a05190c0804060c020118050706120204080309010e15040e09060609090a2a060203 69
    0x8008a02c0010b26a0b04e00072010014030709021680c201144121502c03016500040041004820a20300ea942c00182d0b0016619580580c1d00882440114601140300c02c0d0b1103021403109600300821150000c04030040d500c0702400b1024100c81c0c0f031458a5054001c0500d4640d0b85410807400301400f54696000e8880b003c0c19000142c0100f10102410b0710313a0900c5014011500c440d101b0300400c082c032050700c44015224a04941d45d5440c961030a1112806018400c0e004003800182915008481000404920010641180c60003c41501c03054004a03d07503000740d003000f800200d0030903045042c3c8c01041448660f0001c007005900303140801600045c1502960400d0303036030605034080b120300d100a82c0030304d02034118180c00c180402d90039035101d403035004440303400100551503581c0c6104c01042158002d801c0781e185842106e00308181d26a040008c6500601e00f0340340341082c1d1174001d5046485500044000b08029245240d5a024403400c0c02c1c1d00b140c0c403284002c0d000c20550b60346006940e903805001d014 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 801199136 1250 801197886 801197923
    0xc051f020408161a03100612021207031d06070207060509030312190b0904020a030f0303060f0602070303020c030d090e040f1e061b0503011401141603080a1505090601020c040e 77
    0x9140b50400341c040c2ea004490b1b1030150482c15043c80005e60320701c07070405c940307103100360b0700340003509200810700665030050398252000120103028030325000c2043c2d4204044051640081c052003c500c0d0300207041011200b0a01e041a2079000c114006410b61084822684401c282001400b610a04200c0b200b0740c030b2103107080200720a460200074030030640c10840f4042d500c090300d14000c0010030303444640d902da03035882843e000940310344882c0316002424035030300710200503032210b2010700805030100034028400508500400c410161554001c200d02c40900500c103010303071844042410480700f0307d440841145d01000140780d812001c441d4400160402c0c40a03281c03a8105209941c02c05030a42c0301e8051130b00c0c56514507140d0380c2080b191800f01e01180c881a070403c00d000e5000c95411607050003504804003600505503a00d11141401058540041c2000c14621700d401d17000d040d62015402048e040301e034151030b03441d0140d8030400141d040c048000450303500107003005103002141741d0100c1c100104180c4030300382 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 801200386 1250 801199136 801199169
    0x6070c0204090b0103061422080901050c0a0b01062606060703120c080f0106050a17100b030a02070c0611030405040906090b131203090507090e190308160c051f02040816 74
    0x1c232071414401f5031000301d031760400744800089810726004114400040c100145014030540c2e0781031034208038200036158005030400621107164000c60b28513280005c8101d11420f038030300e800c00c02824040503210318410340d4005060810107024000100810065504c1040f8581100c1d00203014035400711081502c44055500115600340100d0640da0030326006d5941d20f261100302e01c1098107500005e04140e200821188002944119031002184200d211600c00360321100b82d480c000c0d103400801c0c2c0051003440300060016040b01000070603201101c0c0e00311004100d811881c20700304010450032074041c0214010300100600d0180e0f841c501c009540c450920042040303a60041102107801c4c01e2401030071a00308440801814816070070590040c40b841043d940401079885200003001ca1303042c02180400c01c203a0800241c600031103d10305249106050030048200c9ca9540d89444206046990fa106503e544031040030240e103034183c82c0548082000c40341c0064000303c00300780300e02482c41203184880e400c640 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 801201636 1250 801200386 801200401
    0x12f0f0303100506030705030f09031306020309040b0f06030f0c0f0c010c0915050f13080303040c06020f0a0206190e130b0901050a030b06060a020109080301091d0105070206070c0204090b01030614 86
    0x705d0b4400e1103140d49550840d1035450f2014421034011381003d07142d100c2445540c0e0100340c00e8028034010441078000307540e03034060301050000340d901900065104012400c005000750329600200c0e948007013522003100499a564503014518000c0304520b56005801080e1840c0010055100f0440b200302d540b120480d055880313030003a600744203500c08078000510600c030901c0b502c20480d025083d080110032a2502c010f444841040c5150812201074941c400d0400041100b141c05020800c0111105000341c0230b00c2c01d00f6008102e0364400c4e40d46600d055288a005644064400c9400c2c24010368018241c1c02074041803519403004c1c00d560343c1c680b40300c1c61104000181910703105c0b40003421254031001c8103060b40c0d594401c020480d005070015909554881070000000754096008601802d6401400251401c0607510307602584a0b00416080320780c984003d20907902c1e0000f41469201206150000701c003003291010070080e0128201c0204100c080d20004010000c803500800c5c4ca06014400004040c1ea4180 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 801202886 1250 801201636 801201649
    0xc060f1a0414010803040909170d06030b090309031207050c1201150801090c030305130b030c03010303031107031d06090405040c0e0c070b01180b030d030e010506030c012f0f03031005 80
    0x321341107032580b0402041086a41c41c0d04100c0e2840d004503d441c05e40215010001001d0340512009030140366102428030802001d03143d03e5030040c42100023035080012800101c0c0d0754209540c40107400c003801003021010007004110050a10801400702046c00c000c40040c0380c040c11486603030f1140000c4148012807079650502c107240003140c203c101040c0052942d03d00361080e80c021000b8142060a0210208030100c0f5040210301600003418815502c1d890f42c100102112030000088007a10001c22040011a81c44048100100f601810140c050500400011000d116080b800c1da0071034184402c120a01c040c001c500f4041350018000c0980d2950381c44200d40c400d1080050082c0040c10303050041c0440050381d044c0d0005031406010002d1300ea0000c0c40040e1605895444120029840c0c0822588440d028069190040001e07001061144d181c100043c10300c08040c102c0f02c040700e10200325514524420b402d10390300c0c1d25520050711400f42001011545a17441100e0300d1040c1b90310803030002502c1c08c100c0c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 801204136 1250 801202886 801202889
    0xd02010c03180b0a060f0b0a02120901080a0c0306080d02060a06080c03100e120c060601140f0702040b0d1407030317190207020f03010606051305040203040f02010c060f1a041401 78
    0x20440707611041003543e102d5036005000740c10000c4180d0b5458010403810f4072002d40c000070f440c3c00500252a2180f03804000d00c0c040f100d409510030202e050051182c00d980007070590750070056041e000b14007508950310807001080c190740019580d01c0380900d2402c03550b0f00410901d00074160550103021482d11600105d580d05240d880564150f400070700500302e80d0015030710000c02c2c4d505030001d41c1c0300705001500b0309001d900700b5007507400d40c1c0d00400180b1000f983c000c0c01e841768000381003100a081c0082d9841844030341c003c02e040079000b81d4942d0100340441c1d0701d8005100b00681c0c000e1161142140003080195600540d00085020815030050b4400040c005030780d1500c50b000090305201582c1e80c815500e8041d400c100c0c8101d0f0800070a1b007100150340d80a02405020b0030b029550141c44504d03050850403050559031046020b039204000380401714000005000d15943c088c205410780d00101d1410100030200d05c62070802041c5405d21501c242ea0004040d00140d4000b03d030184000c800b01c2c9038140d40014213 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 801205386 1250 801204136 801204161
    0xf1404060303050a121113090b03061012082a060f04050706030905150a0506030706032a090e0103030f0f0807020a0201080606070501060b09030721060209040207140d02010c03 77
    0x14042080308900c110900030100c000d001c8041b40c59800b160317074042660840340052048201c4100301f441112040e105034110000220f00904050410600103003000f010390294841c0401410b280e2010300c4181411500da107044803000191510003000078142c0341c6041600341d01d0354020303840410380048660071811300640c1c000e030140c121a850302000350000c10708624103c9042c055406010b24100503108014801c445a0f072001c03401d41f4000381058100400c5070000c5043c546040641c2404c4212028800c0c950750440d61100500a4609025114010f09500c000c21101071980080700301617014502002c1c00c401605e0b103110800090505403400038049a8040040c0c0c44010140090341c030a0a000e600001d015205500d41f460341c3c0c455909644e0170f9000800705000000b88010241400c014660043c00488485441010600c3e20401e104000c41000307880c85401003458001a81c1c1c030f0b41212580741c0c0c0300508500f20002c060304162610842c95582000d54a418a03180f140d500a0080d003035103840 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 801206636 1250 801205386 801205397
    0x10b0c061b03280c0809060c1c02130506070f0501050c04080d0c02270105030f28051606080406050a06060c03050708040f0308070b16090311030a0203070f1404060303 73
    0xc5a03c03070240101901400b508400c1110581c80b1402c02c3c5a2259080d20025641c6604107407a000152614000001c1d00b00c10140604200640d51500c04c020240e140c4113202c0005a035500c18441c41040f000c900d078001551054000075003e04000400241d1b40c0c40a00c2030009000303aa41d107404c1f04031180180e00c51408240c010540301140ca500c0380c200390342c070f030751005050043d1000240c20388070f185030103190101c55100301c5100501072458200a0a94039141a00c020b00d00d40b401405410b491010307440c2186c00082156001d50100803041c044104107a400302c080742051656041300a0160100707403020f0b02d500c0c0c82c0401252111030305006860640b03003182c0322080340104903501260150b00030380090b42c0404043c130020906140907501d080013140105240c5807910403d0a000c2c00703a0002800e00000c41076805003c03180142c21030410000ca07134210304d0100c03403c00b490000c6424825001e0000394940070300000401c101034480c29605c10f542d0381c0307000b142540e1115401c3c031044910398000900483d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 801207886 1250 801206636 801206641
    0x50c010c09060504060503100b0309010b01021507020a140f030304111c02090627070c02100e1503072f010c030917160804030803040303050a05101a090306010b0c061b03 74
    0x90050004541000c1410004032307105a03a019020407036042a110745c0c0560351500300890742503a04015403803205124600d1003035a4103140e00065a1220b00030002000c5042210043c04901c03000d00c039556503a2001e5090320343c0c030301d024030304600c00310140c00b0b41c5403140d000d0107507541c000c070700e111f900b55000f41d40508401035035101c1200304242c2c4e4403605404030140003400c0440308400003251403240101c51039120900380c14214410030008000300001141001600e904134091580c5201c405001044090fa140d691f80d12961000c0340e00b000b84040c041d00b145a042c0340b10f002500c0b09406102c3e8140307110020401c1d01c5182c00100d050361190a13003c0c102903180c4044034621071107100144200004034100095159403507407003580580041d1b1060746d104402004010516401d400303034603440a240c84040109142c1417880c188910007078001e4481614516500d4641d4130340010407101c5001004088900c039694440750301506506c44003640340b60340180404940c0c4080c0c0c007200b50701f00080a14036039040d03a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 801209136 1250 801207886 801207899
    0x812070503220507061103071e02010912111e0316050f010908060604020a0504030f06140a05010b1215150301170f030d020a02010225110a0602120d0b030d050c010c09060504 76
    0x1c4c501c654400300c1030004004840016070500501c5010309d1046400040390305090002510901c003030b5001d10780358a074600001c0006803404c2007080c6641741c01c03030307030781c807054104810780c4e90040d5007091807a03018480c00c0c403221401400100214111b5404580c610a00c219100c01103410550350701c00e2500590002010944501d0a0303005880104598640f250a1650f0ba88404a4204001c41c0607100745507a4806140210b8001102660045e9101014480c6514050001050b0300c10805098502000180414052101c0d0404051030140080801410004010072014030354070130b1041d110310442c082c1080c194004007181c0c0c20480549040514142400c4101c42c6029511803030207030046541c2008101c0002c0080310003056201420000c6d1815183d442c030b00f040a42030108503640c07240f40d03044000c00469038001040201c100220981079102c0c8801960301c0003030040d94001690501403011b100c1b52641e07001001d0005034600f00c009201001c10110250f491004c80d00801000410822090105 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 801210386 1250 801209136 801209147
    0x604050a0e0c041a0910060315060807030507120203091005130b060d050f01110d0c0306050901090e03070f050d08072a110307090b0102150c070f081207050322050706 73
    0x25800c44602e50482c0340c01410004890010407146c00e0304010321301c0f90502403140d15103d00e44001015400410840e801c00ca03015004080c014241010551200002440c40d8820589004005c0c0450300654403400c00c2c06806469132409404d4120140c941000a014100e0f00005810b4086e00081c001c0030300d03145c1c1000e124180800e080c042d40c10317115109940c6e850325000d2290f0344040f9040740c412522040001c031440250380c80d10310004101820007005000f2652072090712411614500070000351000004d60841c158095944081c00d1f400030003000d40c0a1000106038a00000b489550b26889035445440030b60b01c01d84000e00d03095a0050031000c8500d06800100da03180007a02464000300074200610009140c844a90002e190003500e901e802541c5503010088460302c06402401483d461038481d4148089000c0c04101030040c00902c1401c1c02400819411240c407801c180094a1091500b11000741c01644140c1d01d200840107140b4034170360845001c20380c00f44405e134044050808039282500483e403 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 801211636 1250 801210386 801210401
    0x90f0309180515060c12071a01050405100501030e01060f030b0a060e010608040f020f04090515090d0e0409020402160c0317030408190e03161701021c0c0203041a030604050a0e0c04 79
    0x2e051041100e1405014a100080c02a55100740150342c1c00648c1c00719281c442c0038042e880745001c0c40c1080d00340050040343c040400150740c020b1034000362a03040000d51070b025061aa0100460a1000c0404000c0c0322000d0001032250a0840c014408942d4488108001c80c0091007190002090540410001410382c98103440150004001d07910310700e41ea60020b0b080362403080c41124107038494600145113002d1500525400241203003d0029129480b8028058030341301ca0000d4452030303a4180c440110344d9a40d06079030103085515500100d1210520f40345c0740c0e8540500060316480111a414280018170008aa1080d03910149907420501003040c451813400f8000d01c903100b482054020310015481c00c015035200501441d403100d800d1072402d100200044607907040b0445a03401000020328041d178100224040c02246600003d0b020324651049007180210b03000064142c1d80004a0b01c905500700c8003550280c5000c0701d04000c41d451f031040c40400c90307412a1905c00f0b00d81001184030864682907001c1c51 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 801212886 1250 801211636 801211657
    0x30d020d060f0e06040b09011215021b0a150c050403020d0203010f020d1a0904080a0819051810090c1802041a04080f07060c11010201090f030918051506 67
    0x815a4a98580212400b02c9401c84801a0641401c01003103160034002c2c00c0356800e094072030b006503505003100c6141c240301064000d040c54040b0904c0c4d05010b0026030489411408014041030120501000c4a4070751403440010740303030414400309110302601c40b4400c1e5400c0c02d82d01e840c0c0310324003031656080c08620492030038143c2e030656031030070941c0d04207196000138260294011400941205070010080d103001d14502d100307004940c031030100310000700c03000d045809038400d90500202960f12240110202c0411a2080b0784842c1003405106200d5111582d100c0203014040079503103001c0803040207200305d403c01030001c1d0540400802c101701e00e050001122008441d030380b07c058985038699522910a020b0310b00d215400704c900090400002d0320a00c0300009040c000c001401c0312070302e003010081c5141207605024052500f030f2440c0e079180e0781c003d41c03260000d0766001e03081000c5c8201c0b40c14050240d03103943c40343c031030844141a0000c3c400c00c0c4501c1038a21482c40b074494041c1710040c400510286421104011 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 801214136 1250 801212886 801212891
    0xb181905010f06030506060a08070e0106141e03100801050f0703150803120105120304080604030e2206060207060f0c060c030902130c030f02090303070b2a04050a0512030d020d 77
    0x1c100b5102ca0b0041e0030142d8013076401800207090507810b00c800b50011344d010b4030058001140600c44c543e680180581142c405181c400c0c01440034600039441d07403148400e00303442ca80010041e216140b40c903c000e148100940044041c2c460340da400344600361082143c1d810303400c4002d200003c484034000d078016442c101c070700d03446844001e0315a07640d9417035a802410680b8902c6c110500400140c030300442c00d009064010701c00f441c00c1524010440740e031544040d1000707061100c24580318216445100700d101c1100114000e164600240720400c01c001c0c130150241c100180554540400c445005040c0030095020310366038150f607200c4603242c6200a048480104040645456105025a03503190110000040080000920700304984000d42160241418814118010b011404150f0b0700441529280391f0800c0035000103694114020034101e468400c8110721581008600107a10080c80240040d65015078203013820544076001c1240c25482542803400c190300800001c0600e4080d5009061005c1065001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 801215386 1250 801214136 801214151
    0x10c030f030e030a0e031e12070f1205130906050a030201051b0105041406090c0105030c03060a0302040513060b150f0a05040503070905150f060f0f0d0213030b18190501 74
    0xc10f0035030b4407540216000419541d85681107103414804007840250b10211600c416010356841a29001b00804800e804400440d03554140704082c4403c1400c90780c0600b9843d2122076018000e403164004651003120000054404291510288140c8065500c02407000307049a01d03540c01117402c1d43c0090700000200f04500442c40020780240a000c3c02244a4484281d6500c103080c0191b24042c002000c54505600c80202c01a259802008032600300481944203507403036580002184120f10740b07500080d0420300d08820403c441000c441c141c4152071141400b4403440000c441002802c0468001d0142844d41c20001041141844402411103042c0c074105a801d141e0788100082c1400503607400726070803d890b00c040000014403009840c1302110b0855030301c10b01d880c0000c0454840c0c02540a50711110300005aa000b5011071942500c036a09800c40b0159604c8010480c09402100e40e03101c11200c3d1400314003c583c07060341e18400204212840002852084e1000d040c800d084201d00900b0390309956203110 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 801216636 1250 801215386 801215411
    0x1060905040f05061f30081b03030114060306030f0d02101118040f020d110403140303070c0209040309080609011a0406060e0904020a120c09050c09010c030f03 70
    0x2081d1140b03000e10354054a1048600342281003a000a042c0c048602504d4180300c0c2c132a01c60b1110704d00342c41c0c0142d8502d0440d45031400e00096088150041000280c44514010401c940e0a008028800a401e65241002c1c0081c8045a40313000a000d0040840e03c02180740b02e82e070030660301441d030012000f4200d5008404100d502d5040500b1248001e0041e000045281c1d92014640541c5920048254101e40740c4022000c034001e007070182c6504507105a031103560700c2c1c580b0210350f0180d0b22844019117040003070500321440c5002982c0148012220303000b00010302c03c1c400300003000b0350b44100c01d20785891030741001c039a00300000c0d0a40284120301784042142c01084002041000714820380c04000005100c881640702c000d818150b41c0740542c0b040741840c0341400f045600000e107040e03440c3d098880c427101d40c43e0b80c400200d903d010360301705805040c55100188140000f2001c400304507281194101308980303861041d15210301c00c48001e04d000c61400d070040070000c1e21a451000c0c2060640c600001d00403c410f5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 801217886 1250 801216636 801216641
    0xc0106030b1806281104080708032106061b1c02100e070b0a11030714060a0f0b090f1b0301080106180528020403020306070f0809060405100e010609 65
    0x407070402403140b08100c4603901d0003040080540210040042c5011583c40300d5200788010602c4031a48941c0c2d8907803075002c11a5a00700256000b42c03565606903100a900c4200c525a41c1d00610408075900071452154401c411403140703014040c2c500504214608400c0180010108a140c08200820321039444070310781d10350203504010500c00440c0d02400082c1440c0d0b003060300f40e40078840d04540790707046610300b0040e203030300b51080740c682c00143d081400c2040300c03040300d0754150b00600001800321014212030809000f804540b0074030070f1503c0d91040140c018018120701c2260246040700342c20000040c04a6881c9502895880c0c2c060308540b425600350b03401da04500c03016002a440b0801680d1100020700c0205550000001d504051480400507460328004d401131421031808103450703104601d9961280303080c41e034045a001c0c43c0c01500301d81c01c50804800c010841d80307072161001c00054200c40800c0c554240814400c3c003568100004040803024981050000c1c0301010001c2c9680d07507500130009801d120390 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 801219136 1250 801217886 801217891
    0x50607150f060510032a031103010f0305210403030c05032b06051c110126180a050c0f0f0307090c0215040c140a1809030e120c060c0106030b 62
    0x150307000320322249000244664010001c00c0c00d41810b0401901801081d210107007288031406060421485486580d019401001640c0c088502500c0c0007001140034023a4040100450f0f104800b15003c8031071802c4003640d40c0a00c4022170901d13030020017003000400c0c8150352100d201c0e4011401d41e880c120754850b04918162076407503454002c3d18118650700880c2402e110b190700501044c1c605410202d80524060405405504000e01c000366000c4200116403094410101c03808059882040034060300594400401b4121041000000c4052060541400c0490a00a8694031100074421010300504100c4d4014032900400d4200c6c20b21610704446130b408102c5d400007000003000c00a05031640b14002070a006a4852a04d070390010a402d000000e20400348000482325450500791984007150000b902c032500c1680100a0016808802480d09200d9030005880b54880e4558034008503094040c44004000300746400001e801850003161107081082c000d0240414582c0001940c98983c2d4400482e054207 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 801220386 1250 801219136 801219161
    0xe07050c0a0309050a060c0201120e010b0d0b0610050405130c030f09080729040b0a1401152c040506030c1203071b150c05150711100b090105060715 65
    0x2000c4041086045c0261102c002d01904d00c0e00d0550914160006071480f08031103401101c4941d100d203815002c0f034007135101665005004190401c20507841c2070050040c001501e0452180c0d03e80c5c140152812302070b0044600701e40010b4485100e4000e01031403080100101d503020014543c4450705402c01e148071744100c500451013640802e443c0c2c802e9007400b403401081b040691801c40c0306020642e90b015502100d15500a03442003c1071041d588070201e42000e46152410412600c0940d400481c6204c001284420f4811480d569a000c070100f201c6242c001390040309200d506428450040c2c47e1509194000c1c580c04140901110245281c04021420141e500e83e105200758001003503440412100481c00404540292400e4401c0c5080402e080600d12000c050841440200c400b00d070100802480101d40c070b032100303a40b820014940480050b0010b800e915410301c1e20700035520303a40d800c44024814100b040c00d000d8401e107000e03800c03e4140001c0c0c0e44150410b45894091300b0314130185001600410f10300024 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 801221636 1250 801220386 801220397
    0x150e0f121006030c090e19080d051003030f08060f040e0f070801060e1501020309010c11030d02030309010b060c0a12090b03091c02010e0607050f0f0313021014040e07050c0a03 77
    0x9035044c41c070310740c55054200c940098103184400703800c0c6100084c0d055001c000603000f07071065201841d003129603109111048584074108000c20080350003083c0e5071000c0302d0003074603008002203280004495036481110342c65031104c2d0ba00c1c00071125040c40d5000c000e400d503907042110b02c90b203060303081c0c10710b4500349500c440401d0391900000d10043e01090b4225801c802c120071b09070261003d05001035240d0103195416030402c050180140240141c6a90030002030002900755a4080c1c200c2d50004c0d100e900441d150602c41d0708113504580d0320700b88041241c03080f01d074040c05800b901d5650b40c0d8000034058109d1600b010011118804102d900c039010085001304070140051001000302c200c8410280706aa80d81d20640e450641c2000b80c01c0360200300140c0c0840f503440c0c056510384031082800c809014903200032040d540003001700604445241410580386000302d03402c7c901902c1d030003800c82e0064424a000b05010f4804d01c0104420851051130305c0c2c00401604003141403415030303000c282c40c00c103942009a00048 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 801222886 1250 801221636 801221639
    0xc0409080417030301031205030c0706020a11120c070b0d020f0d150e070206150604120501060f0902030402011b03050405121c03060503070611010902151201150e0f121006 75
    0x150110014031110b0321800503504561441d100e42d540c02421005140500c400003002868400000044403046680f141c811500c03030180c824000c2c50502486401c2078544907504520f40803035403000540f0070940440700148031003800d240841100d0f40080f51040c003131076001d10801c1d1000018030043d00d100e00e0b05850000e1002d21031b010380560200c0c43c0d400752a442806509122081d81d020a4032a40043d5039851107161101d1213020841520882e404034404040300400102040307411b401c510226240307446540d11044e186d84070b00003284000d0703070024007240b0600e00700c5400342c408162018105e4002c0c00d04500f895514000b1070383c0c00044403000c1000d60031565030292003030722001c1da444866445160030808a420070b40403035514803290141505120000f0042c2150b4102501320041c030039130160003d1141a549958520160405940300d60082c900c50000314070f09800c2c1d00f2080010686035610200d143c02c007014460482c45101006030031035030380f01007004061410080c010745407030044030005145 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 801224136 1250 801222886 801222899
    0x60d0f0609090f032d030903020a020901080f120c0c01140f030f071805030705060c0f1203160c020a030605090a0b0c0306010e2e1b060c0912031d030c04090804 70
    0xc80e0902d140390340040c07001d0b10f1143d40c5200401c11802c45e101d40e040c00a0019603504007a8078200e42c000000b50311007070741000401c202c00d021404030700c5041c6540440707030840d04024500809001d400c1c88070303945901c0400d89041d9580f040717800004203040c5d00b0b686803511095035410221076000301d078001141c0580d07100380f01c0703d164442209580860306407041d0308424109000203483e80414405e861250340c0c049010709603107005000e0414214980002c5942040d81c0d10b020035000c1d0000c41c2c245417503140c80c0d8220300c422801841890034540c1e0041c141c444650450352038500804010702040c506101e42401c1c000003455130305849004141c0700340959201e1401500061242c1084000c2c11b0041141c12010b070540c4502d1074491515402480c0c40300c854007071219003240c0925442040782c0c40642c07164910428003000d9404007810b800c1316a900c050301034a9203c000700c05100c01c040140000c1e1a0078052400c91006e2a000f0f6180078001c094a21000b458130008090b142103420542d0318801c0081c040240c3d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 801225386 1250 801224136 801224147
    0xf09020a0504090b151503040f030e01180509070306030206071506050f1e060705061906150f0f021606030f0f0507050714070b0304150b01030605060d0f0609090f03 72
    0x2400215014060303c200c55035060078002024000c400a00178151248010340d86003003103a038004c90000641c0781c0324945418028650004001c0c241c1c085100e03005040780c0c070b51083d40d030a0174404e498041548000c0c0b40100b400ba1545006002d901050b039039010120041e42d07240000d06140340900d6003035110316541c5010340103c9959900081c86502143c010281a845101da0728614500d154500c81403200100c011401502c80d040006002d070169030300300b0030607412504450058031019141000071a46810381c0829020342070b0080004240949a1150700c64858644e007403680142c3c0c41036413643c0c1e0654400c58007442c3d071904024040303a20780101c203003442c05030310a440c2d4040110f00141f125051a24018119100d42e04025140b83d07850400d0100301c0300200101c40003000c4808805a403880c1ca414009501102002460781003814030107241803940c07180c0a59000d0b03e4009040d5440d00c00010410710050200100980381107894102c00280c41c00d15102e4800381501805080c0b03150312003860010710 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 801226636 1250 801225386 801225389
    0xc0405061c0f0e2d011e0e06070e09270f1b0603011802070f08120a1407050c0f0f03120a0c050702060d0e010507050901020706050301030f03050306130f09020a 70
    0x7585032034080710b044070410000da03908020206000d590311600600d0700e0203409500d800c1d01042d4940c05d08508180502c9402d1b952014900360350010802c45100b0101c180e181d031001d5524070000354501c90306111515160041a801c1000d2380b0700410f100e10300c54094032403c1c421318030401942d04007400300c0031010710034000c000c1194a1600b14400f40505a030014440e400180940c0c1050441e1409910100d00303d40d04460990782c000801c0240b0404500d0078034402d50000100c069404600d40c003080e0f050340c590050385c0c9909900382c5404511340e1580c2080315141c0111540e1407041c400c1140d030380c10348002440f4071006603487c103003c0c5640c1d032156040300050751000341003100d096282002810707441d648141503600817641100d40365981e40424003218090050031600040b039501e00340c00c2c009015000401000c40300400e80039110603940d2000181c0c1c060009110250020103048006000a8420320055920050040c4495480c80c540000b1704112480325400c1280980c0d904941c03010f524020b400c2c0b80 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 801227886 1250 801226636 801226661
    0x1e0c0f08040b070e030708192102072c0405060603010c0503150f01090b1210141302090307080d02010213050d030e09060102100f090c050415030b0c0405061c 69
    0x4030a0405940d030342201c2800030000c008004400c06010441d40d030074403552000b01958011582c0c0c1020003000800141c0204a04075024444a0055400000c443c1202000041c0640142c040e880c90100c60380c60a8407291311408590220444401e401d4081070072040c0180d000e20000d00d0790f40340075414035086039004c002c40302c240a010300410051111140040c45210400d4828250401106c0c00686c0c3d04130312038101503a00e19001c5881e100c1b1b0025050050f125810301c1b109002c0c00395a6030810140200b40d04503c6401580340e5203542c194443c150002c0408060280460740460380e01c00405040500400d03100340141d40000b82c1d035010380082403a1300d000e4034044802402104840d6005403007494031589041c020741c0381d42c0000707009038000d02c0341c0d8040c028103034001d01022020070003c500420b802c241c11a8a070080700b1000c142810144100f03000c540c400490014401d04584070442428002444070075654001c0201046c00c0e00d40a0150031185081d6000c94100141c0c0800c980035200c2e07610804 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 801229136 1250 801227886 801227897
    0x21504021309030203040e0a200703021e0d090506090d2909060403020c1f0315090c020a03080a0c200102391f0c090308121b0414040c031e0c0f 63
    0x3255030482da05c0c0c1809da09601c4500c00c1d80d07a24000e01d03041e41004e000755064031011420403918006100c0c0401c0c100084049035980559031a2901e0410045010f0302207026001820580c00e5000038441100401d8903a1084564060318512201121034030300c403c0b907850080d85c1189060008054040189080882040703078002d200140d0034801e08650021141c42c10b08040e1100903090701c1449501b03902c40a0a6140000d119800340250040d50f58019403100b12b0008480034001000c42c0c00f24411410103661035034800059525140d03612505040c8212049603d56080224a801d22205003006048190210450004407041c07039034030345011905807240c00c0c81d0b04001c0c20100c4100c068403440568080f000c8000031800360a01d0f00301c0b0040026000100040e00c002007420b10307684211030a500c10044c0a40b10003901c1c40203c40750a01e40918031900602d43c441001c0403029140c180c2000440e40081e2900060040e501034500e4108041c42c00403020700c070fa65055050300c43c0d520881800f480b000c40d0805 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 801230386 1250 801229136 801229151
    0x1409010c0509040507031506020606012309010e0102030d06030c0302100c03021e150108030d0c0f090306271110020a03020c0409080c0307050318040903021504021309030203040e0a 79
    0x544075200b01c2881c24030640da0340c80050002c41c003a9101c80c120034503444080081548546029643d00d506444950104003a0741d03d80c0c402421001d88921801c144016071814010504015640c0100c0e0940540c1940020f100740c81e81c0c2c0c0c0052142800030b40c010b84002c840e551440c01807185403c00400c11204016000c5003039408203030005810f44562203110394030a94602007000550a00000509031078490b2107881c0000307000030000001d45000060820700b0410240110426581c12041007202c07400318002d5035080001c0740701c940c88160081000c83c0f0101041c106041d43c00c02c0704541880455803841410b101981c2400d000106210240781400203059400391624081d40d6888810345840c07140e80c40e0f815103010001200300b82c50500d50844100d07a2941c100e85005a12500203007406074072441000e4103a0072034502401080310070703600b580140c403c1e1581d01004005c6664000c0099030003050123074800320701c000288503c100c00c0d8000d501440d203c0341041d801142d5070034040c0c0840b4485060100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 801231636 1250 801230386 801230411
    0xa06140a051804020312160209100e0c0c161d07020303100306021e0a020715050702010c0b0604060b040b090901172d0102070317060d0c1202010e1003140901 69
    0x44403924224802d5812042c0c2d81d07440004d2821400800b411503040c40891181480990b50400346070320343c404c0390003080554801e000b000d1840c54034800e004181c02003001090408801c64018108800c10310705494610b5a01e1490070b0030208254030000382d90b0716011240c880d885160004582288981c8082e40c5107041061000c4030038815408040c2815600040101490070344001c8541c0c176040c03050113140c5802e07402e000a0f48800d401c0c030544607244901d0b0021352165126074110782e03940d9416150f06075002c1240e00c8050098038010807458015590f65004610030f210300d005000103103051030050755907070030000900c41c8103c0180d210b107100442c3c406044014960110701003841c02040440000090010140100d644402a4400045510000303414080c0769000b0f40005071080c0d11642140380d520b54109110401020b54005000040191418030507004020b2628405900514101c103800f5004000102024a0500400007003591381d034080f240c003803a03004210313400440c000081102110418 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 801232886 1250 801231636 801231649
    0x5010507140d0e011407090e01210f030215011e120804031209090e03040311030d020705041a03012c120d050712051603050c1e210a06140a05 62
    0x540c0894064803081c2e103103d5450700354025464180b100c6078118039414000300c013411456480c050304001d903c81c0000450a80510040b0407046070f04250042d0300e81c1c4094465803240f1b06203070780450440c003440001c07203540c3c071182071414040c0943c0e0b1001d5840403007040000d0902e2000303034419144001c1280b40d101c0445d49903010749040300d41150b030103c1d900c100c4400480c3c2e45601500f04071032091420101d428400e03000030240c001d0b00c0c0f08861403890002070340100350741d030101c000108006901509040c40745080035040404410795003801c4171100305007000002e096a040041d810b11040300a50b00111500c001441009015100c0c0d000c2c00030003102080201c8140b00b4448104c0105440b41c0200f065948a0344c403d500d00104404104081c0c148000001d55041c08404000000703070404003ca01c03100b0302242103c48441180d4642041008104e1000301a40c005200705483c105103003071440e04099560030050312034500ca180000f201400d220b510300c00003a4070941d03103020700c804500c24003881d162038 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 801234136 1250 801232886 801232897
    0x606020c09061e0303030109242423090a0f030f03030c1e02010b0f01031107110d020a061713152a0201021b0a03050f0c010e06070c0501050714 63
    0x155110a0703c1c030601046601c00f000350358000341c0c142c800000005244000c030f92002000e480a030800502145000590807010095405070081070044103a0321038a030318148102d4103144019003882d00800603241c3c030050744013040032819500d28034002641013451401020044c013a04c2c81b5030f50b49071038070709549680361a4104100c004080c142c0c0c684996290074014004040c1c41488111090103201c00d25600034083c080180e249030141014070000b5086600070301610503900098645a41130905584a82110b00c80e842d0480d604039a80d54004400360f29003040312405019161207030b4640880c01521140d41200003000c1c004101c0304410084006070603d100f07070726018501540841d1502c210b441034004480340740390403102c03801d04040d241c4d0755a406401030425a102d001901d8003071300c19240d010b902c68408460080c00950308000d40b9529100d403b01500580b41031000004840c00c08101043c03078601e0582c0e03b480405c9510041000f001402d00880360700c00e00b80e2901003c92002c45241c5107050041 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 801235386 1250 801234136 801234139
    0x4080f07050a0c12031704021e04020f070b060111030c070905060117040309060207090b1516050d021e0f06040201050a1106010b1b03030c1206040f1a040606020c0906 73
    0x6210401d210042005120954203c0c100000d042d5480d6441413115050400440c08624a50002e0700f40c0e040c0300d0b20b00c1d44241e401074030f0644d00342c13a0098044600e040804501d0341c003a900b84400710036a042c402c09040f1070740c800c002414140c00c1c81c40000d02030000e00304a254040d0310401c285009180041000e00485d50070f4a030108481d120140142c0351145454100400c01811504000c00c0c0755108030400c04462140d0280c410107a11228080c0a5a80e03071004160818012803105943ca0b0090f4010710b4404100318100700024003ea840900b011302d0720f102600141d00200f480c10792009a002142c01c4081101d00510150f80b500f28003940310000200081d050090214400e0b007e91700031031440170990101c4046c1c2d10305603140c0d032801541c2c0c0c02181125040040092200304400c10003c103c90156000245060a043d40200304816132080104140c0c7c2260711020340712409407060040d581007002e860322160f41564070000b44000c8800c42c4e80020115401055151120380318124000c2e0441070 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 801236636 1250 801235386 801235417
    0x4030e09060604030b0406060306110403081c110a050409050a1a010e040e0a0609050f03040803041802090604031217151e09090d03060605030c030a180803131a0408 72
    0x80785000103200c1e004560016100013810780400081129503844070068910950301000034140805c505030307650181e03001c02056640100400d0300c03c800c1c02240807030550400d10021811400c482d40c00310b0540c202d14070340c4010600215061083c2a910701843d07900a0200ca42001481d2481c0709003c256100031900c9410b21503c161200310270341301d90b08a40042c6007420304890078150145820001001d5480047d502801061003a6080d03450100032203085824841c021130a0500f41400c00b01d0800b10f5443e0004902da08103c80f09186e1200300241000f98011581030104000720300b400340803900c0941e0001d42ca50a2007003080540541d07908110406842503500e550141801ba56140011040031042e42d88080c1c08802c00c540c0750400904030500b0001d940e01441200d03a00c03102039520780010b4558410a172010701c002040a91036a010f070151200c9242e882c4d45400e0180c07039510440e4001e0300c0e444003a0110003541c2040c003000343d800c011444011421810545072a0310b1380c2401d1701039030764803228641 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 801237886 1250 801236636 801236641
    0xf0f090102010609110717071a0711070e0108240114190305030c191a130606080706030b1906081f080c040507020f0c1216080109050601080604030e09 66
    0x340300b5401503029000050041201070240300348802150086c5204075021f0403295030001ca00858881a61442540070040c2c07030403140c115042106110005140038100b20080c1c03c01c500b4464100b00010080c1101c5034075000c10b5040c921301078240641d0041086480c014024008c51032170720126803d0444440c01c15204641a98000140405041414080070741030182000305c2404030100040021030b2144080701c5000c1c084001e0003c03540100c0078007034020031826000e10b6400c030385050b5480e4080400e041288888030f10340e40d4002201c0300c68001d040c1a40c0078000600845816100c1c0980d800d8bc2180c1c111405042801c2c0c110580d41d103070144004000d8035001003036400c1142c0501c1600c1d103050b5902e4580894075040120f6440c21020b80c014480ca0600010550450000c2002020f5100003006000d56107100001c2c80a801d00425000b605881146c0220b501590310043c4e410141443d0000070984401d00e0626900d004010307000341c0059003000090000198200c082d680603020107481e1482151b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 801239136 1250 801237886 801237889
    0x31e021f02071403180a0f0501031d0102030f010608090304081903050c1b1e090a0b120d02070305070603020324060702060d0905070e070f0c0606050d0b0901050603030f0f09 76
    0xa001d80c040060948840351240c241070f90000c00905a2081145010b581941200d41000311030103440c416440d20244e17040051059520940282d2000d07c05400c20510b2401c444055908a83c400c48524240c50286030041c03002c213a00140d040c2e04401d100c0001c50415003040803143d00c5801a15680e1316101c48406918101409402620105018081614441103071000400f00c1c100d88081028807805620001030715544448025032100c0c0009081441c4a940e1524101e00911005401c80d9016048501c1090711600070000780840c0580b0fa8040d094192551401c2460290700341c11100500d801442005100040c00d44030f00c1e01001d030044010403042001d00800d0582c410007001a401c134000007001c41081e0400c1d0011035290344175904664029954070001030115a0a031100c078001070074584013403c0d251040d0b9452405901820000030360583e038a000807809201000211b84240d400d404010b283d0300c0030b10885901640c01d034003451900c0d401c84590702240c42803007006240c0f44404920307081103 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 801240386 1250 801239136 801239141
    0xb0c0c040b030f3c1f090c03030f090e0106030e19020d02011407051501080f0f03030c071707050d11010506060904090618061a060405090610020a0b0c030103031e021f 73
    0x265801343c010040a5002140305501c13010500b802a4200e000e503e11190000100e00c181d01c00281c2015041518034111380d006c55503200c210401d0420482c1c8000c010981040b4010858000c0c4a80d844c00105061016003150409600b10030802d41c84c0350000310f002c00360b02c030550703884081603091030410791f81d40b031080944145029118000d4030600c01c001d9045d5035114540c00c024107032210384040300d070022400200315030799100070780e1804405d400070300100320041c1000000c3c150951041000e112140d0100003c080203801850b0241c6456100030f001c00c030b0140e0045034902d16900e0110091041c7d18054010400b075106036680c49004030342d034070081d000f8499558054404451203d00403003c0450b1070800d0350150140d07126203403580d001554400c2d0140340400448085801c041c1c07820520f41d9560042100764086d0620007015405100101c82c00144e140e40392a10400064a00c29220b5045050041108010f00e904440c80340c071215007100700a0b00090300c0d81020140250b1480300240e4201312101 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 801241636 1250 801240386 801240463
    0x20318100501060801172d120d0b09040b070e1c0b0106111902060703020708030a05040801061a07020f0f12010e01050a050402060a11070b0c0c040b030f 67
    0x1054000c22418140580c9503821031070403200b25a40344600c0d0b0b41c88058440d00040007140d0940503600c0f00002c0d010f6052041d165401c030211458090126030501d890f10790030461801581070043c4c90020b00600c14100d648100089460f0603100020f052030180e5485000e80005001d0b6010710827400030681ea00d9844015060b41c58540c180d0b0141510341c1443c00d8100c0207800c2c02000b0108001800d42143d0050024003040c1c2541c0220201401c2901da800b48507460703200240a404500a030500810b407620200020003c001482d6a41a943e43ca4020b40c1401c5820300d800032001c0c03505148140064030401030603605401c3d01280e907014120300390b800003060000d13800c500c15007004009a490010178810b6107c8003d000031400240300c1c03541d0384000002101c0781194002c1d40800144842501c041c46407200b00310543c02e0320103e40c442c50701c0e110b0451594210540c0c0507000e0348841462515400d0034018034107200400d400420001d00005560b64452000d1103002d07801c0c00482d0780c20008412038000c1000c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 801242886 1250 801241636 801241681
    0x1306090c0608070806240309160f030309090603030e040b040e0d0c1406060102061603060905100815010f12050106050d0615140303030f15030706081905040b04060203 73
    0x9415652075502610b000b8040302c0d07540115803a640041c00d582003184880403100d804100c942d901040e00c124000485c2c1002d40507e01324420140360380400e13008441d144016007213095152040614615000b840c0030b141d900500809420302d84104001703500100003070b0201004480104902c019003012800904981e6800e507180d03c124001d030300b1880d030802c50f40044140148050200e40b00400b080da40e0310501035980c14016030006002440701041110754000010140c5408101c4641e19542036083d202c094403800021000103a0410144404100f044003105085011400c40e41c902410382905018500c281a107540d4a80000c4042090070350001028040c000d02a441881c03642c10f01b00c0040400301c1c683d420303108500304007203406061400d0307111440351b00400035031456071404c4103151845405046c510300642000e216038110355041c0a014054070141ea03880880d8500380740c4440740102108842038a1030f00d002d0a01c00483c0c05440503c0c0d020790030100141c1d5070780300d510442408290250040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 801244136 1250 801242886 801242903
    0x1b0e0d0f060507030f020f0d020901171015110a080d020702042901050c1c0c021011011113030f05160e0601020c01030b03300f030a0e0312130609 64
    0x150204007007548418000c2e0380d159800c20440b40307488a03d0049110300c94030261100e9013800b59505001082d0018040d610043c9002ea542503103041141c8214141902c0c0039030380c000e10450500c43c0c04140300c3c00000800c454034180d4500401c26000581750590301c000501750700d20002d00e0090104083e0104c0d206154041d10030824242500c1d00c04950b20822507045e049045800c0c5003008039031144080c0c540c02c40b0160007074401030150117031181b2b0662003a2500000d210341441c4000140e078820300c416030302d035001391a03500d03a005080305400d08650030001068040300c8280111043d20280d05081300036250700445201881d015424814500000c155000c0d040d0106c100c008140e401842703074010301540c400e808940700c50001c540150b0503944400e0409806a0040760401a207911040d950240050707408810900510321040d07480440d4403040e0320721128100041804036402c2c2d0343c8903011401d0807070300c0070b9428441c0708404c0741901d0704050a48034610782d1444203002408869401600d41302d50105c1403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 801245386 1250 801244136 801244163
    0x60a0f2f010603050106060c030f0e150d020d0501050103060605041e0b0301080f060702031c0906110d1529030712061508060108010e01051c0209010314101b0e0d 71
    0x52a001e060103010413500c55003021000285c0328000c000402e069035140e21801b03036006140302c0458400080d1003034254400046100c40300607607400801001c20181d9240d004d070f0f075903400d584180140e0f107040c0e00641c1014580401003110719030001c1618252030b490502e1040800d400c0c9003288001c2d0726a084405600400400004c02441c00200301c0c0020020310140e4909590300801030f40c9030b002d4840d0304401009203400030a040d660f160b01c00c0c1c03c018802c14000a29050000402019420210b40428a55500c41d240c0442080e502c1c000d800410302c0300c1481c6040c400c008290500a541c004003a481504e021001c2020580174803482c00c105002c0b09001c00c0119550822001100e61200e0307407e012602c0074021500030752280c04200e042c0e9444903080c00059103000b00303000100144054008002c06210030300801650707241794903402540a0031b0500c441c9221404102c0c186042030580c0341c1c800f8078003c03215000510316007002c010f0316114141000d1002001010401c42c48034108020048c070b140c03004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 801246636 1250 801245386 801245477
    0x503270f0a03170f27070609050406170c041508060c1e16020609040603081209010606020d1704210815030a1502090d0c03080a0e060a0f 60
    0x141e00d58414000c0e035400a00d50801e000c16411804259001042050b2030350008a00c1c00e002c0e540340317001d081959041403100550001c5c0310b042a402d0b410110000354002c1e400c01091030540250009086c91294680507071440b180c01c95990310300500c80d2800341d621100c080c817800000c110f4800040c00c1100640f40c8030b2800c1a4150320607800b0610500a104d91400c2600b282c90320b400964040d884210702c0e081c0c8075900c1d0303000c01c41d450300460141c6510545071540440018600c0c005403600c504410384a10790b40c14003103211403d58445030081e41c210340c4480090b20115910482c600d500141c80d400d000401c0d02c850400d0100d1001d0881c8011800c1c5503040000c09040c0e12641c00d5108030b005401c040d4413522660308158680c4401d036005800d404036500e010442c40810381c0148440007006003203510032030a546d07500c51140d01903842560300b0907000c2549001035030001038a04d40c030182120b4080c0f500c903441101074121380f114101030b0b00f0440803048181d484c030310140c1c0c6e0089464082c006000b560b207a248c0c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 801247886 1250 801246636 801246643
    0x110702210f01020703080f04020108070804050127060e150a0b04110f0c060f24030307050d0203040e01050118170f01240b0408061602010605040f0203070806030d0503270f 75
    0x3113040707000580d80f10010320f060a210003994011981699101d03000e840c0c101d0104c60b0610040c1055865550710025420409403865601c13a6100c919112418010a0343c14160101ca003e10444580e07600081d130880301c604443c42000d030b48144500800070350485040c0c0841c0051002c0c4909100a0b140042c496544c1c9507000040c003220790400003100d003641c2e540410800203035020340d0105d0b0324140d0042d0180590741168001c030700c40070000c3c040b0380c1003601c992605481d00c6944411000940c0000900f404498075000c50f03107002d40400e007401c081003103402001403602c82c41c1d44074201d02156890945510303c88140095820542c0c984000c0c003100c50298286201407204032081c00d82510040c00c00148805008152422104000098000395480b02c41e03603192000102c9805007155070300c810105840d9107500c1128121010340000503144e03d0a040060a01c1c0c5005c2c040074400c0d0f2001c0b01809945a0101c11640d1212000c6800080c404030020202811485008524028020b00100c58044071000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 801249136 1250 801247886 801247897
    0x20d060b030d120e070803030a020a0e030a0b010806130f02011b0606090204090e06040f0b1b0c060109060501050c0a03050904180f02043213080c0619110702210f0102 73
    0x440d03041100c2200c0038804e90703851440703119050355500144001940882c0c0c69000d42255540c6040503000350380c1c803000180c284600403c0c11201588080c006012112003006020745c45610b01c1035404d1440901e0319400ca82241e00103000b4100206455480c44800e594148405444c0e07125005100b020703100c11351800690803501450014614101d07668004038000a1028002e6030441c02c240d12849141d00c0d10044110b0050146032040080d120680f170000b40140280700c11842d0401405441d41440300d0b0b00103560782c59004504204050000c04544400418661807c90341414070a580380703031510214014220400180c00e1a80c00300003010140701d05080800c4209101b128100201c0a903400090907034a80100c2d0400380c91000341c22604900e0344000f42c20380100ba4070001d04610140341ea2040400d5000c01010380581d080f0f2002c0c07084403628a146410420b018610070b0050001ca101054400c2c015840068420402c04460b03580c0d002441c42e084a00110b200180c2e40440070390305003035010754082d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 801250386 1250 801249136 801249167
    0x1006090b1b010203072c090a0504021809060718060f030e0c060f0301050a0501140a08060102030702092703031b090d0611070c0807030f14330a0216020d060b030d 71
    0x1141e916038990040c0311602d84071b10400819070740090312242d180c08024a4024002c0760000c5142154160410195600c0d6108038160390040180d03143c441c0d4000e041091299807a64100014801840010741145c0381180c134208074940040c040000c94092480c0c080d5041007642c100c6000180a503241c0c101070300030340c1030300c1c410743d80d14004684d200e004494080c40c08036407441c0144c06024846181d4030640c0c0054009105104072818003580e6000511a581c040d00c0d107540cc480c03034080c0001d641051444c81c002c500c43c1d11000c0c500303600c2c0c000c40d0300a6801605044400d03848000400c10060340d91040c0b10014550040340c100514049007101c00c5c02c0b80c0c404042aa6440f00100d400141131100040c607005403039102c03104002c400304c1035440c1100c003440301e00c2c580b40900410071804004022122502003106040005101c0003400340a181e52050002c1c0121000700e00400c054101481c19106103503c0a074140e5900107094007030b04000008103038100c00c00b076160150420007840158421680056140c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 801251636 1250 801250386 801250427
    0x103020a140f040f08070b04062105132f0111100c020c150a021b12100621051c1403010b1c0504030c03050f0724051006090b1b01020307 60
    0x1105c814041e13640489201c6e440e51050104170a1295500c60588114550f000d44980d01d01180b41100380820303074004460b01508010703031508400c103000201e08a0a4844007c00c080703002407004900454900e084d8440c8141808048003d038660002d040002e200c1d4211000c40800080c85076260081d218044003103aa40308210030242101041103000444030852401d0b0024a4018100782e028030034170600541c510b503c050b5100300340b802d6038414007103480010b81c2220009940b900b00380171700d00600c81e07603844d59882140003079140000480c00204200040310f41c40003603c10b880345139070032a0003550708015000c8000700400001202025a0060110300c4c00d02001c0d803403452a1030341d82d841100c408a40c080c0c00039140d003041e1004240580e005001017000007994a107080429100d42c2c5030303030000105030614551010a980d0110b10300e4450680c0151080310b040c904545058402000b101141c02a800c40190000380e01c600491105500c0341c08188a40096440380342070741025041100c8009a20384400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 801252886 1250 801251636 801251639
    0x30312010f050a080a230f0d200613060b0d030e0a06051912060b04140f06071502030702070e090c010807021c1d210705030a0803060103020a140f040f 66
    0x90b10b180741d081a00c0c4c03404000c2c00856120b441c2d9650569806031030b041d220303059542003024aa0b090104041d00140200240059504110b0003048050150070312001803000709000320b9522804503010f07811940d00d40c504100c44801c2d051100c010100c032075030158001c00000c549010035070018000f4038030420450b0301c0100a5520b910039542403099481d203003444202d550350050040d01800440c5c24811100800083d840d4680440e229541d010b0303040a002c4510281c40c05541c0c0c504050302003240c3d9402e235006400c040103590344801c01c00840f0614610b180c0c0120008040034070801c9004020504800c0501c140d042c10445103484504a940c0c150000313015400240c1614000070303240700c20b98101620024010031460044401c504283c1003c0c2202407444000e5401ea580e582030407000e2091401451818610024150700c1c1c481781da4801c3d400ba4010200030390100340c100080e240c2c05442800c0240e84e0340054032088400781407600c0040716000020401d4207100032903c0c09007003551103108450210a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 801254136 1250 801252886 801252889
    0x60d1b021009080306270109140c090303120c090319030201150302100c03020102040306020307020c01020d030506131e0e0c04060602060f1b0d0c050a090603181b05030312010f05 78
    0x103401c1202d010300214400c01c0441c40600b40619007403540c6840140c540003121604924000700c00c42a40800c0b0401d4440c1c05401c00303032040400040d0000b01d20100e030b0f031424000c1c0b00031a44902680d0b040012110703050300043c1e1000c442d4000c9681000c1c0040c2a07031070803940c10700c0b050b8140e01c803070341c060f80107600c0c008420f85150324150031070050301d40003801c803409454640030032200501805d41c21000c55409100c000700082880c0081d5024404a4000d410f0301d00300c00c4002854104000780c00e01c01c01d8109010b04c002c5844a6005a4074114000008a811000851009566201540d001114901d1302d1880040f03100c02190185060804950500040d6641e450490f0b555205544100c4006040008200c0d80c2c0502030800c101c44042c010301506040c00d6030105800c5070040c0c6c1c101c001107440010020f0300d807175002d45541c000e0a800c0c02c040000810004a42e1030a241109009101e24038a8441c031220102e100000801030000404603551010030300c501e104946002c0c45964949118044082501d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 801255386 1250 801254136 801254141
    0x3050301181a2b050c1005070c05090c0c1006170c03060619030c0303050309100e100e0708011503110f010219021c0308041a0601050d0209060d1b0210 66
    0x7019150081001d50202c10010824000b104a00c008010f200c40182d9100e02d8070000d03005005540504081c1c00c1c000c51200510420303c2040081d8010400f0400c9a80001501c030741003441035900a0354041010303555010000b443d8420241880d0712441084c04d0020182003641210050302e55004041e420101d0107050560340d1141e03150b941e54150040340020703c1c642804802c14881c0d5548100c0007060b25905c1d01c5a4000702166001500002c00000400041201c1045a0301040d0b00704182001140a44040d19444480000c030041803281c03104a002c5d00b1800422a141c05489524020060701c80003880502e4041d44ca444102c40c103c2e2904845c20300f51501e0343c100c100401c41030700a00b106583c9d418101070309003c2210102d81c001c1168402800f45042e0a4811140f2480303034840401e1401c103410800b20706154124800ca4960800c41001400c1e40c0c41003ea8406400280000d84c40300070381400200f00c0e01400040807020b40c80c0100c14030b08096180380043c10300c02d26800f030f1001682d90403018400d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 801256636 1250 801255386 801255401
    0x81606020106060c06091703040c060806091e091f021c020f040b0d0e0303070309060e0c0112020a09080a0c17030f070b0702030d05161706030a060c1202070305030118 73
    0x214013503001d14400300349142c10842400340300d4411408078402600d45202c141d0000d41c0c090304c4801412100340308454004101c5038226400322480721840c5020380d41c500d611080d08411442081440300440c0c4c00400c20001c1140c0f020300211050840c100301007072403009400006040e000c11801040f26401e04d14980f080f11810a2802500d0746414244030a005440c0d0010b0b81d00c01c182c07030f950842c01c2800401840614002d116641e400304560410342880b400782c034203044148a150b00b052010410316038101818004e040324688015864103400f000540b5801255401030001c2d0044080490810101039480700c00c0d6680300403991446400860703080c4c0e40b8012220a120035190805c8000c0100b40c181540a922290920441e807030281c080c0c40352400d446098625220361070008280750415500300100c802d0704410b411100c0070340c0ca0854002544c0320341616015044d2903964040c1d00c1250304c600c6101c2850305400000f5591441c441c0f0300100340360b01c02d11030701c0c4502e160b81802c4803510009014248 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 801257886 1250 801256636 801256649
    0xe0705060c1924021e090109031b12320303040602090d02060a0c0203010c050a0813050f071508010e07020d0f180801020d0606020a0206030103062301081606020106 72
    0x5050810500801d803284a0000d003540e6403d100440f4420300c1c103404640400010290b0009600c9125500500c0c00c0b400c5c1d43d2440c40e4440c20280301c51011030740d00104072001c40781c100c511803000c001c402000880e04400c0e034028004603860700c121041404181070b09140c601082409215002010701004070ba41c540301c800104058104001041c003194643d00074040c0302030003c0502c058180c032503000031036a0380880b41b80408103252050010941c90288a003641c0e013500c50511518100c5030403001840d00600408a04401031808074502c140201085180f032003000d944121040d19807680f102254031000c02100c140060703010400031a040c0031340b210f0386018210765001003c40c0f440d505030075100c45605c0424001000b12164041e2445807252111a00900300000016559110010f0100640700c10781c00c490155404003022303000585442c022241101c0d0014000641c1003200b41686142c03400c02c55460090210100010800300310101340c0e40f410b030040e400b4100e40c3c00c2d0384503001e0382a5461842600d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 801258992 1106 801257886 801257893
    0x3050718050f0111070807031b12030804031d0a060903110901050d020d2109050906030c0108070f0504180e21071103031c0e0705060c 59
    0x214840c00048544654480c10900400c1030052010b91280c1003100c0101c0300e8070400014400100586083c2090750342c2d980d80ca08080d0358440003035150304d1400341c1c0e40c100043d600c1c079403c5040768020340c103480704441c0360b44648041d90f4108601d0702d0b00b0b0304010180081c22407503a0306c01d0318402400352501e440c07080900314180100d4002000d035006000d07500c1c010040c08256201d1130b0001105a044413218940c441e14a440b1585030b07200d0194041c0c5401403910111420340041d1070b4816100151086500b60b80d0b40b20415585800054615010403416004100d905101e5030b02c1c045400101c0c2042464a40e0f00c10344910008108184040035560f00d10410440071030038411910109810007280c00310b41c000440c12035451081c5035005011281e0b0540340c595945040c000e5941041141071504195810100600050001e001407078001c1d000f041004101031508406032612900400c3c0207 = true := by decide +kernel

theorem cover : BRFrame.Cov 801079136 801258992 := by
  have h0 := BRFrame.cov_init 801079136
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801079136 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 801079136 ≤ n) (h2 : n < 801258992) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
