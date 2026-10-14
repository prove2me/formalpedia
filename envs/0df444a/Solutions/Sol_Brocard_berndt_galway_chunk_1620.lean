-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1620
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:54:17.648687+00:00
-- url     : https://prove2.me/submissions/3d340503-1b47-425a-a7c5-fb3d8901b9ee

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 291187050 ≤ n < 291366906 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 291188300 1250 291187050 291187073
    0x503031e04410306181c05270d0809011214060f0a060c1b030f030c050d0302040308032a031303080a150b030702070e01091a040b1302070c050405070804 67
    0xe0b080841c0559499000009560340e8001c1c1540c0558821300440001c0c62500b0b0003080c1003c00341142ca19021020010010400d61180c17041c0060045003400047c2e100351440401c050208004104050f8941240c541d01c586a00c40030303200b81400506545810015007501880c0c411718280c2003100000e240c20014000a0031910f00079a12442c2502024098190402c0500f541541c2100c00b0781000c00d90340e44034081c00d018982000d82562011210b1404061b40001610400d82c0304805540e1948401c0d00b0540c10b900940c0401040c2100500000726942c0d01c1905480c004100d45c0342a078855034940a0215140d403080d0707400c8000f41105220708051640082000703810210012080088200240c0c1c44032505c106030040503c41c0d0b0002012540040c402c0220300050504019101d40d0365940d1072110b4001e100407040700c00d41c0c2003503450b070403035900d0240b281031b070080805042c84c2642000105d2500081d8808101290405000000824103484038441e140c0b04840a0721110558100740c00d14001800 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 291189550 1250 291188300 291188399
    0xa1101110301051c08030a0f060512010522031b06090b0a0606110a020307031205220e0c091509060c07031101030b031603030e0103020d0203070c0204150503031e04 72
    0x4e500d400100000703070301401169404804080300066452491300d140c0d020b080540d00207640089040030030b02e40d901c8190b010902800e40041041000d0700c1400d8400e00700561042c2c041c0c0454580010b044041140c40c0440041d030b880740200081071000360342d0f03800e41100195440010300b03a8558090085d240c00140c00c0a00c83c030343e14000c00310031015030b0010760b440c40b04e8003009288081000c0b641500a02520650f2405000194000c5c00751120030403040000080d0310480c60b0300034050000c42d500c60348007011503078504070103004a104400640d00c0c102c0c1c16072180130160340200007003110039015030b4244500c1c8090340c415083d1005e1900501d000409407860443c0c01440b0b5080320300d050741c014580001c080c0841e0f5040c10081c07406200080103030b009000c3c22102d800301c0380c0004104040c1c1d950240341707050410300c01c407010068400074004030750b01c8482900503a500355108000e01070082d43c4560031040b008203428985450a0349541d20041010350004049880c80c5615150781c010501420f105920075 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 291190800 1250 291189550 291189589
    0xb01050102150c0903010b030a05010e01050f0405030d0b03030405030d08011805250314090f0601080d02030f0d0b031603061a01090e070e030d020a0201090905060f01050a110111030105 81
    0x501d00250141c00c200098000f080d400000640401c541c0c40079003000888003001019103980340d4050500c01e002e00b14803c2c0c022680e5180000041745100e00b18149030069800500a41c21b12030b41e00301c1e140040499142c1d20340d1520003403100260340e59080111118414055840365a10351420100c001c0b00d881500e220101d60b4144010005006800040c0c18005c556a42c40400d607841d24003002d4006046480c3c44808040c480e00030402c074620700040c0320b420050950129000f9070382c1c0742074283d158155a421030006800421100440c0081d46014000801c4c044000040520312440028a4030041d0780700103900c001d40030020000e1046a01c1542040c80d1140ca4070041030300e0100008000d05040d02170700302101c0100000c5075565200700c1303007169074410190403147c0d80340c505000a50744000d0000200e0004101140204000210f8002d040c00348070003400440160020038010740359504410b003190204148001102e1920400340107143c3c8103002c111050360b0329410a01400141d081e5107001c03c415 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 291192050 1250 291190800 291190813
    0x111c080a05010b0702061c021602030c09040b0604091703011e080a0f020d060b040c0201020418022a03070c181d07060e0f06030a050718061e0324030b01050102 70
    0x1c0c00d80c90800c40d2010355045548540d1114400c110507d0300d01c501c20a007030520310204100460b44409080c0c0c6034118001c0741100c101e16104d504100810a00b1036004151010b80e002186140c2016004214003500c55559054490804982c8414035002648188602c00c40c0c0880c04640c1403141851304007070541200074080c003e00d941c540c1c1800307800610009000c1c1d03070444001002d00900d9071046514540003401804599880b8500902030341060142840009214000420041c40c9100311200c030b81c2521036455800c40074400b12008213500d24001925800f0400599001078a242c1000d00038007402865070184041ea100d04900f00c50054001b803205240f1012038840280f0000341e60821140705240446828403d4408248903051421000390022804003c0c480101241c1d004184580c50b00d61f54a07460717054012240d91005001d11402001c15070030400c1c40c220340010700340d480002505003404181d5400c1c07003d03003440c4075085124058000e00c091106100300505081c19030f004000900c02442d5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 291193300 1250 291192050 291192059
    0xf030304121502040902160209012111060918040b011203300908071a1012081207110f0f03180d0f0c03110103140a02030403111c080a0501 61
    0x44503896100040c00d903400620b11000d50542c15011038003e040b05101c00c0d0b4580440c0034802c41c01c0150b42d03c00300c2c852036594002007008800b10307000c484480032212011044c40300c6030303c0d01c0300480d616201d203070380081c0c04002d01003407500d44286d41c03280f100c43d9a4a072859445e250a00608051040e0010113075060507094890100b540150300412264000c0b80300314000319883e0810001c8010700008400c481d0a00480c0400c0c070451002404803c2e0040e03000106483d20450300781420f08048690a41c40c02d03031020180120307030707112500c4d103946403281000510b090500c00c0c082c091600d007114490001107080c00b1040c541602401282460f030111380040c024400c00b0070360143c41e4020f00001c42480800350315503503415038074490400351494202c9035141c40b607203041c14040c00c004c956000603103101944004540c40c951207442403114200580b01510480d0310b8940035480079500140054041007a1003200c80c10343c10701444a201c00354010080c07910400c100d4200030388005002000c440f06a850000100b0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 291194550 1250 291193300 291193319
    0x60d0201050403030806010c0534060f050711090a020c010b1030020d0c0f050313020105030a09060507020c03161206050c0f030408090a080a020a0b03090a17090f030304 74
    0x80640b513060401c9945559070500481c3c20070910782001e01a071044c10542059032080c0c841e100c8910040c0718814229041d8140b41d100307988200d10400001850410510248034424005000014030900d5001c2a502043c0c000940700a01550301c1266075071b000606003640c2c8800d1040c00c007615002c0c1c0341103170f0f03044070941d015285074a1184408441c00079405060389107003072251030803c2881034010854460301071103444801000d070343c1783c1d030004141001180c0d03040030302440031759100700c420740c2c0450f1426aa96004440d40e420140c4481d1405480704940000640640a020700c0b49c03581e5802800106804010540313007034203100e001ea1803c11058001c0c00100c00341140906aa41c000c400454181c8841080c00b00078071034070070a500030070000310520041107440e030004c2241034422030380d10581e942c94014041d1030310100c4600950080c8142d20403c00b406010307014543c4021007c017074404400d155110742d20241080e05600e540c0101c0000c080d0000d2603e20300415010106400031414071f070038024580d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 291195800 1250 291194550 291194557
    0x1b03050703051b090f0c0306032b020d0216090b01050d1e111e03070c05060c03092107111201061815081005060f10020a030e0102240c09040e06010e060d020105 70
    0x61600140000012390380c0e480c00c021100045203100200305422000022201d8454030f405102c07001801500c0780c0c8074005100145070260303408906411240c240c0352408030401448180c0507241132000510218410012a1140003003079103035210420314001c40440010215201018071788100b010501c105980200b0a0982e0b0301161002c001c0c03a0355986403100245c40403401040300a0a6128100c10000700d00800405180078904410844503140040b010648045140500c420020305092146d031000c6650308808000840d00546040c1144111481090030741b5010b80213442c01c082c0c07005c0b1001c14040c00d4820300b0744404860707004014207400c1c04180381d00d9450074003041071003649940100b005942e070540c032021011002000020500c0588a02a4848443c2c4005901290340b002c0e01d5840e650000c82c000348842e400210042c182c84001d54580c0c07101e80040c2011100040900824165446500c9000c040200f4a40200340303d601d80044284c202e41d006042a0140a07000700719401030741c001095 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 291197050 1250 291195800 291195811
    0xc04060f1a04030804061101050a0501060c030c170d06060e030d05090d080405041409100b010801050103150b03091e03040f120302010e1c031a0901031b03050703051b090f 75
    0x9403910300d10302102001c15000d2900003501060300050001045038124840556140001000f80b180350340300783d0050300b100c40c2449000085845d10740800002803048100300082481014210702d00c0e000c0210f070310301e00e8001044811031503a60b040244402a0031120301a20707079404030010b0000712144200204507001d1203202c94060f20044085030b0401030000180d8001d410068010030001050100b450103002054a40e14002c0c02001c0e0b112500158030b0091041c03501d0180c40d0000c07680d00e0600118000e041d501025000240d01d03a001145a69041c1c005502480f284001884124600c07007401c0d000c21388002d8003884030341c002c2200300001d8a10303441450480b4240e80955800342c8443c24181c0c00b40040380e10181060080680250291a8008025044001580e010054080c8006514610110b040074960780451210010000144119087c1c10200d415151100d142a030300e60301c040c985403094104032101e41210900c0003072131090784c20030074220504851211446c140000c01e0200048050700 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 291198300 1250 291197050 291197069
    0xe030f0d03051e4b012301020c120a05330106020c0103090f080d143715060f0201050705032203090b070b0a0b040522030c0819020c04060f 61
    0x2440c0a0005030000c1404122024181c103460650041101d5408203009000c0c4000c1e03021006041c1905900300c6c41959050f00041c0c000b003c0c41030038941000072080c6500000180c5d446181c04a4000038400c1c4044401c042405207200015170f6507003103041c0c3d6052600c0c0d5100d101c00070340380100089a40000d62100912003820001002003d5045c49803c2c441c4000c0050300f0041c0004440c02c105605034065010501c1040d0311240d262900c0f00200d00c4445000280c41c24101c0b00b800c1088016814070b00c442c010b804144d8005203603d51402c040c001c0c40c1c0c80782d100710f0202d4003c011241c000ea4081c000c09074400845d00e030061035894100350351640d074140465542c12421500a0107002c042c003450410b0050444a04140d07290501c03032808110195088810002143c1880b40c042e2160419008440c041c0f20000c40340700d078540f582c52400706150300702c0750305404000e40f201c3c4101c041034004000f060190180c61584070241c0a241c00646012200d00c101c80c01145060000c201001e0300010000070b640e01b144 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 291199550 1250 291198300 291198361
    0x711060f060439050c03040302120304030b0c0d0c0318030f140f0903010b0315040b0901090f0804080c1801060f050d06060203030f071107060e030f0d03051e 69
    0x2080090405245a007081200100d804405400c0050300700c0a81020340f00580c40210711100807a9203005140100c07005502c03e000500051420258000100d8030b801c01720f0f8185aa2510380c008030300400d0300c401419810029411502c0c05071805140711031545800c00348103040c521aa0082d400c0b82030740b070140800110051158026204a00d4254640215103426484805d81d51070b00440e0303840300e14542e10a6290000c81c0c0300508000c144400042c1880d6024181a130360350310f079030030f0080008046514956030303a190344000803440c01c5078840342c0307000300c40e1117441e40d08008a80346051000e404d407911400c0c0314820081d00d0200791440ea8152080c40c640010244071a183c142c0e05405640d0341e00c190303d804c4c16808200e4960002c0910b1090141740b4421000303865015081d1000c8035090040552500301040520020703001d4884035040c4500036080300c60f030581841d0700340d061040140521000a0321a000e008182100c0035800c00500340c00d03041074085041080c00c0310500c9100d208001d540d41102c0b0f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 291200800 1250 291199550 291199561
    0x507080f09100b060d0903090513050603100c050d06060806040c110c010e01020106081218220207030504171e030909040f0507170f16030503030426070c0306050711060f 74
    0x3042500d1422144603c01c0c03003509203030707c0c01030100c003020301815008038100b0040d2040035485020b11409108040d010b0040c0418070040400903100fa640c80d0014800c00f0445050a42d1180c800c07080201261b50708d011050600ea810041958503030082a001c0081004011200c16030100b12848400805d01301291607840c240300503809030805500c0214180240c4241d85104807200f4010712490413240300c007075081e00100301080880601e00070f0b04c3e5201da00ca1148452040160350062034a10b0190030968101703540c5180e00c0007041a5140d4850007034002e07000511482500e103070742e4100c491b8040080c60914540303002060143e480204050001000c0c2c40503002440170038010360f8040c0000070164080c40c4807070f1402c10f0340c540c6010f021641e240300c0c00c214081c5014030441d1003401d46c0c0c1c0c0040914510344031a2940c000201008001500c80b030700c90380c2030490000301a002094054866130341c1011a500c2e605140040f00e0000745503e042c00115030b10503c1d0040b000c50400d0303012030b64801c00001034840 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 291202050 1250 291200800 291200809
    0x1506040803181903150b0102121605010b120d0206010b0f070b0604060b0a08040b0708010b030114011809150e010f060815060301031110020706140c0a12030507080f09100b 75
    0x8400304514080845002006205e52407000290044601c102400034600e81401244d60302102c240072100d5942c14040f07002d06403c0b920b401c00301503010b81d00120740704c0010b00c00115020b49130540304030141d2002e0305c900e0795190140100d0f401024049000b60911507801e006640901c20180c00400c426404c100003a019a02c1d5402000900920041940c8a04a80034043d000304404e860030b0f103060318654005201907204d41da400b416200c02e01e14103401e40e4a04034200102c075181c40b01140c1030090045203606001d60300c002d01720042c00310310408500c0c295004103020f000c0c0015003002c008c0020240060081034041600c08045805515104d40507940e5844050b005c90a0f040359148c0c0504004000000c0c07082607002050320241c00c0f82e40c40d10404c2c40440a1b42d40c0d191500c00c04003c1403c00380481c1f10f140090300a03100c030307107010300076180c0304441551400c5001c40d1149030140071030b50341c000f0300c45000e502c038000c0b0394401182031206585d03007080c04415a5444004545060365510341000000039100c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 291203300 1250 291202050 291202069
    0x323030412030504030807060212010e01050d06020c0c090907060f08040203031902150103060504030306080d0e10020f03040924121203020d090605060108090102091507030207150503150604080318 86
    0x100801c80c0c6d61501b240303140810295004c1001c49051000d907200200f00ca83c00740ba0294100d507401003240c45400801e0b624071001c1c2d04a616800d000b80600729092400703460300d00f640d0b88140002009000c80b00e04000d00644080f02e10326070303a070402c0b40020070800161800821205011402021261a40545c100403490501c0c891001d0880000d503a00002c100b00c52504124040c503c65101880f005840f400100d5413091030040080c0011103121042c10b5500b004c61400f10404001c3c41035a004600d030b554501d256038456400160394030f5880203000344080ba081c82e03c0348051108038003403901916102f003103121818800c0026002d50500d5140c0c5484500031382c1184c0c0e001c07100d00c0c0180859087c90403e0b10041400304d50403804500e00304000780e4140018400c8940d40321004107010b05807013200308516080d03000102c0480c294070031944040703080301042c0c01c1110b5003151940c909035245000b45034510251082c0b5171304c0303000d00c0003488140051a404400d032416032940640c9a003580c41e01e03000003440f420b03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 291204550 1250 291203300 291203303
    0xc0e010504030b043002010501120213050c0c120d0c02073c030b070f0918050a090b04200103021206060d111306110d020616030b1009032303041203050403 68
    0x901d41d229144000c03178203048104600c480e50000c0180b03a9a82580650718041544000c1d803020703a40d03d0042c076000c80d951000c0c1c3c1080c41404241c5c1420704145900d80340042c132034114180e1440105a008002d54503010b034041d11b194038030240850a19144042d103821100d1406900190044182c00e400908444d1017641c0848400000101740b56032428510403111055640000281c0f0ba0340d4480b589078003d01e211002c560750180010821342101503180c00422010f002079850303079210a00794001c14032121f4103070300480c022000c805c0b840c40501c03a940c403a0401c4142090505005020a0340604141e0203030560190b016140310b07507188255103c5c80000e01c4914a070310319150b400308004d50031071003400c041c409031119a03c03104510322030000c0160b621103102c0500300c01a44040001768810081c64090381c200070b640e003400b099441c117600001e01e022101800c41c0c3d002980903081082072140744265009800d0740349132260003c41550600503220710441c0221036620208081d1402054481c004640096 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 291205800 1250 291204550 291204593
    0x60724020703021501060905100504090e031b011a0d050a120e01090504140103080a09030503040b0306010806010e01081602070801021b0c060406020a0303090c0e041103010c0e010504030b04 83
    0x10011214025040400140c0c0180318a4900280004813894424181d501544419500380e140170100401411036401810401c00c0500c00060301c080309000d0b4032803009030a0040c5441e031041020032030ba1002c551420b4100e0341e040c4044480b402c1c1c00e1940c0103514000642c0d81240c8a07060742002482c007410b081008140448417480c0740340311070b0700168880ca4203000366034101800399160704100130340301400c5a03103d0080e0180300410000306914010304a504481c1008400b95907a900d4060a42e000b030352140e0208030740041007007070a6070310081c82540503009080100b40030400500080c03064600900d01c001018011030000ca040b8000c000640040c8205802035603540d61414080c0402100c142c2e80c0c880d00c0c403c030252600540b1f01401507409951980c0d004143c150150344046014211413603050f02e004080403c041501244131051602c503e0003031182c000b1507410581490708580d02082004100710100e500108075a03846000c0b2000c481d000803031040b143c0c4a500780000d0f10303142c078183d00710907 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 291207050 1250 291205800 291205853
    0x6030203060a050402010320370210050c0408061902090a0303020f0c091608062205060111030c0a02010c060b1002070806070509090103020d06110f181e0607 69
    0x500c2c10b2500050300c91807003a42d050000100590034111030114a00000340c030b40105204407840118808109000340754106800480320510310b071200d52105412404000503003010710b081002e10103e004482d080380c0c0c410240c43c50f0515081e401511802d024000d1000201503900d5419203034925011b9907401400105451502552894040d60311503a600d80e0b50001d02560054100d81e10f070000b00381d0712a81c3d1b020140340da001c83c0003608035001c250080c0290b91241c0183c490201c5d60610b02107001e041440044000b8060401d000003424812400c14a450703558800c04c002c00340d0305d8010407403151440d0b0a00700001d44034000c3c034007100070b00701c02d01940340c000c0201d10402c003e00781e002600004880c0300005a41c7c4580316800d080780c8900c50040c1443c0c0019104004100604140031003450140c020100046d843c403400e081e0440c19401000b51240b030241c0400c0303000210040305408421a002141c4a505031241d8545486100700e40c600602e21030900404c400e001c2c40001400c000c0d042143c28640d002 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 291208300 1250 291207050 291207061
    0x6050a0807230105030609042405060108060d0201090506090d0b0a06051e090705031306052508040f0201080402030a140307060c030515120111040909060c05031e0402040603020306 79
    0x140e40038288100c54035801482c0da0400710320b08084180c1210300041e50381c6880c60b6568028010001800380c01110790b07454a01200031459140c01d1400c0d6403041c040c0010440703040500c0014045400a441a8850000c071603101c0f00603a042440d44048810a131a01519001c803030f0005004500102ca002d0300d0201d105042103c241a0b0390b00030420342c0c408540140a418040c2c1700700c40300303460b105800e0b9001142d00d80440c1c075843c0181c0103907510545034018001060310030f40c0c03007006440d0b00740c5a0103000c90001c00340242070321100c0c803065041e416500e4080214507240d1140140040c3e0598084d050100c000081420b5407004e2021218241c0c01c10110003034103074201d03030b05940d940c0040000d4680c03074030300940f00300344038030a008041c0140e5a207180c00d0181c1e040101040416440d074a540e080070345d45d0b9a80302180d40184005000200f60b05100010107a10604184007078603e40c0010004100080040000f000e14001c1a807101408814403440c0355079503403011030020880d6420103507152240f1020000d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 291209550 1250 291208300 291208303
    0x80723040305151902090d0503070311190506060906010e030a03050304060f02070f170d060b0301171501090e100f0207353406050114100309030306050a08 68
    0x200e0307214204035070303e14114030003007031800381d054038100188100d014400030704040c66000390500f840020544603d5861030f586507465648802012030105002a40c1061180402e00c8041c1880c110400c14800d04001d50743e4146c0c031030380020141c51086c5211030114150340d22070100e260714a000501201e40e200032500b406402a0401c80e4212450f600301405070044102c0350013516501640802d60161091003a80c51551604a1481036a0113a00070f00c401c2c00300340c09034080c3e03170014480303001c5450b900c0d410300e81c000800118040901301e860384113980c41c401c0d01c402d5200181c11680320150000316100490160360500358000e00151141d801c040b44070031b10421751b50007000000e02c40c20442140500807880c1d108042c000b07282c0313140924181d80310700a0a203890f82c024240032050429150241020b03c03540b4140c0303100140c0d0260301a084449890804c5400d2044501411038418000305403c8600d000a50510400b0104000c041d1545580c1003003600a0f001076014110003082c00719111384440059 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 291210800 1250 291209550 291209557
    0xb040f0c1b1104110c0c040c0c02090a1b090305100501030c0302100c082701140f090609030708010e06090c030309120c0406150201110f0d09051002070302010203010608180d080723 79
    0x250040c082c6c025000501d1805228035003001c0540e858910900c0385540811503010002000110403540760385040d40c0c030801c0701070421141c03101501c4400369181103040c620326015010304850101032801005101003000320040c1d004480c0e04460300a850422130a0445120620000003006410003080e0b1440303040d918484c500000784203066440d05c244500d0f004550f404a160f5400c21504c00421209901200d840b0003840c00e1100505018941100c040110703190001a9021290302c0e5035400350024514001e22280741c001108030300500205a4000c0041d49911074ac1e0000d51141040c4810020110401d0164440f0070400074003c02449582e0340c0e030523044c02c600c03001e01030055180c290300c5102029804c0aa41c8420845a5154244001c8401d84c40043c0b8141206071080e2007480014141e10400d030006042d00ea2290b40007507120751419201601030381010b06482c1c8a41c0d505880ca201c454800164003004600628225025850361513007030704e103000850000540040300c100039524003a041d9004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 291212050 1250 291210800 291210817
    0x32e0303081501080f06091003050a0501141b0306220c0216090204080a0213090c060e0a09090305090108220309080708030913051e0a0b040f0c1b110411 67
    0x446100201e200b0045820340310440e0a002c84104d03100100c0d109051190300680d00c00c0c3c00007512000103480740c075a83e01d800841542200c0b2a91252000a814400819026000240d024500018100d070700c20200e91800010410340c000e501845400d074421882600c00450703100700d0302c82040429000b8100a4a8a041c3c0002d0030b014121008000f40e000308a00c211030072036140b803010700302403903042d4200700d20381e40c1710b0742841f503103945924100e00402c0301c11504200070302c403030b403030704444003000600b8043c14080a038080b03a000ca1400314040c0c00f09412400701d90009000746458040307651046400700c1040203000540300281d0011215001701a0010890000d42d1701c000103e80380c043e03070380000940e284920324003250468204402108404d90503008140c000002c1d040c26080180c0c4150394409117107049a4022146445d00c2100e100c5090501c0743c10541840f5010500c074150721010b0107080d0b6503880759480c203007009040801c0d050101c082900c103a01c0074010700502c001c4d8540708500410744c124618 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 291213300 1250 291212050 291212071
    0x80a2001020c060f16110102070b07080403090b090108040813090606030c091217071104111b0c0f0607061b0e03120a0f0806060c070305011a0d0503032e030308 70
    0x440d003804880c80d10b152080800817012501d4010f00401150040d200302d03a001c0241d902400362400103105038802600c648411740d01d802d0345180500b8001c24860b056070010712034031810003152015036884411550b001d90456151551b403809070020b0002109641e00040889251a10210720168150081c035502c45107959004c607950345401caa121300d204000401030550034038503258910608000050000b060046800c02d2092400700041002e40700713041891444010f001580030a0f10f04404c0c90801c0c40030f4040010448810860003180442404003451407040c100031500c20f0070040e05410100c0c01e46036004820b44410740070040904038101d00c4240c2e900c80c0c0100d2459501d0210414251080c1501980d40c41c24040029a0305449001c1c01034040d6400090400c1070600100c0d00700020b4004501c20400011900f000001d080c13074000c141e4019503c100f0390390481c900814000030999030480b40c003158214441800200413403180d041a0300c0070959002d4074100000b4550000401445034400747d9 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 291214550 1250 291213300 291213313
    0x170c09031e0309040e19110a08161517180c0301020d0207060c0203031608041e050a030201060f0501051903090b090106140d031b0c0b0f04080c03031303080a2001020c 73
    0x5000d11b45404130844c2d42c1e80700703075404400d813408144c0c141142e140e520070282c50925400c1c0c8034201c46051140c1092012010000c0300b10400440e0304c0c0d012072540b04a81e600d041c40713140000641c3c072142408003500920b80c4040b0132030320b0003101d46c061080d2f008008000b00215510034000050b24043d4101030002d4030381a1810110805990000c012a4452203080c03402041d00c44210600f90b4024001510503150380c0300822101801c036007214a800f0440d4081c40040607418440c3c07170001c0c2902c607960000c4016002c001c0c81003241da60010162207141c942e10682c1300300c0428a03a000c030010100100090030a403000c030b041c4200d280043d4040c20030384a10100705c06c00c1480c98004c2c44001c542d0110004e0000341003030300310f401034030a0360038440049115003400400d0f1544c844c41010503400c10700a040030070000060403c140306c020422039042d500d043d400386060691502c0002030440075031001508010300007500b00c030428440c0c0c01980030084510484101040c1c51443c1034001c0d0044c3e1000401c620514 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 291215800 1250 291214550 291214571
    0x110712020a05091909080f030403020a0b01060e0f040f0e0303010312030615140a020a0203031c0b030a080f0d060504060603050405010c0c050d120b090103050606030607170c09031e030904 82
    0x542855115655480100303811030324020f008030090170765181c1071300c201905000c1c0c0e490301c008030002075015901a90040105032104d0401101c8004103a0040781030104070303802c01000d030b00d90147c0300f52407810072600062120341d8103507444040c042c1e80541c1c0c542404000004400c00000654081c04018541d42c1000120b840c1c541a0001d101d486000e1800309200821441c1c043c6041401000160000c0c030684c3c118100030303804680f86402040c86a034103000c070f0f20280820000e0a100309554004d04500a143c030704c1183d200d0501c24070420b00481c0a480000030525a20045500714000402003e0010451599034400080042009580881d155420008150080c903c501c0150302c3c602c0c2c000010b00444080d03800c0c00d45120169003a078443c1035071951034003891640c440d140180258020001340101b807030580c00301802d01e0b01c014040740c180700124060480e411000080300d03901100d0071500da50380d4031507003001a1520010180004d000c400c1a908135411010200242c8444c00054a080c403103c20714 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 291217050 1250 291215800 291215809
    0x105070f0c031704050d060908090306070e12031603030e0f07090f06050f10030c0309080c03041703120f1e040c0e090307031215030f050d08070f1d01110712020a05 72
    0x15031044540c400203090038203020910648c0100d5015101da8102441d01903007002280c1810011201440480c0c141d041c6051142003c0060414285108014515000f000000c0d03403010503601c00081c04059948000d00e003546010007003084403403441004c440549a884604001410000403008034242c141400003601d800c08441451007103100810020050b80d641108800400760b04201008150300c0b03010120125042000418190104002840d900c50074848481141491741514030795541c030411407001c00c117200b00074841e00400d01d0702400c21907848080c56824007510301d00d490022041c4040600c010031104454240c129030383c24040c240a99610510682c40e801442d001402148000c44000c0d21304c0d101c0d0780b014035242d003076200900c849c5859031034808580710a60412580c581c0800703100e0803802c0d0481e2034254000c07900e1411036540d41c8203071401000403003604844044800085544421a8020000c0401402c0740108441c101962070f46111800016500b050340984842000468036040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 291218300 1250 291217050 291217057
    0x301080a0501140411190f090212010501090b0301181e0e0d09120b06120a05030c210a0e01020a0b10050f04060803160305070c06030c11010b030601090b0105070f0c0317 74
    0x805c000c4059080e1424400e1268955580601011507a00664082214000c15198801504050b28016101c004180391660b1108041e080743e4140b01120004011074a410412607055070b00700e51452801d1951805d035040942065108050789440001d020fa0f1170703d10603880300451000031700031604001d00c02e610641e02d01c0c1450241c0c03c14001290700f0a004a14404005a04940301504642d81845030000090414580400071215600001207640c515070041006008400222210319111903040120164030311440000009000c225840c3c0c442ca40c0c0280414403032035410915000403480c0544c002103092036540607107440760b2030b0178500c4805814540b2500d002c0d0b0382142d00070740c5080d012241503c4007510149084040040421040d000203c0048030140144000d440200b070781568640c019003451454182c013100c0da0301d0304104c040c1554001840c60b044445807600060700b100c40000480d420f21404a01402682c0102c64030781c00c20050702c0091084a0003120030781c1e010720f2240c455906511 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 291219550 1250 291218300 291218303
    0xc0e0910050619110601120c1e090e0316110a090506030604030c020a23011214041b050405040b091203041a06040212190b1002120c0a02060301080a05011404 69
    0x41d00340011003043e540c0c0041401907100714280381c24510802c0440500d060030903080b4102e0409a0601c0d003080250514011019040c032509070382804046a800b032255807114030440c10f040d501e507201c0b070380c0102d410b004540c4014a100151041e644060415206490b4045482801500010341c0020070070854440c0c0b502030b9000401400c02500c89440c1115008519031003a6441041180c000a011843c1081461414000041ca101c0502c60300c2c00541284100003e00842071308103401520300040702d42c2159072280c0d00911680a00940e0720101740c003055107800c01e9401a2408080c0000d101c02c0c015194411205401140c56102c20f00e14070194278001a2002080e600521102800041c0d00c811a03583c4082d01408c0142086441a40d16a040c3c00c156465050010442007036411004c15000741407040001707440c0e9100780118010300a546405200c05654000c50104155034410340602c10201c0013500102042c0d01c958461414503261421080111542d6207050010a811620441168440d5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 291220800 1250 291219550 291219559
    0x1407030503013015050f13030f091703070507060c050703030e01020309060414010e0406150e0f0a08030d05010510050702090414010c0203040513021e0706020d0c0e091005 75
    0x59103003851804122407010940a8800f00c1c000140c0035168480080100e20303070044010100c00440101540c04070f07000038006581219881007000543c2400f06032518001da03151401c041201a0305a040340e0304506a0400c041d5010114a0f01d49066000006064420301a40c2901c103a42e40e20b0b14103450320b014412004205801c0081d00f000404e00402114461503810b005884c03900c41c5400018031079a102d90801000c0c20000e0041c41c00e01d5a004800155054041e1004c12005007440749103803240c441c00c0040400c21694038109401c50b102d0400c140340170000502180d824a0b22460200d07145c0d08001c40aaa03801d1804000085074606070386100300245464844c0380c0352010507005d0200740d940040c419202ea01a481d400d03400c4080c240b150b01a20052a4013a6850782e082c402004860422112422280d5006010320110301d0464202400b0b201c1007128080d55030310240c039148010b40520031204001e180f8203c2d60035611078000c0c011040c1a40c1c129000c60403a5511440a0702801d124010203402 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 291222050 1250 291220800 291220807
    0x60910082a2b050a06020f0a0e09071b020a0509090d080a0207020915060c060c031e0105030c10230a030b1e120a020d060b040b03190f0c15030c14070305 67
    0x40c800c940140b100214051400d9410703210158071110207a0740800020030140c0310000300364400c1e5600c10b401800810084a034240d060401c1a4010400d100e05c1841020f4000e00c41c49601c01c540d50000c0700e20040c000941070382c80610b01185c0c119103400700d103000c4202180e84100040e010885900c02c440d92590f0040480300e042c0c8a0240c92034104060f1102541c2040c8100002e01c003203401000740034850a0142c02c0b41d07a50f0b183c11321074000d0300b800c1e50317408081000c1ca8000601c036942d40800e20f1420600142c81d5200740710603002e41200e0220141588a5035203000c2480a40c05140b41001002035903200d8806214560760003045c010407950201484c00042000d00b030980ea00d2509002c4422a46842e5044075a40d2145800041480031801d10448800d9500c0041040c2402c0178024515581000c030040c080703a82243c0e502030b00c1508900b000809074405041110700700301030040141c000c2e1443c5140c02c08242807020780500100352400c0c3d04800b1030140080d240d041243d000172100c1c8181c0c1551072a06 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 291223300 1250 291222050 291222109
    0x31403070b1902070f0b070e06090a03060506190609060e01090602030d050a0618060e01090c080103080307051303110918030720030303040f060b010f08060910082a 72
    0x103040030111121032107140c0821411004c6450791303510003085c84c0a18242d414900381000041c0003d8002558180101d90a006582540c0d071003034000310403280c00c400c1c04105030750740c200090f0200c1088a17108119001000f404140682e00c18044030a850690b15041801050303c00107650309180c6105400040e4402c210310a01c018103900500d80040001c40c010502648175411141c10990009080c001c01e69500000c0200311180c41d9224010300d50b809081020000c0e1860082441c0c205000c040c1c14404000086484548601e00b210f04280b903000307201035529203d1501c581000000d4000e0351281c1043d5002c10154000d1226403a18013500c81c0041d0b107091070b60b030386980d03001546c40c840a500031541c4030101030300e40307040c4011403156100e03031200810160240b400004807084060081c0c108030302c03116042c8149400001294011204603144000d0b66110310400e030060b40306070058001130080b441903410300320707900c401003d001d9840d507004000d65088000703105100804140b0312011010500744503030b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 291224550 1250 291223300 291223321
    0x30c02060f160908030a022a01020304052b0f0201030c301b0c031d1c02240310051504050120010903050403150504030c020f030a02030a0804031403070b 67
    0x1d111520b0350070103210311580c55a0403030079500080411005a04022a0030b221807500080d001803414884400001c10340c00a00002e5890040d4080d540c00b840c5d4034044202d0225115465240701c036074505551103256443c0c54408416040500202d022034140300010700ca0030301454041d075240d09050b0191764003e9140c1d81100c0c04c140400d85403070016130b481007906252110381d603032040d00f06955281c10003807002ca13180080080105030724504144002c280c1c000910780c1d4560200d6000100d840c0f110b080c244082c000a045200d43e080e942d0300700d03850200302c5e02e0140480c4010b0b5220b000c08218034000315a480e070030b00c003a81d14140c01810104204000510066015507020b01103000c094940c5104444410020f908580b00e52600760042a03012604004204c0020303261004072030001000d100c107003407a0b038000d400180c01e02d80003845003100306507102c5e07191400c000601115030001c04032202c1d0b4000703040400096101c2c0c00203a40007107205022140303841c0000101d482c0c0c0d651200348e000d1a560382c3e46555 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 291225800 1250 291224550 291224581
    0x4b060c0e04020c0606031608071a0c01020a020705010305060a030f14010e0a050319050c060412030b0301020a0c05060903070302030a080403140c030a0306080f0c01120605060309030703030c02060f 86
    0x1a414404045529a42a101c500c0030788a4002000010040744c1080c0040520308401c1401e000e035141c079124414080001d020606104840c8841503075241e420086040c2c20050040e510420304562000c1644d600c407643c0060041c0403a00c0a0f01e00b001592507041c20301480a20600000c0d00f41d1004004400011b68a090055030303004402c00009003204c002a002414421484010f6070940c2c4007003042e8401d50030864840720100c6c02400c00602d841c40c50004103031604002000549209010410300301040e00039000034038000c00080c0215556180e4a401405405155105540a120b01e074001410550000101c401598043c4c0056003040c2e0000021200b07003000901c11810440656100c60b1040e074808054280382461001940e03c410750b03c0780c01000c0340c00390b83c8154101c0e80105403e8110708004070b60451034527020f18041e0021321401c2d24010140001e43e1050350040c20000411440c800040054600c4501c03d075030602c208800d0307440c100e0f07079260141e5179040e40b4422440810603c4e02c1041c100b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 291227050 1250 291225800 291225821
    0x40e040c031b03031803021507060f020c030406020f030a020a02060c070e0103031110110f0f040803040305071e03030e0f0301182901081203060d4b06 66
    0x222140c0a48a41e240d0b1900e0311401180d91082c19151400d00815400c4181050704100d03141290340c085186030000707401205180021107a0750301c00210941805040d400025400e60440425580c400844104030380da548a441850700500401c2d02841103100c0c003104441102c4d442d54010301c0740144075001c0211560003884000058031400340c000800030303040c0000e03500a6011703407521101004901100390400a0304c0305030300c105502e40760400c040c8806240c107840c664601c1954290722601804283c0140c0d100719000a20075105c041400400c106000480c5016600296030b041c02c01207020500d203440340b0b02d9010060105083d20f42081550071b02c00400030b01c400c001000403d10070800c032840e42005441c001d083c0c07440c004800300c282070081000c2c0002d12405040251256640c5041d15060700c0f443c550a040c00c0e04c1034000040b403c0d139510000e0010270150001071640b00800d0410103040100381040203420b90004060b181001704c6141e016050500040f00e000b054060a5580d4407801066030051 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 291228300 1250 291227050 291227063
    0x1103010b131206020406090b1201060e0105271203030f0106030911040c080f0c040506160512031602061513200c010f0e0607050a0804050712050c01091a040e04 70
    0x200c4600850b040304400b8061480140d4035414a88001c20700381c903d8200e01500c02d02007010001400e4840d00f004e0454020346010031000d0300707210048030140324040b000300d4031549104102100320350462505080a0080b10700344c80780e01c0101c200031b0b2240001c51303444002585400041042e14008d81100301c416201d58211800c0420f0900090308640e0442003d9000031182000c00521641030030303c5a400c03800c03554941d810710745400c000845500c15490210003c0743c00516600030010100403001d9200b1410441548030f00d002c0440035005e03041c0301c251100511a20011440440d19031003201c030b03800300142c06c40b154441c040d00d40c8005064440c401070742d0040c00c00d115104c0560040040e054070342080c2c001064480c100803d8030255134940d904101c1a4208038103004d09103030000b048030341480035801c0c103c005030b0321070401a06102080c0d101340c641e900d11101d25400c0040100d501d00700c5c81026220440003a0305d80300c00404414182d00d046040303880401041c8051505241e207103900521444 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 291229550 1250 291228300 291228337
    0x4020a030b072303041203020f07022103040b190806010807081806100305060a05061c0c030213141312030e01020c030c01021e070803010e040f050d0f020d031103010b 73
    0x3d00841c0ba00380300c4440095242004002d20040100341240400101c40c40e14040d030400714684031440d07a901c00c01034000c0c40345911400d40c0801a0211b05402c04c2000e06100380c03511145d0b10440c403651a070003184018080000c00404018150184007114051175060b0f544030010750303d80900f500e44035005042c0ea00124041034041c034583c007080000e1489406040e05041001e4039524110b8a408400352041c3c50071800d0600300100b0307031a4890302c003c800107038501a03204044c40d820000d0114402c1d40010f0f400a4100750b12541c0c03000d1680200d006607144445c4003d0b82e80c0c5e4031981301100030481b00d0040c2544458007a50103014030980045100344c3d4075034001842d0100b444025841c55200e00b500c2200c43e50042000342e400d500d41d8151341140d6000180c401e1801a440c1da8001c6580b205000380c85000c80c00c43d001c10103120300c5031030700c807850b541c010210340b1440c91091000d0025012640c464005101d078080034440c1a121b8000c4034080c0d030300740c0c90f09425030f4248000044a5002446010300180c0100c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 291230800 1250 291229550 291229577
    0x1404020901230406030e12031b0705060a05150907020a14011e0507081003050a0209070c0f0f0506090c060d0902030a02091f0b120a05060a05060a0e040c0804020a030b07 74
    0x64a003a05001d14840320f03a846241c00d40140980302c207001c4200550700a00f8401c40b20700111021a984842c910703903017a030301c1480c1186c1901d4602684402608500c101010442d515a043c1c0c0858010f00300100307504149075100080042c1c0b02002c48041c0c0040e00837196103000280c1c101c0b654628030b0b02c2100041410071103906c1d90300f840388500b828180c2040c0c41740280083c654200c0c0304241c0210900501800a03401c54843c0f42d0f03a241d104100a00441e44500012490f41c404c080f10030322680e001000c40c442e02510709014003c1101000306132954062070380402c6400000080f8550786100140000303050107045240a801004503c1040e0307058002c0b4452880141c1c1d641c00e40503c81c120b82e10441c8182c0d40c8810b840c03c501d06240e041095100020044084601c98100142b540b00300031140101d003a5030380b0000320b0000d400d558440b60304050041a54001c01d80c00009800c5e03416400d84042201c00e1400b40704030f40d040000d0761302075040103426000340045012450a9544036140b41003003000031014 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 291232050 1250 291230800 291230837
    0x60b09030d0c0606360501030b070804230c010e06161401090209090d02060c0a05040311040e0709140a021e0d180303061d01180207030c05010c02071701061404020901 73
    0x4d54a80d44070032200e46140031303041d2940820300452041c500d01b00501d60450382d03482e03208440503045c1014090f000f40090100031921849460180b0101b082045281d40d00c4c2010340d407507110031a0140401c400108088450510200740d500f0264a640700381031006098640d004848445120300600d5500c4007041000741c0c0f1805901401040540028900d190018000070305001d409840b803000403100700040180702d64890b058800380c80d00081e000d80c11410b0607000074010441601c5014660180b0800003945c400c41d984000380308102c00000c3c0310640ea0303000d6420102e00c5548040e0ba2110f41403135405900070112000780c02d00300f01e0307900c00103214180108141c4d03041001c0002180080e4807070006104e001c05260000c1c03d1820390025100e480c0d41000b0410000484290b107a81c079039a404030b0010103040c03003490b00c1344003260000c0080000b0328050000a40301d06003401140c65405003140392009000051085400702d441400780000e006018004010182d84120702040c1007101c0d10098907004450b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 291233300 1250 291232050 291232079
    0xf0903070f0b19020106080604110102010912030507020c040506180408040e091e150723180906060703020c010804030905040e06180102090312131703040801060b09030d0c0606 77
    0x400340d4041c0c039964032a0540f22049100340c07501c011641024800c016000d000554250001d40c04090313000007076003010040380100112103020303240b44c040c180c0c1d40d00030540642c04140503460b01e80c00d54101a17021400d020035944107641464112a040c4c62040c10710480380c50b180e800c10311948030b10f45095510341c42c401d050001036070010840d41159008514100c144030180c009440120003601c0508042d040740707401c42c0c0000340b8000a00c02c0c0b03d070960744010080078039000f03020610303540503482740b01103c0c2e003400d20494410094080c0b070740440810040d1412000352103045074940c0c02000d0151f0b40c9001120f0015001d0f0085091215095010a040c1d456024000c1c4500f07050008001da40303008540c1848820318a5a903803900d0344100031951458902044465560f900307070540954500b4601c055803401013450744001500c003030024400c4c0209002000a2007203461240c002c2c880c40342c541e00044458490760a655505501100501c200e150040e00d81c20150380c0a00c0e0002130720382c0d640c000d0200815 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 291234550 1250 291233300 291233309
    0x41407090614090105130c030b03010c02010504021503040c0306021303020a0801020a0e1c080306031c0c0c0f06120b0d0506090706080a060501080103020114130e0124050f0903070f 79
    0x180c4560702880000308900c000c035000075080701c101e0a5545002e001c0703051100e100346030846031511030884c3c644180c00ba402006011714058002c114030107944038002c0c000d20051350100d102e030800342810884082042c00380c9015a812140f1061a1851940e8120007540060074400440b5441c220003c0581ea42d00385080c01403031044009641c40300c01200c02491456074150700fa10420340c04007034140c1e0103484044901296400f4070815a0f9480d0000060710b0020b1402c160300034241504480c20196500006011010703109400d01c2c1001c603154200000104d0050084c1d40010301c00303880e401d050006680240f6070580024296103903080c49900c0361420003000b210645444d603c510000c020300f17544040f40ca54403894008003041824140400248001c4061001a040041d020300309089480340c0c1c0100c4401c24940512410495030300d0f02d42e0b91491009110f0940c106250000e8103407044c0c1950344c40409242c80e40d413410325010320701c3d5030ba0582340c0151600b41d40521074072101080254400a4180240 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 291235800 1250 291234550 291234569
    0x313050a0b0a0e0607020703082b230c0309030d0b0613080c0f01030b0306041b08030301080714011b03050f040e010f0504060609081f140406050a05012c041407 70
    0x40f80100c05207043c40117000c807421940168400c20200e0120410303218603200710b0340c0c3d40020085a1146141100c1c150b0706400410b850240c0311001b8070146032080151010110081c0c4450303407100d410b5541400102d80e011820340082080d10b18800c0b5a52203c61000001040076040c1002e00041c501307a070b2816040740c0c2a5910001d103916440c6440d02c0300c41d280d04c0342440e0502c0081c00344d8001c60b03160320300a007004028039803803500c00145400d107040000140800008481e16582d507440c006913200300c2d0344070301486d082c1c2804002045510030a10700107003200e030004610440d41e9543c1d04503107550210b03070141000c2c041407002140d102001c48240f0700034500c0d46c00f4000300600f4403003000308403000da41c403074401d0000a4000700410440841c41c000714400c40300503400304a507000300790741c05080c4420302c2110351468101040200f256543c1b1503030042d00c0a9100b00802c2e03888048401d0703001c54249118003864003224480d0308010404644681c0710b840381c2c1d0000307148803c49141341d142641c00d4201c201384 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 291237050 1250 291235800 291235811
    0x30512040b0f10030f0602030903190801052419020c03010603060902030d0201020c19031407030302211b070c0503061e07050a1b0201020a1e11060a050313050a0b0a 72
    0x82c880c419581542000303040d007500525502e99a501408060000360051401d074000c40020382642041c002e0342c1000001c2c50840e21008040d4100410313000c0c00340030b581d10404492030b0022081e1920202141804860b400023468078683c8143d00c05c64402640c21001144601d244565407600c00b802544020351084001081d0188648100350a050031801d98800710380c41407240401002c00050b4411041c040c0d6282d030125200307203050440712045100042c1da0170a1001884404260789a80108003450741c0301c0c1c3c44801d50384041e45c2180750741c0040e550f030044c64804918500c0c2085400004210780c6110303401c840329103641c400100341441e004075220459500e4411a0742d800780007166247d0713800700313030b40c0b600310314004180c2d8010300030100b01c0b141c1400c07250820350150b00b1a40204403075a1100e400c0b801c0341c8081c4c518134903803440212407104201d9180101d24100072980c00c00c1d50581c0e640c1c0a480d1209421542c5003c0c1800c00d921070f0410907100d03032003100403000c0461600382d84c890090b03c0d0300101060 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 291238300 1250 291237050 291237061
    0x503060f1e0411030618040327091b12020d021306020c120f15040510050a0b0414090703020105030426030f0115141b0111093109030512040b 62
    0x212400c403929140f00010030020841c00b0b07a103119a0061910840e00f510080751540d041c21103000303080000d1300d0303c0e075400f40c1941c1d410800032021240407206000e0040c4100c42c51940520210b2407416040d10220f54003540d038550311202500070301140c003909000103007440c4404140c49480d044550102000d41c101814044090a20b24561440c08c800c41e40102414080c0790b0115a4444a00c0d040300d945e440d11002107020031005025101c003900050364180042e081c10521400141031504171030b07100c1da107040100050f6402200b0520300c04d18150f400340000c513103076800643c1c0590004004482a200c0d0740c8142c107250b8041e07a115105c2251452225880b481d04c003d4143d240b10040c3c1100d159400101c445561083c0d0107000d4110032802c08819903110460340619008a1075800d44280080d42042c0c00f407404e016801000e4850720004070354070030100515000e00c861000c604d0100302d0790b400f0240e00c0c09405c02440d0b00403088c11403292420300e1420088504d00d460307480042d1412100c01200c18140007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 291239550 1250 291238300 291238309
    0x606030221060601030b210106060e0a0303090905070509060708040e2202010c03020705030f15010f08100b0a05090a0e070636050d150c021605010503060f1e 69
    0x1101c40303101c01a680d40c2840c4510a555200c0000380003904040d25014110080c1d00c0d240c3d052020010442040716040b0410900356011340220f00840b0f00060300e0200070030591405082500460b60540c43e84030040e07003049100c2002d040020403400500100300456412901c0d40030082403210b003d504015126810941100c202c0300c009440e41c0c01c0315980908052451480e40d41140e80c9942c2402d108d83d1102180c9004c1c0e00f021020b6120030b41c14090701c0503115400c00c012448081410b000c200c1301069a8071030003c1c449080080c042d1070200d50120a599040900b1680040070315040244480340050b982c4d40001c1e5014022202c801101e9291002405c80c00f00c00c02ca0b420281040f401d1001100608601c24141c40c810700d1201404985d1042102585911403c500f0303010300b03c050719844117011182004080003901341d241c1101140380c961205042c5101144582c1c0304d50750b802d9403a0701c0d2072900e00112601d4001908441e402a11305401c0c20f080d9485a04445070b04400000c00d0707102412910420 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 291240800 1250 291239550 291239569
    0x20d120c080106030902121b03121213030c0803190c030b092403010603060b12070e0a050c1201030516061404120804030611040311010e09040b0a020706060306060302 73
    0x2050818103103840346855a0700890701c80d055444516000030740711010b00000c2e200c410b4100c0621a0742c0582c109008481e545d01c206029003031016422560304982400e0740b816107200b00208026804266800f1604000015a02c461040d02030302e040d901e100d50603281c0c080b496005940f440d401070743c10b881c02c260b41e003428081c4c02d071159031038101006000310b01004929014401840403000140c00f985c05110008091500c40320018060000c0010a450703242c0302000348441c41d19184540c070f4540401607000b200240c5102525410348603807201d80c03a92040c1d1009003102078000e080861080c840c5482c4000003001e500d000794000c400421100c12180f1400c0d0340c4000e503030448001c01500310407400c032802c803400c1100c0490b00c05240750350303002c40a030030101c5141c011034000070601400c148400582e10441006403066038019400d064190700d0b002c0055844400d0801e4841c0c100704084002000301d40810212039012094070005840c00000b9030f82d03801111420b800c01c40d40c86580345014001d60410800c02d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 291242050 1250 291240800 291240827
    0x9020f0c0102220b270316030503030a0e070f090216061503020a09060b071412070b04021302030f060d02030f0a2604082113090905010c1404030308060612010303020d 73
    0x41480d001035420252503002c10001340f048903052008010105d910700300034615068075040c415019154a030b2915a4a9034001d443d0359081c0750901c030b400c010865011412404491803a40b00074032191800007a0006500060503076030040e240e002205022072102d0060a007100054450f00120070b00351320402c07805400c04c0c1c10105640b49400414400b41507420b044842140e00700080040840703c4840e811b01e000d6041c000790035a9030011500300104009200854010340c82101c15041107507030199003608a000881e814203004065101007017007403c29a549440c810b0010301910144c04084c41100d10309442240b08807120003610b540f00d03000100a0003061056218602840d161510309076400d5a40c2485901c440d148076170a1040c0b0a44010b00d030210f480d684c0352450b13a036450035610301d0100020304000da000d0781c043d400c00d0100840180304801c440a51303600240000c0c206421510304582e920741c0208410740020003040b000d00481000d80316039000718440d40c001d000d0018624401080110007400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 291243300 1250 291242050 291242069
    0x30f16021203091e0d0906030b130b03010902040516030f0b060304120e0d030e010e0108041707050102070f0602211905070203070213060510081009020f0c010222 71
    0x60400416a000c01c004803107480c108046601e07a12112141400e181d0000014801c0702003901c00d0105040c03000c101948150415242c01c41a180c3d940c1c400e6047e00c030740f006608e90007a00f17803108551b4810340b94802c040d0031001800000d89080c1c40e6022508440c802d0300d00044010881c80200109503150080d000c0d2040750240500610745070201150319400040c000901c40e4191900000b40d00388200e13400840d0031001084034042c01c00500b4003500c01060001c1c0f25000405181c0f00d100c03254000d1184a008a034820400a940329441c5a100c616401055003154255001c00a42003c581c0340300000410324000c00340180d44140065048109041c0348034100f001c01101020404802503415132008207000900d804111540e0f00c4c0802ca05510412200960142002030840b000740034a034031120584000766441c196281c0803617000e0b01d41910131640c41e885030015001c05d0214260540292101043c0300000038103100e640150607003603030400c0308404e0080c441800007082c0a13084003240e10040c902031a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 291244550 1250 291243300 291243331
    0x503220512030702030c010516060510060906020609070306020c010204031b05040c0f0806040203060d1a0907060302070c0510170115120504080d090206090a03030e0301110f0406031802060708030f 86
    0x1404240c41d41511b030360b40c905001c00170510740d10342500e4198062090ba03000c003003003240e4581600c001c41c490015003d40000138005110124505000088150164400301c00820b004c500c1c40d543c51000e50b00047c2014186c1d5024800000000c0c0e04080b40e44140c0f11802d01e00040c14145401c0c0011514600d05642c10490908443c58080d81c0080049411101c156005a0350303aa504004c60502039180e0001031044d02407002c58000f030314a401010340510b49210030340b5407880e035681c01201a0f00803040b0160020101c00801c001518008030900300401311411b1200c0441002585c80319104000d0380040718141c4003142c0c00b20303401c0d808082d1904000d1448000c001509145c1c4440381d59014180003c0e2580c0e80d00c034410404d5584a80c1a1560b1101c01405402c4c42616403400405000c42d5142140c0a51b080044005034010008242d030580135a40700640d08151900c04218080c2c440442c140c0072140e290086d4402503103410008084090190021a035242020540700b055000018503c0001c0510315 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 291245800 1250 291244550 291244553
    0x203040b0c0a210804150b100f0807090503120c100204030c030302060618010311150a0f0e09011a0a030e070f0302010206130c06110312070e01080a1b0c05032205120307 74
    0x111364203400681040e24011409940f01002c402403d01903040740e40401520804085543d00082e116006111580e03081d120391980b40c0c1c1911901038a01581c0d5244d0003420102d110b9135480405026070b0b101900885a4549920908004036030064000f070f240300710702550902c103140d010032055411071400c0da007550710542d40d49241610000f06000c01000c02c03a55114002c003907030301c42c0c156000108102d440e107030b0b94491200b1301408031603128022401180241001340014500006040e049070358800e80c14540c2d41c043c03801c1004a81c0022400420305588110f07204602100700704c980c0140117101c0f42408ca0314114000a03180c40c07802008107102c0141c8003810340005915100180880e202410408040c0f1800000340341180135041007101d40503840b40403c20060761140007903160b0075080e01c0326103850700c074078000209407004071494143d4240040311489205114601d40c0a6450041c019a4101085c4a03003201044855100308038152030340c00400e004038070702050204840312048008610344a440d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 291247050 1250 291245800 291245807
    0x1406010e070c05030c07060818061e040c0f0b1b06240d02063c0702011409030a0c140a05030616030204080607050c16081b010203040b0c0a21 62
    0x800c510200b180140080301001001c0050b607030048084010b45d500151100c40003000d601080b1041824601100700002d000300d00826664012003c40907003620783c0c04102035211035000c000d4400c50303c084015074005051584180d07810091300090702240e035500341c6541d089941c0051004140c441b0340081043c060414000342c03d812080f08140c0c0d041d0540100100040d203898a0f10070f0281d0403820018104040d880c03d60649034200b0742411204804003080409454800302e04481c200000c90204200307001756004000d80c1e8020102d0303489030752402d1483e2021070b042c0100b4403011650408071140600200081128840c0b00d1042a1a039031045032038980041d0f655070001d003403440110680000d00c078040e4480d4041310007500d1610111906c5042c00c03440244168041d010100581c02051100c10586004000b4a4111445400245480180310055814681c8003070360403410352100b080300081c20030040028100a41d0604050b10200189042407060844420410381111031700020072000b5540 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 291248300 1250 291247050 291247079
    0x8030304021936020c0c040513080d05100314011b0206071d0d050109030908070e100902030a0905010f0b09090622060b030a0b04021201050106120f0204030c06020a140601 75
    0x1c407602c84814000120401c1d44043c04501c10030540a000107081104581c000410800c801c3d8103030b500304000d680b6100c8100000300008001012007030100f103640c0f600c400d1900042e820405810800200c603941e5a01c106607000f1b0300c800002265102d54100e422115030f0841c100074405540094050f81c507140c50003d00c1d069000716846000c02001c03026800c10340b5401d42944240d030b407010003004a207140d401c0c003520f000d901d482501c8071132250740d8020400142c0003114a000b402d031400c40041590070181a84040c0d0402421071003241d980b22080700c0814824000e9810300d0688903400214540010288012810001d242c00a5680014248401d170040d1081403c9400d5516100d20f030004114503100010307015100009a0510501058006000d070050709140164400ca40da2906016044403413800e0314024851140480d40c0034280c01e0400340c042d003010340a01490340e40149010b0f117075607a40c211040755404c0032005921031003189042240c140003d4400b510705200030040b540c5000003003104000c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 291249550 1250 291248300 291248339
    0xc05030a0f06080a030c0b090a08040b0f070c0326130603090203031603080a0c0c170313020414010503060c0412030c03051b0f241b13080303040219 65
    0x5607941114401c9100036407040028040e8072050b41c0541c04c0d9410000c0640c17404000982c1d1410031400403480c44240000c0b2003050718ad00024690420f0324110101116030009000c45010380d50411071400050600e2058001440c81343c50103a21200030b011a22f0100181c501d101e038400c0104011001c0c402c0e03140d0700400100d494600d40130481280c6440800c0c1140030701c000040883c417921502008052308010303090700c40c64000c42c08200c83c0580303d604580d0f05506080180800044850302c00000141c00e00651340302c041030364501e80c01e1031a640810204c03400700e0000c00c1c01d180310a00500052406001481d00030041441180c10b040c1810047c44c0c1c0c1c9900490028241310700c01d100c0c40c08140c003070070030741da10840612414070101b450b207600c0c2902c03002100c24444c42170264101200791b05203c01d034501a450540804149030b0b658032900d40b920b02071000d00740c0700481424464680724000b004484009000c2180103580c40b81802d00c1449908040004808285102490244030300b404943c1e00004a4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 291250800 1250 291249550 291249571
    0x20c011e09150c0e21010c0503010b19141201050312030103120302160204050405150601031109040e0312090706030608030f0712110f03090a0902090f1306150309050607030c0503 78
    0x10fa5800d4241c800c0003415207219003000540c0b005191303481c1c0c8121100c600b0780f2040028809071448440446552000340203119502c001805528440805074804005034101d50030403070a042c0781280410b0f02900410310109013280305400511103405e00f40f00c3c000b086070541007030b54199419544c40040f444640c0d0031000415034007181d403002080e000350400f01d03901e0300503008120034102410302c1d135121250031541c1d50485a42c08040340c4035500c20301c208003208a441c0e001c40c0c00c0060041c100801340401102c170903141c0c032090040d400d05c100c1440c3c409001d428a94000e013200c0d40f8110300071701a180b080d0310480140e0014010b0700ca900941c0c404a66809511111140e0505034020060302c2e0600da641e1046614450b0b0500f028490400000034441c00c0c000305e42d155101070f07403014840e040e88600d00c0c00340d070008200c18514019003415501c8a40c810303810030001c100d007074171005404a0400104d90420020391190200801d004d014004190881070300d10b0b050185025020010b4464030024010312541c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 291252050 1250 291250800 291250811
    0x17030406122003090a0b0a020a0806090c042123070603020712030209060c0f010606020f0601080703020f0612090c1c0f0305031302131410080a0b0a0609020c011e0915 73
    0x13054040c44040000b0390b10510141d03a90500180e000020341005081a010400071070110346146400f442007440b0b00c0303110082a1030a4200310700d20081003484035048030800488000440000c48401201100c181003400058141e000ca00c40e907850001d007030b070101c01454410801c08000c502003c00c480301a8016007070143e541d820083c04500301d4801d0144a100030b010361241c04035503800c103401000485640341d0840790250801844661210300a204450031940404000c00041c241035044035038841c0c00515242c280f064644021382005011118010030341c1080c04105030601c1c00000311113000c142e8805011080c90242e8440f4082481c4000140500501100080c404009108000b05155000e0b1240b4100700d140c254050243c61400102c030000b40c0c2c40340000740c019007203440d81c1044810450041c04002034035140c1e09070240e00608002482500d803c0049001d0480307000134205803500d0000052180c0038843e02e242c5001181c080b18100d03170309216070b0501081c8003509003160802d52030703000281c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 291253300 1250 291252050 291252061
    0xb100f09020f160c0801060f0e040f0215030f060a0e161d0a0b1305030309010f03090204021603050c0d081315020702180103060e01061809050717030406122003 70
    0xb02801824111a81680299070003000c021070a28000c0c00c0310341e150300a101842e29003074400e0110303080f401940308807030303210000401056169044840301400540760280d11b0b40003201d001c40c1a0b20403114280d000b5100c505101720341c24945e00c05001040c10400461541c2030114501c046e400c003141600301000100341d4100c0340390300482e85981003854003c1098000030760380c1c5462207481d041815045c035a00980704000072242808801c6500d0854160f494240341960144142c0c000d10725101d00340e82203a420f104148440c46a564100d4113035010340c40c0e0b0f03900c0e0704400c0507051921031085807200c1004030040a00c504003400032165400b41c0c0d0720114440c4c20360700c200c80d03501c0240a0060301030740c400420800d43d0006108003c0083c141e03402000300307124011140d07020702d090307502070310030003010007800d010000b4202d6517a03100c900064801c000344c5211b20380c2e9642c246005851860101640d13000018100a0581c1201949680010314a000c0c40400413231030038041482400c0c0103541c0700400000001d42e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 291254550 1250 291253300 291253327
    0x30f0a11070b040c0f090b090123060310030c03030c0516210305070507060f090b040b0306060c030c010f0507030605011b0f1a1e06040203250203070503030c070b100f0902 75
    0x30b0000480301d0440e05d540c410305500030f0700e452041a1300641c3c03164004110180707a07081e011540c8003c0c606803108030144005008881e8402041c1480001d04418081300003179507126031344000d6000ba074440c80002c4190800300d0500d00341c00f02c4901c583c2d20300c51040048130742c402c6d400480000030741400301d0080002d040955003480360f528003c1603402880c0001c58220b40264207074000000310b40e642c0c036000303032200b14081d00e500c01c50094240752501031000940c98900704c0c0040c07090800040544e402c000780c03013002c00c2c23345e1b5814400d4110300340c580c0104010a42e051050324014002441c01c0300c503900810070003244200c1518800741481d610084160b06104228101002d900321b900c0306488207180034100b20081311300740c81c62039240c00912004540d00d40307031900940c1d000e020b2044480010a00e0a0172403400130400c2c040039030540c0000d000c0100461418401355100321000c1a034666034a4aa00d414503007040000d00c00100c070a111001800140424111035007604c0ea4840c3c0180d4902c915401b00d03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 291255800 1250 291254550 291254573
    0x3061e05061c060305161d0606130510020109021513030f05031905030a0f1a01030f1e05010f0501030501080307060507020705060a17060a05010f080606070602030c030f0a11070b04 79
    0x1000241450400130070008000340c80000c419121407140720b000c0e01c956114006800c907941201c4501c1204010810303a00d4032000800d5810329081d060440d0710340c1c406c0410700a600440300c00c1c0162f5034a8900e0800d50804c001012030320601d08440c0b0f0701d4420f00301008000d80000340005084604865a60020807600f0800c407102100e8007010302e817066106540c000c040b2741c421030315645c040d803c003d114084043c80c0d0107050b160103403010380700240e052201c0044008100440380880415110321180c1041544040c07089003403c00c080c0081520340c10300800d10004041944514101071074000100202100032041c1c515132507010b0008102da480d210001c0f843c007038490b0022a8489400500a148907401c407440070710307104840e25020340d9613480608110b8070707848901c1963301050200300c7c0780004521401c0c0710356110800a0400342440d0003500d50004a070022110101000000800d102d0f03100514582d00e81d2010350a0303824808042c1d014216600703800f800e90000c21840e00280428200304804060 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 291257050 1250 291255800 291255847
    0x7141201140405010b010302040f0e130602130302120607270e070804030e030604020319061b0c05190c03020f04020d0f150602030705070e1807060c020103061e0506 72
    0x80c0441186005200c08540094030b00f19000c4d03280c5450544694001d000380da04444002403074213516458031010500c4140018049000b000c1c3e030801c134200188091001c3c040303645410040c00886401d61060009440d21340b00c15004076131219007000480c84d401100095103003040c0078880f11707402d0345082c0140d0380d4185802841d0700d40b00342001c211049074040c00780c0340314502a51780c0710b4604c0503071000e242c0c6644080d100650990842c1d00601100c013405074410121911035400000d500803e058410b1841521040c19400501d00000c03040900c1002c02c5003c104800d4425890310400710355075810190700003484000e01900030f08040c08007940c0c49038103454023114400414018a9071aa12001c000c2044140524103c2041103020840e1403002081c0c0b51259400001001c1d4581070060040c5030000062034001c0030b400c3c0c0b1414000504050010100404964071003944041191001406851990700030031541da0035403d0301e440101107001110100d80003030798070a9544d4689150f2800a4055249 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 291258300 1250 291257050 291257053
    0x105090a1d070305130506070503060a0509130303060b0a050d0f0e030d0510091103060d060603080c030715020901050a0c05030d06081b030a030903060b010e12030d0c02010b03071412 80
    0xa900361925007454071944074030440d0f9400c108039a260208001200380d20800644140c2c08100000c4d0954018030046407c0318004002c03642081d1345a0004400c0801142c0c00a51000e1001d1040101a014040c0c0c8003d00b50342d525060501100d01002805400760041085c06540c0350401520380e0300c840d9003d04101c0f88000700341d9643c0c4034040034920103000c081e00d211061182c52000042d840303142d440369004285440403290f2640e1510003c2050452034804140c802d56590040040000e4120004000301002c183c080c5032100c00310f08140c0049004c49500c0c04a403401008510301c075a038400304407943e81107682498000300c0701030b0514903e14041c403064003416600d00040421103400c00507280c1e80740300e800d03221206529031000516032540e0aa090044c0840c207803030000d01c0011540d40080c4240d202c1031501c400c800d008100007500359007108814040f26080003d4051000800c0d02542030a007007913000074400c102180c000301c1c0d0f5400945c440c006449400c100403030000d80c1c800d09060013000b00c0c40e0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 291259550 1250 291258300 291258329
    0x206070c11190834050d050c0303190e0301060605030703020703020c1c140102040f1a0d0f0501090e0705061803031e0a080106110703030c0303090b01060201051b03090c0105090a 78
    0x101440d42c802c40d1a03210202401804d030500307148602598030340448008001111038a078501014000c11194446c000c907004d02401d8040e107003a490410242850444800800300c0141c1d035041301400c0903440c2c0e04583c0c028ad04094040c8800740d08403040f6900114180b80041ea50303c0507050481c103101030080c145601884402c2e9102c00301082200d00a0400e01031806821041407030008036080b0700c0b0381d104d075005031080d942c0e080001c69248002c21040f02d003151005860900c04c83c8400c0101c40c000f5001d503500301e540c2ca0050000ca0824071a0440178050746000301000c134105000151680640d040c0c6140000d0000d080c0ca9a0391000c0c4190b8420303440202d89215a415009103911244c1c104848840005250800000c0e000340300d80c1c00744007012910b00185c01d8143c20340c4c80442e038400080c0419003c0c541c4481c3c100000502c03004850340208901e500019990500c00d445c1c0d04050440364948400c4d81084c424480c0d0200c0200389460f5150090030403660f1460400007080e41c032001640034003074625514 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 291260800 1250 291259550 291259559
    0x50904050702070906080309030604030c080d0504150c0c110f0f09010801020a0f1407171b010e01050105010c0506220b0c090a1203051207120903050405100206070c1119 74
    0x6420404d41c0c200040500c112500c0e0200165280030f1140c4140d4141c3c483c1f004280031900650710380001c80e010b03a034014904400e0664241c00c0e40d20a40341207508112850803112058030910540c80e9248492401d8030040d8459104c5200c034460000e401407041d58040c2a403245a590003200094991016002d00c0702d0b9a55544918000d41124103172001151050b424000118482d100c0c2c44244a034520807076003454503503261410a5a010071913145c14000c200b02e000074180d000c2c007242014044403000070910000c0380c1c0c0c3e000d080d02c0c410b80c01941880f00e080c0407030f80090000703c2c0050b40210050403072100c108400100348040c00340904090300f6110304200b8008025001001400c0e08541581c0c0d003580d040d9240744001d11281c841070090002101405580d40c9404d000151f01d400907418905402d0f100c0c00c0c0f080300c3e822107a448808030049000040d040001d1304046025807228080750000e00b5080c13070228070141c4111100f02006080c801d65a408294039544d64400d05502c1c510b9010b8020302c1600d6 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 291262050 1250 291260800 291260803
    0x50c1b03180d02060a030e0c3001020406050f070f06090f0c0e010608010b0a0908071e050d0c0b0304030c06020a0f12061a0906210711030424050904050702 68
    0x1a803a5210031401c15091540500300002259101540034003007901e4000c020004500501ea00c00d061074180c06058a40c450a0f0744041c102400c44000c200e2445c401420b64005507904c9504801460441e40180010000c0c80c1e00041038401300400004c4460388c4101500c0c00340c14558043c1c4000b80010b01d8905241c0a101088a43d41030440c8220b551b01c0c6150b8442c1c50145008000340f090200291018005020086059010f8400000d5506120044503220003030705007410704540082d036a0782c1c81c3c0400c48121500241c0e80740018081030b90301c07a1115005441d032400d40440c60180001d01c01c4000003040406104100d0300d0042600114115203d51140e5401040300319411034080004111107406c4000c0d038154032440c41181d400c5003580203001c0341c0320390200c4150003480c000c42d030050090003041000c05c2d000050310100101c0b1200741e0958a0000c070090300c1d20406111072032035035100f803100303201500d107826081c030401ca003800555030200341e00801102c0794400c12003400d421509040c14450010740 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 291263300 1250 291262050 291262057
    0x30c0606231905060405040c1701140a0605070f030f170108010e01060504020304080f0921030901090905070206040303180b2712180d061406040506010201020c1203060402070816030e040e0c04050c1b03 88
    0x1003143d50334451503960804980390301408201800c60070600c00400002402880309a00d007441c00d05209091546400c035180d4145401da00c0303680070b40d44030a8440300d609020b1080c00050602210114150f0515840300b0403a8007914042161a981c006628031440d91080d01c80e02c00c0310564030851881d003480703010080d1a9000491581e012828403000810810207600805108249075401001e469440c1d4901710064000c03c003242c20303500d0a1104200205a61b5840300303200308003003140781460400201e80c500005500e010030406075080303016400110706121045404294620399005000c050182c0010745056200500800451501882d403a0608085440074810a8202c80c10800b541c0c030000113a00340c2c452034500c079116401a80c11218109642c0b8040c54008202030401400c0a6690f6611507250f4840d81003403110300c034090903040815500040250380e01c2c3d01a9018400c0c0c06004540654400d05040100c0c0b01d03d03159400507295100035001e4440c100070f20804581c5041e83c02d80d605441c4d07071 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 291264550 1250 291263300 291263339
    0x5010e030c0a0b01150e040b040605040c020312070806030307030e27041214040501110c0907021b0301020f0d091419020f040203070c030c0606231905060405040c1701 73
    0x40f01c000001090074101031405042d40c181d03110769440100040c1000024940b40340250307400b0365551004509500c45210307540395a02550000d641c2c0d03102d01851000036200080c1f500303003008840da04200d02d82d05c021058a100c95414280100011000000103510310b55000f010305d00c9105247c9141d10354078a1070041c5002d2030044e400343d0024901000125902000c8442508030440100410010355204404040759104000f058510420040c0c0004078000030948041e00160f008510703215501000e00480d42c140e55085008520302400466600c8150149030b69800441c0d80d20745580080c442551285101000c1c10015206000136201901d4211482c0240c168060440c1221981c0d5900346842100d00505407501c0e036800e40c0b00c15079030840345c4001c0c00200b180c200b40c84e448001010403005060a06001450001d4100c0307c54003810f00405a080341da04000f00301000c0c4042056403038100c11070b0309540f8207940218051120000c103031440141c001a00c5c28a0040f40000901980005021050203 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 291265800 1250 291264550 291264563
    0xc03062919090b070309170105060f01050d0906020c0606031e0c04090f05010507090f080f0303060d0f290f04110616080f0307090605030405060a1802041d0106090c1b05010e030c0a 79
    0x1080701011f036088503000c0326401e420005600c4001015070052003e400d141c8031a200c040707400c00340c0765250b00c2a600040b6041081b1341c403c40900043e446d0a0200d81d41d1000d1114000b0a1010900340c903aa6030b840041c0c002c0e026580c0c0310444c130240402480e80504042c0c201c0d0080c00f1600308402c004017050342c940b1408103210390360080403841010102d2141034030382d80320300210308546942c02003100080b6401011900c040f1a0010740002a142c2c3c0d01600ca0044c0d100304241c0dc122088001041814000f014032a0048c0034004000008030310515150751400243e80f015124000b1800c036100704001994040e04034074010981c140c082c140900198424880d070740d1400c9a5a640382020385003400300713940043ca5500700d5000100e48805c80e901040e00c50580919400d280160b44e00400d00315001e407440c000c40100200c04101140009004d041d00619038140d0411113138407600d40c010000e030031406610390103101c1d841032107040c03007425040200442c90740d00c2980da65807008020984c1d10744552400301c800 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 291267050 1250 291265800 291265829
    0x1a09061e160507052e02010b180403021e0607031109060c010b0f030303042301090206040905040204050919030302031009050702100510060804060b0307090c03062919090b070309 78
    0x60610320001d801c5242184c910300055074650a85e6410030724410803407004c42d90b9803c0c199001c0e980c0c914100c01242078015140f6204e00741400d0081c1011a04030a200424441e04e484202d01d250021741301d42e0013106c6207000280a80c990650a56a202d80744241d54030a4011030810302c046410f501c003c5100904540d11034802190f80145500c07404201e4000c0d1002c802c606040e4240510450b0b50b90f04030b48090000215448143c0c0012144d42240d00100070240d51001080218101484bc554011070240000c01d041d2584a001c100034212245006041607004404651a0100f18003044050320584a082c03056180c0004025a1080c050091641560400d004135000039030510314030043c3d6181b80d68841d600e945a07142c440c080c144480960f600340c410b40c04001032146c002e01c04c1150000250703a02140303461410b04001140084030021450403251401014080303112202141c0c00c035480c0070716004004816a0701522501f0003a882003695210010f030719010103238081c403034200355448803400300030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 291268300 1250 291267050 291267059
    0x819091a010f0807090e031b0f0303010b090f031c050a030b18070807030506010914060c060c0c0f0f070915150302131d071d281a09061e160507 63
    0x1b602e420711407900d0103800c1044030f50304200700c81d850402c00b45404021030780c19401c444051480c5500036800000608408204441a441c11102e81d4052140880083c0100f941c0111007100900343d03110110240035000910780440c1d40290031003541e000740201035004d8610580b640d01030f023440844050000408100000711401e00034406c40740140f9040c3d642280c41c90601c100b1103101040340381140d42c0000288014404c40c00208051407144030440c0780c0c40d481c0c51600e2002842d26002c40e022404c02e4000c4d21409110001c000b03940380807134410a4000c50441c1d403590701e0000c10070164000d19048908001000850b0b509500200705c05171042a003407002d40c0c1d5035104800070300d80d45148001d40c181002d0200d84d009100c1c1c030403141084140502010b540c080f0340002400c40405c600f0600d6040717009840580310407490600b031002081ca1032540c0b9100f89103001c0f42d031002d00c200a07a032440741d1001f00b540d040c2032407080c030b065565801140e0410f558908a203006506907031910411686886a40d90202e13 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 291269550 1250 291268300 291268319
    0x50606010906090b090103020d14090c1201090b0f1807030507050a0e090a020d02030313031b0801020a050301060c0510140f181002071b060507050d0819091a010f0807 73
    0x4132070204800504050304000118040c1d840080031031842c5458410054800a0301c450607030007401d0200041c00c1070200d00e4244034480c10f041c207080788983d140070150340c00318101014969103e506401d0b1890203541d80305190b004516032810700c1819214414000c000c003c00014003a054543c00c07204e42e8030312543c2d007951462040003200e000341c06401540b00100141800e240000c0401d200805590400d2000510481100341079030094445035113000501d00f5909850500c0b402401003003000b90314000400e10080c009106c10701c200010491004484d1040c0481030100c1c40c0c400801c61010301014110032000400d02d98262400890f41c41d507140850701900c000a0140740340c6491501a01c000c441d285900c0000703412109003585c258244524070350004150104400103003030301c2d46429413210300600b441890003c1c003051103800d03c840b0400744000d104400e14a010080d10542020489115a2034180030510360070109401c44041176001244100d1481c1e0382c0403e840d801b4049550103030340c0322030a4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 291270800 1250 291269550 291269567
    0x206010609051c0318150c0201180303020d08070210020301140f09070e0f0607060c111b0108011502100c03061406070809040c05070b131709030d08130807050606010906 74
    0xd04603c0c0341c0d81294002a0040c5174401d4040080000c001800b551102003000b1901d1a20101c40001e001841440442d80c00000d140d03448002d09801c8090300b07007142d4029544500f8408100280101803000400091007042800404001518150b4481d6541d040307150442a40308502446400340304107424243c1404a18540318000d1030b69038500d40c01d0110180f000c500c0644c036809402180801c031201c081012402008450061952071381c000000c0c00142c2400d22043ca10702d40417000080c1d08480c481d030b07440340f03003981540c503501d81d01d644c046980c0605a01e01410800d411840504000c04d5694150b0107a00a10032078000034410716840010500300505445024002418010280405103c0742080c0c1d121400440341d40c10040d1034002d0703a880e0404115030403251541c58030300c00c00458040001103403070110082c03924003200d41050b40610000345c540764a08200d6007040440000140038860361442c00140300e40000c540c0b0b030b580b161410043d490700421100b140c00f0902ca02c0f00020102d1044140d03 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 291272050 1250 291270800 291270829
    0x724020d0626060a0c050d05040b1503061e07030207021c021201060506041701060305071815050303070f031b031205060108041e060204050a09090c0905090d111507020601060905 78
    0x24000c103a59906094004000d05c84805040040030f101c440380d100d007a03214940c020340c051a0742440d503203040c40c001e81d80300041c0c82400d4082e41000b000e018100701c845c1042400f5002d140c0104d00c0c0c542d901c820450080c0500d1401a510005c120318400c183c880c0402c116403042d00130340d6401524034007540d07442e00340d400c603125050b00b0010410040000d540b0801002d03501800d10800803035a59aa070700c17014038181300c0d07400c020032055106003031031000c1c4520302c241121400740d58038032031000e03140000003900d9008040001d4000ca806288150070503106215054034a5440010700307102000d2030900038070508149010a003d140703881c0c081005036009070300c0c1d180700c1c0c0d03031210030308140790001000c0c1c101c5020444000c603511902440b001c9055640c0a1509000e00b00524000070310150740d00701800101c07540d602c0000c804d072501c4144040d07440082050078040c0f8107401c0003074001c140c03148458640041e202400c40400004001d11070207541c00304450b4102c0e0300c0c076502d4070354560301d42c03003089a151408600d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 291273300 1250 291272050 291272053
    0xd050406091403010213060809070602012c0a0c0b070b06030f03040b0c030c010207080d0b040b0f1203090306150328110f0a030302010b01090b07080724020d0626 71
    0x104140b8804240030341650304040c0c000b40c105625800d50411013a8103400280c085002281041401d10381000500002c00f961300c004d00c4100c1c50628100003280300f080c103240150450060030800c5240800c036489180382c2c004168088160794090300d28543e0091441207550030690390203c4c0d202e1600040e5240c8103054440a14a02442c012429030f0743d600c2070146115600017440004c3d1b8105007072018006490003102c14980c0c034406101301e40c044889100006220382c0ca00720302810f05403586807101c40c40c890161406c0c000039440c103940070b103113015144106a05200d20000c100445420000c0843c401c1015411150900c001d05040c07140c3c00710340c0d94500422039250b8014008214079051a40c200c1101401d10301481012401040319031307421fa00142c000d0b0b9124a500c000b20750b400280d40008050780000c05080c003030603a42c0e04485100320200548202c0c01c00b11078180500c5c01e192140001e2041c40c1d001c46d50382c031104030100040c4c204c51188461400c1d01040c0040c081d0484000c085203ca0b03100d0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 291274550 1250 291273300 291273317
    0x80414060f040e060d1a06090c03070e040b040b060d0f05060102070605070f0c15020f070527041b0801050a0b041413031b0b010f06050f0a033801020d050406 69
    0x40441800e03d002008240e01c104a46889404211084201da56420036010306c10344c0e92601e1001d1122848005e0448210385c0340c100200111180e00c00804d200c11081200e0209011511000040190210040a0754003600005c0c4144003403440c2d80c40807244260420b018040f59603148016619800e141c03041c1c90205c1e00070000e480c00036146800c150980c6101c1d84101c0d40107911910400c5504001a4100c00564040e1203d0300460000f0041ca20050008941018581d102814829400500d1a580c0c602103414980030404000d0006503004120306030005404900355150101c5004e40320564050392507500e082c221010300e04107800382281079607034401551b030b040d00d903401c091080000c040c0b0309900b0411000140c510080d1040c0c44807202a005c3ea5900341c241d414048040c01e5410158041002d0003002c0103200703004006142544c106242e11704000518140c038421000080c3c0c810b040100380c84100046c500e4000144d802030808805080c1d0803200040310808041d01c0a20640c011f2201140540 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 291275800 1250 291274550 291274559
    0x4020301180803040b1b07030806030708210d020c011b0305010b03070813060e0303160e0a15050a02070807090501080615060d091502130501020f1b0103020a020a020d080414060f04 79
    0x90206070300030400903190760546d4040c2d03000c0800b64000680440c0021045400d0004078a020808840030300f0031813002c1c001e480b80d034024043c08501d00c4003281608000100d410b586c2c01c0c0e9207034107491510b42040300900502c3d1005059140b00303012000310314042490680003040c1e407008502540e10401e039507150703103090717031031781300b01d80100c0344001104551071915a032505107146010320141d0701409070111001104010008042c180305154040c090181505442c10414204411040c080054050074a640e4410980320101c3c24080d20b40c00c052034078450140001a51511a40564100e172401c1044e101c298640c1d0451b0004084c08a0b40c3c581d100c40d050040400040700c48e130003000b00910822103988680000109101030341c10201000c41382c9a0040307403c02040d6014002e00601c1c007841c5018000d08a25071051540d000941d103807050425501003450711700180200312301c1c0305036a0010001d50300e54415282429013036000b80100c4000040c200b14140003410001c0588408864211040b41080d060 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 291277050 1250 291275800 291275813
    0x618060e0d08090a060905040c0e280308031e150d080f0d0504051501170a060b0109030203060f25021507030216080406080c07030e0d0201021609050402030118080304 73
    0x70030180c0702281c08100301d42d5195281c0112100410380c03916203085e02460f007070810040300c0c040d21200d010b00c0102041424503950343e01040c0801c0040450072140c5440801040c250482190030007081c00d000007042c0059031081113080c40c0036480c142045910341e610704182c9168089030507203240e001036100c200100000c03000c2014108184020380a0703414804418110800c0c0d80b001c0d05e058a00c0d4114000071041400741241c414090601018071045145a99810b156070301282ea40140c20182d580b1420b14240e0b03c900c405034004c5400034100c554034104814042124070301501c1a60314a40c11101c40000c0c40d40802c10301e40000c07002d0300604610303520318140d40104c1400525800c10584e0801421034210403500192003003500030000540c45a00348100500012805482c118805509004400c0002d40c055100c4105041c1914021405c2c0828801070f40b901040003800b000040c401c900c0410809200e03400300d44624001c60083c01900e401c8590740c5952014503030081e1540c2010000039022840 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 291278300 1250 291277050 291277069
    0x80c1309021e0f041107260a030b031501050d1b260d0206070203040b0904090204020708040602010b060405211c0314060d0c1a0c0706050901180501050301050f0a03060e070618060e 79
    0x91564412042150300d11f0002035100c0c00ca00804a540ca2442c86140d0130104281d41c8000d00c06903180c074665040c0b80002e50481c4544100800f6103184455000c2d040c0c0e40180700e80c0040c280605140702c1041c43c25a811040c440c4407071440070070711a510200079810b03c00180c0c10f010388003c0e0041c42c98982040840c031583e91044015503003041e2103010020050321148000d1001c203008104203900d840c2400c40003402e503075210030241c0c82403d0a1005012030f90302c000c4c803900540042e88802c1d0407042e0596074070b424401c4500d100d043c00044095030641c0b05405401146074802401c650700400c1d03848000300701c0d82031070f2a007018000040c031080500c14010401c0c000440741d90301032106410303d6640141d0710300c0d2181c0c68116200141c00825030030744a507080482d8018100025800400003030038000009c002d80014450b00340315610001070706081d519140959006950824014000d00f140ea08801f5a5103401c4e01ca43c400041d151014030b6030b45510078070b0075400e40b000c503540c8401e04405181003200e0140b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 291279550 1250 291278300 291278333
    0x106051b010b03030a05070c060203040303020304090b010329100309080a27140906010e03060a1a0436170d110a020a03110106080c1309021e0f041107 66
    0x190380b14408261540c0c00c00c09800072280d50350300d01d0360f40c1619180010402c41594032150545d1300030302080c000244c021068500f600c0070b10800040400b03405004078007400021012551400c40c2c082c0303071401681210103511901e1010758010f114507510303144c200d003141c90351400981345010601c04da02219100b0001184a110301c80614001e0001100c0c004141c6241907104505011001d4884a60b50400350103159001c01e0900b00251441c80d1a40441d8032400002c00900c80c0a03510441340740648200f1011001212010340104400c510321581d40c1005040025074040b2101801c0d10f121100e001c04c14141900e6031300c000c0b40c0d90340305440e10141485030040d02502e40701589680a0101c82c00744100505240042640100742c18a914140600004141c2080a00741c0c1d04001c401e005124000513081c089c80010b0320703051000d1900320748140c001c01e010000258003000010141d44003003c4984c00c00c03171101044a4401c0b902207140100811590110a170a010704402c0c80401c0c042042030304102c0214 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 291280800 1250 291279550 291279553
    0xd0b0603070503030a050304020405011d07030b0a0f0803030906061203270409030c1b1d0c070b010e07091509061b0b0108031c050105012304082407080106051b 70
    0x20750302e41c80002e00b035401880031880020004400c00c0158646800341c5801440e4401c0581103c00a400c0c17560f0420000409150a04da1100100c840c181c41d1851494024610503506000c000c0d19410026120351040d40c50b21000d00c40d8201040b594a0003101d400308500003040207510340304c03043d480703070b4804001403218450320000c0f031041c0f1015444038000e41084a100c5d0b55031030424501c6150044c003410340b018007040170003c0740f101445a03556901d4554002400c0000035641e5a1310301c1c00240f02071140301c0000b807110301e00100028906d01c1d10312170680542169180d03142015250f0801c010507030210f40074100020f20300070080290500500200380061002250301c0454289a1180d85960720280e201c04c015920020704050580704105590845460180040c0081d516100c0001c04800b241000c4041807048038800c140e4440c007a1048600402207501921110740e01e0203608a8101140054207100594074000150014811480e0606980d40c5864070f600b451503110440d40e0b440c14013003400625 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 291282050 1250 291280800 291280813
    0x10b120907032108090a0c09090809060406030b03070b091c2909010c03180320060106080709060e152a0309040b0a080a081e0d09020103060b090d0b0603 67
    0x414080007051550f04402c800c648551040c40300c00030030b0300c88000c4c1786aa89801503100070340000c0d0190000401c4403502c0380003280380900d2781441d04280c8201404a944070a001500190b9150103401c02c0704444c504030190750308155034160b0344403e841a003c00591040210f0710f10041c1d16400c0015800e524000c080c60700c942c031811322240107051094040e5a00310030301c01040020409090194035001103d42c601880b03850306d2901c424440340a000701c0103051050012441d8000e080c450b01d40c07940b03500c410341103450f996076078000a8007242c0c05840c0e01001401d558800f0505600078290342a403a0409404c941000c43c0c00140c2e44925000b600f048820540100c8543c1c2918030031682c00101c00088002540da120318010410089444444042e0300503c1103050401c20f0708400718000d006190000c100b60360303511105410444a142041006440f103001050004100ca203a0303101c40e540c0340c400e0f00e040020039180e21b46000c40b40120116154071022000402001500001c80b241c1c0043c80a0308071400d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 291283300 1250 291282050 291282053
    0x30c0506070308071421010509070c05300409093e12010c0801140922030203161a0123010e13141905070c060c0c1203140c03010b12090703 61
    0x10646c116039110020001040040c0494030707241403126046090b60800342c030342440c25584c8541f07840d0702d89404a100131001c41c0b640c2c0144011041e1a14081c00a01142c0c0c0c0c43d40c482c1c601c0e80c011320300d0050039607842000c112001800010380c101c0210020320f4a006194a403130004014091202010f45190494040480800701c801c1c2406000209031160b181d550382c030b604101811281103588a14a8802d5200b841448860403d40c0c3c42030204200303100f88040c40401505040c1e103107201c1c03003468400b20a00420700d003040c42800c1ea003050200d024524010720503640c80880c0e1181541e051100d01c1d2180401c000b0008640c000c28001140c0c050142200c41110f01800741d05d812113407110002031a40240c1e04c1003000c802e0b0b5507048004000e103007d9080105e4107001000074501d0120030001408240d44510401d00b01d4003450504801d20ba00106000340c13800d040c40020050b000c0901c1400201c085580840d4921540006583c10f03a5041c41d041800d00340c6c81d5014a28034540644a0703011401011000b00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 291284550 1250 291283300 291283327
    0x2904260301090b090a02070308010b2b050603010f14060d050708070906030314040e060105071e060c12110702270103080415020a111e19030c05060703080714 69
    0x18000c210000000410502c10300134000c0125006014428440c81003003030100194000400c0c5043d529400010b0307444020f07101d1041c00311000840c0c0e4070f05100765659a42c22889150300035620955041e80240135101400404800307907108e1003c684015056240050710320b040480c50208542d000c3e1007103804080d40c50480a04084580d00004031240d190700e030500a158200c445c01c010b249141c2803091505103403c62103280041c000e84200d04000c0b00088400901c001c1581e408000c61342205038881d202c4003898a0001170140144043c02301d074206078580016800c0d4403c00382110440314250303207440d54550070080400600312440310320800480e0001c0b41c000c0c2214620703018510503400d041c0d95038100400e43c04240100302c03080d4115401644c40400180714000d20050b00b000a0b170341d01c0002c000c00058050038000400115400c071045446490300c0c500b410300d200b0704a9000d07050303400c24140c8440034001c072032260107400b03408a00c1e440007050703a9500c101003000c0c405000a0a090500040b5010107 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 291285800 1250 291284550 291284557
    0x60c03020708032401021b0108071205090c04061a040e06030a0c120c0b0a021b04020412060515010206090d050c01090b0f040b0603031303030509060405090103050a290426 75
    0x280034501c44660010f0a0390491345000d204090009081c45400c175605441d011014070701040c10002140042580980124410019814211424452844d0078543e0945e03804040307424500c55400c0440004401d5540c014414400781070801d12450103040210190b011000509019094411440d0110100d87c20800403030151081c00c03500d10007402c0c1c90524060030110b503045050b110030104040300660360001070211960744000300c5203c112075400700242c0240610751040308802d81ca16800400c0010a6000710312a0420070b108140c8100e201c40120303500e03401126000065886042003c014a0007240500751201d4800c3c00807a90041560b10288281d1051310781c154900b82d070200f400100010117415a5006200360021800e280400c2c0c2e2002c20004507100240501400081c02d40054591034101e402030305000e84484103d50f0759162480c0ea61403101000d0760748105101083c0f0340380f504581c1b0701e48000c02c20400079280740c4450310fa01c200741031452490b2686e50300e1401004030007200107000c0c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 291287050 1250 291285800 291285811
    0xd1b080a02060f0708010f0e06010306030b0a0f2304020d0507090204090e0f06070219031209080705210f0a020316030e010e06030105030a0803070c05010608010501030303061e03060c0302070803 85
    0x14010a062a02d1144a80d02000d800002882417040040c09100718118241d0221080a490265030f52101001a0014507a07070304081c1042d60444100311541100340c0000034007691520040117400300c40d910703186003820f440c0503040040c0e00360380118000d45840c07550000424080c1d01641c4a032030b0f84100480032a8402d0307100e0030703c80352035090b0600300e4a42885140c540f180d00a014184a01d07001360029210041c0303180e40e01c00c0580300444582418490041071103840440041081080c00d0781c02c10a241360001d81040350b003882502c0c265001054030310510f450050810080c1406c0c00c2c082005030031031360400c18a02086120610103800d55201c50003c10503094000e07140d50b00c1f9508140b000400d2142c98086440c0100802c000400c99a14005881c4601c4c2e50011265512a110b41c48120303840d2141842c02740583d820401c02141400044d40128101c034843c3c0c0342001800d82e40c0d0700701c284c04011405036030510301c503100341000452580c1d004580d50040601d0014540070450307564130f03216082603c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 291288300 1250 291287050 291287053
    0xb091807170f040f0201140d06030803040512040b0a0f030b180603060a06061707020f060408120a05061315050a030804090501050607020904140a0602041d07110d1b080a02 75
    0x910703111581098211035000840114160076915060303c0300c29180103902d10003030421403c0300851094280060a8985402840c1800c0c80403590b642020200d5410a03034055400b0b0151080c41d940c0b558a0408540031250710048007420720700c404100f947c0085c41241500181522524034260607030319010140900d80c1c988501c44c070203043c0f120a00d07181c980010100e011651800c0828841c081d040400904040c028864624890740c0d1800203d0800310000b0000348a8421503090008100c12080541041c6141c51502c3c5000d5640e03110b03810607100140c1d05581c024070350007402a0900c03107a400c41c061661035811041070136a560b401060203001c441d803007950111000315042c0014140c0340203003401803004075035280c140107058000888544003d0001070482111224450428006005240841c1c1d0090011501c403950f6003a29480000c400c145844280050000a06118090214800c440006800916010300016416290500b46800c001c0980020b110b00c880000e2040000700020307004ce90 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 291289550 1250 291288300 291288317
    0x111063601050a1a13020702040e030a0c030f03060f09090303110f04052d0d050f01020307030b030c0306010602100b010c080a0207030201080a0207050a02040b120105070f090614040b091807 83
    0x182c0080320410b29955039903003655a4004e071250780d0762a8407194050500801031ba154103a01c005001800000f042e54000c3c040424180d040d03e1f005003030308202c54025101c01345550070b110801c500702c2c0d441c0d0148262146603000c0a008520b483d0f4444050103100303080020b211050102101400d1b00701c900361019800d80002c3c20b1003541004001c1450601070882c001100b00340940c11000d4003040e0701025400390144c9000e450034014100506004403075001d00071580ca0a0095004001c0c1003400b03540d6019108201182019080000c0e403203048803015405454010301c07402905000d800311264450400c510410b40d41c000c6080c1c10000e002c0c040654004017882451840050420390f4028803010803144140014808101c000c28030b200b526034102c80029004940c1400244d0f0003054505d440c040c2c0d0310b0001008103090b00000c0b504401046d03912141c2403030303070780756011103182c080e0f44134030030200c001807000f008000c0c0113901801000300024600301021842c980380c40d98008013110140700042003003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 291290800 1250 291289550 291289561
    0xc011b0207140d02010e0a0f1409180c010e0f060d15060809030732100b06090319080403080705010c140a1704030504050a0e0a0b011106360105 63
    0x1008818001c1c103650b104101482c11620000c1c01c800d80c4020068107000c2c2d031861050882e42c1e03e82428010b844404400d04000380c8504483c8601d845106140c0d02a041100114245001021014071000103e00c010803412088100444041c0e002c1d5180542080e0480424480d5654110142021000c204400607008141c1072500300e03e280d640e48460281300310203040c40340818000c401c9400158000410040e030840816400c03110b22401c0c0c0c00d0085c0307188004419460340101280b5821001004041400350381980c07020490144501c4019581c150f10078544c01c180e1024403810800400d000d614002d04040d640d07210b005c1030303903c99035084030265074800d14200c40341c0d085552201c6404130742c49550308040030064003401102e0800d80712410b040e80b50001404041c401c20444010307107000780455054994842e80b02410000139580b6807111400c0000e0004507500c00e8110501c8861070b000108115102c0c000700766203000440110000e1320028a255540c1d607010010944e0003811107400004007442e05 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 291292050 1250 291290800 291290803
    0x3031c050112080406030203040c050405070509010e330f070c0812040b0403080306040b0307060309020301050109020f0301030f030512041a060307180e161203080a09020303031b0c011b02 82
    0x140c0202d40082408000c0d80b0114503000261400e0f582107040050b0f17240c46500380140318140c2039101030750140c101400c10100a5100f00a0020000d0030f89540780841c44c00ca003004010103480b070f003108074241216103c0c01d850840a004156144100c1c1c1c00c00d1802d209208080c0e01d40d40800010388045420050030800d05c6010081e429049451150684c141030828810b01c40c1445a071002070720511010022070381659407036102c1c0c88110001800c880c40c10307a56010150240501e400145d00c20b510307140001601d010a07000b00d80320b400f808a01145943e0840d5101210407011140a50421a040c015804c448000041c6039015500407140c41c4d90240c040141e0b108403a00040c0494040d030002007041251642000c0d409103070060301c18000c10246040c00c1294031f08443c054410200c0c5160101c001690902408044126802662074003030981c0d40091990682d00100c41c02901a401040010300800000f0078002202c011181c001d031910340d500e581c032400c1d40c0c0700581c000300c01103d110409050580 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 291293300 1250 291292050 291292061
    0x40b041e030b0408030406230a0c020309031903020a0b0a02030a06060314150f03100c020606060c0a08071401022701030b010c1203021308010501051e06160c0503031c 73
    0x100490088000c0307041d42e445079481000a4801040c100022000c541007002c150000348504504d21464200400d001707807012804001990000c2800e49030400030340c02217102000b11000c03200c015006113542040da20000d030318101e0800041e000c600075151a2000180201100e60050038502030250300c87c1410703c002030483d1056444001818600f0209030100d00121f017a00fa4440445a90410481d902c80b011070902c1c2d0604107121340c5405110701020301001d403603001d11801d80c0707a6800c5564a544070000e1201c144207012000d0700075884030140c003000501c07020080c0200c0344515800301000203540500350990b000b41c2c10042e2401d01032030944c0342002001444010707900c002d20f001d200300324005002a1400d180840050704015071801c90300e000e03034040d804940f4114200c8140f078081c1d07903a6890301d80c002d20007805401e10401000c9007111180d00550320140718000001d28651406e003c2c0041d403130841001100844c0c2c14081400300042c903560500c0a0481400c1c84041005d442d081198003108460 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 291294550 1250 291293300 291293339
    0x5071b26060703060321110d110607020a0203120327010504060c03021801030f090506040c080601060c17030405010605041a011806090e18120903101a040f02040902040b04 75
    0x52601404002054074404c420f60403400c02da1b0785d224950500c2104070303005154a80c804a06105110140100640c070191700107030000c07084147c90903505c60880403a1601400c05020354542c1c0030706c03001d601038201c50303009540141300f6001d000301e10a501800c8004610103250b070724043da50b40d81d007044103102450041d0948465070307280841c5440d00c40d0002401c00c5030305801842c105940e0304d500d0b02e04030315194080301c829034100080741c031280303800d20b04600020070714000c1d00168001c10000103003140c02030100b540040c2d4480c007070040c0140792540f842420b400003082a11107640b0707020b0014164469118081b003150030600c014001d07940680016100c0103081034107a0078000da2640400081c6e6003c16200d081d5080c0c0a5010155124100100001490301034940c406000306d28a4180c281c000c50003c00507081c003501500c0b28404980128800c840340c1c030624558900800410522078501607020b1070034500013500050405440e60070020498105412030082102e00040034002c4a00c00060b41c81000d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 291295800 1250 291294550 291294557
    0xe0f0414010c050d1808120118180f051c09080f2b12021801110c1f030e1c1403010f03060203060604080d020d081605071b260607 57
    0x303021424010201d20480c1c0480310f00d103036150450801c0080100f611701c2d0181d0015192901d0b0b00801c0f8040a0001c0280b1421120252403806603980000b140204840c500706041c14150052041c0c40d405225501540f00300c41034003614650000704c1010848100d241c1c1c0705965051140340c1004409858807509005551080d80181a804101c0c80e8003403006202c903032006d030002c5030505505415034a407800f10210054180c008640c81d200780000f903c40c06295282603a90300003900e5086440d1391a900b0707039411aa003000c0117036426218080468080c11200e8483e00d000250000d03545001c41c14111a140040070401140c80201411036028610041d82100b20401d06e15552400d13001500e2040240300080404e038011000803440e83d210360a41e170003002c018041c0c074046403d0040003074840901410311400f240e0290007044082000e40b650f480d95000c40d423102850004151203180030583d80c0b50004480444280010400182642205950052161651108034601a500f9003464030091141042 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 291297050 1250 291295800 291295811
    0x903052206020d090e19020708040303120f0603120c170c1f05190b0102030909010b120a0b0102030904050408070f0b04120e0d060e07030602041415041a0307090e0f041401 75
    0x28912800c17072540c00050310b92000500a1031188030704040d019045010301480350104000082c1500300c3c00601c2c0214150701c04000c480b490308250030490780c1c0760002601003107007141d0741c03030140d4060902c000c5510700540299030050b40c0e024100038075510180607034405400050096107024614600c0b075169244903401440b2034034001c000f1034000c00d42004040400c039164011807003240d00900885c1c0c245600905000d01079a100c0d50803211580c01500c14003036650081000485c00d41c810301c0741011200059003c0c1d45400d05440420015000240c400d0710a620100407140c001602100314030030b44d52207110246040e2400d81080c5042c561075040c407405004001e145503026959000d00d24003503e50000c000501e110b03103019113900d000919000200101d1002401280003240070300c201204500840c0e1403145d5000302160280c1034042d61044030124030f540c2d45003031411136a08025551008681c070304151802d5859803846800f500c1a070b8601c04011740c21003800244120241d03900e0a4490000c0207000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 291298300 1250 291297050 291297059
    0x91e110306010f230403110916051e0d0f0c0809062502011e0e1006181d10140f0403090b0a0201140411030c150d0903052206020d09 58
    0x24500c0090f410104090700301d007804403c090004060401440b400c00940b03494492520203503550141842c0d51203010700c580040d0707415044000301e424070ba5035a9142c5090200300785040546000610203450340203001d111440c0c503110244152000c4011803c404030b01b807500380001a218078800303400600260040420820125140072280240c0d00003d800032030300c05441c0b00708a0044c240520720400036002c607808285c00303c039290014218282e080381039404c01c030045420750040b100301c1c0c414804080d100105444502002d6407148049220170312024005e41c1c0b00004483c2088506425a44215624082c2800248a400e4090383c0080200206101070400c0d0320080c01c64103a0b8481d200e415400000ca00000318070039000701151a0040c04481d0041c242071178004ca01412140b0018064460f0100505c200d10b403032400041c00c2e00202403141e290520206480014004008066080c400100005c4100b410320070015195401030341c1e6183d25290400c08002c0c03e10304109004030412482e60020710 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 291299550 1250 291298300 291298307
    0x70614060118140609030d02010c0207060f080f06120d03020d05060603040f02040c0306081603021008010e0106030c0e06040e06190b091c020d0507060206010905010b04050108060a091e11030601 85
    0x1c042d5110040303d15464540d401c001412441070301101901030252a41d01010503030150803c0750080526003e60b0310366600c50b0740c01c4074000c0d03480a4403400a03400c0e6001c1007107182441c0200da0003078400b51401030b45202503880329145c10310350707203444001940c0010705540c0b001491080641240d03003220001c2c40d50905885400800919000c003a200b45ea942031715418680c02940110002c083d00b070152808090640140c105090b041e11069010340c00303114140c00340380c0c0300b0b501031816513680d00d00e4107807140d013440740407001091105c40d84000d101c008810800c0036070710400a400144500340321341c000c51404005200f0046040c0001c51101c10414005009141041d4161070000c903064039980340580d12483c6c07165001e5081500030b90009400041e000511401044103030076102d10b50221031442c1d030fa60124408580302403080c0c0d804604240011b100c658030811009402c803500404180701241c40310b0710b01c4115284007110b15a20000e4401000a6001d41d00900800c0c402c080422811444e1070700010303 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 291300800 1250 291299550 291299597
    0x170a0204030c15090302090108030714030304170f041e06261b0904180308070906050a0c110a0b0c07081204090e071206051e13080307090801020706140601 68
    0x344003043e1403400c03032071076489002c0c8a4003c0d50028915034440d40c0d02c0ca203403038603540540c03000d480282c14049080c2110070000102e0b8081e40d8000240c1131500d2980c6007030011900303c0342120300d544000308000140c0480ca140c00015050f915091078407a11315095001c2c019801202d40b214801b02c0150b42406c100301a4840640c0c849042d000d4800e42003644140c09100740300304034209a00c030303261140e820246400e180c01c0b13000c854441c0c5c480038240d40710031400b592805220310030307000085c20400107100140d106001c0101054454513040c4880700e0004009440c82d103054002410040c000314a200b40328004010300340080071141c000c4c02c640c00c00024180018411341c01001e8000740c0315181c0c400b03405800c118410081401550821400f030048c41c086000d06415105e0762a000d4410101408008021126902070301c4c0d40c0c4003407a4131880641c5c0f414807a400050260040c03085a40f400200c42c1000c0c001084000d00c00d8800242e0141260101a40820f01030f0a090400c111000521284101e40c10b00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 291302050 1250 291300800 291300809
    0x3902101a10020604032316050d110708060604020f070f1506140109090213030b04030521010803090409060e0d081608060102070306020904110f0c0d0305060d02010c020a030503040303170a0204030c 86
    0x21800481303146d45040810310542103d00501c1c50210142428082c0c04180c45030344201c80e54513099040d01c031102040c4d98141c01e0050403d41d40000020488519240d402482501000d4134003d0810080ea00e4203483c08420324030503502020501840c5032008118443d68002e0040540c91100b40a02d10000030807046480c020505955400103001000200d80c0350310320001d40c0d0140940d04140303070a04c8d00070f001e81c008010140c1602c0703030100d007082d00340715814000d4141c8580c40029402d1120440400001c1c0ca89001e0035100c10350350741e10040d00001c050100301c0da2081d0b00d841d5a02d00c2d04003040128100f00030340c8811800c10001d042401210ba0740401d0400489030000400b58a41448400150050080d81b11480d81c040d00080c5d48503032900100c010b41822504481510b0040da4403110907400d446d4101c1c1c1c115484507494103180d00543c001e0140084450025000100d403a4996403480e1a5034000d41041c0c000c220290f29000c260944d82c00041d40c85a0710100641c00c080c9540c0e100d02c000c0466016 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 291303300 1250 291302050 291302087
    0x3b0f062104060e01060b0a09050105030c0a03020d110307110705030a0803190e1b03060603010603021f14070c030b0711060f060d12050d3902101a1002060403 69
    0x31070240000c54005503501a42c800003000042e0b605d050341c1502d58000c003892000300d54540300000d4190301580c240d9102c0e10360785809625141c22214200e009600c15201e0320407803035035135005058009003d0f014601c200e480d40c40700b140e40a5424400d41c50151550302151103a4003000c07180340020110810b82c2e8020341552a2544048940754a01024101007001e50409204810340e0a480c40c0440c4520706c032000c01901520b005071601c1c42407509981c0980001782d00004038994101d881c004060b940c0c2008401490060484402c070711100c001c80e4099a0709a8003102c6030f460600602c10f51791321094000c2e880d400c000c0598010441000e4990034010406504001c4000004850b500c031224000c8480703600586202d415008200c02a0150304401c0c409484245400c401101d13980c4039020030802001040d02090720580c02e1039945880d80c441184c148218040c1c4210107420199501429101c00110b0070100c841c00ca03e84244a4038102601240341194425014040401d410407410580b5101030340 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 291304550 1250 291303300 291303367
    0xb0c0a030c031707081008060609060f01091211120724141201060e042009030312040f1707081617040e16031b3b0f06 52
    0xa06581c0e0103110303d00e059900307009000300480103900803011481004004103030040c43d41c072800102e55410040343d0403600280d461000c9104c900c1d21402c8000d24000c1403402d10191521113105074040c0b841d0500c00c4410304541c44501600e8504502e5041e492042c00ec0107051807889c041c07040e01e0f04413180a80300001600300e820803803102c0c8a40c1d1060340380c925000c403d0717666885501074503501c540c091148000060111501c0f60362460917020710302d56100e110000110f0000c2d0b003940602e0a034407120a07140d0611081010400302c3c1e0102c1080d603c00d501840801340046c005092450042082c1190300000c014100460800900c60380c00795080e60711803c005503d0f010071841c000c0400c0e4007450010300c02e048080b400080c1600e80991252003910162113003498104c07488010760680d00c0b04076407200c1c0c4c1b03005007040b84401c0748102411060150324500303403850a0b07080b44c0401203c5064028140e054004254640d40d0381c2000e0304154507081d0207483c01840e240c0170403c075181c2800598101d0881c4040342 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 291305800 1250 291304550 291304553
    0x7080a0b0f0a02041205030901180f0504053403140609040b04051510060e0a0b1b2a10110601090e0a2a120302030d1e060b0a090b0c0a030c 61
    0x2075040d500a4032615404441c1700c1c3d1142082aa250480c8030603a00240700d203200d0f40314050708024400201d558207d40c024516091504100141400030004076400710b851560b0684104100c0c100803900c0400d0480f642c80c00d04886006042c0c820080c2c0841000390702030284410343c0c80380340f0b286500c035400c40503003503560700c07989407040c2011105c680750309a9810a02c1444440000740f00300e00d0458071240c03280e03004600e000c0706000d00032007244540401d90300c1c01c0c01101c0481c2411200c0465540e802d000f524120b601d031885e104207211841d8135002413910880c0b20010f85003004d00b40c081580346141000c11004442640f0595a86414003441c600a41c5848041040c40401c100032816564007580350012100c1400c1921010104041004880d0005510025105088801c8a02c1058242d4003451410070503542d9070018140421400104070080d9038200132a401911400d009003180d0b0300465600c4184403001440ea41403600310300da8a16003044401140100040c07044600b5a150030110a8000c05 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 291307050 1250 291305800 291305821
    0x5070206010612091a060f040b03060606030702071a0406030b011b06020a0203070f0b06040b120303130f06090606090c021204030b0703141519051e04020c01060b070507080a0b0f 78
    0x110130000c080403420300c5007002501c002800180f0801c42036480705807a105000400c010340d00100300282d003640200c40800d496007803000007140d20401d0380c0115405142c3e070b1030041c8028001041070158074000400c0038090300703605004081d00300740301f46031421482403075052803200000101001080540d0014801075054028010b8a150540000507214807110504052104a4084804500c036070b01c0d140740c020042c5402040070440d050702000440c01d5a6035101d04411000d545101500c090422421810000d4901c2c003230651a40c1c411800460840c0c90117200300306448442e21018107640150a01d60740d080352903015134080342c2d000240d48901d51a6104190300800e175500080d130014104004100780040c40718494211440e068595a150790500d081d9042162141e02030b260b4401090003400003050780c030000103186110f00410040c40d04000c16441401c40701c90b9844003000d880e010654000b8881c3c103002a40062901030301030080e260b04e658840c5200d14000b0504420142c581000c105460030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 291308300 1250 291307050 291307061
    0xc08060603161e02100e0105010303050708090d020904050c1e13050c040f030f1101050711010804170a020a02120102030c09120106030c0308091c0b06012601120b090105070206010612 80
    0x2031610f1070542c003443c2100a485490094182c41101d04200d000d000f8134005200b894103c0744c165407410304084082e900c82400f40d10400650340d0210510710707601d0250350b6644103180035034880d80051402e510400b00307022110b008050411941c894a035200700450b21407000c0a6486a4840000141540c4114041c0114012504000c140b100f0303820011041010120000e40c080b4024031040d8140281e8400446071403040b028020540300582c490302046500030040c0d40c3c1c01a10070f85031200340039841d1840c0d40550708020803100c0141e00c00c0401d503086d030800b0080b215402c84240001e40c0f40d450f104100f0a0944201d03281180910901c03004460b5114080d445003020b9640660907100c1c80e51b03a4240460341e0307000348241511440c0450b401c0c504840c0702280c02541182d001101140c0380e074800b0700645400110304003140002400c034100c19010080d40b50018080c0c004281c900407404000d003010b854145004001840d644c0c5410107115003a60000b90f8181103802603d0004070240108544801800 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 291309550 1250 291308300 291308327
    0xe010e070e2d0c04030b01090203060f010c230607170c180d060c080a0e030a020d030510030b04080441150d0e0f0c06040306200a02030304060c0806060316 68
    0x29002c001d0050101e15900200f044901600761140141d0b2601d400c0800ca00c402d4800a501001c1c01050303c269500496074a008540030700d80d907081d00d000c014801e0821401005140f24641c00c10000c0080140d040b864402518800d000c0d1251145048041c0304200e11481401411200384c898900030190f03918200909a19407003030301400500c41480018000311015160840c12900380310390701041460020544012034502c0c0d00070030310f80000c02025001841c026101c400f040402a030044041401c07403000ca4019442003003010368881c500443c00f1115055110003148484000100c1c0010301074a9407046c025103045e40790030094100d03c0c3e0015682402c55121003089101c0490036014880c03103680520b041040342816600c48403041e0b641d590310341e1030080340158840014042030000c601c05a1103100c9000010b01c130405040c15004c034424403500710518001c01031f13000004200402c0724a010318031104a8606000c007007414203400244240c08010075028403c01440c1c2e0003484541f2841613150f544 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 291310800 1250 291309550 291309631
    0x10207150b1f0c030e0d030f1107090c080603010b0406030f1205070209090a020906040213060302090f120d1e050d02070c1a0c070e06010903020628030e010e070e 71
    0x14600c42d40d01600d000401c810070f038085503552104604034200344d00a01030f8150b042da680e0002096003803099540c100c0301d402c03005030351158a4011900b50654441e0110304030303251b1615500d915101040509545002010902540c02e10000f0400154880c0b54150f400e680410416136484011008840e180180c2602a5101121005010042e02c01241e80b21440c0c4c001d56107403500c1d0b9901002d00042c2c1c0f041126100c00c109040d802040351520030340c040e10780d81d000141421501210000040c0491326540d902408580002640358200c6400c000803084c1c40c8003204454011545400025025001d8000c0b40751080390001090301c00c200c90f01c1c5001000c0d003481000b1000400e8040401c0c1072642061034038a140788103444c004102069408031080c0301d0b04050799a14420741c01c641c280a4190081403105210400154501407480c0ea410072303403001398499980005d010217103940d4550030740380801c00c402000c0d04030380c030f05001c001c0096151b942d02182c9102200e290320326203440016005004070054002 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 291312050 1250 291310800 291310849
    0x30c0f0a170c10020f03010302031b0916090504061403060703090206070209150a0306020315010804050a0f2402180d030f080c0c0307210807050a0c0c0b0d060e09010207150b 76
    0x1e411720050340c1a01d0081e000c0324900002d03c03004404024264803403560001d608000164050680310360803030300140d1481e042c19803d42c1c0b0008a800e46102da0060f00112070290401c25560604200641c0d1162281c0382c2030000b200e83d9000b00381d062082c600040e005405d28400159528811040701c1201d1002030032580c6040d60ba41040d030002d403c203a46084821450f000c10a05542c820421140a01e421001a203116449a901c0300604c03500b10300100d461000e03a070214101d012004404008101c0d0700080560360743e1480007582c05506444c40094410403404e54050007103a401404ca0145d20024140310615450ba041e0316080b900135034481c039410b4480095080e08010340d541c1c540340807070402000e10440383c200f45000d440500084038144000740c8144190301c0d40c0c0d0300c20021010102d006100c01041652201d400c507845920144c1090940340c0c8070507003040f046004809156010355480002c40c28089165643e40c907858200061000f0141c0f10b0805080a40d0390180b0780d04611800440e8508 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 291313300 1250 291312050 291312067
    0x10519140c0a050a0c050609090c070f0503070b0f0123010e0415030c031401060806041e0204140702150610030f02090406230d02010f0807090314030c0f0a170c1002 72
    0x26154010f15003103400c0c170300001380016a400c0c2241500c2d80c0c0f000050100302e0030313511803251200c1034021801c2520080e400035a9480030503c280005d1000c58094201d510702450000d582c205070500690207802c1c9074030354004100034180e45480e540440c1e0000d1800c0205441c2000005000d480f0908203e15000a0740314000100201c00d854941180c0c0318201c0c0f03225021006003080e080303a065205030b4402d60081d00009000502c0301c86007031003071041c04000304402c0c3d100e40c022604a0b81c4030b45000e40b03203585d07801c20300c44640c0e010009400c3d40d05590068007040d03d00b402c0490b034103440500a88040c10748803402096001e001d80c040e20004003003c2c004000d010341c0c2e030f90701c1145075050011001c1c2d04641c0110001340c5c2d04010170f00b01e80c100c1d011707115100305c0ca254240454803a800282407000300800c2c40300100c0000c01442100020782c40780c00003141caa0101d00012402c0c01c2c0f11500b0380500703500c44044000085d1803445d265800064400166448034440e032030203800e194a942d100880184002580308 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 291314550 1250 291313300 291313303
    0x7060e1203091005060301020a020604080703031509091a0601091707090f090311060603030313140609030a030b0a0e01030f050708060901150501020d170912030406020d0506010519140c0a05 83
    0x903e210800c6606010b00c1d01d031007051500b00c0c03164060920041c0c20410000e8007141440b0010a0118403d10300040c03c1c003e042da080740f090010390131810405171540c2a0005100100c201030200b03001403800394549045c20b20002e0000060351048401c000340042940071200d509001150091007128400d00c020020f605090005080452049000c01c0350618000e07074030400040c40380e111f5000540118950389039010041c0030304011b81402c0b01c2012501c4841e0800200a014242c060b400040045444900800b000f07005d44600d0001c0c580220302220040203012203401113641102c3d0012032042083d030a0b404d00d5814090380e80c0140c82d0900c241428044d80700015401001484c1041d6610440035071a0b2004a1f03c1e0701c01501c40c24002013680440e0341241c401d1108081d0002c034030b00102d40a2490300c620284080e082144d080e1079041d0b02040074400010319028599004009103061072500888058540c103031540100500c040144c0c180310803440c5000807017102c02c3c0d506d1a01c21603414010502c0c002c0d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 291315800 1250 291314550 291314563
    0xf1002010e070312020d0c081206040216030903020f0d08090405100f060e0405010905010602030a2001090605040b060a03023604150c020120131a07030815010507060e120309 76
    0x3440144200c540301c000c1d251044034850911f690040340e80d46007405003090000303680006040240e2240e400c0040582c1c0103290200720131054801d484e40c0307141ca40f45004002203003031080543d90085011003402c1c07001402080445601d08400c0740c2c0010551105609205000302d00d4010300400240802c0200c0c069030845c0c150160040210b07002e01580c5c0c0c0b81c02c41002522001e214500150b4000c6c405813a0031405100d0b942203140f541100f6003d10200b0702982ca0079a0002082650000d81c0c1350140300c2800400b0508550203101540d07101900c07855680840c5082c441110410030140310040150814803000703800e81d80103200c00340c00301c0c03640c1050309003030002d03020468448011030f103424040660320740180608101c050740c842240c0042281403011841c00d0740704030030100906002160108040c075a800704d04d0000c2e4140901c0f6038a4040d54070b0f0140042c4006002e01d0036400b445804400b6503a44201228035503035105030f0100d404582d100072245044400074050440c0d0901004204400700b001411 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 291317050 1250 291315800 291315833
    0x616021905270c040f030305071a0c0408010b09060a06050705030c010606050c1009111e06070f2a0b09180a050a0c050304170c03161209050f0f1002010e0703 69
    0x1290440c0c0c450200c83c000910135440398a0300c02d81e24220070001f2900940c0544145d6000d21855400303400c61100258800320100c6d4890010100410240152142481550820300381a540020282405800101c00050314810802080000130380601000340c00c1c004e84560f0a0070000901446840741000b5101741c20031540c903000c070320030f069241c2481c1c10075000c4ea94009800c502c0e041e0b0321822002c140485d00010408048200700060f46008040d142c01e801005441e00800d0007040c8040707140303810b1446100e002e2100038443d000d020075000d0284004401c504840ca581c0b0416540c110704001300e1034240b0410401220050240100541075405401161140b40b801d40c013046102c9040d801601e45010a81f000341000043e8002415460708140c000c00c100d10441080781d0520707a0307404e829485005481400c881c91201c43c482c003041c1c190003e42c030070060502101c0f0241058107600100f41c1040114044034454a026011003003218001e601424541c841034040e29805620707428411156038a1104 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 291318300 1250 291317050 291317119
    0x1505032a13080312090318060a0e0d23070f050103090c05130518030a0c060c0e1002030403111e010305060a09090609020a0b0a080103030e0105120702060907050616021905 75
    0x110503010106c200e407500401c2d403451014602581c001c0c441d10b038100326519418040780d12a188040e079140850784004a10609941008000e0020181f007850903000b001c46081c0d002070024070000c0b1060b131490042d0b400030f1900090013501c41c04d00b00320b5001c266100503002a00d00e030399800c45100580009105000c135140c0408c4820130490b046950384124100c85002034119104540002c0e0290011660141a40b40840b0700501c05c80005011541040b07514002d80d10000b82003003007001c08603262000c030314225080600300d80c00701e440364103000c00029290304055440f00054440e82e500300c182e20142450305002c200c841030b64a007103001040440d005a1051412450000d007618059085031700701c280300c0c0d4030b03980300781d1844e5001d84145000c40b20160610105114440c41c0b40c1c4040403052050203140c1c0102640c0c00c005a099040810a8001e58028441008103001003281c101859a141c3e0b0705841d8035442460030170618012038010b8101552128608118038001c030014800c44075001c02c02c89 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 291319550 1250 291318300 291318337
    0x30e0c030c0622030c0816060815010c03020f010c090504050c0a05070f060207050607050d0e0606060a0e040f020f07051006081207030e1003061505032a130803 70
    0x1000c1566514a56601c00e910220403c81042038004000c1c200c2c00c58039243c2082070341d03a0703200e690f16013440f00650050803e66000038003400200a010110f0030080c102800d03c0c6030302d41440d000e100e4601c510031a19606001c122040c1000b010300c00c001e40711030341c003044008000e103852a560040460b140f030b101e02803081c0d06140119a94009200481d2440111a01e9851414074950384010708030008080c00d0780c0d115428084000450018090340303200310383c0c5545032039482c0d41801e000c004aa003540c041c00e103a076000703a04001d0f0326102e90301102d810400b40d0800401c0861203c000502811250240680030790020890f051103051000261050611410903284038005001e03d5904072491446400c03003550205508150b18081d25006211550091429001020356078011030300544c103414619001a66881b01005600c0508800c0e440d02145403400600e14100308032080d58280c40808003120b00107400c086020144250b10486000d40c48002c040b9116580d034a400540320f1b080820304001d400b0350b68 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 291320800 1250 291319550 291319573
    0x90b0303070f0b2e030609030504181d1903050c0f0a0b09010c05030702070303051602040213032009060906031608060105010906112109120109140106030309060c020a0b0a030e 77
    0x3c2c644c0d1101d205060302c4038040985181c60b20030140010078801e5080c82404c00002c541000780c103403114480620680080b031380d41c08444214018500c91040009075170407240940701a440a04003861250f42c140c0350082c0c8034140c0d030346d03001e083c0a0010f41500706881000107181c100b0006000080c8200c0c00c200c001c000c0d510000b0340598142c8402c94409006812560051000a00440207041140d2070b00502c40420341d040d0340850101c3e400014070799020b042e07044040040140310000c60300440803115480c524402508007056107100041c01184c82806054001121501e0410030b8200100310780d4444a055a91500d0f40f9032180340a0140718001418a840420308074007814044d048030700c002000300040c888901c1c0301040e0b074041d41c1c2045110a400c2260b944699104010040b100ca003810001581ca0303000d180410148d02d5403000342820343d0400070704201194010000b501120122b04181a808045200083d2640e10383d8000700102000458079505180e8143d2240304100d03226021180076171690f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 291322050 1250 291320800 291320851
    0x110f010201090b0a050703110304030c0528020d1109040b07090b041a1c0c051818161205131202210a020f030703031509020a0801090b0303070f0b 64
    0x2d250b00985002c01a5000c141081c0311548030950040c40c81c60001500b03007c100d184419580f0a07030b0160300040806a580e02403142c00d03c4440c2140012006180c4280e40c860000400102d03014400380c071558211200d001480072101024840c80001080000c00745130a1030002124442516044009041d0510119142d0720140c01c460648064046100918104015003c52944003d109040d8a40c0000c5144030a074020b02520107150000d0300c600d610340780301441e012044812402064450356108010034501142000003580040b40c0b1007a101c82d0f500065816500745a40b2004842840e18260400654180c2d2000d00000a03100301541144000300c01802c03640c460080c000c60102d52882c0809034075001c00714004013540c81403030059440c4a41c641c85054116007080101344c001c20749410900200f410b8008181020b0451008114107105081c1001400302c03e05000e00c40b01d599480360079403040e950400c1035444080d07102d00705190340c19545c6041d0158400903228890b030252900c000c1d080381d288 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 291323300 1250 291322050 291322061
    0x2030d03020408241801200a0e03070f050105030c0f0d060e011d011e180b0307120b19090807060608010516080f0a11030c13060306030f060b1507110f010201 69
    0x440a241c900c203612140d0480b1540b10966480c0c200c0c56685221004207c8860a80d04406d400303c4200315031941154900500711240503001a0310030f4110040601105c00034a04900a9410038a0980d450340d07600d40e08d0206610881c44050700e2000f0201d40c00700703c000281c00190a40c3c41d8840404126640c4d0602c10700c21080a940f400c0d0304c0000b00c4014028548421004c0e84d81c40d02c240c404040d900c0e070351400041c828401030b2181540c0da48a8020f0780080c01c08000f940c00070290111142c080c0300032500e03094000341020385802544840d450621390080500c0e0440d035280c03a0401c1507590740741807c2c50044c0042105100347c1e0344e20350801c000200d0003c0406c5070f180c488100c58550144540d18981c200181840040080383c3c1c0359030301c15400b0348188845000e58803504c2010201d80c0d5030542031769030302620302050380b2860406003003410520024403003010802e2865400040403501e400c410300010201c0b010300d5403080d440c00000c140d280c140b041c1c03a8a000c004041c151006291078400700012400da45 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 291324550 1250 291323300 291323353
    0x5040b03100f09141b0f0c0703050c06030c0a0f0302070611070c090b06090906150c07030c0f060e0d030c12020a0c05040504120503250e18010614130302030d03020408 73
    0x11305000040c07450214942d01c0d080c0c9200007498240b800841c440880010b800504801c902035004d60001d204220082055400712841110f41034194034081040000c503210b00848103041000c000d1480207294003039010f440d61158864030038812092100a60710040e003101200303807141c0c0c40707115002032000110b10401c4134a04015200702d2409101d001402602ca401400c099008204a031701c5084044604014241070400d00f4082c148241c9181030404051712650044221000007020820149820132051120200f0540c1c0340344048400f03080c1580c0c400d08840002d000e4a40c0b000d104100e050340070644000c4c1038810f60f100c941c96a120028401140c0c2d080701d000b046040d0700320015803e00c0c0150059a4401d00006c00001c410060804400740f003407075141e503d404038070940c511050500d44101d070880851403040944005615000c3c0007403913001c0201054000b0300000405034801107841ea8003001958001e02183c001d99a6090014000d40c071a1080c050617001da004000320000c2e1800002c203d00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 291325800 1250 291324550 291324581
    0x30403020124091802041a030d020d0203190e100504091112070804020a0f080c090a0e060c0a090906150e03060103030215220b040615030206030a0c05040b03100f09 72
    0x10b83c2441c1000c0c0003490414584600e012628110f400182d41d41c3c001c000d98a12031880c074540d20410b02050514008071140e154055402c00703a281400e0750f500205950f001040407d500148050148054075a9500f20a00c9504126600d40e12103100303800c031004008856117050100000300d1251100d42881c05800034240d040c800e400040355a107407007290345942050004120820b80d43e0b840c0032004910100c0c4d4881c0c01f02d07070800c500500e01d5103045e03a0400c3d403040d10700c2c405006000000f0100d50300c0705001041072028540201d094000c80784181c1840c00901180307071041001c0c9440d1102000c00c810aa181f460000b04c850505406504011495034122079041d00242980c041d1154942c0c04281e00030b2a205c09032110341920a0ba0a01501d01c4914050250b01c004550341054106107081e54201d161901c001e800205003040182c40703030812680d000307204940000742103a020304200c605205035400381901c070f5008018840c200001005910454008011035000740f40da60b03034510300741c82c034005004010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 291327050 1250 291325800 291325871
    0x307061211071a061903030909111303121202030402090a090813090e0d1e030e1501120209090105071403040204060806071e0e01090510030605090a0b090a0515190b040b0304030201 79
    0x100350b070942149902100a2b140b450406085480c0302e01111001e901c151950f401c1d10a4000b07580341c1010411100e0f1782c964a0542c070354a0a500400c1c0c81d544042c100d18089550342107010f0900104806664404000251004881d83d03100c5001014109403204000c60307020f010500d002d018002c8501094800e5203002c01110152880300c03c0e80104903d88a062031401035951a0007001c00004041d4007810000781b032040c0d0300300c0d60b00611204010041050070960301d04001e02400c0ca0f0003184207026254101d8142c0d5036666548049070140030194000601c0b40b14031000c0c00b81c0103030003d02036040d01100b010740c4800e42d554085e04446085c00500541d000c00c84215040c001c600b4803c4151481004505001c03441541e98004180d2101048440c41c120710354035030300301805241031003900360400e5425400b480b036410b203015840b00c0d110440d584135128114500340a4400c1002100d403000a2090415640d118dc3d925440301140e54000c6400314010351030843c04031b40720000d81030040c0e01104080c880300030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 291328300 1250 291327050 291327059
    0x111602010f1209140d020c0a0b0901050c070807031e0317070201090c090b0a0b030121140102030106020604020901081b2b050a0605060307061211071a0619030309 71
    0x4000c0039441461081002c1510700340e550020901407600c0443c407800034908940b411501160900d070b04220071608642006050350b0707003562403410180603150104146a9503111060040c2e585105803405200203004041000a41e5100070404c00112030003401e0b15100316242d00200901001c3c504001404680380c100042d00c0444000f612030313032000150000054140705a10386080f6800c640d8000010582c40e501001002c0c14000d11400040c19030441c480c0c1194144540825211004144242c613101c0680b542c0e002e10925070884205085920001c569a5071600c00007500c40e00304a030207900400b0743c0400001c60b10400940d045240c42d10700d48100c1a019120100006607108501c00c035901c1d14401912040714500f0290050128880c0006102103680c0707103031a0090380d8004120300e01c032381c04c110b00400400b42c01040440400104c01c40016040d00c80910380d0f0303c03a000b40c5001070041041c07040d0390000f020b505200c00740a5a0200c07039152155048400e914182405404000e0005440040400 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 291329550 1250 291328300 291328307
    0x90b041103090307031b050102121f0f0b0d0617060618010e0a05150a0b190f020a12050d0f021b01021c09230303040615031212060e150411160201 64
    0x1940120003d20f042e41b1000e031a210f29080e80c01c041d41c05802c90f01400148110f03450001404141d41d03080e001590395039841e0250304c1400c0155841540340c051000038071042174646a0388030a01801d0401d000d0b09240001e00801ca6581700211940303806020702c012740684004200400c0d904030340c4803420511071030341d0b100e810320050440074082641c82c0c0c0102c915030249603290440c0d0350240500b038400030388821100c9075036042c000005c00c0700000d0018541e8048c00065001c26143c01043c0c2202c11140030001c181022107080c07007640300e1020998034180690801c01d0341900202240c10300c504096564004c4890160f0807440344041084030020034044801034080b10760010702845000707046460b450004058020040c41100030892415000001004100305440c49001d001c08011341c10074074401e055503600400d41d00655030b400c0a110400040c001040303a240c0042016240744040d032501420070b124400e117800c480b444100d104034240300c1c51241084900d01079840d0003070b03481c0700c1c04d0a4503910b07001034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 291330800 1250 291329550 291329567
    0x60b07020105072d0515070806010807050d0c0305041a0f070c05210309190503040b0309011b021b031504020607030203041706041a0601080117070f090b04110309030703 74
    0x31079040d14210078581c413070791004020360355601119a00d25610314140c50010705141c4500c440b102248101400d21030f0b082e50005c1d5042d0301c40c1d801e00344502181c40b00c541c280e60230300841200240550418009010031a410340003580190300c43c460207807072105940c1560b003c081084480003034601c0400000391465208001d403c041c18003940030f40e80b43e03041103d034480c2118407140224030409e4001040c0007040200700f0041c4920b81a59140f5648200c980d0f45503501c03407040d41b10b400c026400c04808079000c58000c1d40310a8004d8102c00d0360711012880b588002c2d494042a80c00c4100902641508502c10b041c0891800305400309280148132660b51f0740c0c04c0041c540c2020b902501140300134040070400041e081030f414a0050444001c0c8001c0c9400d14010780d4400064215071030b02116074013408890b92b040201c42d4150b500e05071018160055080b80703e0b2034444294003400c1c0c07d1b08003900010b140000d982c0030240d0040f06403014460041c8840c1703140782c1440b0541e0a150300b980100075807804244103d105 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 291332050 1250 291330800 291330803
    0x110606011b0503130f080327061b0604230607030209040f1a010221191715030705010e0d030e0f0d0c09060501050f040e090c060301150806030c010e0909031306020706090801060b0702010507 83
    0xd1307414555891400408040b4080e8ac901c01913100e2000c0c0030a021507244584245a40001507042c0c80001450160716428003800400501d500850041742654a076000820007407590f0342c0410504a1420b95044000c880f14a03480c054080d04910703085602c035403420843e0401c800320f69a46062203450724600c2140000d00e0750000c01004400c00652081d20058489c02147d0f03442c824160204103904050074545c2d9503010781d0600c07081c40b40300c400a407191031016910580500308224468810008191001302d104111603100180f0f15011040011200d00802920f49048041222984170401941c00e481101c52204480300107000420040000c0103c0c02d41c840307030b14416500f40604040100e10b0581080e00000500301d02c08040986003503104044503403241c4100c006003003c5890500180400010074a242d004580303100001d2507001c0100300b2601d0300341ca401c0950310300555840d4029152079030f5006581c0000d800b03030381c00101d41605000319003c0d50f0f42140130070700d4144242d005407540e5116400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 291333300 1250 291332050 291332059
    0xb0a0b0f030c130f1416090302090402190308041502100504020108040206070c080106030c090b030c090a110f03150114030405030a120f09060f0c110606011b0503130f080327 76
    0x30903e1301c95100d00071003000842c03c07140c0310002e0811284200051000c1e0f80d018040000c84081080569503039152240c0081c1c05465041800c10000c1c0c02021000c02074001034055903000900140d5000e03001486109684150300b030790885032000717004030300365801038501a0028000c280420003502d4010000c2100790b10405001201c2555003e150b400d440700ba52003551500406441006054428050320311520021000b8040c49444d090015030380e0040a400c080c9515500c00c4d0f1500c1085121084429180b5410000c0b42c0300e1504008501b0524100446680060058401c92016680940959004ad64404095810a80d904104859980600c200600801c0c0ca414801401e64101c6c80740b481b01900030640841d0f88500304200328180d654402d0325404020036901c02c40420000800e019030425000d207410044007030b000325014640c844501c4041e1940c080003510213036140480c00d503401100e409003072a5502c15602c1d44125124064014005001462100c1c20f9004640b2803100030300c041030090 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 291334550 1250 291333300 291333311
    0x1b0901120b07170f390904062102030f0a0302100203100e09060a050601020d0203120604020715060303030b060f0702120f0106062007061407020a120b0a0b0f030c13 72
    0x207540e030401e910f054034010003840b041c80520103034500300c4110f0000210201c00103204260038010201075070707156841c0d0010020022510f00880d036200e40052008180404520715410303100c61402c2c41241505608034803d100781801294100804241c0f80b140c582c05030080d009860565000802035032009280030351400700414042220a909003001d4007a900200041810f881c00c9030300401103850290440e41950f03c0b45c080c030b503030107580003045804010745804142a0360311418045400f80c00b4402c1c005202e480d2144161400e0400350f40684204c0340640d4050080800c5201480094412a0045403040e80d042110901506004038101c0307808024804803541841418000b40c00c40e81c0c00d8018000180a184c46140d524a943d4904c0c035640c1110806000d40c0e5150ac000501004914109130f500d0060115003841996500f4602400510503403140140315401d62601164002d003c0300c512918a19000790b04009041c0803905903242400a0010404c400c0c3c40410020320401c042d00c0b801a0340d4888 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 291335800 1250 291334550 291334577
    0x705090307180f06050306132003011118091b07020307050303030915090c0102030301180908130302040507170105060d09020a0f030201080a0e0d0c02010509090106021b0901120b07 79
    0x1090840c42d00b652508001510200030103404240c0b101c95014900c281d102c08148691400c100341401140c56011410081100e04d420204206005012040d42d00d54a03054820080e4041e140080c66096522901e00588800507405c00a96503025030352224040740d01e01c0403030054075180d401009690300080403184156940d4000170700d1548100c40f90b5016401140500c2c0848000489064200d912003000c1c0c00c15881341c80001395603000500c01d00c90a80c00d00f10396040100b070303141d004e07003c0302d601301c1d8102e9075a41d9088400e03900403c0500c4100c0c002c03850840010f8a00d8400c44500c04041781d419030000d401d03403034001007066540210024002480d560451040183d440b81c0d4218001c05080d1480d001041c5180005045110001c044217051030500c600b0291903000829941200d00b4181042c01d80d0190300d0004880f103000d8620301d903400203000000401c5964000540c20f080c0300e182142504100003100503c03122039003c3c850001d0143c544000303440043c4929070700541c0105207141450107035180 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 291337050 1250 291335800 291335819
    0x40f0905010609061a12070516080a05032502071719050a03140a05030a0911040f0b10050a020c04111303030e130c020a020f15040f0513060b030705090307 68
    0x103e034810095940ea40300c0801c40b6011203010344a00f0721549004a0134022401c3c0c0e00400348030010285010000c0c0000d40403402c42d05445119260f54000f40034944a0b1030505001d00194001e4680800c0b4030481a03407045d0017aa0001c04644c0301d0503542c05010101c1c503000b00c0c031240d4050f80c4001e52181c003e0445540401d4008440301100c02c1c001c10042c070000707041c1e06010b083e0072038034500e4081084080045c0300c103558024045980000c040d10000072848003904000c0c4440c2c40c0e50503020343c02030400c500900050860303000520b10311011191100c0340803107001d040c0c640384180601640584c0104540300781900d05680654080703001d04c6411803512681c080341040810b0160000c5003c1105109040c0c41e41c1410000000c5501c0d41d1070303041248080b004006907483e1030004c002407058480124000864a803540000c29040c080c02e00c054a0355214003070348da0304415601480c0c3c0141002c00140c450400139000360360445201111540c51502d130300604070350507800f010b8201d8040c4a00f020010b8070301e00d03 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 291338300 1250 291337050 291337061
    0xd0c080a060f0608071208031302060c061e0105010f030509030d02070803040b010e190c0e1c020f030105010f050108100308030f150f0907120603050d0807080a1802040f090501 77
    0x440c440004442c21252280300450740250482c46256224480c288041011100b10070003c80d0084002034899075240c45c42d22001c3c485810087d0481000714030303070707040790000a4031f14040c2d601d180801c00b142081160b4041090000d00c12640080c10003004813031a240a540910741125441013660b19125480341100280d80c001c180494401c54000200700a005841c0011380c00340407c4401ca00c400d0800380000052844c41000d1100043d64880709481c0329401814407204040000e819000c0b000e1414400501861120f20140c0c0203120169101d10309240601c01c041c107035042c6010080801d420b010046034007410080207a00719604900e008004035060078003542c46541d45110001ca28a060300d000e0f100c000c004004a401054682e40d0300e02103990780c070b0318903a00401c1840d0400b00300e009a0102d4018200a40c4007a04600942080010b180d51000c6054400c8600e910b07080304685800c0028004c844da200740300615103410101407001454241c00660142e401c020001c00c001c1c60540f40c2500710ba4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 291339550 1250 291338300 291338303
    0x6090409021f0f0c120302220f080f150f070203070b0c0414010c0203060a02030c040e0c04061116030b040f0b0f060f0d081c09200f0406140d0c080a 65
    0x1590300035040140e112884894000340c0c4e2401d1085403c1550b1899600402100f00b10305040d00403801300c004030400b030350950350300f860a01203121080c0c1d81c00c1c400c416119140038042145c05125032140c000e11000404000400c00c001e0341c988035941d0301c2004a81c01c10040c06401c00c5020400001010a001544460081c9031641c085a42c030303458100b88651881e58204818140100090404d01582c2d01107080e5602c00d410090150b901e51311032501c00c44520480c3c01c580c00c07280030a4180007410400744003030010388080c0c0e1a91590001031104441d40e0f04083c1c021a1031451a055051000861031502079402c188030304403500a460b2159101c1a224000311110702c03880300c0003001c10038140b070104004c42c1581307800c0c2c0706081b1605680d2a6803031750388038580601031a2030404500c4009107105c1d510000d000740e0090100d00d04403450569040c850103c021000d0722620684104078803a1819102d10000c54145481624a0307004020501100d2000c01c1419106a90010400a0114001e100344248203 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 291340800 1250 291339550 291339589
    0x50102011e050a230106020601142808010e1501050603010f06031a0405041101021e120304020d051c1101020a0903120306050405011502011505030d050706090c0308030a0f1103060609040902 83
    0x660400400071314000c0c05038031042402413402c0d41e000c03040e1030312582c011202c20266005140300042f00850012000240c0c0f00642030340c1707400003044620b040401c03101505020440c1c441e006913038410801c00240030030300801107219141a010017046010b81d107c00101e0320414591001048164005011a241103034180c901e0381040103840030540e41032109102400103170500f40346813000807200350350383d1002581c040c5420070004042400c1d507031280009484140d0200450f401088560120320f0700400707003c6180049100301c03110344003441049c001d03940c2209a0350b861100161031522240700c42c14507000c1c035006041d074a0801081940741c5015180c040c0644021040c0c48a500c42402800c6611210182d010100003003070900c01a640892610640040c0e4a09280c4034600381c10300800504c0c084600420281001000004110119020390310501851808106000c840074802d000d95101d8030341044058000c06c002103140c6890340280112181c0504005810401a404a980111361b454050f400b07 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 291342050 1250 291340800 291340871
    0x910060312020c010f091514030106020f06100e06040f0207061a030c030115030209060a15020604030f05160b18060c0d0b030a0c0509042f0901050102011e050a 70
    0x1c1074042100c480b000000307190240303101e64480c40090030859980600b0840351284003103046100d20480148050103000340d005642d950351103d01a40c3d400c1540101702050240c1c000140c1110864401503086454004100c200d5a45800c100030046c24605008880c0310f41c02e02c200004900d061140c0803c0d00c00c440601600451070108141c50300c0c1c11401c0c114402d030b04141120a00c910420204000c90b503040d6101030031611944001411007804d41c0010b01c07000c25490100026950000e0018042c600a840c0c0c80d804409410080301e5603c240700304020491130344c4207a4030000d1420b41d61903a01902da046140e841d28000403c040c106070043d2481c00d8000c0c030203c3c40001c120300c580b19821510100301c00400074900582d8900c90003009610419204103d400c0c005000e1002405443e030b00c246c101411003403035400f442148403440002900c0b2500401000c0f0021449500501c07450f03040210b01c0101c0000e4800000001c00074040080800303c02d25120105040071540501030302c11020b45e00e040c0007a0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 291343300 1250 291342050 291342083
    0x2071b0305071403030715090203061612021810110f030d0e06010e0103031d1c0309091e150b16050111030708040b04062c010608010213060809100603 66
    0x1d440c2d0a50807140300144202000001d40c0d034000200d42d2140da0184450885141c841440c5000f08040440690140104010486a100030041d0200d10084a4031a00c4a2290b8155881c040780110500350808003002810302181b072808a0449000c9036852900d000440b410303901580c21b0a150300c840a4207680080342860248909016950024034001c1c003d00d203c1d0b1400c42003801401c8184006000c0c0f19094403038585005030302d40141a4040051b01e407070340009400f144980254580c8105600240d401d200214003240140125002d4201050700001104010401c0303000a1400840c1c000403202415030004882e61014040c0000d20b0003041a00084101420281d094540030a0b4400d00c40d6020810482e9030350304072200c642c00c00d800000000706655140740c01001003031205903004410145069090543e110100130a90514284000348447d0741d0398032a00f4281d0061440f00c220300103401905101c41445500302c06e80c4802e030340c01114030411400d12400102c5000b50402c2d202810719140250 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 291344550 1250 291343300 291343303
    0x8190c030b041a010203030c0d0e1218041a011404081b0a0e07050f031305060103240b030c01050a090905010303020d09060e090606090f0405092401030312050a02071b0305 75
    0xd0b0030312030f0940124403070711020000035204d03c00145a660300040214025017020165800700b50204101000c4034a4040d15001d183c10541200f069029450407820346c20303060381401d001c0c106a154000c50040b0480015100540e0f4114541c0c0c40d40812580501001840d10410030441c03204180142c800004000b400090000d80d070708a030441303010340031588180941564018100c42c1000c3d54007540640b41d840d5441071980c011006480a045442000001f05c24000d440c80a080044181a55034510303000441401040d2040c4600386a4035400111740c2403c0355010750010001e0310221319012503d00c1c0c0f1a008801103c10030b80040d00164030041705905402d4114090300e014052074104000700518035000910020030081c000d0b03006a001050103070b299102d4984504c0124002007040c001b07440e10009969803007a4000e03030061250b1201086448031800032140606807501981c4000c101d4038022041c4014090103440300c000650708116a1003c2004002c080401d4444040f2440b251031550a165 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 291345800 1250 291344550 291344561
    0x18150a020c060406050106270b1b061611010605011407020f0315070201050c0c0a0212120f07061107030c06051314030d0b010203030115081f0308120a0b010f08190c030b04 75
    0x15903038206415600c000308d12900c6103400407140c01c03140c4560380318140030110701c1c80d04002003400325601c545014480301400040d001d05caa03002540d90b2202c40c1d41100c10701800c2e84c1891289a01103080704541c0e110800c0400c0041c4012400035007a4480e454158000c245445144810100750343c9020f0240304440398203001d0030780c0050b003035240c0506040c070b50b514483c0c9515003100020310400d41c0d00c42c00b508001c000c0c03050001002c4050903060b1181001640c20300258400441103401a1900d414074200202c144141c8a0b071680694600720003103210380d11140140b0003e0302c5404d01121a50a03100026844800e40c4010994003010f140c560081900c0c0006451102100078195001400180300440c900410061002c08501e81803101c0c2e1106019440c40d207040000341c3c4444041e5031804402d0003035600c02040054151300486403150707910403e49003181c07a107201c06400500c8511801200310322070613005d80c10803105041901441e81601c0f404040300c00f800a9580401e48403040e510307551400c3d1152 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 291347050 1250 291345800 291345827
    0x20705060106021c1e080703110307020d090902040803070b0c0418020901110c060d1e05090f070b0a080112030203160b010504110343030603060518150a020c060406050106 75
    0x1480c812807500e10303035444000400040020021b1940005120078402d810669030764020141d125034a080070f80c002512201565030400209180c0440001c0b08201482201d00700d0390030320043c50070319940d540c42241400001d05540b0b40c0305018040808d050041190120700c142d1200310042c3e540c0780600014140a001d0b842854035a000f0108559040c0c85480c101e41d034104007074100064079103625146011001d0351240181c080c40c6081d0401460030400103241407070b1042d041c110ba51003a6980907800071803040c1c40310000003507031100040000703505030402503403030034030074010b403070805a112005481c5401f41c1601541d040c0040b42c0100303c20705152045400c03600143e40c5003465491700148045100704440401040c1c8202c1c10100002c29142c49404100304044c8070000c0c02102c04104010042c00440c042501c84e2407034080495841d0184500c0c0e4400002010041c1a40c0c40100020b20701c1103000502c50300740c843d020003001180340d04c18000d0038800c503c44c2c8000119941070441c000c002c00c2c0030b43d09 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 291348300 1250 291347050 291347057
    0x905030d0509150a090506060108060d061104030606170729120f070e0102031902160b1e04030f0f0524090d02030c1513020d060c080a020414090406020705060106021c 73
    0x6010003191000c2111f90b0700003020b082c406405d488400c00b00f0600980700002602e010f1a100f00c0c421103099400c010801c6a0040400348001d54a840c0da0180a1420040c6100c031170307110b070404001d100d040e9002640c00150b596107210720f005030121001147d500011141940301c618078200098083e20311216504541c0701d1606140b034021040001c2d690384510742102c48180307407008001c110240700304292071045460176003007421a070703861802c00310540261100140124207818440b0f0303650711000684003280c2e00410034000c0c8640303540351000a254404004c1da0580516584900e9282a5000000e8102c880b014480014a89103010324103007140000400d00b15001041a180040d000256100c801d9030352a1010381c641e1100b10454070390b0500554000d4008050744426018042d496008250315541511810690b546190f41c042c124421409107440c40c1c900d046083c40c840c1818030007035a00038400c090040c60000c00341c0f00d403494140240d2100c0010b91240d400704200c4440710181100a800700d04 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 291349550 1250 291348300 291348311
    0xa05070c060f0518030705180a0609180201030509010f0507050a110102031e0a02210601022415030f2e02040f090c05160c061b11040905030d0509150a 66
    0xb00d0040ca14455111070500348490910400500d540520021008110003800b4561402c0103d00c00225100201d822000c0d0b6460200000303044641401140c00c007070342840c0d060340c0b085070a6006600610700603007122403541d03850b50a41c0c0000698031550740a8419031321031303a8460303040880003444c01085889107a0240d0040c0705000034800e4180c010048003c1039848080d103a62035010320002801190309100d282035060340300341d908420307440400b4000c130000e90a80380412178021440c180034605001110450803c2000510242401b04c2501c00d448001802d40d00540e0040024078076044024009a03019000242980c089584a1304040c003034081d00d420070360502d880e24001821407111072040e15501a2610300d042e00c0d017807241c2d0445028441d02c042084101790300781460001402140070306070100c0c7c11001059035184603000c400941e654041042d00810076001c0901000e010f0048045031f09110034850009030801c41d00a0394411007801008000d16220001d05100441c00036040e00c00692500 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 291350800 1250 291349550 291349577
    0xc09050a03020f01110d090302040b01020c090a020a031409030a171b07020f060313020405010515090f03030712020105072d0c0201090915150206010806180109080a05070c06 76
    0x1400d6080440703070100d9402a0711510b40005030341080c0c0d021207001c414041d0719a055203164000032540280c80c001d940030072501880000685c1c0d10b40c045140c03e51f02200c0e0300009202c0038855002045080060300d40400c440c0c1100740c00051310903094039403424940000c6110062281c1c000b202d0101004000f40707203d03d604242c00c004609030900c50441c0c18402e40029a2019526001d800b80480600036114941c4e9190900703403841c18018100080340320b01d0403c0d00006503464040806102209110340f128a00200c4008000c01d02801040b03440c4c160105114203004600b140da110700300c14810740c00114461030541c2000301115100a03045259244880f84403200c8450300043c100214a10b00317100450322040e000680f007503621680a04007e606024205007007682c66043c24003140c020050411652030b81c1b04069848172024001d041107640200c0028207001a142402c40c9001041300c000503041e0225140c000c103950003090700c100802c070005440300400400d015035030014001072a0030305499565 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 291352050 1250 291350800 291350809
    0x10518160608070513090c080a0b1503100e070c060b03210307020a14031206090606030402061b0d1e0914040b0316060e011701052b050d02030d0c0905 66
    0x1070096504000c070364000640d0342801082140c50901e860b0f035241c14040d0303440c0e0030103001c0c001d428800000116040003040700c007400d500641c001e240c4000c14504035900b0b4031550395a00d80005001500c90442400700046031090380030031074000c1a40c4c5e40d44803c0c4e0641414482c0c259481608028066800380c8031800885074076501100c0035070b0f4800021541c90300e507514201d16080e03803200040e1003000d550a220740701c03002c004024000e0241d0500c030301c142645c50304200000072108480d00703078020074100001401450000000c02c15094941c14401241c00c0c60050035103409a100c000d400415081501903010a000c140805428003039450004e41060410300407a403002615040540030355214403044207070f5074040c0f0007080c00512054400f00c94690b00c01e0000e0444100c000341901041d0480344164094400040490503900d01502720f0403c0c0d010000c90f0102507091040a0100700481c1e5002c40020300180210b1110390074560045d40c581500d05048421104014030340404c0c03148400c030400180e100c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 291353300 1250 291352050 291352093
    0x507030b101409010c23100b0a1805072c0a05040509100510030506040b010e07050a021209010908030723030a09031103011506030c030b060f090d060609020705010518 73
    0xc1c2172030006854006490140040441241e03004500b80804001800011000541c0c98207400003a505215501c140002d0200c00d0350350703014201043c810810744914410050f00301c141c0108862401c50925404640105c225900b0034000080c294598451482d1901d018802900075007011a4108510304110840c1c540d11411000b658000b142c0b60300c0081c507100c256040507001103800c03100750f4407945018070302400900e9003402100000481b5001165039070b42b0071001e031120007000b0b400030030700701c4070380403614610b41c0100c0b40c00b6041112144001c0f6105809002034042c40740315141240c0ea0300100a1440345400c0080c0072030000ba801809224002a8441c410104030b83e003040200210080020100f030241840609262010350341c81c00c00100c030307a403550000d0001c046546e030411190323820310104015807054200c2c6150705141444042070f07a1601c40c14004900313102e001e0014034180c2e2018030000b66001b8180540b8140d564604021408803446507244c139180c4104041c00d0b484a89402072841d001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 291354550 1250 291353300 291353317
    0x9020c15060108060d061b0e040507090803270402070503090301060911090108090a050f070e09070303080606030703200d180302070b2101121a0106050417100507030b1014 75
    0x340b05100c04010700100b544100743d1f00410344071400710700ca4528005000e0b4410b200015000720316200c0003034052072060b0305010030360780780101952500700c0c1c4c0c03090b4032254004018100ca10301144078920711a0340d070760b02c010480c50f4894001f442c0c45d04000310806003100c00680c414242c4a05150341310740c0101c0c036503045850308902420311030f840d901c0d540e5005241a0141d0001019441410300e0724807241000504001280c1400c50080ed52303075240740f81302d078603101180301c002c1c0410000c2e00440d55526000024540c000680e00e80051080d10150020000342072100025984107000190310784841d00130700034607105200030341c1e85000700911340d078000396120950321411070304d104041041900341d0545660312070f078650600c02d82d641030350319441d290030041440041121040c1166020302c24940c6010070b0b0b01e0485410741c079803d04051400c200814825252007c000305401000c0e00b109100480f84511400b980d00307550700251a9401c8030600c0b508854410b0782405000364505016a0a80820100c070345c0388 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 291355800 1250 291354550 291354559
    0x60305010e0d0e060d0b0a240f0504030b0c1210150306030203030717040b0d060e07030902010e09090f010f0204050a06020a1212020c031602030d03060b040b2209020c1506010806 78
    0x31140d4501da80006d0000740700c0c0581c0441d031b0034000035510440d0081031300e1180003034001800310a18001c0544485045a00d00c0000c102c00748020404601588282584103105610042c07030200a500b8845480c2030440d4034114124000d5000d0110020000b90340030810603908042145070b0941c1c000950300e0080031801040440724001d82e12043c0401802d4800a1078410701300e81d00c85000c0510035003d01581d0003441d00c050031480000e640c452090040083c41501a155207440c01c00e07280a00091840007400150782d8802d0054080003100309108008a08884940c0141c8880c2020100b08014001d030740940300310340c021540e01012440160a0b60103c82c1d03d400c7c0982501c0100c00b41202a01882d60400224000407a900408070900c15400c81c60342d100f00c0550f190712045900584c1241d409000c0c0c51031521051105205031021480240140900104401c001c0c9038181114440208640c01030001240c0202d194100c1c00700802c00d02c0c0109002007000310720782c5450300000306041001003189125 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 291357050 1250 291355800 291355807
    0x11062e121103030f0705060601030f09120c0615090e06010f0605030711070e010905060f120705060d0213060f020d02031c0c0e0307060504030515090604031d06030a060305010e0d0e06 80
    0x250342c10022500300f145040155a140d40140c18402e80740ea10031100c1c6800309083c02011401611071b403051503a9190312200040720360340494403c441015110004845a0390740f0000c03900c0300f041c40142e130b5006000c000f00101d032038205006414100b40c4180d00c07040c0c046480d004140030141d081010360743c0c41941803a013440c1401040300e845c1d16001f96a4000c1070818188400860003210700d4001d00c0c840d44050792120791040c0a0b00600c020302d00301a00c1c0e44469082000705001c01c0c07401d50028601400110000340c1883d1807038010f48100e881560103000464484901031101c0e540600980082840ca80003a60030200a51404080f2041d45100340380e00c1e43d61200e40f02c140d54080c54070315103103540160072110031503120b00002e485503000d0700007a12a403184102c65400c031204101c110b40f00b0070390303500503001c40e445031303034007602c80150000e02c6020328102102c44541035114207014501c1307800b800c0030200e40f440c550708000382114000781c10488242c11081c2075480003900101d0108064500b500d404d070381c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 291358300 1250 291357050 291357083
    0xb01060f09030609110910030c05010513050301061502060c03040201090e04030507140105071b1203021c0e0604060c0e03060403050307020f06130c050105070c1511062e12 75
    0x26614407680005211034609402042400a00340780310810342c109881c0c0c018191120042c400f000c014900c8002c0030780c02c60001c00e1146c0d51244000d8000c1c100d000d45070101594440d07000034250381140d0400c3e0240000700e00c810428550400426411466012000345981059000282030f44210301552925061801c04101054400c2d400c0340c0311980c000c9418940400d0400f00e20340605001d80345800069690b0200440031028101c3d201146130b8480b220350001031800c042034019402040881081200c403811684043c0080c1c003440c482142c0341c501600d06858a450b103031007154001146441000292045180e0f0358500203003443d00306425040103030b22a81c0b410300c00c0f45080c8a21503031000e14041c007000e220307040f010800385a0089205200c110506902d42004440300d0080c100c0183c901c00ba11482048459410a050b020000480c50620850989500348030300d8a601a60b44c9885a1070203422188546104420340410208034604000c626140c00c0c10100b08585061014000303983d0b0b41031644 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 291359550 1250 291358300 291358307
    0x1050304080d02031501020606180109150807090f0617030a0c020616050705090a200d06030c0303110c010504050d0b090a0b0f1006020105010b2d0309100f090b01060f 73
    0x1603a9a25842d4199500c0c600072a0301c052940e181e40d11240503104000210704c16140c841c1c103c16603202c541281e0550340e8648030350324024020303001903800200880c00002c50040c4051020001900d00d82e00c001c41c2c0340f401841030b1411100582c0c070000a195403451008002c0d5004011540741d070040341340403407980945000140d82c034840d04200c1614201c40203481004c1000202d100411507404940119440c0e84201400e8251030040c500c09009100140e10b040c54181003801401a04458082c0051829141d9442caa02c0842c0d03604140c010030b6101e40b400e00303e103100b00305001442d03100307203003090030946000c01241549040f90030003001c03015a040004e0305840100011004250421b90720059424003080030b58010a0598041c12603085149010911900500601d4100c500000c0554a807800c80f01103610303030b80018007000100031001c3c28029101611303034029601a84140c4081c00740b19128a07110002c42d401044050f000a007132407215400300381310a180d6811180ca90405462012096400303c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 291360800 1250 291359550 291359557
    0x1020a0f18090f0c03050a02070f2402030a020408010e0f1f020c0a0303020a02070801180f030e0904122601090b01050c1911061c0b0105250201020c010c110105030408 73
    0xc070b80340c0d8070b8030481d49000c0010760807198800b0603540302004107072900401c00d016885400c03c060100c0c9115914403000a40000905000701201c4004980e8aa4806092300c2680e01c10703a0400030094004c6020700080000b07101d5002104007c4005000400906100549542844c0c2100d1035100c000810102a1901d54044a800510700d0040c0c684c1c107015807801034025000030194000520442c1804200c0c0d510512400d140c0e100080d000e0b40041d0f4266546882c0d40c02418411000c02907003488800c01503d80c0c0c3d0030140100c0c03051803028840140000002c2080e92030351000214180074030f00e070008a121a0b1402e42c19580290b0b40418060141401030380c2a02c181480d40e106441036140741d00400d65400300c8400094807540191640320308000c100000d0f8000c07100070104640781100103c1150352580c0c400c0c080f090041c10814107202142e54070f4544540f8901203000c1c101001c140001c2150b0b4103125000d4109001d0802608040290f150044210b061914140c10f02c00000082402c1c8080442078 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 291362050 1250 291360800 291360809
    0x180a0b01380c10060f1406030f15010c02041d060c040e011e050d20040515040b0a050d0303050901060603020a02030a0804030903080315030106080f0a021e03010204030b0708060301020a0f18 83
    0x500501c5d1303950b400a051500c50b44248582d10780e1a481000281ca00003084a0188010740c502a8040e180d21007011800c9284601c070b54184406031580c040140c480d03005035250211150f00820030750f10601030f86420080000d018a451340700400041c0040e451050440c0d055900d901c20580b03600c07944114000c000d07100768100c40c2d032240b50284000104035490503044000c407009250403c5850300d840c00d010a45c1c00550354200d19625a00d000c07036403410710740d100820051008040c101039554650104140d0340e5040e80c00d40029448a0400103900301c2401002c005050034a000c500e0440e507040002d4503801011034980400c50001d01050030b04d0300c00d0300d08401a40d004526169a800d050903014594034400000600039402c2410009440b43c02041c0c00341d54032601c00103013205204507400c010b03524010322915000742103800c150344c0c2c658400f403018101031480b840961042e81003d107805818000000c14552003603004000407901c490b0720811009a00b0b6a80c14a41400c410094248102c0c40b41c5801 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 291363300 1250 291362050 291362083
    0x1403071719111308190201080a0b090106020312091b0603070201060b040609030210090e2d0901140f0123040914100606030908040509180a0b01380c 65
    0x20240b510b15508000f090743c0203070388190626896076250b40a4a074110715005c44900c48110038031601550142d50306a07401204c500f03000410040366400110004000c2e0406401a40080380400c522411180810380110010004003004c03d941c48405025089000714203005241c08030200b4000c0f03000b50005000740c00881344064a89440e4180105240c071a440143d200700111050000d6071400749094005480c11a4031804141d40d07075802c00c00064400704042701980345001d05415039600d01184103402880503c001054502c48103104074280c00005d0001d410540d2404010019001b54807050141e0441e07d440c02d03000400c02c24001002019275610140c01c0f10742c51030b414500d2800c0030a41b24440201e1850800c40c25450b00e90480840e9007136440140f00c80400c0001340a185420b10707405a1042c0c81d8229034440514141c03080d403e0401944040780d0200701a001800302194030308140e0700d80b029803620b44009100c605a41e01c103021000328030030044800016000f0105c0018060940c0720b001144 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 291364550 1250 291363300 291363311
    0x307050604120912240b030706230d0f23040f0c0b12010f09020c1509011814010b10081506090d0506091c080703020901050403020a14011403071719 65
    0x801030302e80305c41200b08150421703041000f01c0c50400b5a105174201c0e50005402003580c60b060100541303541012454070403506a0840c4080503610503100200010ba40a582c00708446080d459020240d070000c2c40105203030860b600303080701001d95100030923501c90f1b000118281e03514207900784a82880e4480c1c0100c0f1501e140055036980c041c02c5207040e40d0494540448a50703e9503035501500d0100c0c05940081e030b8044d00700400b1088510707401204290001c503041c0000500d1181602483c5001c00c442804490000d40f02c601034541c2d010a00c16080d100c0800e840200d010365003500c0040c62444010403482444040780740d01e891544484040e40d42907035001d454006060b015040c15655400704070346031421072040c4401c40d20761003000301080100c000a81c9860b502030321403001c1900070350041003a86040210600000000d0b955603010007001707021080e152a91000101c000405a4034407603143c0325089810407c0c812082d50004200641c140340d0110400c082c0c03182051808108801c05203200c81c1402c04 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 291365800 1250 291364550 291364553
    0xa050a081b031e22020904050c1c051204120209070905130b15040302060708030a18110910050919020c070f061b0c05040f020903010903120e0307050604120912 70
    0x20340342d800c40854400c8500241d601d46208140101d00701c0c80c01184082c1544018005082170407040381c1051152027600c0c10707d1400c0011400340c01502d040101c0c0d6030b881180c10003e03c807041c030070070703500203486c407040c82c41c1c10304000c2101140041c9090080c007a00b80d65002660f03031403041080c08003a003c001c182c0e001d50303c0e440d98500040c2c010f083c0b4039403040035804a104072814010003118100e0b58050300d000d0130850380c1c0c0c0703880903503400041042c0c04082d101c2c565200030110308803d012402d0704c94a1140d80141c0f00d02c00748020420000c1019011806a4100f4006950713020b800350351001f1006d1100381045900030508000c1d00038880500000c0c802c6503000306080140b036040c0400d0f184980d485001008503000003447c04500140301418521030301c0405d000c2d9003015001254180b4102c0005882c19407410701280c02c40f607100106800140b03080070034582c03507201805002d94034040d410045041c1801a00c8a5484900c041c10090903144100241401a8082c007400341c01400345100402040609 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 291366906 1106 291365800 291365821
    0x207050d0204150b0708070606060206090c060c03210105010e0913020405060604050d0c0f08070602030f07020d050d050315100e3705150a050a081b03 66
    0x10f40700106822800c20300415600d0300c1280066075410749401c0c4202100c107181c0020b01150401400d000840c00001079064501500f01c41003941c0d10b0070400c1b203500d98840c006402401c441000c191480e2001000d02c0385040381d00a0720364414580c04107080122455040b0b5049488401121301540942009d60007640e0005024164510301030301c0d9000182d4550803181c040f50300801400303040c810f070200d0319841001020310000600c412400c0c094007039120b015001007a2020600464243c0540d565690360348005a0001c0582d5640306210380000e095510480d446814181d00c1280b00321241000b44102800840d01d90b18102e5498090040009900c0c0c082080070091051911005900e4200d01c100304134000c20090000d80b4500d05002d02c09040d40215000c00d1019050100c00203140e0018102c400301070061900f56655502c0c1911107081c43c00c01014044504c1010041146c0c07410b4 = true := by decide +kernel

theorem cover : BRFrame.Cov 291187050 291366906 := by
  have h0 := BRFrame.cov_init 291187050
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291187050 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 291187050 ≤ n) (h2 : n < 291366906) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
