-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2779
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:43:25.846003+00:00
-- url     : https://prove2.me/submissions/3dba6e01-79b5-41a3-9aab-56d908cfff77

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 499640287 ≤ n < 499820143 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 499641537 1250 499640287 499640291
    0x5090c1c031707051b030306030a02060c1f1d0f031227011a0f0d030809030c0a060c02060112080406050717310e060d170c030414060304080a0c06 64
    0x1038107490001c0d10014051411511250303111800785c0a119001e43d18074070a04201ea1040c41049129a07000822018094044c0c803ca9a01c0c4000001c25052621242c0e03410754814907548114104200c59009007517862074203504852090711000e825481d9211003034412886c4c0e03c14010f4403048100811101d07040320340702d0203c010703503641d034440034a10551031515560030f80d544065488104002d580000980c49044031540180329400300001c41e080050755019042041100010704400030800c2215501801c8408580b070032055441c041000d01410b554440050094600006030540d05030040c01c41550b024100a007080d0130302000715902d4000000598003015405002041e0100d681c0083c680c3d0305408800303a001406602040310035a80304215100401d03e60a810082c0c0300e181100c0580000007100c11000b034444a05100c1c2c3c06c0c0c103042e11070f01448540080c4001007080000020011144100c140000800b805c074100041800200c801800a01b010040a511144a1803030802c45600c99200 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 499642787 1250 499641537 499641557
    0x2270a0e060907090e0a0209010f080402011b1103031803150402150f090406080a02012304050105220e010e0907060503060415091109090108012d020903190605090c1c03 74
    0x55420045e00030f890402d00c03264000791408180d64400c440280140c6c035410404901c3c145640000c084444070328008d0b02c0403100781da0308001c00500c41d00c130b0748100704000e007129203480001409c60702003121111000e00c284a0030100000244401c0d480034401c0c0d4004080040f2402c400111031050f0f07100c03084400340030004004e1803090340c1c0c85114100c00b800040000700b104e04103510000d09010866141e4290f1441715801c044500d458403000c540a6503020b18140b5111590140b1103a50061072488007400032004210200b00745940a100318103c4503007071007aa00d25205e01c04800c1d1100c95034043c210008400f00000fa9150500c1e401c02e401105c1128924882c2d80c0c2e550300e0b62411243d00011a204e0b442000030341910f035140400c105d602400a00b00208950140711042c180b0001c6c2c00304074018500c20694000da0400807540c1510202180941910056220140c894102d0f030065101200c00503d00000326402640018122028a0014084085500b480c8601c4002418640c2c1e0440c00c008480071 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 499644037 1250 499642787 499642799
    0xf13021e03070303080906060901032a05041b080115020d030c020a141c020718091e0305190c02030c010503100f0b0306030705030d02030f18030102270a0e06090709 72
    0x100782c000d50003559005217501382400428140742e80640542c0c4240b040b0f10040c000700340040000308200d8290391941010b60b042103c4070054582d55400181d000c0c1c944500e41b0342a00c184e2003d030790001d0700d81e82c0c0c1032043e0f81c0f070f03c90420300d8480b04200440180d000030410480c5a01907488a19051348500498181184a580d032800c9449089001203594010014002044500d50300003420031801d400501962800e10a0b504900c80c3d5100072420303416201d00381c00f028420301c5c45100c01c101d180c40c1c1008070400b14508014043d60f01407000c080850b2503011f000407401d44280659400c081c0d006010b40850401c4100444107a000a840d4000ca0080c5010002e948010043c09000428425100d5602d9182002c200350a045103540001c1c02034000034400e08055a0200486502c086030240050320782c8061901c44200c0007600f00455003640c400548884c01071160341c40d5480701040c0c41c19401c01d6165580038005003041910900905c0c0711a9404100c0301d02e0040702485e40000c891030289000c1e41e50386 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 499645287 1250 499644037 499644043
    0x10317090d05060711010506030a0b040b0c0f0f13051f030c02011104080f070803041d09070f090b12011116021924030501060c0f031e0302120f13021e03 67
    0x5036a0788041a45c03124001480c01082c00341a5012030102c1c042c0000e201c0c0ca480c0c5113030316400108010004104c0703000080c0301116a2081d43d841e030305490285500c90b290303034440c0045a4080110318600076200d2500003181d142c00325040c8041001d04a03d2100d03c00090002d502401070808048150354a0b0001d400a402c05400500f004014440080201140a0b40c0709800c2030322300d40102aa94000708030602040c803261828401d018030b41c3d114001d050365550f6045041140301c0d0001a4941844c040005d42c3c140f0342d400c9907022150484420350003460000509080f0f554015884c24040010300c80d08040030360000407182d00b140041d000080030004814541a20a250340164200c4841e403030020811900d840d88030782c06801e00f81070030002d03035050a0024050f0004100020035041c825503101003094401c4103004100b003000e040240351042002d0b00034020390003030320740c1441c04401c0a0000c2c2c101e03405660428007507500080030305c051900b15000d01c61f03507034500c06407241584907a40410b00652010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 499646537 1250 499645287 499645291
    0x30c13090c031502090a0e04020906011d0a030b0a180b010510120612030206070201090b01181508030c0d0504031707051c120507080601080c0a230901080f010317090d0506 75
    0x1030f40c0059480c41c0307a0307040240c2a0080d82080010880030000c0000584404200d9a0040424200000b00b80c4203034100d42c454000c2e440d540303900201c0e0b11030004104101558014050500601d003400214020111a00c400200310800381100c03c5980c0100404d0910203020390584140e8a0010305040b2007481c0d65081d2040c9510a81136044444501404c0c5541400f0050300086688000c3c010700090303458010030070b001809076840600c03072000220b980c210668040d031070510000743d80299160f619031195460b9040300d07040c09814007405044108003032042d0101c409503070f485209814061006400c000c81070300040400c8075148682003c0d4100440c2d8404404c02a1a15030345003010004041c0541007550005840d07041031101031810700c81c190f038000d426240d1100d0032840017500d07004850800c94009800c00a10716902146080000702c000d0f88070006d00f000d003420389840015843d0540b200314243d10901c0054900324082428800440c83c400c01450281001090080240e0b90303510790130700300641 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 499647787 1250 499646537 499646573
    0x60b12150a0c08090a17070203100902010e0604180203070c0807120915050a0c03090f030302060a05070206012306041508060405010801180201051b03070b0f06030c13090c03 76
    0x40c0c020064103010602828114400310314100d50341c0d090004e162545c412030604014041908001008007039140301040d13960190b0014110b8a0b9807800c5000c40008207400c0c14140c0c0003031300714260388a05042c49400c480840e04202d40b41514080d8032a4013000a40001d81900100940c1314052804150000080e10b00305000e8884401d1440c15035801500201450703000d030900520151a079840a504442039443c030b041d803030400400f00c074030900c2c0480305680c09070800000c21510704030100506500050301032041c4003804c005c00541c2c0303410006036074a0400348103c10421150980c1c1d08440325062504e41303d41280a890241001d842d104100c00c888040d5030101c00013030265042007030620303282c0610b0f801403581304000c002802003c82c409010050b1644003074144040020444410307805102c2030340030017039210241c03031b16280341c0d1a258115500555220b52441d03802c1c004210280703000b00b5880001c0c0380080541000003a113000b1203002c0c14042c2c006036550013181600101041110014130030b017120b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 499649037 1250 499647787 499647823
    0xd05030406031802060d0903030b13060602010b04060e04170c0303070309060c090506030c09060f19110114010e040305120403021e010b30030a0e150c0703060b12 71
    0x810030100030200d901c00c215020f0080c1404200c0400b60702c80000b104c1000321030440100350441c044c24241e004c0d00c03625500582081c0c410b04c1c4030700110303055417103801a40c100764000c0c0f140345928010031054070620b004102100c0b54240104001407880c201e0180040300303150f41d003414911a00e0580c1c0c15604221902c0c004a40c450b0038035403c06c000d03403003407003c420403501306078105c1c0d4100030102c2c00c90f000080514190504c001484120303940d8400c150340c4280c00d1100140c1e950380f10345c0f005407900c15060b4400408510315001c4000c1c0a2810302078496607181c1c45a90340302c940e2801c40c00158040380030307000380c0c140581008044002003400c40c1c07281c402c078040d80081000c2c02e05051001c0c01e12500c2302c05441a82d15210b03103403590340e807424004500503240d051070350300c12081008103a11441b00e003402103034584400a10300c050f06400180d02407007070b442114140d90034103161035101c1507031040b0040e101c000e80100e5001c2c030000328943d100002490014144407540c0320b140340c44030310341130440c811844014 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 499650287 1250 499649037 499649039
    0x3070327030305070806090f1603090b130605010b04031101050d0e06090c0307062c030f07061211030c160c050315040c120201021f11030408070309091e0504050c0d050304 75
    0x2a082600540c011b101a2150b01007454a4802d8413503055010b13068401101c20b02c0c800040151085d0003612009410904036202c41c10b1800030307844101d075641011203215081000004007a040d0321300380c500301d0381c000c040002e6130f01100004503860ba201b80700c0340036015540c1d45105164401000083d20940c0402d0040151001a50802d880d10200e90302100c2000303400b050600744200c030115040690030b1441080344190010800103070402901c1c0140c5521b071301c90a0f4000034070307961000c1185000c042010007000f04500011044150344400c40c1c42d0910032904005d8aa99242c2d40300300703c80958052000d50300b0303030798136500002d041c84007000340940800010030510046c000e2982050000b049205040000c0100c6940042d440d1418040d40480c4221404815080e25507181c01c03040040341151812640ca19061504600c550052032040c0d0016090317100c08502c18165202d015400b8240414000142080b9146071002d0100140201c42a0045a42514442d200c48807680c810501c0b03007000d15211 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 499651537 1250 499650287 499650301
    0x30b0a0603150c030b030c0d080d060902031f06080f010e04150e0c032a09070905040f0c023a0210050c040302031c09030602031315050916080303070327030305 70
    0x3d102c1c1013489506c203400c184035050081e610410f01e0400c00740d000111175143c10600f005040200303e203600c44d07003800e40000b007009001042d0510000c03a170049140f0581020352151401c40c4c000c0800c0310348421600907500107110b0542c070f034509039501905c980d00801088a00706c1c0c040701074a0a002d80c00074581c4c04020584032910f07051003030703502034520010101d41e4411014420b0b80e5418842455a025403440004240014880c0203000b0291402610a1140310f50180050b4000d040c0000f02d80d0050181009664079101f10056024400c452952941c60011107500c143c2c0e010000480740030194815040c500070400a13902a0511441800d000d603601c9514500606003080d20a00200041c0d02805202c500026002140310007642d40080d0f00680f00e50340c1500301880507010303034006090420503070f1603010b864074547c0085209145240a8030a00d60300b07019960700c00c003000c0c060000d06070814000642b030709100394030010203045800350035400c0b00000341919000709400c04095001030340380e008100d80 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 499652787 1250 499651537 499651541
    0xd080310091a040207020a0305060903070c1d06040e0a0c0e0108150f2205060a0614061602040b04021b07090b0105120f07020c03071806050d030207030b0a0603150c03 73
    0x8103a015824840351400d031036180c0c0169500400b41c0e105942c04219401951200140312003d50303481011214a814509134081e82c0f40c00001045804848030640840c40c03001c01414078441d008000c250010341d4990f0401c00020301080c070702803140c5110740740380c441c0807850400190000b0107100c00000c40a5042104a904204021400b44140e401240c1484415085600c41c141d0040a10060012070303041d54104400b1819510303009005440b685045c1b19400f081607014408403940c0301d1100000400d10014018640141c0d07080005221803541c0840140c02e04e9004210300d040700070700051500c00e042d041d0310714000c0da0302030b940e80e507902c114424000c41c44140710b190141c0c4d009080c95410200d0170051074012440080c07210544506410104802900801c0103031001136000b0180c0d4005e89e00c0b0f1200408030b100c00060012000d040803000155030402c04044090503405601805009085840d1902048000f8051400450395110008040b0b240481d460215514180e80401c4064100781c0040c2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 499654037 1250 499652787 499652789
    0x1b0e0a06050a0512090a060504120807020d2016170d030209090a0e0109080c0124080325020d1401201e070507030309030c060c0308240d080310 63
    0x4107100d03040014903007a6400c0026030b403581d030400410000655508005034201840e0303050081240382850240000c1060b00b403040b80a085403945c44c0d0b007180e0381c2d1180490740c07040161141d001051200743e01000c07001c5001c5802d4003000e4148121035841450307448942550701e0799403201d046007011003c1110302c2c8038103110403641c0c40c03014641075090141d9200002c1c0061009061107102943d43c56031403c01103070a420a03002c80d900154247d0b21400c0d0807490358040c182c4c09400c1004003503d420188000d040155071042610030010065003411100c0c110a940b128070880a030141041c2d408195005a071250071401c03800d40714205034441d21181e00c40403401d54a03111100070145180a2812503207905500541e555103031034400a4030012041010840c1030322440d1406001402440004011f06801000d00411240b081c003144042e00da84100484071482e0340d690040c00100140c0124080400e4580207940e200e0045481149034000e07800010f44540e90710100300c48aa1020080000014039804100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 499655287 1250 499654037 499654049
    0x1a040c09050c16060917030613020c0307060b210321070e010f0c0206041d010e0c18210d02060c07080306060f041d1902090102061302041b0e0a 63
    0x8812410001c210660703a0056060004112220442203014028240c01c10300c6071a40140075090803a00480120f20247d1044410394040c0ca00c03d605ca2610300c0ca50f20881d9000c503100c10242d4240013056807448054a84001c409610170071030b4880310049a0202c2d4440c0401d100000215581e000b8820803040d012900002035000203d04410452615040981107030303280b400346018504035500c6c220070380d14203480e2a4060b401c000041408036000410502000c0d40b40e401090200260703980307a110300c044d0241211036034070850051050b07481c10a841ca140350380b41c400040ca15203110b883c0c915024012011030400c0c0010f079020141c9030f4400d68041c010384e0b40110205509520348403098403104000d04c8042e2550b8010300000a1107a46c409520050b10702030061602039107044511a1034403901044241e503202c000030100c00f45012202c503d4404c54443c0310301030700540b849541d08031038002c491280003c1641c000382c86200a12102d400702000c103110308400e894040f5161540c0c01488100c0002d40c00c04 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 499656537 1250 499655287 499655291
    0x603070e06130c03200904110424050d1a10020303100b09030a0606080f0c01030b0f220e01060303090b070b1f09090c090e011b0f0c1a040c09 62
    0xc80410344440c00c0401c14401c58034004640c100900030110020545550005c66860110b004101c0e500400c1e001052041021a002d02000c01035680000440c440c510405586040b0380180c01242300c00c1e2509103444803000e0409030700701340030880e400050741c40800302a00b5a0410203c1d03583c0c3c91504040341000007046100071400c41c039040c901451042980c1c090031008840124600c0083c0e50200010001140d1140060000594540505075200001000c642c8103001d14550340590703503c240b0618071003a2000389030482000080003407059054030420310550064210b8600b0b000b08031507003e40101d2a142400004000e1b01d1030070000c081007810340003008034030130070018140851124010107400c150320023a40002c1c0340b071050b4401241c086585c0440135550510700740405110403e074030441240e440901c01e01c01103041c031900e41c4c225000b000340d5840a0b0042044520494850340420708288201c0c1010f811029072500c4100d4480d03515a4851381445070369080008110132034114034000c080b03483d01 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 499657787 1250 499656537 499656541
    0x1060308030115020c1e0d0f0b39090d0b010806180a020303030a1515030b2b03080a0f05010f090e0f0604020603040303060b160203071208070605040c0512060603070e 73
    0x2070880f15240c1c1b01c40c1d09046900300340803010380d81c071184500817990100c0d06906130044d9140c403000d0b10404890115050b58241c0c00b240c000c5c5062807103807404407a07450001a00d074410504480b00d40d04900d0728075420041002403032000408415660f030207440300304001d10041ca0003440c514101d01c502507000c0307010b070000c84905d40161000001c1d0b9170403c0c24040007041d42401d2280c110030310601980844003421049c0454510f01c1d415034004140c5070300c1514080b503860340c817110b040c0b058010101038072020f4480c00701540102e4131036103415400c64000c10f4045403941001c40000d0542c1c40030307040404c5507a1b4060080000c400c01c0e100e0f640400d80220301606010300089403094540c800104060701607600040041d041500c40d1748072102504980803131586444140c00b45400d04109207070224041c1c41503070000300c2c40200149800040c42d901007116460031001d652080050840900100c4a034028080046580c1d580c642458450b290004014103203807170020304240c9041030682c4580d9440103c501 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 499659037 1250 499657787 499657789
    0x40b040c080115050c0a0b0a050708040b04061a0406030312050609010f0b0702030c1f020c0316060e04180302030d050a0207030807050304020a030501150501021203090d110f01060308030115020c 85
    0x7416045411000150001c1c0c5101c034801d503058460301541c1c916601806424800700941585100e0040d1903071107041055540f00c42c03048d105400180c4001d0701c0b1955000c00100000c1154020822110020316415546940d8401150584029130030440109200c04003480c800c2d02d9600c40d40f640040100e90340c00d1a0351400400000801d042c2c01100d04500b4002118010364804201a11407081d0240840b008144020700c0e042030709051445220041c000d03941401598600010714146070850764901c50403448c44e03c1c206940e4442100103458205803561a1008000089440501180d0090b0051952000301c1090481200d40c02410914514418030052001c40d9008800f960b12504034102107640761154000201c6540c000d52005001c0d60801500b40504c87c0c0d42040b5030121002a000c48280e80d094148481c403038007003220503c805030300a803c4a0703550f0348101c010300e805140e100305684281940020490035107400b40c00c00d44030080004010801c001c2d4070360540d00c80410398805444080034100c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 499660287 1250 499659037 499659047
    0xa171b0702130603020604092f0a1b020301150501022a090c0c2a091506090604080f010614060903150603100203160201051f12030527040b040c 63
    0x48040e0040242d031003100c40701c6503a0ba000601035a0005e050607182d43d80c508841028003505a0700c4c080744038105045885080c0ca0851211144090100c90750a128607200125940d2815200c8c48080189259048001d610288607414200c0c034644242c1180714200000689403000000a410341d00c842141003080340800f140c0d81c0802d4990031101d45190342c4400302803a0141c0940503680c40140102e9512101c0b403549150a0905103592619187c8244603150404c5603100703081394140c0620503000d654000d41d2800f0402040401d02c010701c918201626000c00b0b5207001c2500310340851980d911132090003086250038a01c1c05400c0222012460a0a0300f07010036120040c0c0361b1354115490354180442c145640900000f80900e0540c80704644a00e409d100700031492000b01680b1015520307010118810924504010040b00784024040a055103450960500d5028008086d01040020310901c401c03626120b000812119000440140c2608180e0030030040fa840300484034403440c40c003032140d0005d035080 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 499661537 1250 499660287 499660297
    0x5071e1101051903020306010504031b0806060d02061c090804031a01090207150c020118060b0f0406050303040b0a171905010f0807140609150d0f05011a0a0201110a171b 74
    0x4e29015840707880f040c005a989014541000700400801c1e59004c1ca050140c41541049444000441d03d01e41c070350109200c0301c6440240d0181d08810704102c6214081a5899010040300e01604001103484958a4203552600682c204441810210355407150055410319981e0160180f0241140b07484115a02c80580c0c06070342d140c0c40912074603403c04e150068001e500904298042c0520720a2012030303881e0032001001e140c1c0000c0e201f401c0c1203120b8012418240705074429114050020b5142a090258040349070f048101c40c0f20030004000520307404004038031665405041b8600d012a46c480006069a0681f24142c0040c15040e1100e00200203804000520030111180040c40c0340c5000500300104000e4859062240e40003200109002030389044000100305a064420040050025440480301921028841d00410807040d174000070a03000c0d0038000f400b4003410713030000041810903401ca0740c0c19600712820600116080c00900042c03107400800d40d035400401c0e1324480c01192680b000308034041c051 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 499662787 1250 499661537 499661587
    0x70b010614090d03180f0b0d050c40030b06031506030c21030310030c080d120f020d110a1706130c020f011109011d0a051005071e110105 60
    0xe060380d0b4800c1c01502d60510050a0340e240203011b125111040c81e0101d50003007072554001e82c548400104502810b1054904c40312101c0d0800940104085010400700d85040d204e503040d0001441072414100e41e0820320000f1031142c00c1407101071800d6030415003000100d0034125507030b280c0c86042204c955804584040003140031520b13015050100c1580b003080e48011040601d5074400041032007158400ca104403401c4907c60060880b0594031825499148c8000d00d4040b004a4001c2c1c0c4e1110550440340c001c180761400078500103040a010b001c010095880120401c40e044100003264880c1c25407003181413040d51280d1101342c203903003081c8010903940640c0040404c0320381d9481104d140e005200b844a903501d12690b4000380800b5001e10041e50003503119950369800709140d1000341941c0d044603001c40c5624800103104240c440d05c1c11081c000d0b5411582000800c02104202c2240099500000071030b80802c24004003d02c000d0354640b0400c0640d8040341d980c1841814040d1111a0351600807103150001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 499664037 1250 499662787 499662797
    0x30e0c010807170421050a1418060d090c080d020c04230103080301051e0102030a122007021c20030a14060a1406030a060b0312070b010614090d03 64
    0x10303502004035968080c101ca44064124200f05010030700000055017140e04c212030850074840d80c3c02c0b0758166840c0c031420803940c0118000700000d81140c020315016146c2d81210750010000c150801c00068074139880540c2110842e5034034201c1d80c0a0000004d4060064030000c3c006100500306034101941c1ca40c051150349224648074514100201508035840b200c4100d001420203c6584a1074500e2040d0400d0041501074081498000441d91111a82030000007040c0c000d189844411401212250000058010b0207a1141e8400400720740c7e441d000c1549071420340a180d203608240c4100a0906035142d501007500b1844580c580100e10038000703010100a00994507000f0401210100c2d00789080d00034081c03c00903007101304101e1000041005446031000790310030041c07252046170051080400751100d68142c0c0c00740d4840e500040d4154072224035051b00400301d6200010814409103141d01c004401c484e900700c454010066a5008103960a54003019030206080881c0c1c107012070001c00b802203010741084 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 499665287 1250 499664037 499664041
    0x3090a030803041b0f06080f01060905100c050f010603030e03060103170706180303050403030c0c050705040e030d15080d020606150703031b0206100519060e131e0606030e0c0108 78
    0x21901c2c3e0368020078840722086004e209a5900c3c0002c083e082c0b2840b1301c07030104544000003005a000d240016059605a0b03c400204c9800c0c07401b882240d0b00c020291100b03100c442c8600001017101000050802e8400301c0c00407420030b0131440c00420f69480c0d180864080d5002c0302c0140000f4428600b107c01968a100c0c000d034903042c250801e02c02900e0a50614018050340d81022014582e043e0805c0c2e00c03035802038900740141e0f02114003c4510411581d405009034000b44000e00c51403a040e085a5003140b486000c50741407040c4050204200d604420001a00028800040001400510000c00c01002900191045240c054003003094a00d00803080c0e100c1500c005140000c15009030301040240014400c90103d100c0c0303601c1c010f965103000b61900080c98180c400009618a03020b48409060600d85101007103003441e0000076a6012820725009034044185101018040500e00c11078a03455203020700700c0c900940c000720603401c5a40907080742c4101410b10001103e910800240003410742c500b07180540190b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 499666537 1250 499665287 499665293
    0x3030109092301051509090706030c0201020d061205070602030a0c03052b06090e03070f020d030905060d0c090b0901020c0d020310090819180e1509161103090a03080304 74
    0x4892442c448011070309414480d07a41c46541503001030300c900415103806000566503810000f1480d030440d155030f074a81c40240103104091007034100907102e69550002604298011a8403010b03111660000e0b199030703141414503414407408000e200000c100350b0000c4c5240031441712000381010703243c403070180c140a0b000030982e649401d5040d40020702c0116184801c1441c0d074010001014100c0c41c401c102d00b0341e01300707000160300d0900071080b6104943c1c054402049402c4075030078003481808440381903041c89452079000855890b441d0003003414060f03a007130000e543c200e0004068015022a0400d0440800a1104003480d0f6000100281d00c80400c070b49116200c18244002450305101880c050720050030501c1104c10441c0e00006001c544080881d5004101c200034400c4800e9049008100c500110410040286c09050369849400007603242e01c64000c09120f602250210300155a41602c0080354241c0c4204103a002c080d804a040707600c3c02031442e04180382d0000e0248030310340c00041d01d0240000089010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 499667787 1250 499666537 499666553
    0xc17040804090501090c0f05032202040b0303040e04140706051c1b03150e060a0e0406060e310201050d0c02070302040906140106030e060c07300e030f0303010909 71
    0x1402d103118140f00c030f0740e110740b211809000c3c85106a0041550044191002405481600e209910301500c02c44203164114800c0d5801c0100c00050340c120343c1d5803064550030f03207060000b040a0030310500703000708504203490a151181c006003841440c54000e554203024660348141160060041c1c443e04216491036030480304028000c4115841303451000701180b280813905a04140400246c0c0240030070403e0f95281c102590341000c5490680c070490841043c0003100f505030906800034041e04001071015190310074003a02d1201654803050955081e00010441d00340c0e41c001080419005008604602a96001070624014450240c4030380f901c0300c0089890340e1007040100015500280148250012070810381300034140700c5007602449949000100304140640103010504156100600603559003800940041c0c06c4064102c8501081041c2d0600f86151152303403407041001074500d911840300620020305500c90203018240207030400c250010304550b01006503030450318903640c0416005030520b08024 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 499669037 1250 499667787 499667789
    0x70e09011b08010f09050105060a050705030c0703060204090606031a0f0d051f0b01080c07021c1406010801061e0e2a030108060a0603020d1502160f05010f0c17040804 73
    0x16021101ea20025415911544490480ba545000c11200039280c070340c5403055850034022550086010402c05e0700d014819001058120f0088081d00d04000a40b500c0a040008950003554000d0700805c00b801018001c0c030803d401480d8038102001310030403e00c00030051b502408101c0b03100382602681c41516484146400000329409015500c8503103041e00d402042606000207916500d1505000b00c4255016070b418500a94070074918505100300d0350b0802041500c00c0a00085111040b4003030780001d026051180808007030320b00a0a00c2d50304044030750f400c5864640c0104908a2801555080740c203005580400303444040c9101c2174640d4410211000f11a4030150489030700e5658903d0800c803590300c10240d41030310402009d0701c2c603036200c0e0542102999264000a54440403107510000001c40c504200c105072486441e0260401501107004102000031b44005c1e50501100643c40d01002750a01c0f420442c0c00c22901d04000d072444505000f0008241e4a00030300d0040800070100d0103116103001510 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 499670287 1250 499669037 499669061
    0x60d02130e0303040b01170604060c140a0203070308100b041802301e15030109020307140306060607081e0705030307090311030a0809010c020414130c0b0c070e0901 72
    0x80103052030714665aa480c1e0040300d064a26a02400001c2031a40c2819411a210f500880c024101900c0d203403158802802030b01500c00c00e010b40402000c104442d060003901080b0b1494000d551203c5d81e030300f0b003d00551001009082000550002804060544415903040da0a219159a803100918521900901c16400320000c000e03144042c0307501e250362800d44004907114803000c2030942d4a50078250417040c0082c00201d255525a100014a40b00c0ca0040802410000600128080000746c02080c04e04100f50001e100030340d542800b699141c1010045a90080710680b0030500d41303039040d142c0812601404814050407907403e200c182828003010141c070b00e0707030750407406481e41e80c1494880682901103500c012203441c4003041c442c114a24000c2080110145c100c1e0314285400a84001160110640d60f41240d200307541d410704500310000700200e51710460320040c81c4000d5040f107081c811000300301680901441502001318a251110104001c41280c2e085403200c0d01c6511f4605290340034210b01c2c084a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 499671537 1250 499670287 499670291
    0xc03070203100902031203010b0901030b01022409010606090b0414150c100c0206060904061d150a060503031809040305070605040308060405090c0319080c19030909050f060d0213 78
    0x40968180e25402802c1d2031313200700e045031a402001942c3c6201070000f4464800e1144c0709001c001d4695010303800440c040241481501c100e2043c800201031450500c1c1012120300c101c0b181000144074091260a010344542d0070408262880c02d01012040d104a000d24440c400010a4014081c0c6030560001d0517040b200c1000b540314101408040d54a4256550482810b400c080c801482e150022130703454000d081c0500b14541070f5803252905806040300800c0c00854480c000400000c0b4203061082003c00f040c41c41001c00355040241141c4155421608444e02c2074200b042405146103541070380c558501001c0d601814555a81e05041d40d0a008884000d00982e0911040204166008550b54820740f4115001c000ca61110095a50303561007a0f558035405a001100038030710400741e43c03002d400c4c4510402860346400002d021560501052000480032040002192006c01d07800c009164041c214540f030401851400d1011110800340280c1800c0c02450036101c480150745034404812281080030703000b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 499672787 1250 499671537 499671553
    0x60506040320120d0905010c0b13030e1302130e0601120b03010204030606080c01080109021e03061f0c0b070f09060503060a0b2a2d0f06010b28080a020c03070203 71
    0x380e1190f1001113450001129000003203120f40c024000510003039040311130300c11036544d00c200d00400300600660503000d1055821030210a079440031040054108a40005078890300d14007000d1b0007000c860340100c40d814520703030100089039911503551442d02c568040041054032080020070700920550300050580780c10900042008080003070161034007142a6240545aa6520103d00c100e003d982030107026100d00501d800b4503c622080030b150000c0c070081030740b0768148820781400d0383c50709003291030070100d804105030b00b05111214a03940d9000106040c2200803900003403004001d8075440c002c0205012000c000708210341c43d01c0040c10098126201c1d4141e4a24800803017101840311030359042036200c6d18008882d04210003103400c402a407014815083e0000f05407103074200103122505035114500c00d43c412510a60803c00280c1e00800c44030406a940d408c00030340501c448c100024000340c1e1203140c1c01c0c2d425002640260182d61200c01008010385032030b041d0751607608610400c007010b54035111742e002c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 499674037 1250 499672787 499672819
    0xd0602040612060609061103120f04031d060322020d0b1b070b0f07110106030309050f0f01171305031308010c1404050d0206070b0f100504060506040320 67
    0x200030400d4030741075200c81509410b0a4103220503542035016000000d6060f03441080058020000420001c0001054034100181d5100c0b0f401d010b042240c0c11543e0a0b003960522051542003041c20b401c006420754564a43d402540200390984001b4103208009801d0008440801507210150002c8582c010245891401c0506128002e030009540f01614400301c910428442901e1030304542c241a401070240000d55205d0903d622110001841181400205002003601413801e100740c0d00a035121361030f50340c0e10f64104424400044d4007240114040c0d002c01601c0051a070f0000c3e001d01d0b020720380780f81002c0c1958480141c107a00942c0408020014800030401c181d054090740707244415103205038000c002c4980d00c0341e401c440c5d5540c80200303981a441c040000740500e050220484028500103400d441c86c003401c0b596900e200c501c0484030400d003000407405100850b8242150b6400400040701d007480030600301400248a032085101c000c100612b9070080640c1001c034070701c06c4120380c0310040002200055040c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 499675287 1250 499674037 499674041
    0x140304110a060c0c0e101a0706060b070807020405190c0e10020a1e020409081602090f0910020304140d0908101a040c02010608031314090403020d1d0d06 67
    0x21046840744a0203039010881c1c502c1265110036a5070081104003010b0705d0a1140009031070064507000d9035400e041b402181c1040301444400d071000408440075a00c0155081c02401c9848640003a01400010442c0e0b0010030640000c3e207540a404460000b055202c0380030401d0b100c981c13004034926250620342580940303034001030784640ca0501603031010122070721100102c1e150300750720b0001488120404c0d940a490502c03840b100c21500d20103400003e4041e20b9407219046a089101105060030300c0b442042d003103007405005550040d113540c0c0c900001c0e05100a10780d8a07800851100511281d01100040038003001c4a0802c4018803400195421038101580040c45800c03030b40507100c090300c2200c2d55800031001500c214031045a0140310217184c00048005c02000e0801040d803101159250764020400420900c000c0c18100e050300000e0b41600d00d0240d00003881c21010181d14400e820708000c1001098000c61002000d207403600e0842c2c40304210b00c5014030b084a0701c82c0a150882200c062030000c12110b9 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 499676537 1250 499675287 499675313
    0x60f020403020102150601021509071a0301060e0d05070612140a14160e0f0d060c02010506210a03111005011d060d0f15110c210a080402060901140304 66
    0x13070382078408444491050342144207040c0e13001030041e88105051030003040c1c030300d416035009034144081e0355042c4d6503000541d4000da0a1060807c410200100401c2400c0c0c2111041c40165803c1c1c500028610080d20340d0b58803101c0307521a05080c4551401424070100440c0d00000040a41c0031100d1060f080c0136142c90700501511024209802e42d4002142c0750300c604444455942c0030950360218a26000020700048046e000405504480b00c0f9820900091240c020301001003110383c0006414540322040018000c0e44031000d40c62003034000303a803a035410804191440c006825040500089460804643c501001001c030090a145030100101e0800d0369401d19158501c0398900c140b00c0764a440d410803070742c4998000b0090840e07080c0d0301c4400007d4000140182d43e440c0d01e075400101c0c0541c840e200045903020901d0b60000350030040c000480740480491035500d911400d080d46040240b1504003502c4920080c0020340326010201d80d03040d09071322821014408400541c28a61039040501d0b203210309040c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 499677787 1250 499676537 499676539
    0x90e030f0714120c06130f0203060a050402150f1911030301060203070309050f01050904270804090c1b11040b060a1e051905070615060f020c0402030c0a030e0703060f02040302 77
    0x2071140d4480d400d162110030742d007000b012080540516202c0183d41c1c2c41042c8030b004110340c880009102d140160340c003409414802e2f034540e43c01044d249800d2042149140918010101f030305024400c0041c90180381080c1c551a120818410800440c80d54050b00e00d401c40b0400b0b02c400d440300100100d074a59021002d0c2c9943c032f2003602c400c580a070312002040605003803612124009103003484209401c1c40c258009680881d08040c0003c460107840c8881070802c4900b280c10382c0c00d0200001c0070445018030f84101c0d140c01b180d9182c0715002c2c1300d0b560700c0d0404070f03014001c0260950b25040c681103269a03607540161804040101060f40e5460103000c081e0031100c06000540b03c06800d45c0c0300001d1107004104540070300c81c50841e0050421000102565290043c0e01d0a0f12400e6a403685040140d50440203100941a19140c3c182d0030340c0700c031100070314264642e07045d14003450040c01488841a150400d450b121000d03400c1c0400c01100e14880c141c90090b050f80040d1685042140c501c10426643d4004c00036640 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 499679037 1250 499677787 499677793
    0x1518010606020120030601142703010608060403080901020408060a0506040b0901030309060c08040b0a110f0714060714010603031107061b06150e042f0a090e030f0714 73
    0x552071030709a00b26a40798045030701d291032500c8942c840081080007140e00000504206003a940700c001003002c20b80043e0246201d030303401c00d9080c5103540c054a0003c02e03030300b108400034030501e030a282885844000240006041c0103004c800705240300802e406460151807402d0845040f07141640310036018140a6030101d004510304041000d5a0400c18182410390707415072183c0d4180c07803821908a40c0da08800c1c0c0e0580e41c1c0c0300c0038000843c2041070b1400400d0030084587c3c400c1038103d40d40c0b0304207052880b000307042c240b6039105c0c0c5006c10000c1c0f50032030303020840c0710308540b040d0712402c0905103550458003c02d500081075203844000f0042540001106402040d8030b01102c80c0e4503119030301501e021700080150a4550300341c07454280014255040307041108044d01e4040001c035920400345444140a842c112201030302050302d480b2890300342c1028040038004220b00d058080825020442d50302c06401401511502d400c0d403500300d00b104004580d40c40b1480030146e96038003500c0c10421200800c95034003481f140 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 499680287 1250 499679037 499679039
    0x3020109062d05070506130b090307030f260403080f1e0c0d0e1009061503020112090201140a05030916180207030e090f04020301110a1205060315180106 67
    0x24891100e80007000d0094405600e00d9481c4661000104090074140080001c10011303180000e509015070b5000c0e241c24074420884002da4907008854640080284046520602c020000320b0b40c00091000f86054904180c1c4200d03900c540d105d91000c0004540c84801010b06060004040d406181c84d80b10b40007034009034003e0344032100b07002001c103000c4910060800c506000304000e02140c0c1e0040055a2003d81d00103002168000325038142158503091031219540d44241c84140110b42c05125202c80140c8990a001820341e40040c0541c0c8090040300700c83e565401c445030859001da100c0010061045607403130703150340000e8402848e540c8102c4209281d4066a0900100141410002010344540d140201405070407100041d000f50000042902000b1a0b01191b6519031145016540101d0224810790036500e028014142035881510310312020000802c010050140d11641c10b00ca5203c0140c40072070140c6079100001e1600d11141a01c80c0000440c000780124881607d409940d0100d464000784091 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 499681537 1250 499680287 499680299
    0x504050103050f1b01360b031f03030c080318010e01020d06050315060d15060f14190512010e0303090114151503090f010e01240b12092503020109 64
    0x2c0c01d4101d1408141e000003080c103c4c10801506e400700f1181407000c0a62100707400c6242040d0b8001c0d0340082020784000081c07244091141c02803200600c41b410b41c1c0d00c5914a582c0c0c00801c00d1030002405840b10740c1c003001080d1082d00b4101549021003401300280314141881c146c6a000394807401070b9401013854000d0005160401041d10040003942000c401c0d19a1388034400d10003100741c00742023190031201c1511080f04a841a102d420007a09003a0b034030001803410282c00503220480903061501c998401c141058140c0c1d00c10600d8401e50f4001d4603d05c144c0304924450f6805009030098480d61808080104049428158044190305804404078041919001143d0f1050b1212080c0a41c001810702078204c0010742c094001c5801c8290402101e0910ba10401980e0031641700d0354941403141d4603900996410311020310888501030864a290040074640003840a55200b141d030b04000500c0020009506240309020005002c40034060244075030101760503a0090400c0380c002280400c0c0043c2001c100 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 499682787 1250 499681537 499681573
    0x616060b2106060f0d0614040c0b0c060412020a0501020304080306032a0d0309081921120f1d060603010f140f15031209090c072402040504050103050f 66
    0x70103509000d080b00b600c3e450300340042541003c0407140c00261610b070300800a441031041000031168000490520f080919015235924040d51140c0590030701402044402c3c44c020072aa030700b20b54003c02c48101e95003038101c140c1c204a0f0000c405442c43d4400f0040000340404e00000303500c42c0404400707685203417003440002c94401c08006259444030780044030700c0c1e000c3c1c1010403440080c0740c0641048a4055035902c1e41501d002e866549240090100b40c24901c20419844201c1da4680041d00401c85041031142005004e01c40c030b143c6400311992981a812222542c40c0d010701c10052018260784c4103030780b40007c0c85540d1002544c0701ca00075031900003a092038007094800c140c0d69603903106030070100fa1504c00165010000c060003401c0100d4040105000941e81001200c88110315180c80944803510501001200407008040c107801c3c038001c00111002880c900701c020483c0400c51502e030300030003060900c00024000c0f9000250001c0c6880008810b1210005581c0344900075641120880b40f843c03004019 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 499684037 1250 499682787 499682839
    0x4060e030f01150b030604060b0a11012d0203100b0a090608090c01090306090204140901061d01080a0308250314150f0d021302040303080618010f050d020616060b 71
    0x141101910184483e824613001150009002000410001c0e201d1000e0141170340070141d0b40021442d20194142c071050300703000e50090582158040c402c4c60544c40e45040d03000e48008402001c1030f03030000000c0c1c100301c103220045001d0a1001c42c403544454078050040e140716040d0160700046480c03000010f0050030b00041d911004407042e502c2c0300341c99186a403150040d03d1030714800c07640b082d100d00308207400c0307014412402e208110000010404614200607150940c8a206d0700105049880005000c0b420000440621495140c0340450302d42e6a040c600510940b07050558140700d004607522690a02d6250300074815801d41465815020380702c032101ea080f2210a0310b40950080c02c41c035040c4085140500103901c005002030564070407020850992001c070380c4a900704a010400241c144001d0341840700d001d508840110b100c0386140c0d4109105410308041901c203071482141400307a06801c548403a070689203000070000d04040b8043c45850000c015200d101d60042c021011030400104851540003554 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 499685287 1250 499684037 499684061
    0x4021203040602101d0d120b060702030d1b08070c0303030b0904050a2009100905091612030e042d060e13020607080c01090204051003110d0c0b04060e030f01 69
    0x1250a00201d60013401400b003649142c001089004228045d141c014010a20554807558440c00c8546d041d50000c011030310041141030203404140100742c01610002030f400d00c0c001903030802c001006602c0003241c40102c42041c00074421031001c1000000c0052503412a03066030300c070303441c14003040c103081080c006814000c0340d0250003a4050701d07405001c42c5a54400d00100560411200d000c640171b0301c049098810700351080582055581000c0001d00e09501c20250020060300150000e403070301c8000c0c010205040c0c05440b0403020300720303601c20030140101d10a29403400c001c0e00a004c2001c03114010310200c0d0340c0d6041e01d2115100000b0100803103440d4403408055031211342600bc115100e20880c51000355030a03c0c03c980014080214101003000d42c0c018142c7c00c45060008205464a4818401511b202600b648071300b040a101c18800100c000c1240211405c040c0c03520f01441140e81844c0b000003155511004001c0b40000700072400c0c0b5480000c2c000852000d500329843c0c4035018907018220ba55840d044 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 499686537 1250 499685287 499685293
    0x3040204050f09100c050c0f0705090603030901090b282d021b0a033311030406050a140a0b03160803030c071a010e060103050f04110609010915020604021203040602 72
    0x5550a08264026070580310b05c0d2800c542031001c0540031902d00717001000007501c81d91140c0804c011a16000360120f40c0700a0560141d03040c00d0103d400600201d00500400072201008940d0b140184200c941404110808070341d02500500d444a000e8500c4000311854001503850340c10017070802004d045842e9243c020b56008009100016000010f240800340d07441e0f80c4070061000000215803e16a00420031840301c454140400c481d07400d000e0030380303010f100888040f801c018800c03403540002010350768081d800200100d00c80c0d80d0300407020000c0c03041d041c100b60751b0034100b0284002e81040350b1000c41322038004d40449000308056015070014018a10415015034001c1000070b0303c7c3e5054501424220744144603141c0080040f102c950032980c0c090b00044801c0d24420200415581d0500465420610480c0c400320175042c20745850b01c116109040c6030f03000e61070006101c3d6469200380e004c1c20060184211548011607a40c000949400043d94240d2090300c0c080907042002c0000701c1240c0880d00c082e001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 499687787 1250 499686537 499686553
    0x1170a05060a0b04060f0f08060702060112060216020d2906031c0207090203070503160e150919030809010e0306072111120a1107030c080708040b07030503040204050f09 74
    0x1860020384840184035801039116000050486d0400d0170103000703040b441005c20015800d01e00d1507803812000074080390440d4415801044034241d140360701e0b035540d41c1100003d41d07103d200151010303400e070303000400a401c00001000c03182400b241d0240c8041c0c02150341300c20090508907625050245d00706a520300c1d810b4101c40c007550020000036a4134041c2e907915005560125546480440490b0070440e60700340030800010402c810340152500242d5002018100103045170300e5100070504414050000143c1204006807401a55070b480d5464072200341004078010700e050b22032404c1002d50700084540c5010a00940041d074080ca00460f24510031040c43c0d6550110010020f0080030802440c2e090700c02d0b00e0790700c0a00b611000c404100a19404405010500722070505d0b40307040c42242c40000e0032180c022030920514001a6100e48001d03020360708401400c2d03c5030a1411320a050f40700716400011104c02c005180c008150300080610700c02d074021582000f55980d40c5607441c800713460032900d60b0025080100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 499689037 1250 499687787 499687801
    0x14033103080414030c0612070305070c0b0a27050c040c080108120f0706050f04031205070512150916080a021206010f030f06080a05070803090f131e0501170a0506 71
    0x80400443d01c000d0071540190a21004079505034040c20080d00380300c402c0b8003000a0180c16000b2150046071600c3c0405291446440d000100c840281c2028840c1b52580c070300c490300000b08101584900185144901da43c0303000d00d002d41d07a400e48000035134015410180e018103c50702400c01c26040b980c1030000750440b034a03007646c0d64480764843c1c0c2084210320814440c80c40856518071801d446403109030701c0c0303074002e05160402810b481240e42c0d9121126040904004030298000199012507010703202c0c1e502d180e01c03400700300341303480b800f030106d040d0411710f0042006900a104035850304118494ac03528400d40e21004140002c3c2e00c0f440e001c025003220401c0c081107041d40b06500c013140720f0400e4500010040c5403ca003d0041d660301d03034007508040c2d10400e0070400b403000621045009155401c0114600300704500828400c5915a00240c45182e000d01041c403010841d8200e001c1a0000c1c0c2103003d040130660110500030034081c00741c40004103c1da80322001c08000011443e80c0c0703e070003000911b11551042 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 499690287 1250 499689037 499689059
    0x7080405060705121603080609150409030c0b0403021f06060f080402180103051011040f0605090d062414010c060509150a1b0807080112140331030804 66
    0x1085034507100f01c10381c08801450302809080211005d0075903000b0301d0164140100100009003003284174141140921401d044160030601052509030f602282c0309519080c281d03188110210b01070078045500c3c0401c400c041d0701040340c00281210b0100061110b03465511002268518054040030a00303594180c0302082c0180101a84076100500005900d078000190b401140000e03881125141d00c0380781d51014114290003904000c900080542d8102444e104554000e040704d031182c40148180004c01855544510001c0811682c101009100b0400c08846040710800b40d001c11004001e644540840d0302c84101c150195428416514800c0303107041902c3d1440140800790146c1102d01c660541004c502e0480b1201d11320900d180b030703c002400e90704c000312010302105940ca030303108000b024010011480d0f04043e003281980d00184000c0c0c201805450b010803c00a8480b41c070305540702c007180c250f41c22514007280424030000b500c0346607240c0360160044501c03160039000041c551002440140a080c1d064 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 499691537 1250 499690287 499690297
    0x31a0a0906090f0309060509030606120a08073203031902190c0606050409020a15032c010e030414060c010b1c0b07050a0c140a05030310090e030708040506 68
    0x202000410000541d2458120744180d40c0440d4003951003141a8145500721610790002e115908001e89000c9103900003940b03d840003007515100360600c02140841010400244140942c0421800e5440025080049400c104020700325030307034100000c0032a81c2d454002c6140c42082c66090042d41907803074201201154161b44181c0e4960b00381e003806100c061100c100d40300707030480070320b42c41300c403082809400c00405a84e85500720500550070b02d2070301001a100c07045031008840100341140030594100394200c0207850782101c80074004002e09402855032105c52010f05110052000800203848488105910380c05644500034420704030141c81d07005810020014108110b09400000d0004481700001d010000220000d807a1301c1c3c104202c4104100300a101503401c0502d03810460300707110000100600308020071030001d201d4410100c8541c0e13141001c01007204225403003010f6946030315003901c1c0d591019101d0320031042c20702c2c04c0001202c5061004000c07960340c0d03034000e03043c0b51030242040c090012036481 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 499692787 1250 499691537 499691551
    0x70201030c0c0c09020c01050a14040b0403030603020a06120b030a02150a0c06050108031308060c0417010b181501081b030709170109030e1c111206090f1204031a 71
    0x250702d0031040090303150070414001e06106000142c444841c10256400c60f4402001007074050314140d869032159450540460340503620041c42c91403981da52804034050041540003d4001100c0c2001080310340e00036200b1410f50031071580801239943c1000425554514220b806500300a4024001e01c20400400080500d14010700b400380000e907256489008580e402d034080445504003142c07180c901406410070400910401c0c004080c141414035003004944504d1141805100c02114840d407025400e422030611090000c101c48001342c5481450701c00300104503501c0c0c3c5141703030b011401c180c030350b0150024601130a58100311403094900e681c1d01c01d40c0d691000d891710050003c400400184010001d05498050520000110308481c0526001e0005420004180e10030318001610031242344040c0c0c0c0300c50b1140e4121001350303c0b000b0f941c4041550300c0c0c26400c1c1030260380205001c1040306003000807134802250344070707080b9a525580600181d000c0d015038003004002c400c038550300c0c1308540401c114003504100 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 499694037 1250 499692787 499692797
    0x3403020a0c0b0906061807090501030c110f061f03030912140609030915040e0727060e03210304112b030905010e0d03030504050109020405130611090105070201030c 72
    0x845038a0703420798410100c81c0c03c040c0f40e1210341008400e045ca00c0e84818120780c074045000c0c40342000740010380b5206050050b141050340c0c4008811800b81b28964501c1c207020640c058034450107404050780c0c0c480c00d0864842c401304c4c440c5445200d11a000f00c081c90112601517950f01800e178201801c2e0304484840c2501aa0180307039a90441100020603c0700d980525035500c0107580d100c25101c00c2c0410641d141c0c000e40d03004034017400100042a101c0100c1c9501c24510719050000c2c69000049850014040164100c075442440307011921a030031234105480d0030000c070100d540500b80024800900c500c009200182d401051000ca000074804002221148200a16032602c0c014102450301c0d5845080b1211215025041580301c00c2c0741c0c22007104d40141c507085c0707003032480303401c000b0042205140300700340040806554500241c1400303c20341c40103502c50360040c8103200741d0030002c061504603060759405403038061605005002103058401103d10000b410303100c240c10b2408a1f001980101454407009040c04 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 499695287 1250 499694037 499694057
    0xc080d060b0a02030406020c09150d0f05060c09010e06070c0315020903030a03020a03140603120703051201030f02100804020a0b090303070219090e060103080d110c0709053403020a 79
    0x101c2050007801d840c000c070750b009644640c60094000c1ca8111342450490141c2d0051041c06a44100d0481c9210308102c00d43d8451001d203060f150000700d01c510080060b196001e0401400714480c400703030041042803000d0303842e2640d43d0b90310020000580f1441030018625203086c00100005002c20207814800c1c142d081c401424201e40c1804241554051400c450000703900007601d030f00d083e4140c8130b100b407005043e101c0001c1615008020030b0f901c4c80385a0304120309141c0030810b48100761183c800c03600384c004402e038240d00c50750356450810740c60b03051a00700b01d10450030707207041901c100d205440181c41650010000340d6664617002d0a40d086038402d208054150100b08101e20140e11381c042400d500b4051b003909015840d150245900856420a800c050700360403480c010000304803500c00395120710b441104005030501440c1034042e07092085c4510091507000ba0440016912034a13804580f00e014000da8817030711303103c600c41c031034201003044c0c010540c022b50034922441c58244241c4c007800c89400c1904020302d0710 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 499696537 1250 499695287 499695299
    0x91508010e010501091409100513061a090106050f040b16060507080a0b0a05010e06090d0b01030506160306241407050303180a021003090503070209040b160f0c080d06 73
    0x580c90740003840440c0c1c1c0d1a078004100b0181c90784242d00c1d0194040300030b0080d50802240301912002035008044540380c03944003140c0e16114a02d001c240c450303070080c0b04004190418143d01c048081d001695441f41540000018245004004540900000340025454581001e201c1071880c0c20030072404960105203040c00000410b00d100d024040c20140e00c0b240d000b8036018115005031503038452264050090780c2d504000c240d8110108401c140d4044131141d484681a101248080c1403480c806446100c28400003c2400000b04416001d000304419201013040403100507070540c1c046100d4603000810303074416440308100c0c2e04880c42d000740c0c0c1840c0043e045224003a07480071641202005903050b0300000700b40300c01d038407400e081000700e08841405851801c0d00c0740c00094044034410b085c80103140c1c07103200d040c0404c00e0034001c03108059801003c00c40f59061900784180c003200121142aa44002c0d01c8450b9015400355101012807105a502c250305c5012565418a00e500446a229062604c905d0040b4407 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 499697787 1250 499696537 499696541
    0x20a06050a050418021801050901020d081305061f050406050f040c030b0604090b01090812040e040f12030903020c01080103120311250209100b041a1303030e010e031609150801 77
    0x2190300c9138000d0385035200010a0841d201800c58201d0601c070781000100000c0c0d80126041c02409a1810405d6884e078406208488400e14000010b00e14041e107130400c07410b00007813022901d1642c5422031440e5419100c5040c402102e902e4020700e1381c4641c5000107040a85000c2d0441d5400070b43c90310b004281c1c2400c1002240c3c4075003040e004074400f40e485a0a0701c146513445115200100028402804822034000d07a44a040c8100c0c02003e2490f203580001900703014503610054030241d800040814a01040c10f00140103020511049005000d11014008258400c0c0e00f0039040e43d4000c001e480400e1202a81a00104038100d005c040c82c038018080c0c5030741241160241c5070717041c100d04500808484544100080c0540040c80c045800301c01c1101489404814801c0d10141d602c42d14089070f414200310f960011038000d0094070700c2c1061980d5808010140e0100f5854122042a2284020400c011040640b00d0045090000000c0d20134001080300700d001e40c001030f840d050780d003840d0340b482c9480f0900c2d01d007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 499699037 1250 499697787 499697819
    0x20313140705100815240d0f290108071103030c1809040f0803040807080c0706110c060304060b060c0d02010e07090c0f0c021930020a06050a0504 64
    0x205400804040115041c4006090500510f80c602000c16143c80c00d4555802c01500034003030b008a06040800c40004140481c01800081030f555990311400780070072460241058440710341d003c40c248103401002c902d4514003048484040094840c10b06950401115940c1c0001c180e10200012000d01c2e00514205000446c0a901c0700050280c0c1e0b60542004d0150822119039107c0c01012034000704008240144070003211240d006008070768035116801e0080d03040c00b0f0170f803000d03181c4680040e8400c003900d00010900100c42482c0c403050381300c0210402881e116050404940c0d0850f50800001e000030742c1c40d6000102005006222506010401424910b40000801d008001d030799548507044003038070304000e140c0c010b1805260a0180d01d03401c141c0204806500c0c40d800c0c00344008859900215521740c02e02c5c03848200c5a00c2100300d4283d4030802d2441d08034000c05401901030301d101403400321454454901038482d03000790048255078a803201c01c071900e0340300c00c19000400405010104054480d81c040079 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 499700287 1250 499699037 499699073
    0x80c160f1211120c150a0905070e0105060414040609020307200723040e0f032203050a080f0d0501060905010f0f1e0e19031502040b0d020313 62
    0x410103003090300e405019180407080410900a202e88281c0040200240c0d0b50440742d40020800e4030f070440c1d440c0344d61418030b0b581141c10708411344800b00030600810741d0018010711302460481e40301a03030b21030714030007464402c0c0a210b0700a001044140042066460368828041c0043d100154950749e9802120482e00309445d0030300003910300140d8000d10a4869541c2c0d0761865a0000707092110315010000c58107014510604606110800001d00207580e1984004c40c2000000c056811201c005001c0036160b901c4540c4039a0f2001501c0c5c3c00e04601a03014625100343c0358084010200c50100d500c075030f006900104070380c0604800820400c3c080880900890780200029100c1240381c900301400074201c0c0f0840140c4008000c0070a41540040790300540030000107201140c0020300036411902180d81402c1d11150742e4001c20041d000e0103902e56444214811640110080920640d0515480707040c2e105a1181482e2403030103100041c2c03406920340c01141c2003910745004c0070f0540c02c1c50750358001c2c0d841204040c7d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 499701537 1250 499700287 499700303
    0xe0a051309152304060b031621020307090509030d11091f0c1e050703050706030507021501032d0302101a09010315090822050f090403080c16 62
    0x5500700501a0114140000d0241c0284200d0f0344451004251805000411640e20811000300c0c0c207001c650703400070414000c054246d816102e0364990004007800c0500c6908046a002c00100007001c0c200202400059402000740176510b01c1d001c1000c008d400080c1418000780010801145104003a2040c81c501d203081c401d40300c0e2980783e041d0401054071220b6260051485030000900829a8841010071f4015170000d89984c511481410188020b00c070804014010321407143c010091000006000e000c8403055074084c4602d540e002000c81c0c0380c040300041035107805401d80042c030000d40286041c61140e5015031544440c4a10303008100303e040131a03034050340560002d00c51015003418600829070101e4910100d940c03400302e45000718104420503c0701400d007a5802c41840c1d100c43d001e40200200782d400c880c84d19141c185d103107000500017080304107170700700108070600c0080c00782480050920f035054000c000390390583d980e40b0f099070321590050880c28036840170003100400d18907422500900324064807034 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 499702787 1250 499701537 499701551
    0x904050408312c0406020f0d240b040303050901021606180506031018110a082a0a030c1106190e0727021303150f14070e0a0513 56
    0x40300044511074002d4441102c0042ca0400d101c0d60b07205403446807503581c3c0e840c0c018030782d00c1e030400d0002400f60b00210981c1714000140c0e44c000c1c2140e60003100d0f51038900340e4904504c6c070360f01021715607003c4d0034450094052414007040000c07034041c0d4050304c080101030060341ea450000c040401d40056168001c580400c040316118404403c41c0086003003d0300c41940c1d4070349503040090034800040006d00c1030003402443c8281c1000000c3c80e0b60401c3c203a280c4040300c196194504800081c3c2514011a00c4041c103124507d003180060344030b003031009080412030919070700e01804040300f1800b802c0c1c04090741c01031004060740603a11a4040061610480031212541c0303120001c800000d09440e400c0f0b0381600c90341d02c02a03040c40107100185506c440c0c840c658264401d10303001002080003a0080c2107040164180684000041c0302c405800800c1c3d404902c641000140386c40018001151100d050103240da0780e4500028090b240511407003892400000c01030b1104907136410000b240c2e001642c0710b118203540c0b510f40c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 499704037 1250 499702787 499702867
    0xe0a02030901050916090c02010f050103120807140a0c0201020a02100203030115050903190c0e0403020706170f010506032809020109050a0e06041d01021207020d11030904050408 78
    0xc1440d41000c4a0f0020f0410300c0078000201c4004005401181103007a07443c0044c6900500035030001d50b8141c00ae550601c4079603502d0410340c0707407031006007090000701c5d104c240041c001e61b11582414403010001e9210340c0c201040400708a07000c4500101c100d06501c1014074500c050385d01c1820b8210b004a041e03004603a00e6043c2040c19070301c041010444400d000040c80410641d5502103010070303142c0c2d105200f0760800031084c240260f42030069031111002070344174024442415808034907031040e91400d071950120b07164250769105040d80202c1d00c0b403104c102c8520040c001c0d4513021000750303000304d81c0c8100c4244035111001c40d4242241d0303010950070099541c114003000c55801c100014002c20081f140705007202c3c5410082928600001c2505202d140c0c1d0b910038100d008200e0110030000c080d688001c540314815804482c90381c200949002d80076100b00602445004c0c8130711600d0190f818540084c6061481c4002400080c5c24050412903046000303201d460025221608030b0790b405210780c071106481c035607464 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 499705287 1250 499704037 499704041
    0xf0d1505120f0f030c0a08031312050408151302101e0801150c05061618060302030411041a0607050c032e142805130209060a060806010c0c0e0a02030901 67
    0x510303000c010f90000d02010b4031100d408a0941d05071034000031503c0d81c0781d40344027001f811200000c00092054088140a0151550040140040d100f5090440380014520428401d81c400d04550680313203403c101217840d005040c4030722079441c009500d0410030501144583c13000011460984090009405600100482005c6061540706035985040080c0440195113030715885810083c40000184003421000030032522480c0c80c45650b507150171141c006135407030b10001002ba500560f000e0310120318201504460b440c0a224003024200b021088031440001c02050003125000180140c68902074041403192945051108828070314643da04001c10701000e9900207860503480c1c040b1081c041c40c1a40306001701c56000a070340d811407a82c220902504811842080d03d1400e4080c0d5250351608000900c09080c000b2038000290300d1007111442c2c0103503204010700482150780e1040c0400521070030003003403032940a51404183d041c080d01900c180c254503040d00c400d6564054510303d01a0340d00000308074040d0002c3c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 499706537 1250 499705287 499705303
    0xe04110a0909020702012f01020712020f0106060815190e010302011103070201080106361502120d0908070807050d0f0c0b06060d0b0d051c050f0d1505120f 68
    0xb20004504042c01500001c01003441d00100e10b5031a5a65003680e084c0c41d407440601590000c2e20310080d991403142c4e1a01304041d200c106004409031003842d91542c202e0700117000f0501558074554603140240e41c2c4241a4042c420030b10407558024944420031010280210040d030302410000000070b000b94590310006042130308002c11902140c1060001400507a0300041180c11911145003030500c02c0d550020032103240e207890055280300d400740c0303000c002150807222114040300d17520300690840c5003e0345400d907102c1d003160600440d0980108800d01144809030322144100e405007428030308080c550750310804607900000003a00c00c1d0344400c18081c01180d10811011200d841445c000f0f03480803e96885000c4010701400191241102103804010742020354019105003000602c2d101402d41d03107062a5480d0031041041c50300d4100c0007907980595a005204640c48030181140701450300b0700b100307030881c010403143c042c01d2100d860100d00000c0e150380311907224603803080078806004100395442400e403410201c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 499707787 1250 499706537 499706549
    0x5010504030e0a0806040204200c161707050603090f070b0310090605011d1c0c031a090307110d080301030803061002011a0d260a030506010804210e04110a09 69
    0x14900c3c10f0020510204140360403d50540c0d004c64215009000d2800c154034030111060300b080c0105445010f0b150001e80007a10038024003010b025692035002030a280c2c208202c3c1514984d21a0a040040c2c2c180000115802040d00d42a20340381d140b420a0541040d280380d006030300b0300d14044240040da0600601444c014260542c080209516220000c0c105040500c80290041009141132032903449950403941d0140305680c100d800d07201d8a1510744828001804103450741c0007407000e2014868205402e0b05e01030350b05800103600704100c6d03540710341c4642d4000300b01a81103440c1110150000c0c4141001d940a14884c0070300329224600130007401984080001e1030002c680c10711001c0c0300a4030f010070103c0c05918041d125841000f481e41000740340440c0c004c00f42e10155200b224640c0845a104020380400117640c0c5d01408a51a08001180c4640d800c1e1005000540c8000088990801980300312030b420b0300c01d0900f02d1484c03881c20006400c56a016a14241150300066000ba8407a030004d1400d019001c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 499709037 1250 499707787 499707799
    0x4080619051f152109110613030b071812031b1211031c0504051506090a0e150a0b012c0607020a0b0a02071505030412050f090d05010504030e 62
    0x342100c0000c80d040051082d150402c0000c0a2070f00c180b449200110080501d40007200180f00308041d0b00c070000c2940c1541603a584801c6500511140f400404490300d202c60030040a1000781951070741032111101600b64000e0080d001c0107448021400d84040004006203611200c0a40305410058401002c00d1501407200041e50b11001c0001c03030b40315000c54441c00368503200401d42c2240d0a0246180324411401303400000000320100404c41981085100d244075200791001c0050f110009040c80c40140c80713403548114400700041c01100d032503000c444030200701300c211000c90b0400d4084002541043d02c94a032400e440c0d01800c0074030b5800110601016540c00410011002c0351803800380d41c014000c510610503400000d0f182c05565a0b40613500241802000161341d0740d2140401a640d0003e500c01d1841e104481074164001038020800e40384a00d420402c86015500040b6044580303a02000000c5015242484012511703158600002c07810b901c20300001845013000d08018002c00000e1002078400e80b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 499710287 1250 499709037 499709071
    0x61503100b0a03020903010e010629030106030507030b220614011d010c0803150418020603070c1b061101060503010c0c0f020d020607051b01031107020904080408061905 74
    0x101030603510225182810442d450705910300040f0040d2140454695041d07092260359089540198480801c540041d20441c004001c0c9118590854031a5820310055048c1400100070060180d08426848000344c0390008003001440009090754504d0740c0090b00c10703c400280c4003004c41c01d91041401404101c0c03100c00c100465400006c010100b0160b04083d4808880d1000c480f5134020034049520f16408150103031a03280ca1000054608500c0020a03c110308103070081c0c403c403000c600350710318040c1c002d07029629542d160340c02074514a2404030100d070141c0b65442440b00000e80b02c0355070005081e060380c0e20b030004054040d4031070079510603030807561113a40f5041039070614940080138001c20903030000b003c0310768042500018203448007400001e9005080010f8070400c104c00865000c410150070f80aa001c0700441000440c102d40b1403100c08144140100106405490440300c0e03143c1c0907201e00b810b00d01e043d480e1081c10b41400c00c103544400b40200f0140c04280640d44601945602c90100c0f42003440c00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 499711537 1250 499710287 499710301
    0x3140a050405100302122202010c02030733030623032d061807051009080a030c15050c030c09030a060c090f06180905090f0d09060311030c040308160f0b061503 70
    0x80d5647d00303000b8148003000c0040c004645080c4a081e004090340021091240b482c03030000200100f040c03180800701d00040307407442e4006000f840b03900c0c1038484c45490381800c003803000b210a00d54095071080d1941f40c41107a002600a90383c18610b4a0504107600c1ca20800321441108035103000b8015021a180000c040707400d41e41000001081c0d2308450080340c240c154900b1040f0150340400098021740801c0c0100120041410340100d81910400d205492a40c802c68108000a049450690340d075032444000300f000c07840207090f480180444807001000e40e000e1040584d00c030307011100c0f4078030202c001c201001010041240411000350042489060900b20f090b601c0b131041c198481c03d03004100c984d9590b680070134610b240c03c201821810409a044a80c44410980080e00e60ba80510504001034201580c545501d0281016240604501410141450709607907070fa0f03503181c2184041010005010900c0008642c00c80440419140540340481442c100181402171000a0b14a214508507041080c0080c4d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 499712787 1250 499711537 499711591
    0x9052116060c0c0b0403210e0a060f1113030501060509041a07030b0607030c23030714011104140a0e071e02031c060512010903140a05040510030212 65
    0x8960000e400107401104940c19200340300d0004020700140d03082410081050740002c1d1030030507900b5503d1f404143c107081c0c0d0074900075281020016052500103401070000601e030343c0c0107800100035a80000c50382c181e400c0e95444007234115110000c52480f480508100740070007072080c03001401041e900c8405900e440c0c0c440c0200c20f070180700e004810815520000c1ca105201e68000c2012100042c01c055452226040040081024000940b405807840203440d6a48409100c10f01e008201003024600748000b985030000d0f0184100b01020443d5225035891910700ea450009102421308200b1066491000c2000e20844032042d07000840c08103604414001751a42200418100051050500c03030084000c120490a6001e00100100c201c03101120100d441e000a401c80c00680b581601c042003000a6400c1040c00c0c1d0300b9411018022400d000861a010405103005200824003400c2240c81d1076a200701082e00c008903805450002540447c00809101125000540001c5048189812500a0786401d58 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 499714037 1250 499712787 499712827
    0x1050903040e060a03020603010e061f0e09041e0c03200f0d0c080f0f060903030705221d01030b0708060312090d0501020d0c02060a1a10050904090521 66
    0x111034040440002c040e41d0310b0b00511303000396038060011600d950307443d581044640c030240e42d9141303d60f8221101100c649015040d142e4081403950f6140c2e808000c00c001e010000c0d20140040d0381046080c0421110501c20103420882d0328402d00304a84180d14500b80001110f070500b00a05129280344141d00d06996196260941c000003141c1000008040c3c0c541402600560340c024665805a181d41c4660500e010a882005058410683c1e034075076103c0e07030707c9900d074401240c80c034012070014890380c2040f10f03810000082446030304a001c1c0c1c406032202a22111008807a0900914034071100041c010041038810140d0003015a00b00341d0b480707052a00020f61203420640f00b00c00d08200208140b8000c0c0d503a606856403541d0400c2c001c5640b120400001c001901c0e150009101500c900c00200352240c0d42e520840c56003c44d40c2040803d002552410894284403611a0300c0400070709000c11a102c0e65940315522503184203100902040310080101910000070390b0311182e1159091101300380451074204010 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 499715287 1250 499714037 499714049
    0x12090f01120b0d030302040503161a07020d050f030d0b010507020d02040f0b040204090e0c0d050a060b060f130510090b19090317040e15011d011101020d021b0105090304 74
    0x340700d154000d28048014914401503540c407188000f140301c18141c040c3d0092098035000c0c1c003510030000307101d199a640348586220319100d4455811018030400002800b5200c050720043c54081c99042d503484840c640186009c540d1029000003440000113102d9100f204155102030030410b00f4001ca540011b8021018510080d000e95240c00b41500028400c1d40034100c003550080085444607101d40f40b03540240703414440d101c000e04c215680200507103032404c80702c00300c80d50180040c0f80c45040b644c0c83d1009008214500c48c0c01c08030510221010f80200340c05040f1042038820001c020601d403200b00504d00c24034801820a1144c0c51800f4466600500e08441070a0244031074200d036104000412581e881150740b0207403c205002c0c9241002d070000e00c00400c00c681607070b080300b0115210044a41640c540e2030440c9070116200e80f011482620028210030880501410310000610204e0760309400e9a0020b600006200e9000580e4001c3c00c5400c0d02210004a00e44000c1000346800200148c0d0380c032440c0254 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 499716537 1250 499715287 499715297
    0x3050d080c0903010c0302070515060607081602040f09030215070903080309030f0a080a0c1d040e0c040507090614040803040e0c0f040603050a0b0306091e011404030c0512090f01 78
    0xd01c034000e4407000c0b200d031031401500820024070028001002900040c100f01c600340140444000505040c030802e03805018010300c01881c00c9205d60b9200c1c1d5070761102550340084a425850100580c0c0da503c03a21415092104012401074600d28000741000c15079041803030303040b90250902a106610240101c00ea80c1e000030791913900e0700d42c03800309440c600914100704100318000440d0502c041e4014030290241204010034096103401c00402d4540d00021481d0002c007080007403513800680340c0754000d2180c040400302511811040d500200d800c1e10412690303400400c20442c404c100303060703000c6503165510040e0440c0500701030501509584a200d5841034044111b003080c041040300c1862421030b6117102c071007202c00d40d540e0303500d00000d070141c0740c2190403100440c0780440c6440c0d1400c02041d85880b0780301080150030350030191280a110321441107110105507603240c500c00c1c18281c031b1400c000c0c0a54002d03103d10440e5512403030b01919004a85182055004040c0f0241c0300a40350310002001c17000007400c1c2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 499717787 1250 499716537 499716541
    0x30312090c0e1e0a0b010518041508010c090816030204050415050f10150806040510080a1a06030d020a12120216020a050103020c03030105212b030603050d08 69
    0x4080e00c00121508120800b00d5500c0a00c000d4960006291035603521000042e0115501c4441e620222032441940a011442c20080e1103440410042ca44043c10700c014400123281d104c0f6007040c00714404540100d412030b075451182c0c503c10340c0c0280380900100840d4006200e400d0f800121903413164428803001b801f490b1220081000c010b100b404031036201e003042404000038a494003000998400c1546c07180646001c1000c003040011003003159802043e019154030b05d4a03260072051000800009164050061510102290100f42401403940881c003e03010f884403c0d50041884202c40300141a0500c03d078000207200c2921030b0081391a030a042c0d0064900000e0302c00711308040d034080410100060000f4800902c10a1707101080140881903030080d54923042c42a241d10040d401c80c4078032215400203a0040c40104a02c0c41c0600c0c540c50350800f0b0302d65110400b00041d40c2c40b841c05007100071a0200340c0c1d944d1782c001d40480c0200965900c1030150301e001d02006103136843d07450712103040a41c10004c2060f0540 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 499719037 1250 499717787 499717793
    0x20a0b040f0b0703050f0c06010306050112081b03040504020c07090b0a0f150216031a06060a0225050a0f06030b0f0916030e0f0a03020f2b120218030105070903031209 73
    0x155150001c0c0c02001b25601d030791900e0200e845501c00d000498102e4038000000c80d903034084200048645034031020791498031040000d54003070185401d1880d2207a110422000c41c9a07180c60020b80b0b5a0004103004050242c2000428000c2c0d4120204203401049050000c1108004d40030120041b40c89074813603c58a2018518105e09000b00005090381c0c442d0400e100000300498200030f00b00c0f0b4a18503031000707c0c6484107010031082c1e10031604c1c01b90059014410034801d406801c514050000300c4c0311142c2c0561642c50002ca1000c8885a210b0450303185411000c015440d010302844000d0203003203500090b80c03501000022402c0c80013400032207410480f48106000c0c6e900943c4013090030100e600403520041421848070303544185203071040f4014084d59003030004044000a1000c0e02c85506d005001281c940700d1a007010f10042c88003c00c082103048403102e4800c041c0c03440100210b000741c000c07040d007145d8031200f45400d584028006ca0b00300b00e100442040400d910040600403000c0322075002c2020001c2d41 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 499720287 1250 499719037 499719047
    0x10c0507031b090f0e07051009120c0f080c0d11061215120102090a0b0304020315010e180604050705011b15020306010906110a0f03030608030a0309020a0b040f0b0703 73
    0x500000c088071002103104480910495081c2c0407076607035040500401c81001340308016220240e001007001c0d8003046050003035103441012846280d100f442e01d6a140740c1d5804c00c0394001c90080c00191404000b1420074408810b941f90342a001e4510200180365a00c08200401ca42454107003029141100c03820300c241941d80c486c4110350303040324400210701c1c02d03040c00110380128442c0a0900b42c072502c08507910800520040c0282c8000320401845141071a14240300d06089a0000700200d03494000c00c0014218180780c204d143c3e001e4402611045c07541c0c50118145055003900f0024419140d00c1131040100290f800245541030320000e01c0c00a075851000c418041d5807003182c210048c41045d001e24121400310300f0307a020750700c9440300f60b0380c00c00b4281e030350002540c4085810003100141d03000200c880c0c0c040341189444402c3c5510a140000301c103940c90049070b0968214550080000c1d0701e81174082e0552410b034907030384080d104182103d032410b45825054051000d40c0e02c9240034100000c41c1841c2418012 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 499721537 1250 499720287 499720289
    0x1f060513051806310c02030f130501180305061f0503030a0509040b0d0c14010c060504080307030e030c19080708041205060c090d0609020a170307230a02010c0507 71
    0x70704880100360a010942e050b488044800902034100070342e26a2024510b000d0030216180c030244a4200c0f0046822400b000c0c000800c2a0011340c40104a845411090380008081c00322805210b0f403034982c1008001004101c501c5150302140140810900129401040c1d41d50000c480d440900c100080e0300038480800c0e40d040d440b541d031500012551043d03894000004020680003120f081060750400410410045551000940f241000c034409102d94000071600341070302c5205040c004d910b0345081d982c44003664001c6074125000c081c044140a81150980110903a486240010354241071000e8402c3d070f40c03030031040d07501421000300e0500d1406020f195001c07210b11a81000c17011766501e841f0000400c00c9075440c08101c556104d0301e00099034124070704050f2a03002000403e0071142207581c0d110203024002c508400c0e41d001c02000f07000100c640ca40f816025105005201442c1c42c0c10b46401c00c0c000c1d121025140049500903480408604100822403584090b4242829440440182002c034034201107 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 499722787 1250 499721537 499721539
    0x9090402120d030e16032f040609020406021b1c08070804060503010807151b02190305010506040f201e0706061502010c0e060d09050a1a1f06051305 65
    0x10b1000d0010607198103400a40300780049901300d80750309035408030181403006a0f103c0607020768124080c4450310303d00e40c2c0400c0140c4600028002507860f9600c0041c0c2142d080c0d9006810117540005c2c00c020f01901800f140407151000341c00e0f01d03903510300d6101043c603c007241d002d1042c0d541c00a2010310304100480041c0c3d880d05801802280d25142c481e800035100354001e0050010310b1148074800038624800307100d6100145415516482c42d100700000514a50103c083e0072030b80100c036090401c0c00c00315605019001180148004074141c00c090301400221003040c180c00383c201d03041c285950740150384500d409000d29060412540d07282d83d10b00140017102c90064010145041c002000e10911001d50407400907642c404414811040c0311707605c1a4226800c41d000d00c0c020540001d01c0003020300e0180701405041140340b40c0420103500342d9840d00d007071550a0074100e03003000c603004551003400b40c540c00c0c5030340c445402140d4003c50a40e05949150410007403250208001c0c00251200408814a0010006004c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 499724037 1250 499722787 499722793
    0x2120408010501030b090604170901030e03030a051803070503090d050a050a0507030308071b060b130204060c06140f0c03091f14250e0a0e01170f0102030c0909040212 73
    0xd1541030362806060284416502c004030b0380041000325801003030713103030045600c0040c0c04a030004154034250203800090340f041c1410360712002d4100c40c1c0400e200a510030412503000054925003c0d205035907043c0403140c911000d90083c040740c000100c0c0041103070262035040700c00d030002d0b80141c9811131418070300400c000d2440c064036804d8001c202c00010b06c1803d0705e200b5107616200307580c0c0c00400c071216090039030f41d91503000714040f01002003450380d172010508003c040c01061920b145803901d074040e6403040d40b0640000310080103070320034032403103100703202085d02c03080140c80080c2001c601066080b1006880204004000004202d200701c4c100002c5d21014107600403801200034880041c00245002051664050490400034440400070f0350011840e0050000d042e2a100510104840e05000346100740d030000c048174404980e03404074171002402071281005c14030342c1d10b076101c4002c0d04084140b084040b05070700600c28004031008080a50b130081c201941c800c0e4090303030f981c000a07102d4100040b000030540 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 499725287 1250 499724037 499724039
    0x120c0906031e1503110f0f010806040f061701060f08030a12021201350d050a11031b070603140a0209041d030901031d0d08070207031406040201080f0f06060307021204 73
    0xc0e4207500c00404130390051070741d80401883c10781070008680504c0c52030341e0b1010b0524079480056002d00111904084080c00004c0c84207088510b09003114260703040080d00041c65442e010701050240120710141401001da002810724244000d0b88d00d01500c58214284110745440c8410340b172255041d207442c00004214101d0a581d40d009000c0300549070a002d0741c240c0d01c50b54080103c0401d00b401b00f00e955070350308000c051300d20309464201d0b400d400460201e010070005076114401c0100410191411000010026003004d4080b04aa45404c00070707841a410325003828011030210300d4146405901c04400c2c41e015079100b01810003e4010142d41e42c2c42200f03c06145921255210004090520f03107800380c07001c100307007580c5142e10302501810480e9100158800703030b90056540d101c0e0440580000603801241e910503201d80e94141e01c0742c0030360080d500b264400d07000c002c01d43d03030700142d045c1d04452400301042883c1000c1d04a88404c0c54000c00007400b03043c0020200380b4940c82041454010f019010642c0d80712 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 499726537 1250 499725287 499725311
    0xc0603061f08150f0d030e1c050c0315011202061b060f0117010b090c09040e030c03030f101d060f0a030501091101050a02070e0c04090905010b01120c0906031e 70
    0x180000f81e40c072004103070355041114403038101100780704404400186842c8520585941c201d508000d217031030054014440f60b458480e00401314a40c5224648254050010706c10074800741442d1540d9000100e000001003001042401c03500304c0c0c03103121550140da00c11703074580f042d040c1c5031070030110b1000320038040c070542d070410030803c8611031202d05807024501104250301c0d040704008c3c26560020310390342d880740c84540402d0695076004001d08a00380d004d003020400800101e402c600310381005907440202e400020030820b00102c0f401c12985c2c000d14101c010342e50f82e81030002c5902503041e202c2d482e10150124001081c181d69a00d480010407a80060410003d1500c80c0b42150107081c040c202111580c130500d04501c00341d800780040d514544440c2d401000090300d422081d414141000d40f403084150010071011a2180303442c095a040719006400100c1c5140c0c00c3e038001018100d082028035061894849903041e1903600550303005c2181c0c0a8500803400c03801c0c3c2c0c18003103a0098400307541004145404006005 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 499727787 1250 499726537 499726547
    0x504150c03020d05030c09090402030a060501080a03090e10062115030302010f0b01052505010227011110020a030e0f0c032e020f0c070f15050c0c0603061f 68
    0x640ca1081e8283c8165164240e01911a80000d1b64600c000310401d00c9400c000e0305040b2100d9600a0000b02102c284d070600d03894a4049807001e8100a605800c2100000306240d00200c5000050620001d0880d842c54035204019000d50307079002d1207082284014079001040c80c1b01c1c1c000d5030040d640d80707010081814041084024006d1b04c0c441140503508100e401208826584551424410103071242441c245501c81e550780c502e94804079103002050741d0f0040d403001c140700b480a00010161581e508100000688181c0c0c04400c04119980c1005694181e08031030314000304564202070075500d809611140c4a10003a4098040c1791882c0340b0701d101d0300710f94900040000a220948806c143c1c185c9814031543d95094404070644840d5850541107074a422001200c0341e80141140c507054010141000c1001c51924100805503009180041c03d17443d0a000e0b41c0610308a12029040c54142185402c4054001c6520703011140e201c284070381008000206992980d07540d40d140000710b1f9800108400d0640340140c2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 499729037 1250 499727787 499727807
    0x40608030d0f0b060304170d0f0605090a05090c040c0908250e0c090105130b0d05090f0a020102300408030a0210020a0206041104021b06060f0301060321050415 70
    0x70a807800d248103050b84050b1489507981601d800303082c4c289555910b4840040120398080200540301e003c1110f03c0c8090118810300900e202e4004010035140c0c9081c08020110b40c028000c1c990b0103142209110001e5000910004917039130a483c0402d0301042c0c0c59082e100c11840d42e03c000c0349809100320015080b402000c0c055206440c0446108541d03458210102200030215201d00c1c40c0e0200b00416912903005130090322504006c4203106c07040c9500d8414400d841d411903070b11411069281c3c0148406000180007290b2a0700c100d80c018000e142d07072500001e5444030b0150720311106180106d280014110000000c00740741c070f00f0960103552156950100c582c0c903801540548014001c21555180209d5a80212200400b8035030003081e054030786480342c42d03400f001010250351282c0c1c00c2107520011940744141c0c0d01440d180c640034060368508502031103c0620002d201c2c51190345080020300028007190900014030f0384120100300f41110f090320036602d5110740d4100d1011004c81c0f0042118441c1d21a1b1904 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 499730287 1250 499729037 499729057
    0x309060a0c0c1203050706020d02280908010c09030209040c090c0f090f15030c0e031603050105010f260a022d030601032a1809020910081b03010b04060803 68
    0x40c0216030707a0f6a5001d01216001d400900040042018078007045d9950040c110015800c2401481c0c4456505c01d40106880c890890300d8041460424500c0d031900220004010006000203001100c80303664000c0c80c480c180d00009126007056800f107414400d034400d88502401c001501007000e0703040c02402030310848641c02d1030304c0080c04d10708000c18507021400780c040c112401501c248040255500040c1c0282564240c50f4080011b02020f9a610341d41c10411640640660070045040da42581002420340301d058100e10001c100d0184100b040c50351a403142075000721080100400301d40c929681c5402c208072408044d40c4001d0680827017124984548100e180b40c150090071500e424900414035807600401d00c0054418030f240c8407440c00d0030051128500c0c2030200a24000711031511007401440080070799900e0450a50707a81040411424942c8145800202000d0314030b031140c0c42c000307580c1e0791000c1c400f0603d60300f44485091007906032025000031400540080003800f840d9262120300359079410200c0a1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 499731537 1250 499730287 499730303
    0x1b0102030c19050702010e010302070311060115023927070e01170105010e0105040b040e01090e070b0d1107050a030e0306070923030a0803100f0f180504050309060a0c 73
    0x1c90880f4041d8003211031140d03041e1200d440c0f4003113100040d402900186000c1d014410301c1c0b00c5074010002c0601a6a0107050607401c00e150302020684001d140541e0300b074407017190300a2280030104160b6402c1d00b01c407440c008042c4c2499076a6000c0c000c21400040e4005910303170700c0608201100740c160000c004038490150b5580303010106440000444100c0c0411100758100c2d0302442c0107000c55445440c10040c1c0c0c02040c14203501d0581e5a00000b42164016400003d05940c4400144080c803190301942c980352070030400824225060000b2442c0328407074500f04c4941e2035a190411080c00d40c410007540c000941080a03580320444604000e00046a1040494402e004801c0000c0c0e20303030b01440c10308081d60310081ca447e00258450300c40601d5900c25009056043c420386e80355000151002008522490040f2801d60000745000240b8552280641001001500c800d6050004500100b89600396580b0a14086059183ca05029045225820b005d9812200024944050741c1c0c200c594540003910078000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 499732787 1250 499731537 499731577
    0x1e05180a08041d0112020409081c05090708030c060c09031e01020702130e150a020f04030515010609031a100510091703040602030715060f2402060105090c1b0102030c 73
    0x3188080090241d4011524100b074205c01500f0140c0c005840d4520400b0140d1800d14a500c0b10582c0e401415522a4015103c408010040c4820322801d0020078481006605200d048100030342c0301e0a004002c3c0c03a800c003022076640b03100e0760700b00044169001c0850342d000d5007090440d0032074040d611070002a0b0207050b5848290101d21001d11032610010750020107405084030309c210761411040061f00b07083c0195000e10411402c03241d40c000810085226a000b0000b50350154410242080160721210900800c20030800c04503c02910260791540c4200e503c03041030391107642e07107040389840760011504010400303916800301c1d40103403042094503a0440920341c12840b02c4056680c0348101d015240041e002400400001080c012203902c42601448010614a4444031030764a02610703544100741801140a0391000d584e20309581e444a580d062014004540c1094041802420043e200030040440007a0b460404240d40800785001c000c068000d550f6070400c0354124400f43c202c035802950019007190 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 499734037 1250 499732787 499732829
    0x726040303020703020c0906011b0206070b010f0602060903030705031302011209080c010b031212190c0201020a0e03030909070f020f070801050411100807120605030102190807031e05180a0804 84
    0x1000352303c542416504e103d50390440800318030003106100d00c202e1701310f9010310980740051007200c21140603015540d4000340c040d151840082c50b12002070500d480d682c00c100148081c143c0c1c0030702100c6e405201e20b035010082050610040300d0031441c5122407805a46407583c084100900e11006041c468201300013800300100080030075485403d56500350400003400c101020213000c0b1480c82eaa403005503003600000050140b60300d002600d01050381c0200603540000e0b403894054101d40282c21007001038000714242583d850102d5004a4081d00a00500c0a0710500b4036500748200800b40b40034400c00700f0746074602e55a543c4207000c5c26050302c080b1046c01d0101803011031400e020785295901e0760760760b03641080c9894521341604c1140e00c85030038030049030700c401010130b254509000030401000400d4003809100c058400082244e08040e011404043c20300c00000300c1c41010045100100104000008440c1c88002000070000029400c0030140e0180001d04014054800060012079a1001e08003100c0f0000035 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 499735287 1250 499734037 499734049
    0xd0b06030d02071d07091505041d01030203030d240602150601030e1b010201181b0b13032004141b040605040603090203070b0d0e0c0a0308030726040303020703020c 72
    0x800341071950a589004d01d4900e02503145810b401c46001e09142d01420348820680000001d0b51404402041c0b00103401c100690f03030000260201014452480665411540042c2e100d1055424000c403041d02e85100c40300040c65000f1842c481181e00044100c00361f51044040e440d00801c04401d07040c0e80e249800a00d03594000e00607281c40f07503510790181034050342900c004c10040d0f80441160381107668840d5080980c02404045000440c002d05070941402401080000c0d05042500b001044001c08e00030901074406c078400810540e0340c0f00001d40303142ea00f017600c0c900e542c0010019a40c1d0080c00c101d40c40c00005111b460700790040c0205c00002c074190f4075080030f4809500c100d10401c4006201000204030302403082c2e012041d154801400d48a40c965503039920010364024115114006139654000384e400002000112f00318001a101d104039503103945c8880c207840c00010644410700204220010745912541007003100c5c0325803900070180314185402c0c000c000f508400811070151117081c100009902d441 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 499736537 1250 499735287 499735289
    0x1050d0803011e09061d06012109061103010b091005161401021201090b030c03070f03020103050612030711130504050a140f0a080a0311250f020d0b06030d0207 70
    0x84903151650b40380c10050348140d03407012100f08505404403800725a89155005501c024030341810060200041c01c940c0107040500a0221818400540155140c5240c1c001c40941e07003113900d03040015907550909010001d042000708040c0d00c504004004103280181c00702422a07688140da041c00503400501042d1400e21a42c0d01100c0c021030814401d0b00080c2c2000c11a00110303140300e00241c140010b5100c201c038084401c4c2c010782d003299101c020414640c217040081c0140201d007180100151f23841c10100320350502c0d032800080c0c109501c540000f0f01e0741e140e001c1003c640c0c0d034103d021a0b9640e4a9414481c203907203460700c0c2051080f10420301d14183c11420340105c0d809507070040090b10007040b9580c1c1c0c07000c5100e1820f80100031802a00c00b440c02c00e0005218489042d0b00a42460391780340d0304004002c00301da0720300803104c0c1c071801c1c144070fa111500031507449095051081048444018260300b481c401404083e4402548101845a4181002640d1a045010704019400c85842e805101003e076292082 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 499737787 1250 499736537 499736543
    0x20313031b050d0615060525020d05030309070512150112030302090d030201050a182012150f0a0e030a12061a120919020f0d0f0c0608090604030c030302071b150801050d 74
    0x1900040e0f0303944408005000b123001d03100801e00380c00e4081a13540d17503066070400c803411740068100c05801c200b83c0c1841c0c1a8207581d00c0d402005490544e055020340d4241c914103000d18603031484850130a10402d40283d0485025003030040007600001c1ca6072800a002e081c0c22180030740b1003170500d40030403510300300125112900d80d840388603c0a040d00c4c00300031a124280d00c03543c01790721201e0b80080340d0070181c00b40826030012403d001c4100381031a203c1c2d480d040040001e4003c1a44070b11b0007007850003a10b004000e0700c803180c92900c3c0181304034130384500b140c029091a4100c04607626180c05104c0281c20424000c000504560001d19803503030b21000c100780c4031000b00081407206e160a048500040c40d280401d05040c1c0f02c010128103840d510750f15074a070982d0b44103508071800c1c083c1030002e000d519000321010794000e8907100104031902e480d40c0c0007171801d5152a00107041c190003080800c2081901511180724003c241001c000707080e41c0741e03407039400700340440100d20100d00003400200311410303d12522521650 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 499739037 1250 499737787 499737817
    0x504082d040b13030b07050a02060c030702071509091407031b080c07060603050d080402031504050a240f06140a03170f0f0d02030106090501020313031b050d06150605 73
    0x225104010480b035002c1d0034161943e100b80000400010114444a0b0141130559102501c03210310000191410001400b540d10b645410710401018030360001c0c00d14280e8465061007811802c10380030580b81c40760135400001140742800303010900c2c0441c03194043d02c20000d5070380c140003d0092000b0703100307c0c0310940d814000249144c2e0000d03600e0030a0740c00600c6d03810310844001500c2e85e0307a52901410100401405000281d0401c00d10096180c1000f142d0030401d00100701100c2c0e07003495598a9501c0780d00f500e000300404240010941e01c41005036a001c24800c00071801d000201070100783c180180024020320600c40c01c2e042d0f942d5034074142980504150390b403140c480c080410300744102c003031b07950041c180070b110700d0008000061900e04610054a4808009100507880e0750410301c0107000c00c0b605400442c11940203201140040b10341c1380f622000c503a00100d6803d882000c401d4100c4c0141840c1e00029042003020b000401081901d40c81640f52101407806070003007a0301c585003280c0f184a8400300e228482 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 499740287 1250 499739037 499739039
    0x510150e09151207030c08120306010818060403020a0203010e03040506040315021303030c0203010b06090904030f031b020615030c1e04021c0b0f0f060a08190504082d04 74
    0x3080c044022a000b405100c41501100d8801000036000c21035180090440e401114081041004049036500035004c0c090240c001e80080ca403a1500c07a000051800d41001807401c080340700c071a01682290000040003003514018035207410065502c42e94611708078000c1d864a9449000350101100391800d5480060000340741c940345845003140d0f6440c00c2c1c400d540450f8204415110180c00c000018002c5d4030030b40b5443c103401601c0c0101800c4440c6c866405010304070800c00d1803540d40d69400a0790307116501d420100c05c03400007210100c000f00300e0a40e100e13201c40300b1540b040400300c5e0001461031040116422400103000c6001c00e040e11031303503214251382d0041c0138454444010000040040c0d2201d0019000500309555040300c0c070a80813801402911041d81ca522201280c200070880c5c01c410740c410b40b4911612808603002c200c10303108100704001000b802e04041740500a450781400d64485810105018a00f000c0c100318405600c02812442c8080e040c014050004014200104400000c0e100c164101 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 499741537 1250 499740287 499740289
    0xa05060619060809100c021e01060f0314011b110606030c010c0f110d0f02030d08060a15121125030c0602250b0a18050712240510150e 59
    0x10581c0601954071034041e08500c25500c01840c0319071b1032414800e5009050240218805200309400b1050a00d01030341000340511200911003000000c403a8040e4491807080c0203804018014440c0d85006900000c5441902403169400102007070100b800c081070703c1140c0c0b1483c00b0140d0b1041000e003500d0120300c0343c40403a800300709a03401110700c442c0201c9107664070b5109000002c142118029040ba9148128040344c001d50608000c4c0c0943c80034241010740031400c008000418147c11403050b404543da0810b100c0500c0d501c110301d00310581c000b5905c103020500c03c8080150498021100b06920845841c00d09111100050b00e20300303005400d61202c040302c038041c0e103d40010354402c4a40c0c00950f002e90b41d2811110162440f000d0ba03c0780501119000307424400312801c1591840c42c103940084c0c15401469001c150302040e0340c012144040c0d41c0d44e5100c0e42528120031400300d100a06422007171401411101050303d82c000502c180318406018102d44d8464260714143c000e05181c0000103040071a61210f1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 499742787 1250 499741537 499741547
    0x1612051b0303040f0e07120c1d0a0509010314160b030406020304031b05060103231e070509090a05010b0103090302030702040c050405031b041a060304060b210a0506061906 75
    0x80003000d01941d10381626114065040304040d4000303800c1e082280d080084459000045a902d640d41d0002402043c036001801048845550b00e00410404034019114295a54845010007020085c080012947e540c0c1000642c0003c5129030b0340241c090a0303e9018000001540b940948188070300a50842c0c039070f070700c40400940000708201c06200d403540d1540808011051850b807158071400041000b90f045107081620504940402200000030845c08a5040703404100e02003c640100d011104541c00034202c01d1400109034066134000b180d130800d00c40042c0001c1940300f5105d0080c4003d00104a00800440403200003290150040c2c0050024400601d07164001c0401c2e000349180c02410151100d0000e0f0601910390580242c060588210395040c0c146401503000718680c0280134500d0201500110301f0304e100062000f00301c0c3e56036074601c02d1941e07509160040e4841c403103445541884d0f91031650341c0d600c4040c0c0000f501d180c40358800040d420b1070410004160f5601903c00114101d2402c00241c80c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 499744037 1250 499742787 499742833
    0xa050a080a170d0e061f0f0b0f090402040303090614030708060409030c021003061d01290d060b0901030b0a0b1b0a050f012307080f0a0f0e161205 64
    0x2000404028440c86461180550b807110b01e410340140085040c06c0c800701400e41586035003401c80310a68502049a110340311190b01c1215442c4803025a0f680c10040507101b10321403040b490b9441407010030080141540003032420141d07605600c40580301240c0410b42540383c0011950080081c15072000501c417810560007495029100f8103052034202c0030366001801c001c0003444c03200300081e61950100005069594080501102460800c1c402d504142013140d8a0041024100031172081c0c10301c0c01d0011040c601114028420104100320003500c8041c4c5410301e0780b040d4507550009051040b1010103150008010080b5550700c42e9241c9801084916011900c5051840c8104ca0182511020129405100c10203a4607590400014803200400400505420392a2000403600c0740c842080b03240341e0002c444075000048071644101070341e5400345800140403021000b0012a040c01480b440c0440c0000e4072000c5c3d02d450f100040c00c1240c4800d0a000c20203418803019002c0e61009412a003000c1191285403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 499745287 1250 499744037 499744073
    0x10803031f0509190e0601060513120809010e0d0b040c1805060d2d06020d200301060c081b01051503010b0d02040c030b060f0306090a0501150f03150803090a050a080a 73
    0x818104445e103150f6003050f80980c0a03901144000814100e1402c7c800101c45c0a003480e048480005d0040da00d500300030b03008441c66241880750110414840e035071044150402c3d560b200c0d003550039a141c140f400a0701001c20f44542060390a05850500341010746018480c41140007174440c0e0048041a03c3e40e0070703604404212011140b081c4503100280d4200c80c1c40c0c2c03242890040d20050b9451410408002c1240d03503980c41e90181c0320800c405044100138500450781120201d02c0c1c0264941580d0800d0012441401d2402c03a0f4044911034488210106401c0644a400c0b51400c0506440d40c3c54180740c00d0311307400400940d20800c8110400010b28243d03001410580842c41c00007039108101d00401c40b143d200842c07100d55504044200b00d07a51900510250303020500f000288099454444480d02c0402820f00c21024080c0800c0d800c1ca03540e2096104044d0503840c1184144443d80d11162180c8a40c001003030303036000706402140841c0504112410004a0310880d005100f005925207071814004083c8090f4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 499746537 1250 499745287 499745291
    0x7051f0507300f140703090b13021507060b0a0803090102030a050d0605030a0f0b06042d0f0c030e070915050603090f060c0901031b0e010e01050909010803031f050919 73
    0x85180260352007071a420603d9100005800c280300201080b180b5002080c940406040003070510002c0c00103800180c01c080703604d84071000342c8114070028172400305d081142014214049034182c00d00055401c4000558015642c0800a40d1244441510b0b0301c11000a03501590040001c00c000310b00c140c0003040b0441d50b83e00c00080a27529540013a00b40005000260341244011828805004441040030740090048a00300818210304200d8000408404201c28a0000c880c602c2d41201c1615005003c03003070300a5404002c5842c1c1c030742d0050020480c0c00b2248501c0c0c852640081408a050300c10000c0703000c80704d00e829a4191a040800909a00050104902e4050b1600300071010030f0070000103020380c04003840302c0e0b220206a00018100c8810440f04e0103a071a203040c080703261070b402443d0605000c10a28121640c0c04590006941611503d21100c0d00304288000000700c514000c00690700502241c0007280131210000c80c06203a480103405042c0d440a9110041036407882450320710190f0898001c40 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 499747787 1250 499746537 499746617
    0x4030f0804170f1209212518020f16050721080910110d120b0102031206010302211303082a071a090d030608160302090c0f07051f0507 59
    0x380308440c0e00c0060031b103849035000c4000074001103a031500c1c81c0441d4204100d480c0c000c501d407100d00c1e0003443d185080c800003144e00183c0c0c900c03030500e0042154010710a005016064090300d240c0303295a08006d12641c00c07150303800c0348119034113501c4101206106070403c482d40d0901c0c50080401c48846130043d0345409104c04090075400c04402400f200340c0d81802510b84030880340c030310030503141515000c00c180c44c111341003040640c1365008145d91041e0040f0080c6001030702c50058901d0300b8004041421814002075480007001a401c03a00c400400320b00d8841daa541c400e0741ca410035240000c00b1118032000e149000040c490200320707076040c09001d034a4065640d090003110000c02582030306005542d03010312030300000120344042c0e4260041400500d42c079401003496007201010100e0407185404005d1107928030780c01040c901c03008030040d0703001e40740310045182c1d9560203494516a03500e202901c584044092011034a503175a041e00c00c00744189499110f00b0501404000c200d00719074184840100b40c2860002 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 499749037 1250 499747787 499747819
    0x110708030a0e1c091208030a0c0509031002041401080f0406090614130215030114010804021302040f06080f060d03050918070c0203010f200703020304030f0804170f1209 74
    0x3001a92202c440d8a000b200f01c0e8031005096000a0b005100d44c00b050b0880c0c1d900043d03000702201da0000490000003482c210380e0008a8440c40788076000e962500c0f5190111482200d00d074001c0c03003110815541c032903689554800640340034030126000da49201241002074045001d541040e90b6051041c00005500c400407000d42000c4d9205a0341c2c3e031280b0340c49241460850800305603004801c3ca080f00e41d5800c56142010021010800081c2d1038104841c4001140441d16103101e400e07004001000150b440b00d031147d400991008562040c40001026500800c07507880900c0031180c0602c0003d4406020700103944c03416101c0d075011058203508010a1784046407504200f400007405810185e032550501c0c0d13010300401d800e580c500c1400c811401e10f4041014910151502d104861001c40c142d800c1d110038035414242d08600803503202400c000c2e06020010200303c5518014001c0d00c101803160b0405024103605956940c0ca1a0b00c982038540c00311450404100514000c2c01401c94000d003007040f4145164 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 499750287 1250 499749037 499749043
    0x9050d050a0215010b0418090804050d0c0b0d0509070614040902030c1e03092a0f0a1809120302120c0f0405031507030b011d01080a02280e0301110708030a0e 69
    0x10b070145800039000700f02030142820b5100c587d0b201c10075034001400052159282d07074400340300c0c1e80306681c401d070103130307644e207010000801003450080c01c0c0d1038042612a41c2c031100c20406007404848002035401640000300b2054000c02400350744509003d04613081c5414007200000039032016202e6020200d0500049000321400b840e40c142d1076045a080c1d030317124280082840e00d4490008076880404010380603030345102e08860401420544c5c119000c04411260340003042c2c6a07003141d08030215080100c41b4440001401c0d4118203034082c85071a082c1820200324400303e04a02403100300f50440074130360010824001c101c2c8064041201c20b100028501661000041c3ca40311360003032070309a030720611000c02c031803a50503108000c1041c400f801c044070f18601c2c1251111403207040ca9a06410f108442020622358900da90584a010703001d640107120000032424040d40304001142c0701d80005101c200340042c0350a0602407015001d035450b900c03078208842c43e6039002e00d0b908000c0850052903036840390086e40413020 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 499751537 1250 499750287 499750289
    0x20f04030204020a03270203030d020901030209060406020f0c1e31060509060f010503041403042c0a1e021b16140f010e040203090705060316110109050d050a021501 72
    0x984000508600380c80c001b80c0c1314080e80d42555800301c14914041d000d62404401c641003d108851b0041c2d03903148480040c3c0007401064032040c3c00210214010514640000f860b01c0d66051a204890440d16884108070045000c80030078450141c19000e020341a007022900581c01321200d454140c00d0400c1c504468050480d8a5801042c0c0c41d2602020085030416030b00d030b40e0b0455825510000c01c11440780028002d48000f500c0100404000007071a2410326092042d070f0042d244060303c24101d151003240100c24010820070301200c0621a50204030100894403c102d140c101a00c2c400070110b05c101082c1000790006c8030f180e00101400f2078070f02c01c00700c0c00b4000780800c1a1034603101c00d04103080030000416041e03038040c4180070307450151002d04580e0b0448a43d46000342c0403074000d680d96803005030450404200398401c2d0380240011090000000990f400100303031040703a9403070b078481d03400c41c1c4d035101c2c2a50707511640a0010340140003004840b5200c0e100800e1120880e0048170211100c1c8091070071a1a82 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 499752787 1250 499751537 499751557
    0x20a090603052a090a140102030f03070302040b0f0405100c210c0b1006200c0405090109060e0c12060c043008090a0b090a090e0705030a05070e09060c040603020f0403020402 76
    0x1001444039080e00d405c1508401908096585400d500703d0b000011b0b691344250610343c0c0d0620000300009880c3c51081e01100c0150088452440e11004460f103558460b402c1070007500e00c20b00d400301c61060745034070900c4003001480d081401e10346074561040c088410b104070300c0c0f00c400c1000001e203484008100e42e448030a0281b4035a903102c1e0300040c40c081c002010410b4021010f51014281c0302800c80c1c0c10303000070b100e0744160b808075000070725515210032060041c6030400c4001e1034107040c4290b185c1c1c45403000c603501a0343e42d0207070342d40803020321100171060b21850100c0e910402110144400d0007028a50b0041c0116a6443d010485c00c000c141072400085c562001c0c407c40700c0ca44001200300550810300080e100510f02d11380018101340040e0001400d100050040c02c4119980704000041c46008000d40001424098180d0b0107561182c10029103461050084002d18100c090103d03840010004001d031160080140e0a4145401e04134110082e6100341d064060881081c0404809079445100411503901 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 499754037 1250 499752787 499752871
    0xd050c010b061b070501020a0309050112060e090a0201180f0308070f0b04240218010c08210f07170441070501050903120d0f060f031401020a09060305 66
    0x4401e0422844c00c2c0c0382c2d4100a0454100c0c00ca9880002e402c40042c3c0d05071502400c000901850880c2800d00a2420ba40600406c84040d0207000186e280810040c1c034250003a41e841344002170b00c1390400d18102c1d46100d0741c16202c01c120810000308003c0000f506245200310010303072818000781c80f0f40310300790401c1e039003601ca50800710b4883c0d8240168508003a140c4900c0441581004035007514801100034806016042c840908200e504000300c100c11910705035003000b03008040c00b07000340700c1012501003243e003c50500448000320300c05500818807002810300000f00030f0100d80d90740d03441300c001e014180e0001e400c1a0000340400b0700204007d03008010107c1081085140020201081e490310840f070f408a418884c0c200409406900c0c081103402c0440c0940c501c19654080c0da0a91034002c03d115440361100030710301407000c180c1d150001d0820080381d02900c1c1c8800910000d95180c0e080344a000c4000c0085040d91408211a6020740c102c01d51007500046001ca001900c641880108030b130300c0845418102c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 499755287 1250 499754037 499754077
    0x30c030b09010b031c20011107060605060304020f0d0501020c0601060c1218090908091f02160e01090509010906090803010602070e0108030d051023150304050d050c010b06 75
    0x18100348115100d21404400800420b913000b40d030040b5094064001c2410000006c2c8402007118219a40718040d1040c07200801149071710114107034a54000d10030458441d03050606c0000d092409500790390095030018144100a0841e60402c51503908000e02224955006c3c410421401c801340704c00e034001c0c840ca850310402c0040303510740702142d00e0070f0400c05c1060081c02c040c9540d110884428900035202c211000050070303019402e058100c0d001f100302141d8010600110389c0c1e0080c0c03c0109218003400c0d513400700c404650200d0a83d2090a550b030041b1039071511a24010421142c00d6008070382c2000314a40000780c4001c07907031501d0023a686000d400b41c5a0520000040040c241d04004020080200c1c020301c180d69410000c006869208d02c000114405031900e0200311b84a1900c54100700400f01039002801580b8a42c40d03030403076038141d141076034440d40752100207040d2940d540301102d1182d6400300103064042c0301d250054603560045003032000690340c0e5001c0a00b2940314107004100c516410b10300311034a0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 499756537 1250 499755287 499755301
    0x290a03020d0b1f08090a0506010f03260304060f06031b050f0a030305091908030408010e01060b03040f030f0905060d0e0d02011503030c05030712120507090b160c030c030b 75
    0x144030b00428840c0900b00d070800c10300804410141d031800002540c030340110541c9620f504a4607241c880e10010b400b40c051140006844c0c244061080c00700d9210740c11000c0c802c110300782000305d00001c013081034140400400004001803226448040d90140d5140c0009105880b511002c402d1290a20050f801c400c15010602441c60f141c001005902c100300c428100c02801c41e50014542d004a80d9100c1c040c08002c00e10310007030900001d085002e006100c0440f510303070360707a142d805003c0c100c002c00114080d440c080d0302151148400013101c3c030030f60300410105d421034155503080305e101c0d22598100d820440008004a007a6403440001c00c030f580d030a51400300b4030703041c262000c6003071400b01c020305025a03140c0032080000384a46007224040325054140015425454204142907200d0681c2c020408902400c83d0220305030020305040b0000c2d161401003040c3ea5642e00c00b03a032000c90a0055660340c0300d042c002049a020380032442c03010340d40304520140045940755540c40b41e11045400880f51094948200498 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 499757787 1250 499756537 499756541
    0x30c4602010311030106200a1a0a050108010603020901060503071101050a0b0109090b01080c1303050313140901030c14030f010c020d0f0912110301090c081b09040c290a03020d 77
    0x140a0703004007072078690f501d40b80700030344583c00700e00401140d00c90750020359400a0003481516208c41c0c011113844180d00400c502a111b9000845159099501d04000417501c030005114038400e69a0180a0350816400c10304140d07440c0d00010807130b8081005000034656490000e0203500d0144104002c04285607040720005080580107030004000c1c0c0e4600b8185004a0b03030302001842d000035001c082c0543c1c60f140071250215080c41070700b010304188000113142d0220042c00d6100005c454403160350005011415040020020013031201826010724003900740002c01c101240620410300007801c40d864101545081800d50354648185070144e00441442000707290040d0b100400c0b40030a01c3c04800150401004c0c207181c0418500242180d00f82032260038041d00d096016290040d0012082170325156111002a587c000748111511114401c1c0511804d0741000c5510500903130f800040041c0355420204103140754100e1050701940080b62040c2c0c80541c090b24001040e00c2d01d90399902517680d070104482101 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 499759037 1250 499757787 499757801
    0xf1207060201110c0303040611070f0c030c08030a1706011b1b05012c01120203130204060b0a080f04030215010303030f150605160201030b060a0806040c02030c46020103 74
    0xda410040201c0e60404c0d1000c4100c80c1c0c80f507849100080d001c0307080340341c142c000c0c010088020100c2800f102c1610038424001015000c4030f10a450222403292205c21881d181e014403081d00c40071415007800c02c501c50395032028490703201e8010324000c0001c16100d44141d041d210b6042c02074480500203440d68002152a030781c00000f8143c04e00b0000900c0102001854840162040b80c040842441fa18a1050ba21400144288002d983d03000d40d01d0b030400c03400301c4054021108040b48a28038002c00082c7e030300564000d45006038060740751038040d45c0d60b070300302071800410041040b411402042000003e0b2184401898040d50007642c0c00101d129096154070119010303101c0c00b10890500c46010410b0b03540c01400ca42944000080580c1c03201f00c64801a0302800d0b001203801c0d4081d4002c03906c581581d5204c2d0030365110300400c0740c00b485040b1411400f80e0f180d20441c1c010424503007000d2140d140301d14480c841112903001083c0e2a00e80c0080303089050841070404403d84e503580400c90600000d569160003107030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 499760287 1250 499759037 499759061
    0x140405060901050127021c1505101b05010b0607050304080f06250306050406230405161103090406120308090d09090f14070201091403090312090f1207060201 69
    0x1140b9414174220300d101c0340441c220b802c100e500f44a4074840003100382d01640c44802000f030381c0c07000300785074214800050914014000c201d040c00c0f0070001018502030f07080d55030703c03541900c44964200380010750002039a29490180c969640b0340010400940383d0700003d00000340100051900d86080c400458180103269802c032400764803440c28400700644500f0500d039019030800c101440941203110680191002c0c0e442254030a00e00003001806e030195241c2c100304000b1b030410742900380c0f082d00108001c88105454980300032503800650307820103009020b40700407403400c40d08413418022800d0000d0300307440003a040300f104900342207421020903404c015110f0b00071100f507020f0b102111400000809002c443e120b0350700400d0326508408070400e082c2d40004094070714040301507a5843c0170a006170280081200403111042c450519030601d00003c0203403620600000c01030000f00e5401b80ca03450158000c0d034451640030000f0342010310395a88000c0700d00740380c20040f0003404103240f0307098000e4211100f000d002 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 499761537 1250 499760287 499760291
    0x90c1e0b07080d02070f150203092a040203130c0306020a110f0c090c071b05030c010f020601060f12090506010e06010e010e0d03090e090c100c11130f140405060901 72
    0x44001260a4207071168203456a43c01a150481403c011161410f50b40020f0f05880d544540380b00e80c1c51194004500c10001c8404035640541041c90144803940d0fa83e03c00b0380450108103545043d17140603001103030080744081d4465015a5a52288148001d865008550650340050444101a0003001c03001000e0341d00005803c4c800110400592a2001001c445211307140345000100820010016520050b80105c29001840001045050307150054020b0610920903244122230350340c803c941589140e9000d5001e84042e901e40f00d0203581d01c9801c10441014401203410081810141d4400c0854246c0075500501c0d0030b5140c6804000581c8001c2e00003410000061016151a40c1000e44d42140c00e0058807915075401060404440140803074000800a4558006001145500245485101300102c0d400400700c410130605682050054200174041c1c020300000001c1e0789000d80e084414000e0358080400e1605403010950101d0342100034144020345d2030f80034070003448410094203500c20035400c02 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 499762787 1250 499761537 499761547
    0x5060609060d020409020a12080903060108060601090e0c250b012c091005070c0506010906150e04140a0212011d13080705160801230705090103090c1e0b 67
    0x402d142c2c880650300a8003a585890001c02103450703d960000080c210100c041440410310700d400c04050340a91a258483c0c428400040380641c0085900d0303025490503168042c40c50b01e003c0d15500901c1c00180542b40e0013400b8000c0070010401c2562544000c03d01c0001c0b054582e049180c1441c1d054410f0b0000f80304c0e038004051404582d400400000c400c007540e9858021541c0d90211210300e042d801c2240200454180f005000d14250021003000416114800792495a80c9912112044403440d02c11280554a02200380d8030340c0d80030308648220514007801c00706501c007407840120808a0305444041059a0000d010001c040d0030799600c6000d0542c1030070641515640220200040700043c1001c1c0e1132100041100b0304100700c1c90b045402007130744002a02d4078041521028440c1c0180b07403140048a50a003400100d02281401d2081c0d50040420360040140c2c48850045841d90400900305041c0355070351012802144541581100900705498058843d4003c0c030300302401724402d5400040003000502c1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 499764037 1250 499762787 499762789
    0x10e09120f1c06031b060216050f010e1206071413052704050a0b060f0d111201050c030103021207060909090236060109080705041d16030506060906 65
    0x42261140d24604801e151078004016a0700728000c0705003950286103140c0349000041040d00d02907800071484980aa0405513500c1e00300781d890700100312030440d01c00104c05c0c00340098500f0941501401d101854440103100004002c1004510100c020074102d074440001c01202580c07080f5071088050b070089a05080960505120040b25100d02a183c03041c0b04aa0310000d456404104503005801201d540c0c1d00c807420141041511052583d4055500e441d040001501505140050050005000e010b8401210703254039480e84015040c0c004d10b034020402c03140c49220b00424000d15006400c45e28402e560b9500d18410848944520070302164076411000c0c0410020760000d07145400c44440e880081a40401031000502e0340740709403002c200c000b200381c184142c1103040c0c896500c907100c0b0b242c684200c0c3d500e60f040150307880d414a03c03801142d5406850184151704154200100316900d001800b51540c212007056806c00e81c0f150301819180700151020028007400300300180e000102617450b004030341800d070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 499765287 1250 499764037 499764073
    0xf061d0c0d080a0e0a140112050408120612011d0f010528020906030103030e0405060613210b07081e010e0106050a0c05010609060503011b0e010f02160e010e09 70
    0x250740900340103404556504410300035200300c400360500a0601d04201e48486004070202582000c150000340700c12030225542d4560b01ca00b90007030b42c0000a6904040c4060035291318080001c0129401140001089050741024080e50f6000206903d400f10994648130303015242864010040345103a040400744984564000d00040c0082125519040c0300410b22440c00060b00c1403184454005d20700000010505910020900444108803800d0185844480802c0198001c100d00c02080d1104814200302c20310000300690764003d0720314281c1d5400032031615600000c00c011190580491500e004101d0341460003103487d029107583c0003e00c1a83d50400d403142c800c01c42c05014140a1040000f6404d15003030003009111003da038014004d005480d02c130a50705000e0529031041c14020341c03e1441510a405019181c1e102c4119644e55000b240103404e00111070603011f04d04c14200798040e801070502c611008003861005841c80d64505015549400710018002c20b001f80181210b0304503041c1c05044103198 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 499766537 1250 499765287 499765309
    0xa020304030903031103120f010510020111030a0914030705070e090f060103140f070f210b0a0209060708040e061f1e050903030318010c02030a08010509130f061d0c 72
    0x54608941004880b14003075285208001034000740c1c40890301000b00c8c02c0b8000355680d060b00c2007a0b03030002c032103089900140d00340c4003840031a4034410010701c0050010846a441480c0c018010040e00d01925841505507040d903100704c5040d40d0540000c2000d002143d1010301c500d4120780b40354000c211000300d0820040d1510410b010041c5412072101c8401c03e801d504000307060048014009540300f25544250210a4030440d219560203904a00b80380c2d0580c2410182400c0d400790800039019440da51140c0200013503014428180e84108140100b501041412014002601c60b580704c0d80100e061110030007074903016036201040c4002c2182e0080b040d8543c400c0010407801c0c1d040507100c91004542a0503202030080c82500c0e41c041c8404002c02c401c0c410662014ac01044110000b0000c21000305800c80c0c076485505403480200b4049001004117040c8031b461940d009000344500e429001051307031450307082c10b0342e90801e0f50801c0d1600020344890400c0c0d80002440c0181000601100c41c400001c01c5001c824 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 499767787 1250 499766537 499766543
    0x30c0a0f060f0c060e0d080a0e07140103090b0c0a080606030c07021306090c0203092e0c0c0504050c0702030c01050c0d0e190803040303110303010b09041a04020f120a020304030903 79
    0xc0b02c80b6108180540b000c90010340c1d000e01c0510401650500d00d5640d41e0844100c10001600c203004038506002a00c1806070019819020b080954189401d00c0c201c20701030001030741010360f0356103088045580e9082c4a03010f51040030f08659503003440e9000501804000c0c20aa00c2202c1c200284006130643c07004070b070b8001d541541d2a00d0403410f58900e03433006100c0c0d640001980390a00c00841c09142d4080010500c800341281d0303c20710110740c2c413000310444003074003291588801c41004d440e180301e0240040e0020b0f01e2203407104141c00c0d40c070396010905403081034840f0004d21401044010031840c00340311a0400c28800c0c6000f60401c2003402c0d0407940c1e1b90400c01c0340c10510078000c081485036102c500300041030746203405001c094190b4030000d5980e070740d11a01c030541c002414211901c40251010046030304861943c43e040e400d0500603800c06c0010203012800301c01c414002512800152102e0014040c29a40c031040c1d030740c0b00c000c01000f0b210405001020300300d03210705c10810000040c0d082049a419a60 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 499769037 1250 499767787 499767797
    0x70f06030f1103090a020102100504110904141009120305160c0c050307080c0108070207050603040803151002031903062402031b0a0c060c0308070e010c140309030c0a0f06 75
    0x140c0e07619441d00034030180c4550200014000200103034204001541c090a0340301307a01f00d501c281c41f07600003c82201d406580040040c22080c0d0801000d10b442014142c00c2070040c0100d03441980c03c5031002c0c1c60108600e00711060643ca480c590000d0194201a00454140c1c5050511051415100300c1d800149084881c00500c6803180c41d00c07040c851032503040c00107840060f04949109466170752040c2d88600401c46680001c0c81c40380000e81840c80403500504480010704101d0a5880d107503a098140d400090880030000d01c90020f45000350f4072405880c000340d107e5006150b4841111058907030b26444030703031580e09050a00c08208448540c295560346281c100c54032400100052000880c150710414141c0700c005000003c12010220003c2183c98140f0304c01c4204400d004d54948003a54106013440c405400308240d4000a20700b240914200781f0880c40502d42281100780a503100f021004040c0344001c1d00382c2c0003103000311580c142001001e4070100300301d03205081146880700742c40107001c10740034000c2000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 499770287 1250 499769037 499769051
    0xa020a12020301260d0917030708161b0e04030311090d030801171504120333150210050403030b060705011a12120f0d1e0614010c020d1a040503030117070f0603 70
    0xc03c052049d01c65156000307601c0d9070b848880740040c4843c00c1c0c0ca000140c451100840100e9030801c0d4600030142110001582d542e0644c0c2e40391020b90090070785206c210341000040101240d10341c2d41411380030600340709440e0043d0355410030141c00000302e80461420400e5000f20f0b101ca24841c1d03407071186648154000d56007000e480b030303617503044029015000c9031946d1541a01c0494001c40b85442800e51781c03010303071100308243d039584a01c85100c1e0400c2c042404056000070004102142c020740099a105010f03007000710b18000e05402056095105c00e5080c0c60f180d42d284001e000c5419581d0b40318030141d07170032141c8c00c85000c1500d0100d52502c5901403240420400000c2c02218008048144e5411080c040010010b2141c0c0c040c2003210420703140e9400c2c050714038062020907000022501590340c0d00c810380d81c01003403081307942c00c0c02084803070041e05950000408003900910102c41d02018800d6200e4009181c4951400030620307e003840c0c6804c0c034800b0f5001294180480e44040c260001282d08629001c12a0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 499771537 1250 499770287 499770329
    0x803070f0e010923131805120304110f03071503021c06081c030e1e06060a06050301090207060615050c0d0f02061603020705010c080912040e0a020a12020301260d09 72
    0x1030708010102c6442103013007006e24255001440e05040d5198060006d4070b04814a891111403d4803084400030460034410081c0c8980e801c01c108001c0d4000c4000d0211101c194640100700403032a03812541600103600001c800940c071080b10550744240c81c4600e424010b42d418002001c0e107515509804d000d08811040301d0813900c52082e006450054400341c240c03145c144440d946441754828666540c3c0081c400c0001160260504900413011650a962500d0859081c0b6205d00301030342c070101c001d03140c2d66220b41012074800380c0e091000c05016070702d4031082d0340c0c5d001204405e0b007040035414180040c0300e50000550215074000c034025030300c40540c0043c41c103070407020501078000740070381d0308050200e40c60201141c0d00c0760b40040300107000d044840119000300c40c1c8032032001114401c50107840d0b804000c0e81c1c0441c45107603040e0040e1004c1d01c040d080c092000356000d1001c03012a00240c1c408070420a1a6400141070030700e00030843c41d0800d4841c080d18544044000150003480c141c4140501e021000500c4095 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 499772787 1250 499771537 499771549
    0x308090111100624021914030f03130c0e13030e150a0201050f130317220f06050f09030a1409180105040b0a03030c1e0803070f0e010923 60
    0x2c600000d4000c018107520b45206014400c10040e80110052040403001c4005000042203031400b03400c0054000c4012084da51000741545200802045200920811111000c44006903102d0b01043c440f48a1060103070810f041120040c0e4880883c22000000380120340240b40e8508050a805040c00200f14003582c01103000c00b410303059040c1544401151807200309506401c80e0340224040410010325848203006050801b5241e1001000305180f4502c03000032520650400d540039500c1c21009800f0351141104400603c9610422505e0b9400910359104010042c880c00b41c2100c2d000120885615104415655900c11040c1e00c2d4103004015240480c40d143c50021108061409041254052b03600e50420003045000e0003124415410052010400c4c2000e08521003260341680d901c2c5030440e0551520030300c065207183d04d22407461003001c407140821007110043d030181d5802c0e501c10051080720b60b001044002000015410011048010400c1c80040200918802810151040140191400039031 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 499774037 1250 499772787 499772803
    0x2031303052a0c091627080706050a140703052205150a1d06040b0c0c04060b0a030c03141801090510050f01062c030a02042d060308090111 61
    0x540307004000c0340000210b501003207002808030150380d10200758440c41c03499110603060364022000904c145000031038040360007a003d854560185901c009840e1604010740c28900541c2200001c40d0740094421402035000d00b02003c07034001c0c0c25011b8203004681e40d000301140704642c000e40300300e00d404041071104d6030b00d0100300307006210042c808080004500d00450094112003051400b041c3c1c5040d1340440c12001082400b001c01000b4005407516041401079082c98201d40c240d010544200141c0d801d0b25141c61240d18042d20710001c10b240c6400c1400c800606640341600b562040504010309040b42426081c2401d40040003180c1c0b101848102c101d43c1801084402809403403480345810000a245103680054001d01000b003210b0b1490b80c03602015a000101c5641c0c50841400349500c040700e005504400f9001c0020040070f441c0c000724141c0014007a1801100d40c080c02002c22140c0d10b07501800c9a08000c030340303240c1a006028880ca10340360005036014a56140e81445024150000e85517030a00c03944e1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 499775287 1250 499774037 499774087
    0x12031806022b122a02060105090403080414060702070e060103020702101b17190c08031f0506120a061d0415060f0314010c080105031e10020a120f0203130305 69
    0x1110b07000410358140a04da221a04202006800030f00d44d20200301c4d28141c500c06400581981c50350703a42202c00343c80c003d1041c3ca03200480c00d180c0d00844418010075024078010382c010400241003515035001180c0260a0034140341c41080000d006803a00085100c612042e428440d1044c00040203000c050024100c0c000c1c000181e01c00d01440203001c9602600040d460121628056075800900f9104c1c141410780143c41482d06100048000303020034840e600200c0d00344d100e40c16295070b400200700300c1c1d00603007046007410001104020b10824240315900c0180711424089281e038400e540303000103a0b074020b0005410b00c0d005080c486003907002034200f040100320500f80e250940c1d03034070700340003242041c0a1044880d550800140ca4029485100c040d8107a4038020043c1289021f4644243d02005010003000078500400202c209514154405031510746415154100d4040e491040c010481b81010703c02c1c550b0910500070301c041825540d07007140030075605091a40c0d9851182c141c62044410901002c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 499776537 1250 499775287 499775291
    0x20906040f030501050106020309240f030a090204052a0c19050615061201170c060a031a0d0c06140409050a06181a1912031806022b12 59
    0x103031048494022600b100d0080c1d0080202d6600c440d81240c0300d200d09290141c0c40038a0010f000710601c0d9a020300c3e01000b41c025820f41c9400070b0001041855001202c0c0324140301d039142c00d030b90154203041c05034560098000c50360710066000500d40390303030410070004100d441c52000714020402c2d40e000c000080858400d244004010810303850200d545000071500c0c101e203900e08207d071020b241401415603103400f094201e4044142e00f4012081664284020090030754814841c1450301911640c00400e01704843d0340d0007161075030741c0084800440942010304e500808012a07000e000c11104900d2005072101c42c80c095102e515010201001e5014980240d4205072801342170111401c885d5000784c1c100c0f0254201e810902072144e00400480f00c003000c00380c06141c03041030340500d80d00d03040f07240601e0b0010800c0c62201039526002c0090300790000043c1280411094121540344802401c01000180304c80d1000703091000e030502c1401082c0c040d01800031844c509401d8074080250003440c1400441c1900501 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 499777787 1250 499776537 499776539
    0x80303010f031a01120204020f09040e0c040e0a0b010536070e030109030c110103020f031e1008070b0f1c06090605010908061909020907020a060c0804050d0305070302090604 76
    0x10000301d4040c0d100c1150200d807943c5000601c0307410001c40b14101d0b005036502030350005881d0240300180d0f10500b030b0881500001c1048a06643e103034820740c2d410401c0c000042401502400900044500780026007070709600110070100060408503c03141920425a03c001d9800c2e640f61900c119065070441c0044122032a0781900c41040d10f2040c0c0318030490055803401d1140c4020414107089503460240600015103641065000c5000c00002c4c0081d0720b0306240052412294140321100c5400541d904071121494900703043c0d2201d4a841e5140d00000721034041d050451500c11583d540d1f00e41071150000710400400d1005c404c0c4034141c1039801001c24628a25020304100c5804002000c06020714095580b6201000c507003035204290020a0311446001004aa00c030010200201401c600601c8031303081e200c0210100580b6180c80060280100e50021718030b184140c6450400c0d99401c80b9613008000c100810070000c1140010080341441440c02c0c0050592501d0340700714083e00c07540866903009a80060 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 499779037 1250 499777787 499777799
    0x20406051c02090c0f0a0e0102030d021209060a050c160201051b060907061107050108090a020607030f080108030a0504060c032a02010201050f070804120908070f03061404051f0608030301 82
    0x103030031140700f00c031030407200e58402410b960680514108041c8001091282e2820b59005411260710028140112414601d00000e000c0a9a2082c1d102c100b400031040c0c2800816202003050940080c80c3c48000d02a601c1c0804212025003e40902c20380c42c070180380240419079000b0000c0f100c2007a0801542e8400c0052803000903502c01c8181c4041503503218800c00001c50a100f00d81101140400320050a5260328103c0110b0303094001034100c50040c025188540d006030303503030001800e959200b5183d480c5498074401000d8640501684004400d400070805514204d91140c125000e861160404c24910302080c1401c580500d850840d40805030117404480c02c0c0c503901001c4100483d4400d900134400350b510340c51290012841901c0c10804210802c0114002807006110b01400c4010b03403a00b4500d00c0d0380c0700f50640c80c00400340c1c410480d4006418003802400524000c18414411002c08524103040c16a03c41d6900c084241081001e4032400e00d15400030b120581222000340111070460b0f0300c80d61122 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 499780287 1250 499779037 499779079
    0xb09011412060408090d0302071d010602060108030a02120304060b030f0f010b27060d050115210c0303050d060801020f0c0c010833040c030f11090607020d02040605 72
    0x4845100d0340101d44500c079a03800000b40e851050303500c43e41e490300309641c074001d21a00c1300790f00c40101c0560080b0b0707801007410102d405000c0203074044030241c0303115549803020190403c44103803c5508135800400081f8841c540010f400b0098204103072001d82c1c2c2e0ba5442c10840010190768460b035500d4006d0f00d003c0c0303043c0c00340007481e11503101d9050001c0015031b0b1288100140c60701001c2e44d4040c000741e030207080c00516441003601c0360b100d54054400c010303121381c581c0d0701404c49848500d1102500703080e070014441c407900342004000024060801010307040c915107481c1881c07080d034031005040210024194904d403455410078001400004c0c020f544860000d56103c10341e400403440125144a4042c01d041c2c50340c440c0d844240142d81401e540c10742d0000318140070021711000c0c3c80e000c1038080400391181807601c1da03101d6001640865900050100c01c1c0403c0328080c3ca40a64900c01c40344024400c00c01c0c203076600411184026812500509915520300c0480c0107003545030b1020303500c110100c2d5003014141d201 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 499781537 1250 499780287 499780319
    0xc122a03030b06280512090f1005220204020c03131805040206270a0b0c0105070305010f06030b0f03150a0e01050408070201030203041a07050403030e09060616060b0901 74
    0x2601c0600800c1c40b40000d1050a0040c0074076400c440c210055002e44600001a00d070703c50085a241403171416a60804810741c0800c141e5049603242e100c010080c1c0e511f24180003464122130710040511460810804956101607217000440c1449e40403a1598110354a03a4111200d41c4e5019090300d032942c215080007096a000d80c8a0312401082000c07407090300207440c0c49046d108917801441c003410001c0c80049000968101010b5102c0200704e1040c180d80340c0d0b2102da62500910300003149660b5114030741a8503007507820243c107039400c0c1803c0c0801801500c140d02c55007000d54699142c00580f00754000c001940ca2014007580e59054090b0204490800080c030009a02c1210300041c00d0124500d544902d80c00c991003208c002d0b1a1a40501401005611035001907401600607000000d8200c69469201c143d09000d0302d01d400480c07400a020010550050460250018200e6103040d05240000200d0003600c0303022143d80c119403c0c00c90004c10404250b21854054201501018240d0b84402d0745144590503 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 499782787 1250 499781537 499781543
    0x110d02031b070803030c03100b0417010b0102070302090c0903120d050612150a0504080702030d0201051009061412070b030910050c0a0c110111120703030513030c122a 73
    0x30002410381c0a080028845044581100045203541e803020641c42a80d000a044903203900780c009400101d00f075a07200603001038036100a0682548000401c0c540c2141e00740080c0c141950000c010400c00350f0744d144080d82d400000c56003051303035801003100001e081001920343c11030030280100b00444414215803103075114003020b5512054003217183d0006a602e00800d00981840c01340e000009070102d0103904281d80003803062000c1401c103040c980c0040d082c0f038001031b840801070f075503082003100c8070300e101c0d0500005040385142003040c282090a4403245100e004426405100d0288030200d402000300a0038006040b54914a6180d0070041070007929950031401c180380d01804c10000ca0028161407007160807481c1c0325141c400402400d0756038402d44000c0410041c2c141300c204901054001002d0005051800403006006e903284402d2a000c4c0840320050400718050582011220001c2d804c80b8104081540180a140d010780040400720703011a024920007209100070000c2032948007804c40002d051500c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 499784037 1250 499782787 499782817
    0x10021c0510031b0b040b0a053a1806020c032a0d030209060a0309030e0d0f1704151b020604030602031905070c0602070203070504090b090105072d110d0203 68
    0x1c050f501c1c0032001c080b038010094041d404010801c409013040d0002c0130543c4503420882c0c01c000140d440030302031280805003001d2000400286200349425040c2e4442000d5600c1c408202803082c1c070004080706101c400c0000d0049600040070480d0390020006e544880300c9054646402c1d8010251044032118000f400703080a00c40e1030a440481c03400b034000d861010401401050034142c00510803005000643e0040d0148a640400901c06858a02c88036580d94000d02c2c1003000d056070b034504110580d14501e040301401ea4188024040801e01e01001e0b03090088910306990315403200074040b00c80d0408004020750005000900208200441d00610b07c0303440c1805001c1000101e28020f0416074000b1542000050040f200400c0022519405080481d0000c1c04880640b0b031114003003001c44244050039601103030741404001d2210000d004003940407050f0718013b024400084c00d581c1d4105039030310f80641004501143e01c43d11510820100005d24020b900300d80408044440183d00c030b43c415030072100114 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 499785287 1250 499784037 499784063
    0x200a0f1205121504270203151005190918020102010c0e1f031d0c190b0403080c0c190801060e01080622120302030109180510021c051003 60
    0x250082040d28a219620403040b09140da81c943c0e0303c1c2681e4a64050030740d000303507101403466460201500b035200b01407024200e84020b80903401058984400b0850903421405000204401c0030030345040d11044800940b8028041c0802c00c0107010600a44d130400d00e0000c0c0f5090130011455028014683c9042c002e8008106a5086250403520031514150554010400980c503203206140140c0d440e80400c0186130000303610800042030b8001000d00103003807a60b07900c040940a21441c10101d20301040014945843c2c140740703000001781003805540b00240071a400410441102c02040c40314000d103400042c0381b0610315108940740d0381020490b00030105250f20f4000b01181c2d10394900eaa450682d14424000c00d4103560b81860010201710b10b039400d890404294410784001214048a42c1c40c0e80f005850240e22036040814620888070b000800c0c0460320700c034981607008550003107a054102401200003590300c11144d01607841c17203440d03410819081450031003004103641212440038107480c400c0c5e0003c4050 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 499786537 1250 499785287 499785323
    0xf070f0c06200607050306120a080a0f050c070308090f04051e13050a23150906070804020d0b0a020418200304120806010e040204030b0708070f050901200a0f 69
    0x2400703101c0c00320030b15074800e03c00300b00841d000d1006941d010f4002411580b15100340c017101c2e0b04060b0306007021a1110f401240c8540100d0b0481401e14030040103103022414022580f0f81c803a40c0c4e14841c8405032542c600003032940c03c151a107110404054001900921580c1440d152014540035100c03078145081c256400803804c6c492901c00f5552940340c001d00100070304001500e0f0780100741104c103d111079035094520452441103082c0003885480384030032103030b181c980f61114955080c203000030032130000c00003a13032b04200c01030f6501c0341805e407107603000700c2d020110b40d4904090500170701c200c0c0c200c4e0700c1d80300700c0710b5403035188510540091111910444603004040c81d100c428803420300040e02c00905200108040f004014420786000390b020805161040300003c0b18008074080368000c1d002581d42035011010840a190003140482e00112240b9062070305c1d0340340081c000c042d4000c1012003810070040f08080c2c41500182000c0c0c9148192100580c1c1150b01c50b86448105107040140c00c66400b207203507074020070b2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 499787787 1250 499786537 499786577
    0x30906091506060d0510050307060f110c06032d01090603210c02090408090402030f070e030d050a031e0c0302030601020d0806130504020d0b011e0503030f0f0f070f0c06 74
    0xb071880903241508280a0400740000341c0001450182c075456034100005213903608000c500d0003003240303850f070856400715408010510030002440340e03040d5010400525198440000304ea41c00f09048601e080c0d0302c11240d0780804c05120700721840d140350508400111380c00c40c041e40102c044034032419042c503c0c1c0110380c00e005036081403112500c01042c0518905405401d22030301c00b591183c82030302030314130346090100000e04070b810560f0245092b880650030007031a190840300d840c0441d1801c80c014252514404001030441c4074404101040503102d4181002e41201ca494010070800081c5081c82244171000d4001d00942048500d240140306422914500c04c0c00341030b07414050340c00503100006080c200b00100010300350240c0200d800c0b1143c0403812011440e11000307035020b094040300306403800014a0701c1203c4120307640c11042c0f00b60010811400003281d08812070301c408030180c03030707198032a010004c00d1820f90180050142481c42c44000c050f04010312001810140c9400e0f4586142040d000f16000740 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 499789037 1250 499787787 499787791
    0xe01320c030619030b0403121404021318020901090510050a0311100c080304050a170c0c100c050f0c1306030b040f02060d0c08160c350309060915 64
    0x5800c10008940d00b414100c00e100c5003940c404008801480c0d0720740d10b8480d951030881e002d4001840c902642c801d94105402081010042c030000b41409050940005560413051000301c00c2c4a66992401049203400f814142e000640062480d103d542c3c1d180c041c040a040200d91000c5640b018180c0480c007032a1245508042d82d4000084c00000080c180a100c00343d4480040b180920103014850030002d00624000c45c4214400c50252680556525094a40d00b0008290a80034078003409150b40c04800010000200740e8215104140102c101005070fa0320a4076490107041c9002c1c01402c0e010b03881c0c0008003030707040e10800d5445802001303083c0c1580f82114141d000091040b6024030103d008103003507481035001c40780000c040303c3c505441c0b5419a01181c11240186020940c0c480070015620642c0c030160004071603070300b003040c000180703076903030211455021100310f40401001111640c903072001d0303504103041040303550890303500e06041242541d01c400445040307450b8400c58960803404980020524 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 499790287 1250 499789037 499789051
    0x90501050f070f0804051002070302010b03070503061324180308130b190b061902061015051606150e0601090e0105042403061e020301150507060e0132 66
    0x8803c6124403002110a0700001d8010340d01441528480c40701c600191006041561080d0000904244281c1c2410704060276503001300e00c03c0d040441088487c200f04c1000900403a8000e41040d6071030340d20743c003d0100c000400800095149000d0504025050803110b40300d45038000d0320303814000e03a103000e48020b00c41c81d81c02004003514601c030013007910f51407545a4036180da0010f240115207110400040341540c4c1090064181000b8102c480c01140d540500c0001e400040140540c40050b050412160344460201d4161040242c00600040100100c19500b11b4440d0300001c04d010405110603000340b10003c5002d40c240210b04000480d0301980620081c40c11148880070400b0160311303010401006100e0300b000c40d41e012462a104050421043d01b62001961040700e000628890941900007445000c8002e0758081e4030420051105880400b100b10000c14185492503581045203003180c00f601d00c0b0202e8240315800c0042405003400c86191035003022030301110318084001c641e219074074a902c045d5420 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 499791537 1250 499790287 499790297
    0x60c0301050303070209070318030f030b0a121101020307080d020a0905030303270f060a0507091508010b03190504200102010209012f070f050f011d0f040f0c03090501050f07 76
    0x104c014103061503e154402d05d207080005040c41e01442c0d03204a0051228118000f0300d920501c0d0340310b07030b0301403107000360380203090b6115450303a4280755540048075102c4e400030b08600c0040a212200b48c0c170030400c0303800c00f5a1012945403501a41000c0c0c1c8042d4204009180c007180c00010042440d0030000140c03442510601420303688965420b1002140d02c1024140041b203000780c045201600c1e034104003990246c0840341d400225842c020704001c01c540e0303458000d18810400d2110702002c0e01e80c4001d00340d0542d09041080c980c0da46543c19000c40c411401c0b1030f6040708900b004104814011030f00519100300b00d1480702d02c080500f0b0140128200c0c40b5203a44280810032040313810310b140740c0501e07610440990703237441c03240c0c2420b050641903e4420a40d11040900c2201072080c000d03030611800c0d5651881c028203200031754540344030800145005803801d41d0b00406032501a11190f9855401100d030b240c03444d000420002410b44c41c01005001c2610065810358284170200d803180c075101c88020302c5280c0030b54038 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 499792787 1250 499791537 499791547
    0x10608250603090f11040f0c0203120f0f0c03090c0d08030a050703200706020d050112050709090b060409060b0a0b090a170c1003021312120e0f040f1b0809060c0301050303 75
    0x591140007003003541107410071391f038081200042c1c0c01c0e44500348402c26290025034480d0140b082145d04841c00410325841140c0440c18801030301d00301c460341c64000c070007041801d4403959000c803e245000c0281c2005030340141c1018080c01803014400c001d40c026505400207001e079649106e4160306a8905584030403041c949100d14200354500e180250100a00c14070004d450500407a01410079039500303810400b02d0000c01c84d80602041420401007000b00484241448010100e890300d40700e4070801030803540260b498002500820400da0b02c8440b102e04010501c043c810b84405e0615826006403040390b0081840800204194450300c00311039040f20000003c1c41c0b00c11640c000d0103510134044041e0380034190207100c0000d01c82e2903290100041c0404036800d9a1180b507505084041404000c11031050051024030b80c2d403552501544144907040c103a41c003040c000b001051031002065400d40d164685d0403401258070f51541d1100d4013500410165041300d40b41d031520340700041c4500c400c0c1303c0d2036815402001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 499794037 1250 499792787 499792793
    0x81e160e0f0f01030c02011404050607110610050f0105071506050a0902161707060e030a0806061207050c0a06050c0304050c1e0418060f050402010f020a0206040e09010608250603090f 80
    0x11010028017144004510408083e8900384222415941191241c10200c104144198031048001d0f0040c000300052155062101a020b4080e0150159a0141c804c05443c1c00140c0d020300e00311508107034000240800f10580a110400400b000d00a10b449428003820018140c040f80c001c2d148503940308000c01440c80020782e141c40b1490703012511511011010b02c00301e03001c94200e00c9458280510703840038507540c20b0250740003400503c0c020003442c4191805c0c4000403165103200c0c00a41d1252807414216074865454008038900140350a000b04014105020003503a4030200b006940507601ca60200d0701b840e14a4410000710690002d9580c1840b5000035400055281c20380040000803018030040140e00010344031030064070300b5078905000035500d69050200f156404a401c0340180140e00c003501c0d6040035680050b11a228030f00c1100d24541807000480c40c0404298854001050a00102e90144c921103058039a180000042000504450400041c19074001e00808404c03c2c1d100c441402c022240d65 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 499795287 1250 499794037 499794041
    0x14030406060f122f1011120408030d0b040f0c0c02031005160302030c120115110607020703080c01060f08061b1201060f0210020313060f0e0d081e160e0f0f0103 70
    0x110062258035268107030001c045d1a9800b080c132907058590b0780c20340798844070b0303a02518111110510b220704100c10002080702c10307008405c1d100860507803400404e8038822000018040d0070b840301103005e080d00e050280400550002c40805580388241c003511200411a00868111502220303100d80c3d13429610140c08210344681d000b194400d42000c0c806e810405000c4950300380700400d820000c00e0702e401c0c03c103803581d094000c61808140104600102468a4484002501d89841d4800104040008141034600c00c0007900150064100c1012104c2080c0d40c038a80ca40d66000151801413441c4402a0009034000148080f110303a00c440c107044034856480c0450803666041c0c1c107010001140201d581145038400e003030000318040c004000604408050605044003240d03541030400f6140c0c1e00d041c00e21612443e001c202c4c04146003072414500b1695440c829800c44d03500303590b803900c0c101468034400c106400343d008402c0e41c4550f00a5445080e460b041d00140b0040e090381640c1a40e000f03034500303100c01540d8440c2d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 499796537 1250 499795287 499795343
    0x2313020a030b09160f08010b0f03120a050903030315100c050c060304051606081902070f0b0408130315060e060a180e060103260301180c14030406060f12 67
    0x200b41203409901481c848601c071442c1e00d80005d080145a03810030807006600340540c5c040000200c0d900066291007800080c1e0b40c40d0880c90004407070744041841840c0c41d01a10544860840182c19070790b0300d14002080c0303d40c0c01100349100c0d100c2c81d0000450901107210f80c1e1200c00c05a800030091112a00d440100b240f20703000207004039500c0c840d507040340004250480c2400d0080926450f083d82e1814845800701030300c00b10304540450b83d403040c00280e0206410200e038a01d8203070011400c035800d849606000b030b824881c1031040701588140417000810040411030403d4040f03103811301000001d441d9054819040c07020303100c4035840301801c10140085500540b441c2c0b4003440e003010028200040090950800c04241c6c025a40a24001d80c3e4018071298850000403c2d107542d0140c0b8915030610903d40c900e5058244041821941e480b0300000803401000d414120058a025150b00c1380782c14a00b64020b46154000c1000310350741d06d44001406203520041110080e03114030700b0107800c0903400703503800700c2424 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 499797787 1250 499796537 499796551
    0x40302040506060c0a06060509070f080f06011403010e06041109130b010908010c080f010e101403150103061d06010b0702090603210721050405100c062313020a030b 72
    0x420844c490141c103041101ca4040362042c0340200e505485d1000b0003030407440091400c0148852070104106155009a03c954482a40304401c0000c3d119100100d404402c3d420a842c0a124000b0010440901c1c0281c3d9070301c42c000031a01844142c0c0c000748005940d028038000140c110002d205103c82410460300078a841c2c1c20189800710302c40d035940b48034900790b90f420203106001c6180c950030b0010380c0c49200800d42c0074200341d402c0c00000b4103002040d0080d204552281c03100031031030a07424100580e428000300300100613107174950340c0d9542c4038102600100040230000004040764604c80400ba5000300308a4103c884c103c0c80d00b42008141c0e0244090840c000b40640c3c0d044c0100f80c0c207845007080d0004480c03203c0120b0824983c8440c0c083c034144110310b420b0b500d006401254418481d0200d036020301100d0640b4801d5a2444100048030016a80c1101180c0000c10303480c24400c07042c944c041d00c04460341c241007581d00c20000f161200341d5440c44103841d21001039003020031100c041c80070561070502d160300b121b0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 499799037 1250 499797787 499797799
    0x106060e100f111f0f02030709031712070f02010b1912050a15020913050603100f150b1903061d060616052a0a0303030c050c010f02040f0e0c040302040506 68
    0x2414406683c1001d24101081c0d00701c4c03000740c0b000c580c1c0d25110300c61709210b0740c00e1600451546c140040080d003000761510000341070300203918581d0421082c41003a28540c012024240c02c05040c000b10280c066055030840b20019031824040421a15283c2119000c400d144c2d045c0300c0070103040450000c084920740005071001d00c29068040e0001e490070848210700e20b10b0890060b00c8a90400402020b15110301c0c3c40f40007a800d040910080755000300e00351000161500c1d000070b9520321a82401c000d001112108514641e40c000c0005d00390084000a01411004881040094070780b0035060b000c444540c000c1c400700d910922007002c0c0340601008200e1700107030300400e40c034200303440c0804000071451080170480c1d0603007294a01034203c50507240c074110328030030082c00300290464120109041e10b00d2403101030100740e1261386800d00540070350110341c1288a030a00034421071aa42c034600010354001d00c2055495024181c00080c11001d1030f21050044d6418a9040d00d4a40b0b55000c00c4040d00c005061564022 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 499800287 1250 499799037 499799057
    0x1030203090a050f011410031e0c030204150e070f09050d050c0a0f05030d05031302210a03020a140c0303040306112511030d0e120a0605180106060e100f 67
    0x5030f01003140f000c030a01000008102003503e441c00034a040d0004e8101c0c198103490701c2080c400a17003003016080458035004400c50307241849051502220826130720203034101c2c0c074000840e182c000c1401401c1040c1e6100b00c2079480349491b0041300700c030020410400c060009440200601980c5401210f030281c0034000d80454520b9a131100006640d0202c42d4000c4a0340510941c08000314142800001c0f24200c036810070710b00b5071812110b030070361940d00e1650003480348a0b004104034040766080c4030899001030310822104144007520700039542d84042c11003078030002d20031407440c11b0702d1000281203890007070081c010b5401c1c6850b503a100b0300648400b15483c00011028080c5e1891400c2c0c0402111000019510511081000c2e0501da00c000d02d404142d030703010340c01c6507010083d41070b0040f01404a60009540b40900040c03061003250510343e070182c00a002034104411b100e0300c41d03c01e45000b003110903c40020444a599410b06894032050615082d810070039020b4030307440c8103020303604030365010181e402c180c0780c49 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 499801537 1250 499800287 499800293
    0x30c1902042013120812090f07090c03060e041a09010b030d0c03110a1707050316031701120b010e15120102030a0c050c03030f0c1306031b180501030203090a 69
    0x38082c0b514803090b904000c00c040b0b0903903c5141c03808008203a41d2445110f44d18040d110090310784503034014609440700060114140e0f61040060000c084000420355204a894041c0040504040400c1400090070302c60b0100e1955035010703005005075071152202c0e59002d82c042c0c021404000007490f07429195640e05a00740a510240311a0701c0d44003d55507240344c4502a0301d4013402c010591248802c9540c00203800d6070000d03030203060310040380e50a04080d0b5100e146a24083d403031481145c04880044a450311000200b5401c040d01030b01460700b41840718216a256085036806a107182e07000381841c186000100b10107030a00c00030a400190142d0f1540c810300004001c00d29441d1608910155690300208000d41400184a0060940310302c1c94454904404c548500c0da42c2e01011b400540c1c00071b080004610341c01100c2c011100a000c800091890321982d07000050004c01301240703640d0030b1041c032110f05540d40703100e038045040780e054407804038072030710b00b010011002904000e090110300d01c1000645404 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 499802787 1250 499801537 499801571
    0x909060b091504120b01090e1f1a0a030809090105010c03021b040b061c0e010903091422050108070b070206070303110c01111e0f040e06010c020a14040e030c190204 72
    0x4c1e9500409101045501d84010b420480d50300031500c0d035443e0007800c1009442c40f00c0c005850100f10814001040d0704140c41c2001c000072484442e01c5902c151007000000802c60480068034503508119034002041c0e076100010348407860f88030b40060050304000c0b20145420034a2180c4000f041d006040040e44000001c0440c00541c0408460102110880c06d04042c00b417140c003502d106251183d0007130200b0404d42c1e4010301810950b0082d40e5030307110100c04403070850700e50145000391003400071480221a0321850a140003042c080c090540c0e18010000b000c500340004808442c852580540054600a4251070850061140038107449023420100000042c460090080d4244030000400b007a0b80d0780c07503440d4050380350740b00548155100700040c400c06205021000648088600716010b0080b55541c0d9001207403000e15444009501a282442c045882004492807100300e110a98007080007107d80700c41d81c5da5074001c9907281c0080303034806d60095a0020301d00240d00800d5101610208002d42400e4000c84 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 499804037 1250 499802787 499802819
    0x4080f04090f090c06030e0a0222020a2a02010c150b040c02070503010b090c0a140d09080408060f01030b0106120b0d060e10060602031614060a020405010909060b091504 74
    0x2500d81d1070f80315070010310200c00400d4000781402e0500300800e07154012641d44402c2c60410103803003842d941c664108900c1344003584404010001104550300e0002d00405410b04c004035400c1c1ca160391426803000d4070710020001e40e240940c3c05845007022401c4c41e90310315a00625683c85c01000f03030f44130b0189418607211402217810248440d0003a281007070800090600b1513020764100c0348140600310501640d00e003900c0840301c1c4450307189440d5500c490264846141442002243e40c820362504003d4418456601c02400c280d071058001c0c0d80c00b07502c2c0c000c060307450b03601c083c0009023007651700c04010040d16004a90074000c0d205a00400b1980d010700000007100003641c0344c81600d0064542075902e007e58802c2c4007200042d044075404200b107500b403c800a40e00c0c092550340d02e60421040b6008070500c8480d0b42d18800c082e403400b0032500145400d410b9407000e5042271160501248007000d01083c1d8003554090502a51f00210500d41030462042c100010301c600448028489102008082180708415100317107 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 499805287 1250 499804037 499804061
    0x1903020c0a03060e0d0e0d0201080603150408070b0718050909070b04080a060501081c0309020105091009090e010b010e1903050307050124290c010c080108010b040b060304080f0409 79
    0x2808903072080091700306401000480100003202c10300c503503a5602c072014040c030580c0a00e00f500403640c94030086407030528900c1c2a000340030605020481080300d00313001400c1d842e101d00070f129200d0b10b4a14054070f006001c2d0003500000045207100344020b050002c41160b0105420086491a07561090300310f000e03501940040d0744036000080510140509401803e00400c244e500a101a030030038000c403840c021a100c0048101a111200303d0250780c819826a0011038005141c1899083d4203100508408414850901c0b000c0c1071800350b921501040c442e440740504103850f060321240c0c45d003007000041084001e20b0b44821685000100225008201610625200c0c07000041d0803d56400002d80b00301c000c00c190481801118002e1000310303082101511241118484000580d0741703520b200c081c600134001030031201d41c03810101207002c5520860340c50490300ca1034001c000c80c4030301000b480103075204658415003101040000c100000c0da00c0780184401441c800c1ca4074102038407502a041070352540c3c4602 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 499806537 1250 499805287 499805291
    0xb040312020c070f05010203070c150306030b0c0c06010f06050a03020c07032a140d0222050a06140603070503061c0f03080402040f06081f021201081e030a021903020c0a0306 76
    0x1404008a130348a000090705003400150f00303009599a8052035100c6074080d102c00c1c00700c4508690b41c218003940255011790380c42100c400c1c0d94a080c003005c2c51039070401c0c607000350584189000003aa502901136140140d643c03039641c0915207111900158043c3d80b2172402240b5074841c5400003c085044090303c9110002d030300d20341010108010442c1c3c4109041038024020300c0da901110405c59a681c5250042007a03030640d010f4100813038030200d080803203681c0b1440311011802d160400c0341940040c0d1008007503645103140c480d40359182e5030038411540400c4401c01d020620406c041206485d20348440481c808400c11030040500c095a107034400e0404520003140480c020700240002c6144c03501580c102c04ca4101c4041007154076081405940f0100302041202080420740c050344040d00903012502c08440d003220a800a5a4850030345640d0000e000c0d040c0400217a1495407a5200e401008803040000c482c0d004001240e900040490001000c0c0012429442148140b14294403103000c5540114061180 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 499807787 1250 499806537 499806539
    0x22802120f10050c18131a0102190209011e0b040e0720060601050a0908160801110c120d060e0901050601020709060f0308070c0317030a060f050d0b040312020c07 71
    0x501c91a150980c00c0750a90360341090200f1140d0000c800950b8001c5030400c2900301d4962038000429518030454107034400036414a00e84100319400b40c0360b50724856800381d007250300310740c032984080e000e44030f0707844000350320440f1356004000129030307908480041011000e0b1540700642da4983d0440981c0f0951081c071001d00e401c0200304061740c000c502004104000704605002c490302d40c0f103032501c400b4018042e0b0305100002c6601038100744611010405060624100e40440d01000c2400d02125620b01c1404203942c24011b91100302da2542d000d66000300d680c42c2c01880080e00c1b120145160b900080401202243d8606c1c0008030809801800d60203400c402c400000c45041220009080078065004861003d040c00000c01000a000d60403108a80e04000d18030307207400f1a450012100368041d40060a42c0c142ca504000c40c1c041c50f20000c40c01009000c03400c02c0f409903600c9100340d440c1500c6c491650300121903d201404102e020260650280c03291518029001c0043c248400700d811203020b13800642d000d590 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 499809037 1250 499807787 499807813
    0xf0c03070c052403070822031d06070203031b010f0c1e02070f09021b030406091403070e040f110405010807050108011a0304140309042d06030302280212 67
    0x1d0b40e400f4181c207084000610440d904084480d61001802c20303000c00c0701c004d001a110212408001c5001000444119120711103414010314251441104455202080200308aa450700701b048034040d943c09000ba5003040007141c03105203040d4031500007540a54880382086542c0402c6e21038100e02d01c2c550340b24881c0720180240b1241307008507103401e4602558071500052184940b490762040840e100d1290160707032000700c04481117021030041c841d48481c0c480440d02044064221a5000c19201034000070880c0004841c101a0b98034424426030b00da1301c80a0010130003181e5142c0c41c059903140a079401160800e6402c0c0850220b50b4240d111148640108505120b1b560f1b01c1901c090060003000d180e0441060082c06800e4076200280c40200b0091032640e0400d940380b1305000780c4500170b00040080140b0b01e00d42541c0354801041145101c2c035213543c4a220342c444000c40c46980c050300c0c0c01d640101600d2002d0041140c01c4046c10309540c0c01400510b00560050351b070300e492003044810503400783c412000c00310 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 499810287 1250 499809037 499809049
    0x605041706130b040f08041d06090403230c1e1b131d0d0f1202070b0c03041b0902030105100305090c12010b130e0c0a06230c0a1109070215010504020f0c03070c05 71
    0xb405251061203880180400700354070601244601d20880c00e44820dc1000502c418154401d00e503108440e030103822a41045070002c18681c0803802e074082d0a95810220a905200e44039421110f550380c002550761040e44641c41591240340034500340c01040001e0740e080f02a541c9020409500000000c070480071408229600400704020351402d0354040d41031030841d40d29624400c1c07000385042040301c1d0100029041c040d24a000b040c645440d5a000000d443d122030480020758403d019903400f41c1c00282a10b5059880f920421303200d81e2804c0c02070b0220200c10420480c0301904820408419921054250007a81c0d8051460aa80b642d80600043c01c010201009090589440e9118454008082d0801c0a1500001e081d00c89a9004900d0000b41204040c0d515080c06010a10340c0da601c101e203501030802c1a500032218180303000b110842461b070b0f01d03d8012691000c51210001801001c2c81c01005642419009485864030782d00c004c0e4101a1403248052941d000500140e1f1021038616081006003015 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 499811537 1250 499810287 499810291
    0x80316030e061c09020105120103050f06160f0806210c0f12030403320a0b010e06030c1203190c0b010501030b0603180c0a0605041706130b040f08041d 66
    0x2640c815040283e0034101d80501911540e405040030b03103e141d020110ba04c42c030202ca09a011200040146585070b00b0060f039141c1c0c1036601032509214010115a611129400c0144010300c41c5c1d03120402050200340c1100c01e010003401740d980100d946061200d0000d03014000d40c03400758001008050070039400c020006a1400100e1140c05080303014aa040210070210407101601d41181707080c008412401000c003802507903900e40c600207288281806000f20000320300f510b04036019450100f41303a600c90504040b204402c1d0f0700982d0560040d6840c00c828144020f0002e81c0c5014901500d00708550b012886550b02160800400003e03c0c2001c81403c0101c10401d6501624007846c082160311200c0010520f1840702a00c03d0403215146040e07c4115041004200303000103010700301300380d0150707120009440c41d0450301601d9233500c00000c0508900c000028040d110b00c1e0780240d0040c20b07410341d40784d002800038080c10680716418803c003880c000c900390500a10051281e82c045964a055801521301c01101c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 499812787 1250 499811537 499811539
    0x31b3509030303011517040309030b09010615180f0806060102070815010b0903100c181a070f0503160f030f1701030b06010320040512161e080316030e 66
    0x1400040c0c000e4400009580c1594024071000000011121003541e04c0030010f40a803071039400c18010001015409282c82e01103900c00d800380b0f40a922200c00b0142a92042c0c0190b102c003482d40c101e4254101e1080740b90300c0100b910914051003042e11201e131809940102e400003251540020148030742540d04000520081052501070040300d01e02d100818407284041c41010f540f1600410710b802299014000c0601d492440001002010304c1d500c1c000e814403810200b0002d44043c5c035400002c0c0684c00941022000c1c0d95592690318201d2203030340d1138401001742c00c01078400d84814098513548403001d28100c40958001c03082580701e004540f800408428448240b042042580d03100c000928010300e0390a41500c0e071002c1d41e18a2035464200490003084408090a008013144446c114000c540500a1040d6081a204048422001004585d5500410410072686000007004118540310040340b007156808480b9003805080c0e85803812807a503007062801160044440a00c0010983c10400301449944 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 499814037 1250 499812787 499812893
    0x60111070f08060c040e06100e0907181401020c0603041a0103030905031204050603270321010b0a140a02010603020d39092301081606080f04031b 64
    0x4140308150106d8071000c1d18603409800c1210f40c101400b030096000100351034000c0c14004081c42c103204000d1085003419902c00b0b4103002e0040100f04a02d00c2d5001c0e40b104401030b00100310004449041c00102c2d40000e006031007684001003000504071f41007120754001d5000b5614903c50a0520042508200c9404003d00c07050300e00300b104026a8640005499106c480020440700280004400ea02009010808007285000c002808820181d0004010015002509609840307070380b9030440071007510402140c1000300b2013113417142110080703050080001d26001e02c00800c1441ea80e40c0415968000240100c7d2109003030480c10311138821002c5034140301081c0301d03003880d901240354a0700000c40700e442c004e41c001240c41d0250305a0613000145c55525841d00f403101d200a0b0340c4d40d80748043c2c031424030348000b2800180f030082c0010001e100707881e16405000b80070000109a1910364050300c10542c01000b0700505da5a01551034040f55050402c0c0c040943c0e808003400010b240b80c2d034001e00c411400300034540340178 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 499815287 1250 499814037 499814039
    0x601050a050105030907090606030f060b040f030206070f15020a0e1905060c07240801080705060d2c03090316030f060e1029010806100503060111070f08060c04 70
    0x158035004150201c0380300f82009540da85a06000509040203900038600580c01e103140003682035032542c00319002e20250802000616200c0d03481950380d20031803040e040b68001805007400136251140c01051240e200e00740e207505c04d41e1075603039081c1c0b9a10110003d50b5203503804101d0041c096001070440364100c104942d1201c64490700e41450046003054003403a4041c8502080c03106082c00204084030141c000381108148400c20212000c0030301c1c90f00780b0798400290141000041140000400000703807580288460f040541c0c408103a0001c0c0a005614a03040c003154041040c01c20002d25010b00c3c250301d6070003450f511103000040c14a00110015081586880c0c0e035003c1000c610101c8a10110716440a4041780810150764200e00e00215050b0441b0542c4c0703007455525121400700007000d8504000000280454100030042d00c6254080340c0c4e0941150701140c0203586240b00b600259400301d01418855035084924100c0f600d000c00581011042c90401481440045800c2183c242c0c0300e26100200b0b0324003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 499816537 1250 499815287 499815289
    0x215090d030f2a030603050a05030403020102150906060f01030204030b0a1506090e0429091b010c0f030c0501060b0f03040b01080c0a0e1b030a0b100f0903110d05012309060105 77
    0x9035503009004008405100341d5000503104e42c03c130f8001541c10038100ca0b80c04442c2c0c06d1007516a80f09200890141c440c111003002d446010000c1c140c41425a08054040c4d507481d1030a02c500c80e0000e00301e082c1055401c00c00440007500c0c110400d4003590160300000341014542112071400e00e03042e0448000d110300f44d001008011481c0715041e40c41584070341c6006900012009a140050301c1086541c00d0f0311000d81003200c01d040000d444540b80c0c44142540d00050068001514981c10300c120140003200d004044801080c0207080a090052281d00001261380d5104507190711600030702c07000c1401c0300b0000705010034880780e05265030140140b41e02800700000c03071381c0016808940c0d42c401c0c92042120315000400c045481c0700420011400940c40325580c2c60440040300007052040c1402d0721800e80d03401c40c20100d0f4803451129040b040181c850741012411600d0b00d8012052110b10994001d011403c0b00b0001030080c02400503403048902104034012106c0420340313200400401840050784204010441 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 499817787 1250 499816537 499816571
    0xf0c030712030b1e061308030a1704030c121206090f050912040509070c050607050712080606030a1107020402130812180607050102071b060912080a030c0215090d030f 73
    0x28003404c00c0404003203403d106000c03661900919445070608140389400056005000c0028843c649541e035410380705d1105400c1100040400f501c0140009039150440c5001586c2030110b250342c0c0f1410f040021030581912407002c06d8a5098100b21035442d103828441c101c3c003501780951904101e40c000602940a0703000c00c1940140620f10031103108584201c0071038000d40c0600d9654030100d03002026a0840d2618240142c071a500080d0b00711100b00c0c104200786400c81c410740750f4500845008000b58550b0312002c0003000903010002d61020200c50400c0460016610340c0b0061140b0164a40d014807800d246c61103843c149520a41e402c401010200900c489035124402d41c1c40030100101da0854039000c050805070b009004010780200f800070640301c3c03101d20008014208003181d80d15626a0380c9561141e519030002030040c03074000c02500043c451141702e240260001d84481c4c1d16441221000707407886d105010701c980709483c1c4100503040100581da5032035260158100c2e90103840303c00d02400c5490010208 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 499819037 1250 499817787 499817809
    0x20f030315010f1403040605060f0603282a080c030403020c0907261b090a1403030f180906040b062a0307060e0c10020618030f0c030712030b 62
    0x1040015550310340d8640d0340501340c0c0c03000702c5505201154072860170b89040c0380140001c2d078072107100b002d01110030021480c2607800c50344a0f0448512180009400c0251480c480400180d01840c4039122000d5005503000c0402801d03a0000301d401030114844403500150010402600481c801c69042041001294000030038140c00d00741a80d40b0380040e03403108401c403401e54480401c04ca141e0a02d01e15224901c46114540380911045610050030152150b400780f0390b44a2158025007116036110208840200c498100c088000701806883c644480043c1440c090342c000188820690500c07403d034000c03410310b440c80e280d100c0b1040c1d8081040c500318000050f10740c020b1070803450729218448001040e012003108040860b520701406c40303407503021501d0f02002402480c1c07200c8101c0e2240341990030440c40e00c2c0d04a061241a1038010300500c0e281c1c0c401d082d51030b07418140307280a00c4c4002c212207001c0c000100001d00040850001454540010f454201c0c691940b4140c110101814864540b12540c0c80d082805 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 499820143 1106 499819037 499819039
    0x16050a050f280207051c0f020405160f05040b070803060f030f0c090a06300b01091a0d050705060c0703021c171303110609040912020f030315 62
    0x82e954440f07481443d51003640180c04046a41c1d8000c0c1c6c40c0c0c0420300520881c0c03040112170700468203944096412904541e116806015202e51119010030141950325050345081e2501c480400c140c000c1040241c03101d0030001c0403881c0c1d81c0d1500c441070030700c0130702800360ba01880072501015214054be210007800780d400c001c006001c1500f148a0350064a00f440d015130600442c001c40007090b0048101200d403004500d070701c00300101d243341c201d8900803d420b110200f10328151078014002103c00030001c0c0d002d0f40d049040000050300128a2200703503501559125145c00b00c58101c1860030281d039001940220266070342070340040751f0305900a5000e00880c000203162000060441c2940f191005038045400c00a0041c8002240c0000d011148540104094188000f10001808840d4812400c54400c3c0030500c440c02d20740e40602c40c800344080550091821842c00304008000103044103045 = true := by decide +kernel

theorem cover : BRFrame.Cov 499640287 499820143 := by
  have h0 := BRFrame.cov_init 499640287
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499640287 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 499640287 ≤ n) (h2 : n < 499820143) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
