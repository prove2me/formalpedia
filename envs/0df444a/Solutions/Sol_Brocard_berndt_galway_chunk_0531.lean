-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0531
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:17:22.061426+00:00
-- url     : https://prove2.me/submissions/fa82bdbc-8acd-4a27-b65f-da32c7e3d8e5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 95323741 ≤ n < 95503597 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 95324991 1250 95323741 95323747
    0x501050d1d0d0e030706020601060f03060e1005030d0c0203060105130f0e030a1205060a090507051b0c0f01030b090604050402120a0b011a03040f030e060c03040e0108240606 76
    0x1041540240014009401d403140c0e1554820035141c00110308042501d8240d500d488002c0085000c050b660f000e903200c0c540141e040f550060005074481d132a40c01c103121450502190304d5546c0c02c2039200014049400c0c41c0079003131300306061082d0b140511144c0103220703861601448400072900000e4860306c0c1841101d104140800d40700300800c109d42c03c082910000d07020304120040003640b141d83c4950001010030005100d118146201c0e07544d9101e12401084050684645107040801800003450060018014017070700b80107000c01200085800f48071030b10460302074400d55825805010582d240c5440d00303418541444201c0c11203840c0c9422255020504a40100e0b00d0b4480d400480e43d1584a8030284d0100d000b4015031009110743d44038064100c039030711090130303140c000f403070f041c10f005400195002081d60b8199880080424812805282a00130081c02140303024240301c00a85558096030080f0b526524078001001841030911618080000424240040b01c584102001c14114000c0806104103404 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 95326241 1250 95324991 95325007
    0x206010b0309070b030a0906060e0115050304081207020d12290409080d090506070801060203030f0a060f180609090203031e090a17120f16020f062107050a09050105 72
    0x41040e0f0001344035094146a0386e00b01811044040c01d500782052312032031300b01030740000e403c01c01c04080b03030481d211190080e017403685002d0112032503480900161018041440100701e8201001d044500a114540040060340301c01f100103481c3c001c07a1106000c102d8588101c40b002d02c4009c8031215100400500090107082c8010000307402064821009419a100843c440010031802c0c3e0002c66514003400c1152500ea4400c1c001f100d51034024000c030f00040e0000c5c00419407003103990420542285101c3c0700850241d40b41d91903038102084540c80501c600503030010350781c40c200350752103540003928a6030401d2205001e95000300799a032064242000a04421310b0024142c00c90f100117840344601c00902c5942c4040e52030340d0424108000703805070301e01802021800d80e18200c010040b10011103c00c0443c07400d1104d281605600d1407100710050b1382004a140d220039060713a401000f0180c603040c0307843c0102c1035004800a500c121000500410500c50100417051a0035048401c4908956092078010390f20840 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 95327491 1250 95326241 95326243
    0x17090a0f020a08010203131707020a030803060d1e020901050411040e04050f0a0609020906040c09050d02030715020a120c05060a0e10090606060f0c0803010e09030c0304030606050901090c0206010b0309 88
    0x2099103e004903510210900100c01e5a41c9002142c840c01243c03c01c2a00c403d40161245510489400a6010000071f40400004480b10051644003d0080041484c00c10075215552800140b000880e00c1c15241d540c01ca0071441d001a0f0580584401d0b05c003080303080304000d2070030007921031401182582c0542c6400a0b0030440104007080380300094900b6030700b103a01a454985e000d00b001390000c920842c4107800003015400c0610030301c4200241681e4243c1180e1428007480000400d0300003d0b605401004404210244c04100403400340d0040d500920503a540d5041c0303805940b001002e00300410002c590000003103040000c682d078000703a40030300014a60001140b034910b001c401c4101c003030a6906240360402801010340c0031000312a0315031a004100d40c000d00f4101c51200381000018680704061005211050760444015400000e540c00c6902d03001081c465645190000c5d40200c0d0040d031210007e00003801c0c41003443d1f0050000081c06e0242d012140006522000305005241e02c54802000194110130 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 95328741 1250 95327491 95327509
    0x40303050621060703110306100302091302030c04031403070f060c030e0f01050f0601020304050a0905060d0b0a0605180f0411060f0c070906150507080901030f11090117090a0f02 78
    0x201e090305200450041d8088548035070f000ca038a100401d1400c40280002140d08007268420200100703000380030100400b0070740082d0008400d103070700300c410945500320b041c2c5c8a200550113004e0148aa540701c62441c9000c200d00100398407000e00542051000c0c1c1d000a82c100d241805495000340003244094040300d04170300401c1a8800c00300315120350900c0b0801c3e00410350250340100440702041c011030342c0b43c400680c2c0d03d204902c00e031604a031091404009845041d4011a00700100404010212070540c840c0541d02c0c1c020f840406220707644001c10062441c00f010084060141c0000500306451b10b1905408030200040000c3c280c0b141c01c00b0310792856030700e08040710300100c0c09c0310707000e070b110000111442e950300854083c141009250081c00300f41007000c40c951003e0318010b503032081c0c5883c2c0b043d610b032417060b00a400010306041d20b0740c3c1d00d6001050346e400f901400e056020b62480c0c40365102c4000500c0f880c466146401017481ea0410b000800401007000c034001a0481140e00f80300c203407031000c50380b080 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 95329991 1250 95328741 95328769
    0x100806040923060109052205071e0e1e0411031f06080f030c070b0c011503030f02060703090b13030c0813030309060f170901090203010606050913060e0403030506 71
    0x1140082e01d05030388400d00c42c000c1512404075085900316a21442d8490490750b0958811142802c0e20201a20b205440020f0549840c40742c0103503020166185800040c066842c1102c416064802005026007202004150703804000010480340d04903040503241e003035035006040544403400306c0c0c0018406480402450504820032031404415444441441c4010000d0b80a414101e015410480030070010001c142e44601e01140050710b2420306c0c240d1850100d034003406140c01c3e595213070740c0c4a01d400031100d82e0f02d900a5003c0d0700c48000921030004000d080510003000402030500d441d951802255044010340c1d442103c0350220640d8141c5410261000d44105034014100000015041103418080c5a1001202e100e92258505240c40342002e59065100301d407114001604001c0180700c40c0d80d6803403c1078100215400003c0c00c01c070150046401d503802a00446c0204000054500107803e0400f113081d400a8080420001c0c80c3c100800d580c14090050400340030145c40c0c42c080344450b5121704082d9a20 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 95331241 1250 95329991 95330003
    0xf06040b0d0506010f0510020a05190317010801151e090506060d0504050c090f0705090913020409050114060d080d0b060c0a0c050f040c0c1b0b0c010603110109051008060409 76
    0x3941e580c5080840c440c075a4040c8900644010b11b04291050001504100c1c0c5c0794000c0240020807a1024a034bc1c0c00300f4416026410041d60804210390b00e0006902c0c83e0191202e0000440c0c0d0400b1030480e006c041c00180d0018400518603421107201d070308003058200a9981454011a90707446010004049029180140e401c403407408040c4010820005240080354000342c4801846955150000c84d00c81401c84075000800c0341000700c80e034a841c002061035802105900d45000404503038022404881d58044d00701c5090b03564a00c814182100758490f142d00044c22107800501d402d55a60320061070040c2c8032420012038032251981220b44c2c07008103072a035403c0000b080310101899818403540f00c0405105160140348011008405070400e8001e0601020301600c036032801e45215a81d0861402107032050704050380340c2090108210314110020880000d5038800421800d00b03500301015040284000c450600070140c80401c400c4e1621410b074504814542012a42c0341e807280081070181913281c07002004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 95332491 1250 95331241 95331253
    0x60915090c2e05071109070c2607080904050606033112080f060603130308060f03030a020c0f0d1211010b0303070f14011e3204020907080f06040b0d05 66
    0x40c03d500c00054180940640308003256111074a041c00104403090b0740c0c14000030080a0700002040721211110019044e010f2008025010703404910034503005003804481d030000000301c030702e26441e141c040d040e0000c4040315610314604110070110480a511050105000e40000c40c442c0c0b031284595140888680149110701c400104880c000e003808002c48486a0b0340b00c3c99800b0800300c3c2460001e40348100091410020601d03c1e6880c1507d051900501c0c81ea40a04a4014a5404d0301c061010b440c0c00005a0000c007030388101c20381007152841403c0a030901a210703910852000c07a4109226510f442141c0c00d0103c10403a400301c2550150140400d015094800003c007001000300d840f03003402d515030060300101181b0980c48100d500b640c040f8000314070301c44007a8242c01c4090720b05510070b00c40003a640700a600034200502261041e443c7c40c40e0082860b900d0034080205606003118a56440100d034a01800d03a881c2200ca503540b10300340503154600545e43c0da8002680354a03840b00001045803c04101c5030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 95333741 1250 95332491 95332579
    0x4030201020415050403031713060608060907080c0f0f18070806040c030b03060c1803010603050709050c0403120503060406180506100e06040b030a11030405060915090c 74
    0x4040c2d03105101e03200c18940c101c200c40c0011845030054806581e45580c07651044034020041e0421a00d005d40300c9140e9860002c40c2c0c0c80040d0759841090000e003001c05c05082e040c030b4000301050411031245e00c04481900304060099031599803012419043c0c40840f1102160101500401c0185a12840d40c0d041c0030076400510262540120005108005c01c880c03d0060130f0109000701d0699030085010340c0c042d0304c0100410a0911000d000e412445554a00624202c6403031000a0a40303103103078425115904080401d200030841802425845102c1d44c0c40c66240c0b83c5580c0d115030a00e10030344460010031001101160a5aa030303508200000d01656820b5205004442c1030320300100070a46181c1e00c82c80c00002c046032028007900b400e000900f0010590707403c16180c011000c10a900081001004d40e80c2c90a1048002212001440c001c6004800500341e0340340100c0d62510f0304080750b003803c6a000459042009441c000184000d01d1001940d030700c3c40741202d5802014500070300d00551424212803100800c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 95334991 1250 95333741 95333743
    0xc0f0105040605011203300f090525090203061f0e090609010612050c120f010914040b07051315111002031b070c050301050709050301150b0a121103040302 68
    0x30700a07401100100056643c03411942c01c1c0c00b25941004021601d05080c18400f024905a043d4403088078460051240c21902c13004012900c1f4007550300d41c00780e039585031441130010401013181c560104ac0f040c9402c04c50b99070301c55420f940041c81058100e070740010000d062500c072035102602c600840e130b4008030038800200c0050011502004914000c40c1c4010010b44540790064000d41200d10544502105a0700051510301402004207900a43c00042001960341c00c86280000c1c41030030b42c3e248090003035040c20020400c0e250100d201c18184044030003440040340310f6152850b040902401c10683d01c22400f51380c10040440c0b03910084400032103001d030901c0309402501c0440360001c580156280c000d191029117080f804280c4410724403402400f618911061140000c290641c05541c00c5071525680703000090075980301300c443c41c0000315180d01c104011306090243c107080788207045074440002e05003032180c0c1140c010f0318a12810000c1d00c0c95584054003d5a001100303c20810240381c0d500e1074230741006 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 95336241 1250 95334991 95335001
    0x21e0607060605012c0d05070308030414070801090b0c090f09040503030a0f15120c0803040605361e030111070309080601080d120608011b090605120c030c0c0f01 71
    0x5601081d48115442290a0002c22158130004040e42c0300d800e588000d42400b611b0b14500d1ba08440e203119501c400f0000c10b82c0800a5803241e07201f01c0015a11640030310b000e1b4201003143d80005020f03810441090001205400420340c0310080c907420300d40f80c000310400034041d004030081458004580d0010310041c0200070008510815001005007caa0700c40303003442007111011542c1d00d240841003681070005811407c0c5d02002c2c103020700c542d0300c0890f0700c0d07940303c50940d4840d90000011031000039034060011800e2103881d140980401182191049140a248007952003e016a00c18a6165444484510300318844c4029450140003045165500101ca41c40307640030754400d41c08183d4999000600d85000940710741a56041ca01911610322551002e860741d4600082001c142c60f02c5050202e40726200344550407181101400e00d1400c1c00144d2400340500844c3d420400411608210a10855400983da1900260b000f03040d2a640d540f8240a1303011409800c40342d9459005403864180f0141c015088 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 95337491 1250 95336241 95336249
    0x170d1406090601050f090f0402070c08070503120c0c1201020d142202180a020702040c08061e0303071e08070b010f0e01060e060a0c051f0f020313021e06070606 70
    0x1482060703202c0500641d000e00034900c405001d00401c00005400303003400180e08000c1880540054245025990381c0c0008a400350000d902c1e40c0c0c000602000140703010498001c1503404120114540310123190420b03114140c0c042c080f40242440c442d68010800254102c036110041148108280c0d0540c00328000c0c440c0302918441d10741c490b0b11020032090080b444190400560040c00160361812408642c2030201c070040150407000c0e0f0900071a03026841d1805440c8100c02c2503900c01560f4a001d02c10003114102c1e07802c2c0301034005039000c0e908030f40d070b1000401c40712000d82100c0d030007544421016080c1001c4001c041c0007045184089118800c0001c04115141640c0c1c4200c1c82003042034070740d940b2030000c0c5005d10610002030500c516400141c2410002491801140c2c40c003210b081c90300b51107403850008681003080d0a0a03041d10203822201d0355204410740700b186039000b90b00c0c60078103c0310120365080d901c0b0044e00c20190140d0b00f07890902c2e040e82c0c2650051004c0c2c9196180d21680c10034400400481c45 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 95338741 1250 95337491 95337499
    0x60f0e070b040b0a080408040f0f05210601050f060712050301030c0e0603071a0c0609030309012901030c11010608010b090f061305130f0501050402010f020601060c170d1406 76
    0xa004241c0030060300c180c070240c3d206071519034141494031a08840044010380141c2e003c0740d0030040450481e00803c84840a40614442600107900d07000c20f1080c40c24008403400000302400c020a4007500021505078115042182e41c1040d0003040c100040d40c40c810043c1c01420300280c1d040c0d82684a0704000079504803801011801c01469a42117545d4007110308580899050700909400e00c6964084a4a81c9217040c440081a050a40c0b00c01241d1824505840702c00c007a031300210070060800b1003401403145103142d0b50043c032040425400030546501c100b0401506054640106030003035403251184011120202c0020b024056640401ca4000c060140384e4500075051400011071042c408021a40948006407001c3c4d0b81c003d00708044401031002900941d032640c0d19014050114a000c84110041c1c0d0207640001141e00b00352001500000e80c026111055401c400010000d00e0b40040d00c108070943c010201600b400c8820700c44003200c2c030806001c1c1031568a8098507010540304403850078803444041d2 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 95339991 1250 95338741 95338753
    0xf020714060115080a090305070203030705010501050f0d02090a020f0c15060a0914060d020f0a030c05090a0e031606090c0902070b06010509030304090e070e0910050604020906090d0c03060f0e 84
    0x510807220b50f6480070450001c5500003002c52400c900c60ba2000342468002e2903d0b900700301f0154002811640212020b130fa06079140d40051205180095a05840e120b044403040c449000303e5000c20081c0b00010610100503a0104a0b6010b10100c5400c803450500c030070044c2c072007010084401103110001510102d01420401401145401c018400c80c0326820080c404041a0380d641000c002c100602e8440c101e82180500071080000d458404600001d0f61040b2508200325040c00709125004030000d0031110800d0034105c1008003402c0120132503100091100350803000040a0414502500790712200600c503000008d000918105151301a00490303100310310f6030321240c40e040f00440382030194207540c0c0d900d9001004200074529496102c000314020000c282c1380045d07603421390f549042c0001c980b0703008190045014118600050b01c07400b41d0025085404500b0070b520030001c201c1c98020159110f018034406d00309441031200c524100e20003558064028015040a44a400081e201c02c41041d00180700301c0c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 95341241 1250 95339991 95339999
    0x3080c0a060507020d09051011010c050c010b19061103040e0109020d0b040615050a02190309080607090f03020f133b030f0f1c053103120f0207140601 66
    0x21501541d05d50155807201c4440742018208001c440340e0b0f510743c006102e1240351000201d00c0a01411803510101d031101074550101d902c085003034070703030318280f29200e402000d05818804140c01220410741c0c000d80707402e000c29890400c08034554803480d080140100303008800001c000340c10f50020240540004000d0200241039824001a5034880c0107103054032230388013800e0b404980710700040d00030201d96204a444281a9001d0031003401301d03010701030f00000c0105a080c0a1003030100010758000c0103c0c60605000c520300035032100700390b0490100a02c0b50036020b00e004641d9440300d21080004400c01420026444009a40c5c4c0e01455020f02402e1800011251804941551003c042002103480099460304d9556558400694803140e562660f8031814004048640e8401a4103070700002a010005954140604040c241c0c202007420004c8020300d900c81c01400040d1490510f916580c5810000c1d085003840c06010050420b0804500e00184081800400e0102500c41ca4030090500002d40740c450b600e13 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 95342491 1250 95341241 95341243
    0x70e0c07030e0409050d03050901140408070303050714160602040b0a080f07020c060304060903180b040305011a030a02090703020904020d020d0e03191d0a08030c0115050a180603080c0a06050702 85
    0x130b010800380580d00705d01010100700b8001e800083d400032654000061540e0b40d000094040201958180e84e6840017081940c105501486925000502c40c106208030101000d1016164410505101e03004100828510200300b480e4040e14040c00c1110025610f916500400520601c802c40e070500c0c81600800100f0105030000c501c0c41800c071400703485240f82d540d543d152039026002d01d4908808224110440081032903d101d0b608019214107541d079580d036851070511500751505800c0c9035134080720303802c103540c0e40360f0300003d03c0e0514940c1a900208143e551420940003030145d0070102e5085400003c008046c2c034003990041018005400701041040c6002044940c1c030300403648400114180c1154400c02c00740034000c14502d040b8030441c481084100d01300821807004240d4040300c2203034000b04a90401e00020301411181010001e000c6848500c0c0c0800203103581194800c925941041840800f040205a00208041c40d0001d980fa542d98043c0500213650b41a1501c0507107445240001080d01144 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 95343741 1250 95342491 95342501
    0x501050307060e031006060503091b0612070e03060910060e0601140705010e01180605070c0201142d030718050d02010509030102130602160f03080406080603070e0c07030e04 76
    0x40060018050325007088010785040c044542c503035500d4800d43e0320628811754036003d20005840c0d01d40d00c250300c81c01c028003801d250171998405407a50440d50b00108110303480790f07025140c0c642c042c189180c00c0d54540090a987c08074001c440c09405011304400c0003910000010349028055400c0410442160348036148403440d882070b2466400a8100913400440c4003850000d40715060040000098120040d034680c1e00f16640c000200e00b0340d001034000702d0288061485562f50000352070a040094003520303030000b4003500d410309038410b52400103d008440d0050b0111040c8100c60040c00811840e502448042c01c0c0d600704540003000112554942d02c0c0c485c60000d8620110b40020341401c3e0840c44941c015100d6800100303041d50950b40c02d001b400c40320321004000d8402002c080d005440012619240d040800100307030810f4105c80c4d0f001e43e0400c000f59605088804442142c030380380b0546d40721900024200541079101c01d4654422006221000750614000c006062094417030010b040341003814001030394 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 95344991 1250 95343741 95343749
    0x4512120103020402090a080102070308010504060e07020a0209070c231c090b160812010603050a020c0c2107080325030c020907050c011404060c03060f0314160e0601120501 75
    0x46921004000504041d00540600340c0002c113588041c5485034415400c80e00180b805a000825a800400c003600303062040c14040c282d4645180c001d807401e0100699661032040b4000d00452410f00000c814900c900400d43e42c480e44500c1a03940e000d84d03244c0d507400031400440c0301c1d040d600400c07403c1d05040d11240c00044110440fa1110046149001d03130226a07600a05070040d031095600f44507000042c0c0c04070061041c00b0a5845101c070702d50401c90000c04444004144041d403e2042281207070300000000c8010540d03104880c1d40380042c6003002e0041e40c140f28070785104d56a02c9094000300d030210011010348140b2490005400703c03c2d041c8c9000e8040840c05101c003070041070341c02ea15107000d0b00b4889001540182c0c1403e01ca4a81071107484410708499480d07801d60b08075403403402400300f080110b0041443c0b0b40c0552030140261420201045000005840001e19200900b0001d05480b0b0342840740440c564103469400608aa440162001611085692070700040030f04003494100f04647c801d4605079 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 95346241 1250 95344991 95345017
    0x3010504020a1205010209060a0314010503010203010b07060e010212090304031a0606030c0309070b040807050411130b0304030e0d030c050c03010510090e10050406092001084512 78
    0x40c9403052410f155080188140d8855400300100b04013516014010322004c480742e07a00041a40d446032090141d0f08042e0007030b40c42a40104010030003e110070703094030007003600018001a02400010100c1c0240b141034103a03141034034524100300955038040702a1003120301940084c00740104040c0d080309c06441c1240ca03a40e00c0b4000303202003100e01e40114050343d8491075400441e100e80f0f40340ea10a80190300150301c15002070740507100a00041c10a03001c0c1d0600e00c0c0c0340c1c03135441d8204500c403c907012440601d03001e4a6440c54000c80003c0c14075100d030700700100300701001d40013503103080480c10010101140040160341c94801c98801c0c5402c0c0c1014464540b080100c88854940039003070500d00c0b80a081b280440c910244039a15950110710320611509000c0ea2240000150b10b080078078040d10300038822052a260241c10090045050b6005500301c1c1d40200e0b120001500ba40764a04150b42d0045101003802c0003044440c0354001c4205071441861240c0c3d1400308440040d508100d080c020340c0310b031002079005 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 95347491 1250 95346241 95346259
    0x606050a060c0f0b0a0b1503070f051603111905030d0506030313260601090b040b150301051309080a02070819050a0b13170703090b0304050316060f020a0203180301050402 75
    0x80f89040c10300ea9001072210b400492175406d104000307002441003500310300c900800042403100842d00f000114280c1900390804c5424040f0030503a20901d51003600024042c8408400e248401a00620010200c448800d8100b4400f0f030203414050303601e4001c1c01e5602442d92030100804e000d443c000003075528181c1c11140340e11015040503402c0c1100100c02ca100c0d90046d41c1e42c20417502310107041c4a594043c01d411907002581ca003280c020002958034034011240a1803020380c810080b4400582181d055800a5071510300400102400070010050010301070084c16020400c506074a40c04241c25040702c801d40102d440380490b00d11160710101100800900c5075000d58000c0780001d910307401d21980b1058072000c80021184507100c004180d007107003038460680340c4000b90301000c05400014110142444a40c10340c21031074503641d180e070b0340c2c03094405480000600b8061602080b80a07008a020351003401825515500c4080c400b943d0ba41000054400924040c114601542814030a05100303d40061007100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 95348741 1250 95347491 95347493
    0x306090c06091212020c130b09060d020117060310091101020606060f0d05130c15020f06040c09020915040f0509130302060c0309030c0a0b0402010215060f040b0105090d0606050a060c0f 81
    0x1900007404d0401020b41c001c1803080c3e41c46a464500000000d411041c0200e00c003404d0204000343c0390300040804e8880c40481e42c4920241c2d0303014450382440321020795044e0064803000d0001e89008251030480c032140303007000c400c2402c110701c03000505c6e4003d0080e000c83d6056190742c010442c240c0074042d00f00d00040707000c0c0100031200c50150861031300403081c200c800708032042d2a21603810b41001a0028820040030010102600360304200708000400803602816140c1003a42d158200c1d1401d5105503902e6540204002035281c0c0d401c008546040c0d80300c801103589659486001044144074450b55124012010001c1d803860b002e1050140b007954540e01811446d40c60f803420399001e8002601750300141c4424824045006020004c1695050140b00078040510b068400240740464501c1100c61002d180000d01c02103450311440083c1404080b02c010861148400c01200c680c021b141490341e1106404141d042440856800282a07070419144141c0c0d150f200c92050710032850f500c00091a0010300000c000c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 95349991 1250 95348741 95348753
    0xc020a0510020702040908030c120106020c060306091905040c05010f050705070501140408030a020a0b07020102090a0303050d15090c020d0c0b1302040603210801051002031209010b0306010306090c060912 89
    0x4040c4002c1c000581c10101f41c6580c2c0207a042128032260b1207400248400d601009040c04900610700ca02c01404803488038000b180c414000585864002e8a0850100c0c280c100084024031423202e070702000300304ca0b24281c18000081043c40c800c0b90b001c140104072900714284500125101075402a0003001e885250900450b082d5525030458a080c41003031001240c070300802c0c00240500780c41d0341d000308460300701410082d041c07130005071001e419a03104018a28443c0c40c0c3c1084402143c0c0c05041294540c42c500c1000c1c4090210007400b0054890303025808980142c4070f9006d0028038645500b1103071030140700d50065585440c140c0c3d018010001d6080007030707540d10620113044080c52020300003048260340c0b80e440d003440e000210410009544501003410741c080d444410540100012901d990b0703110024400a03480e03201d40d9403000d103e00a030b24001805003009402c443c1c4031480160031555190b9580c00c0a00c000c003580030080f40d2140003e0720000364188075128040550f40944151801950700355112 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 95351241 1250 95349991 95349997
    0x8030307021c0c020a15051308060402030105060618010c052d070b0301030c0b0306010c060203010e190203011a030606071b091109090106030f150f140913080304050a020a0909060c020a051002 84
    0xc003c007c400c1010300707421281000c614008020300001440c0905103441007509445004000300d018010603c080208900008050703220900203003401203080c0444e0601c1402c00355401902c00701440d6400300c183d0820086400e900c440c0c52244242c82c40315031146000d1901d88800c2c800a0a41c4d18030400c01d02c180720503e001150004014184074800e821a0f0750348900742c4c0c0099001880014446c401c01511008090003401c180e24103007030451031903060036030018031510800103070f004255020000559540f1500c00f02c41640c0e40105003030702c4403003044128503a40c1684ac010b500c1110300300705502229086c4407041d6041444c00410907800c03a800e0076421401072400d0f109484142d1784656214044a18060403800074000001240c05000d050070411042001310ba440c15002e05804000c0051510b03802c0b44080d03100d640030500650701d45450030800d24107802440040c1d88810503201c002203400c00b6602203101544585c1060102074907100041e6100c411742107003d8180d03002415941034403403042c0c1c01 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 95352491 1250 95351241 95351279
    0x1309052a040801110301140a0503070b0d02070606030c1d100b03090a200f1f0818010507030b0f0405060a06050f0f07080705010b0d080706021308030307021c0c020a 72
    0x14581c14196100c1c1e500d820f495680a80b00701c0c03403000000511407450600d0007104240c0742510149112468000442d42d40c4c0921720034110b14250100384464403485ca5011590b50030b4100b0f401384100c580764104902c000f0300d10b101e039428400112041c0c02c070711790146294900c507100319034015420f9450041c004485920003050300d4602d00905049200244031440d101442e00910342080d01010f0a6105211441c1140401c00740300b17051907608980e00c80c0303a501d44c1a24100540c0341620194451030740700c1500c0380c036400e4041850b500b054100100903174140c1c050551920221801e2610910490511046072001d44245800012041c000e2019501540041040706182402c4616102408145104907041036004842c003c40000b1a2010702c8400d004049890354110341007054100745035100c003d02d1252400041030b8070303000705178000c1d95405048010b0007852070740287d030f1f924500325074004d44401d00482c90031110b40d10220200b940750b01c1900c1e40198141c0c0584508101800c0401005070400300041c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 95353741 1250 95352491 95352571
    0x51816050a030b0d0c0501081b190c050f0109060605060405010c02040b03100c1e0908070909050a021c1a0606070602071707050a0302070e0601172a130905 68
    0xd1020300ba510f80c854103984c2940612203660038113080600041910030060868480d0301141c000203250882648126911840d2507903160000328280310099803180c440c3c0340083c003140110310352403103071500642003000e0151065504011440d120410041d5502560103554002031840000c4001410113500c40a01c50400a0442d0046c0e100e0303042050070390f8110000c000009001e4814030754880701d80c5d0b4040b81c180c040e41c10843c00540c2840e05841d40d90005101c0c0840b003540b00c10159050220170311000015540103828100c8a01503860300c0b035560b446480b0200c4400000d6a0700120700c0c40400509400362100400741c61a00045403505806508000b1059403500080880f01e904c410341000104811885003020340204600b9080103414005503030f002008150b0000100805607a016441284952107401030300450313280e14203598081103442c04e810901c446a0220301801d200440090400384a001021041c0161200c1e282e40c141c44003130394028604251031100e19103900c504880c50b01c40303820007a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 95354991 1250 95353741 95353751
    0x21507081306090e070e0a091d0c0306012706090203010b03061008040302030318010b0618100305010501050417010b0406060221040e010b070f08070b07030c020c18270304051816050a03 81
    0x1141c2382d0490307900c00e00300390020142c480c207445402802d0242804454044001e4a0107600d07110303d40500e0f5061400d5001104280c2c403400120251981c490405401c40e01011901c80d0b031100c032a20303165031068904611882c001400c1d041d4151007003486c0362150f9815130295095444045298800035a4428080910354030f0341041380044d10f43c1c0002c0c00850030121103185140c0e140d041885144881c161101c4101814880107101a903008030481c6c04440c03080e00c0c54214180c0040515004007002c0301c606622034280180041c070036a00103110300700380d849028a00d54028031246564410700ca103100f41d0020420388401049040c0110000c0d01c55140a03500800300702c00c1c40d41d200790103030b84182c0080b5424041d0000303101d00c035039051080c0c40c0280c2c006d0008100034907048c0006500e030704498540c0c100200c3c295000603000c510750110120403441d1000d50140807401c01a002d40c4913001401070341c2c0500000f03801041c20210040c0194040c22001400c01c00c407000c001e20488d1554445480407060545030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 95356241 1250 95354991 95354999
    0xa0207031502040501030513050703020d0809030a030e12070e1b160807150207150e0c03120714010213090b2b06290904021507081306090e070e0a 64
    0x3140240507206011200580d91420b180001d030840d2000f4114100c09900134801c8400124005a04800c1e04e03011124018140c0442c42c0c4a1520700c01c04842903054002c6203003080401d0741029403031840d0401120310380b40b0000c0800200d556a405881112a0302040c1400f00310603548433128500342d8020864114a00000c20f1a181c0520607886030442c0c01b10800142030042c01841304210a280e03503206019031819400e5180e11418103103000c02002810b030340394400301d0500c204000c10070810704090140d03041d03e00d0000249015420903c4280c0f0700455111031110134080c113208a0300900748404005a00d03c1c04c14048900500340c5081c00c5030841c2088012444400f41070002c881160301c903443c6113050700d10384c1c900341044e10b8402c00015244040030a0342131503003a042c401e0104480082d500c01e4000c0d910382c0002070040702080d44041c03045070002070040a1243d0540245607105000d06042082c0ba07890f00d0407180607081d445000700002940c00442c00d9244035920700c98111100400b00c901071600c0f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 95357491 1250 95356241 95356253
    0x206090d081f060c0507090c051213050106090c1d0d080c0304180c0f080106120b03070308070b01050102070605090306010b0d0e010e010209040c110a030c05192022020a020703 77
    0xb0b01e8000c1000300d00002603900400508000900c0507100c04501409501c3c0c120388064000d004080c03004040000880014101000310445410601c0d0088005d11100d82c0d0745100b10010314540c00380600080c48101008281c0034012071140c0340c0d1001501000381c0c00c0c1107448c0c545850700000650b82c410300041100051208410200d61003140d000c05001810b5114a02e000d000741c00001d1021080c800b200d40100500c40d0480750030746804c07056200200c0c08016030f0300007a080a80c2600018915100403484005101c48680058142c520a0b000c42d10420707140d0780d00f61070a00070303901a103a0540c8094014001c58110102030000401c48410209030660951040341c02e580c0d00030303a030300104d039408200d5086510340303030150407401d16103410941401d0500c5183c89440f0164150050b0500845652700c1082200401c004c47c90800b102650040c1d0300c45624000030000b01859884040d0040c00e02c600d400d80c544083c0d12060b81c083c0341041d045100c880c003aa04041c2d0080b0301c402041d801944800808520 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 95358741 1250 95357491 95357551
    0x30f0314070624080d020604020f04110409020c0721030f0e18160903080f0304031407050f070b0c0604241a040e010c0203030f0604020904020a0305160206090d08 71
    0x100d0080aa120301014960044a0343c65a074040c030900d9100b00c4550f2183d40e0045907550f00f094051314203040400011000c2805000b41c90013079821041b001a0018006100754041d00f40b07a010401550242582d88009541c1d004404c9100344900d00c0c00341561001034014010590016060308050400f0114000000c00c00c07800b03503441c010900201c2080084018001144030060b6459042042e48a800c40e00c1da00c005000d51b00c9900701c0d1000c0040031400707160059240c8a20b8140e00600300755103900c280b034010380746d030b0444294405503c503001d0086000c100e00f0040d18401e0070510024442542c0320b440300f0b81800c0c403428084000411308407221810240743e000c1c02d0000c103a5000041d2902d100c1d00203000464003203550510071039241c40900e20500e9400700c200c98000340940e01502d816228440040c0080c410f0a25540d44148005001024513415400052080c01911565018844000d000f42c0e2548412108400c454124469103950180912007444d01f0241280700d01c00803022403003694401d80c0d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 95359991 1250 95358741 95358761
    0x2b0906020d05212805070207030305030c0f0a0c0b010510050f0703140309011d033903160b0a0603081b0f1e060a02071e140106090c12020301030f03140706 68
    0x1c101c5030151000d9044107008a413400d55035400c200300626240070000e48505e00ca00000b4104100000401c4140d542501520a10703002d0301c00e0580d0701d5099000141000e10701c01000c441c00301c1d0807400040e6a14014503040c042180c2603d40e50700e816614a40d00e04140d0100e1002c50030302003075074504032040700c001020311710445041c03000040348080804441d82202c0300d01c000001c69801000a0000d607110f89a00c0c403041000940c00d014800162080075203104120207107407005100205090b060302603102c4803034500a0050040c0c080d11317205c0004d031030700340c0c1d000340006001400f0400c0340b003c5500403500c2c841c01000d800002d0315141000d400400c1e040c600c142c000c0c010030b110907446020300c6480500c1041d8002420003421841c3c404141d4614000c2149040075070b52a4005143d43e4080c0040307909440c03081c51b41d000007041169164004503009103c0c005002c1d00041c0e940042c3e18290f0464402c4a0503030350071000e00713840c102c420742d002c5415124081910300b0041e0107001c01d1002441074010400c0603 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 95361241 1250 95359991 95360011
    0xb1606060314101a120a0b07090603050606071703091207060b040605010203120403181d2401050304060c0302070b040503030105180103021e01112b0906020d0521 71
    0x242c107070002d286403d1120486684803858012044814041141c4080065074261907206600814464803800c140e216400a8182680d02d0308100d0b1040c0e00045aa00f55211514100715646030752090100b14000c1c0200102344072126100c000c42c0310040b2001e198400b10f140102c8641201d6000c511803540c2220104565040c0c407a01411600e207401c0c011300ac09020300303200031401c141402d44108003404000d0030141c10701c0080b13640381b5008910420440c0203803d80401a40501d1004110302800950880381d500c80000b10b8140b2195000740000094046081659030720304545403074076958010f20b134072501c4c841419420481d4400188004003410300c242e00410245460798900760600150001710301c110f0b48035010040044c801a23079520f008410302d01d1440745213840d801241006076a003801c1d4120250b000c0c40b500d0854030200791004141c40c00b54115002640720000000da05442105041c001c84001d40c0007a51a42e0b0703440d1140000c0c1c0318805920a450310195001070418100700b106540010030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 95362491 1250 95361241 95361263
    0xc030c2109090e01050709090b041409061512070905090109050d0f08011a040b2235060f070909020f210708070507031709061006020609070b16060603 66
    0x2c6019030310440c01e07502481ca00911051801d210000c05060315406a403c1260362080034503525221584401d560f91805400d101c501e003015299980c3d11041281d0510441540c030784e04c402d4905100880d00d00d03000c16000181201d5080c07262020113018010070600441d0350b584440c00c0418400c20130344805203165192904404000746000b4030410b4145c200103500c03400d001c8034030021141c1d001250110381028034515200da2030150600c0d00c0035050724003090714101c201000304020560b6507035990400e100d600450b804003d803402100d0300c04040002440950040c4000942d1100d2040400d07501000a20b00084000d8446139900c04a0300080521a107007140843d0402d03100c4250075600301d08400045041040307140c81d410003441443c00034400020048045048020580150b001d003500c5a2540c55200309483c0400410346d4446044540005102241c6030020f032190002c60024003414950b0090a0501d00300741c150b0980d0b5014613a03900d40740f100c070a071a102064582c40b1300c0014500c610140c0398 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 95363741 1250 95362491 95362499
    0x319030c03090e010f12030e1914040e0a02010e0604080a0b07200c0105090402040803040b07050105070c1101050a171f081b1201090c030506070f0f0c030c2109 70
    0x800c81040b038000f03541a1116100520220103204c0400c400c8640524500ca201480c62400326601401480010340110b1103078018403010750302c1108102507507007a0710b140301800311080400c410340c4c092a216000c1a0465a60390b405544a02c402c2c1040d088081d1500f440c6c1030b0741e03030701e1240f0b8036626a40036603c100d013410a100a09602c039a00400c112000c0b1054003514400044441d2101e481050160500c00c0005d8502d61540300c0350151402428850190f81c0c0740d50b5161903200b104e40c00780368100c80c154a4580020001801034130303402809a00900c207a0b10318040c00005407071a9005004900920409200d4280074011a0500600c100c40000410448070f0304107410300710031072440e0880316484d0050240712000e1407080c140040700d40c800700c0711205039611b210060341c01880c0b550b2010b0a071400050010003400760015400f400b4601c1907803008038040240a0413950311a41a114100250752020000c000ca4030404180440a02840c0130250b03028001d41c20b221201d44d5445076802158403200100 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 95364991 1250 95363741 95363747
    0x2301020a020d080f0a05100503010609021305060f030c07060f05041a0609011a1303050f030a0e0a030804030f03020c03010c09080106090203060d030c05100216120311180319030c03 79
    0x2d0b4a0100c142001400c0c1c1c04c101040d40d0f10801c0c0101600505035030b0704000b17664100440b01c000e000f003001400030840c0c9a01c40710f2a6000e98010342103401790f0800741200080504050003200c20101c070802d100c038150740b030f02803062941c1c0d44010f405607102070301d413081180c4412852003400e02035131240301c0714040a065200c5143c0040c1d802002d8500c5500d800c0010800c0310143c2c003003001d10340350004070b40360349281c401d809500002c450380024159106410142880e000c000000b0b001c910b140751288000354a0b114200001405a8000200b0080c800c1c4410000201d07440100b00f002d0b4070070300564514002250200742141c0ea03203101e201c0000c594080c10011444288038040140100000561541ca0501c01240d48030320000b00040810028410384010711005004070441444481003d641e00c0c000e80c106071200c8400000e09948a80719148403c5050b8081d02c650796240816044581c208070346900d9032010600e1441c2c05031b070035014600011041d854040071002c030061080d102d03070601d00d00509000b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 95366241 1250 95364991 95365003
    0xc03161a071505040311010e0309010c140601081e03090a0605070609061406010f0903020d0227160905090403020a0b06060702030303010924030302121b061801110901050909042301020a02 82
    0x38400f203908d4160070050720b0340048201e68074100c0a08001c4140e00551400c407030700d071645e5400304040b400f41c10008181200049103080c00b0912080c04102c0c000031110307800d03031a44200724103554814095101040350034020800703043c0c0c2d140140400540c141c181d4580308150f0366920045243d202e1403004200180d03030013030940c50004010b4681702d14020700f10f42c04103032152640c60019220f01c14041c160300c40c40e080007500400000d005403800c2c400381031002c0d00b4060304c14400748440118115210201d158240b12104503c9140c040c0e00803c2030300c0d1291a0300f805120060310154115508004490158804000550003840304080000b01183c401c60f80580c1a07001c1909030201e6070400e8020800702c2d5000456136000c2440e03103009075403090308121600010310355213000c1340280240c000300305040c0540c074100300031010740d03c00901941001000000b5039102d041d84441c0800c43c1400151328504242081035030003482500402690548107a6105000c0041d0311380200036900000c503800d0440d414041 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 95367491 1250 95366241 95366267
    0xf060c1c030b0901030602091207080a03020d0f0522050613090b03010b010504060305060d0b0f0a060609060c0f0c08030318070806070804062c0d020c03161a0715050403 74
    0x200880310080c0d0015070f803941e040c44080d1000f6004280c204040d0344035982d070314840d62a002101d00c0b8a0381ca012807512102c4800c401c0d000b602407407010008840c06640400e9a40ca03855803002d16103400c2116809907a00101850864054031000c04101ca4541000800d8104000070b40190b003a0304d001004000e903003d440f0414060f90500411a41a036081000d4805880f264100403c050b5503100c0400c81030a0540d00148c11034020005000c0c4c6844c0d041000e41c012007801c1001c1c0061900e4060540e851a02c0b881880005140e0703620740f2003c01c1465803e150ba1603c500c042141681d52846424503540013510004030084000e2070b159440a020080c0740d00601c000400303003c00d40b8003480b000d4400d01e00280b0181c0042d48407154a00c80c084031401415802d0300b04980394120300c025120940d65841107a94100240c0728070809144986000101a0088030394041900a464207080240085203420080d090300144c0502100c0005903400c00d024240380c0004500041d41d14060030020413500d2a115 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 95368741 1250 95367491 95367497
    0x80307051314010507020d060b031005061e030c06070303091b0f0806010f17010e07060e041404020306040201050705031c0906060501030902150c0f010212040605011703030a0b0f060c1c 81
    0x607080301c0c030f0f40c00c0400c2ea2103254040b81c4443d005801400c1c1080589100000039601d4010000c1c100180001684441e015034004e03079180c800041c011002c0d444d03d442c451a02c0b549544014134800d03007450860020504540f0070316000c42d0aa1880c0c0e10340040040706030408060614451040c89141c16800d0840010322000000740155454121030a0188007203004680c2911184100194540c40c02d410506660b12008216001d00b86d440c80024815100505c460b403145050503181024074100d40100f60140d50014040c02140d2076640c01510f00f0351145008031800d0000784844c0018801c801140c0100d192400c4000c50750240c145018012541560403850600d440c0c20f00000158692f82030a021760b4082a8080b07036030b180850001da20345180d90041102560000400b55908030b11180042d00031032240c4001d000720790300d17100c043c2d101c2c803184940410168014800144145079503044a041c41e040640b60340307a100c066201203261a4801c0074030615903400700a5800c504000750704590a8138007289 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 95369991 1250 95368741 95368769
    0x130905060f1803071a04060209061206011814120a170702030105070305090c0d0203010209040207080d0b03010603080a0f0903141c0207060504050d080405090f04120f090e0709030803070513 83
    0x15688104c5c90310140e40350203906004000107030030486554110b4921520040ca010b0300e480354003803d09c01c0300750111071160000d00ca64100080c0340f01446081e005070f850800803403801c01c090304207109145502a00c800010300c80d201100c00483c80038502c1500ea50440016960341c1c600174014542910b02c05040e02c82098549000c2124080000c00d000203000411a01d20140011500010b80a03004411141c1d40c014800600c2c101003241420040201022140c000d2100c403507840b040600721412444003504c0c2c50f100704884808148554036050b0200ca16041445c81280c80b0380340c001c0e482210508a14179076012802c1014440c02c04009041d441d0280e100804109080000040aa0256100d00e60007280310282c1581000078500a43e4050080605980f40c90700e0315a0890304102d4080d50f055a0300c030101080150001c0c8225006110012036480f400c0c42e962070241c40d080140802000c0401300b02036a0000310018101c00c0082d4044c007002d0b0398203a224143d1008054003407400d80c3c4a650010011 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 95371241 1250 95369991 95369993
    0x3180e040b091005090304030510150b13030b010605090906030105010501091203030b09130311010227030a0f080c010b0109050d1202190302061b090a05130905060f180307 75
    0x9841540d0055214031044881e4440202c0d40349801c00b090f9004160700c3c00c0c0800c11040da040040130300112070080085820445050400074100d4660302403415034420036000602404000c00000c0c13403080d459100c4080e81c2d90f40c0b9180c0070722009080e00000c4c0000c0002603420400c4c40c100d05141d40240089008212a514000c000f0301749400d5441080501400030300c00c0c40600d0f000e58450012010f0140001865103040781c2010562501918110b000c120b01000c26010500148280c03540c200032002d114072919001e109180c485684210030360b50500c104050320000909015100b601ca601c602d5015840b803074100021405d42d110b0040003810010060010406076880001044500e5009060791070300450780c0c04120300384404084c07080d00607406c900f011002c1580c00a407861060880c048601240200008075000ca4460401020391080390b0760818000c501d00707040034940502044070000b4001881e59110380c1004812580c415902c04d5007800c0040d590701000c7c140600c0540c880c0514900801c3d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 95372491 1250 95371241 95371259
    0xb0901080403030b1305040c0501030c1805060922051605071109040c03050a0f03090e0601020312070221030103020909030c030d0e070b0408160801020f0f181206040318 74
    0x20700c06410161580184400c544442058108288401344c00b17110b1842d040c203044203070246034400c00c2c1c0060b14003a001c0380c0b0345200b00071100b900c0c3d05542c82910f032a071501d13041180a401c4503600641c00302078406500c520216500760f5000c50060880302082c41d19041d040303019054171001d040424050100001d000042c1200c40400c20604100d44c80300c0c00c2d0712182030a45242e4040d80009240d0311400c0c48610030712038014400d032940c80c401e80c1c528000c50346030366221449202c103035403490159000f40310207400602140c401691042842c81206c581050f4101c2c65140c80014404c6803061b04400001403082d400c0801c40140d00601d100d00640c03500129800040e075170701c80c8080c0c00e6200c56548401710007840d02840410010005400ca0a841c1d6841d540e145032a9542c4640f003400100f924007002540030030600139103000880d03040d8036905040c40d0309215000d6603c06124001c50031948005440640e59010310a40340c1a144d4000703068500e014500a0602502c1d41c6405003402e07481e032810800884 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 95373741 1250 95372491 95372507
    0x1020606010c0602250503030a0b0a14060a02010e070b090301061211060a02030705010f0c0807020607050301140402070206040b0403051e0a02010f0309060f0c120e0c0409050f010e03040e010b0901 86
    0x1600101c0181e41715810f20f400e00e220f00780c0c602d031200c10204021000003444000409140036046451007001344000d4030040020b0b00000784100ca0114808d890f40040d145480e00181400c0001c40c000421060a40c8400b0703814658190407080d0416408942c0e030f450350909218160140c110342d5082d040d00c2c2c55588410f682042105845c2d4414000000d450a0840c0b013841a261040d40c8031009008090301a0440005030036040d8201d00020040000200403a01c00188070740510f210341c940718a941d0034600c008400002c18014150020b8080040b0001a1159001400144110305c0d009403200d0031032510710304100200130030310040e030040c018200340d141001c00c0e00344101c0d81c2405c0c804401c6842d494190050051f516018040920744103081c104c0d0b807226000500b2051850f99802d00800400d18900c084071138880d603026069200204415403410281e001e01d869601502c2155001e528040707400b42951859988034040b40c10204d8200190380d44440900c5c0986416031545041030420030000300150 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 95374991 1250 95373741 95373743
    0xf050c0c04021308061e06010203090907111f020a020d02071409060d0209130201030506030f0714010c02030303090c010f0507081e042310020c03150402060d06090b04060501020606010c 81
    0x1a6000916402005000c2078240c001c04000b42500c8040c64001c0001c20701c1b00c0c440d003002c2816540300c0001403080d840401110424030b0000c4c41b416140e1114a42160013240d50628942d41d4820303549d0842d4220071860254107118100a405690f4401181d4000c1c1030000726180303102954040310052081c00510840480030307280076aa100001c2d0b80700400910074607090308000c0d401c45035590500151000307041c81031113528003c0e01c0c10b200c01d441e074005140c0d4601c450101c001d030a4000c1031062090001d984a000078a4005142c2074000c1405600040c0c00d5134405d4451001c603500078030001e261941c01601d6017048800c3c41c20154207209903a201d036a480d01c558803c00750f0a000008404540380c620006035006009068603080030082000c4100d071007a1504c08485128000e0003589000c114400074040440000150242840303c1d1000c0505503a04406031040768000002d0009072045c203c6441464014400c484000c80c01072900014041224000d800050454010204201042e40c021300c03031034012 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 95376241 1250 95374991 95374999
    0x803030408071e03110c10090e040c0308030c0301060906020a02090c0a0207030c140a050a03050307081b060406320705070305090301051608010902090d0605040201050909010b04060f050c0c 83
    0x80c525440e0480c4181c41c501c40101800503090088803d0551082120041d8094107044550001c5500100f24403042c44000150005481000500c010109009c11903001031141608101c4103031640d44035143e40c0c00032900d40c0c1d50020080010400f20b80c0c401d0042c4002c00682c006021408000d4010030b8207080300818080c294180000c04a090307a100704003410045420040301401079441c2c080012050b080008000d2281c42e084001103403510f410310205044a500000640c43c10202d6610809180c11071403002c80700c0400d6426003401c4080500091384654414200020300c0c44805042c4100950a129a0b00d00a10603049a8648000018005401100d58241251295803500c3d080750b942c130079407030390715010750800050000d0b00d031f0003081380d101c0e8040b240c8a20005d40e8031284000228040c001c1c0e400e40c0b1030240d0000c00d021078520741c00240c0050061401e18038100402c00450fa0350002a40300d11403041000900b002510b50007501c2c0312449035103150062503c50401411a640d484080159200e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 95377491 1250 95376241 95376247
    0x6090c0301060f082a04090c1d01080702191505090a0c060818070806150d05030306090c09041802130212010b130e07030605010e06070201021e03040b071b050a0803030408 75
    0x44030381c4080c0700705010049045c1c09111115007040c5013a007151044000181c1422507030455180141d0006510040d0304c2c0c00d807100030340c04000440310b43c0c030083d090105502441c415420701e041060901c594640c0511b28072107544240f45502c0b400c031103006005070501d0f0032141e81000040e481110180441c4d941d0b1804100781c0e103a5451101e46400010300c091001d106612001075003000105946100783c2000361445500728490081c004106501d45000b03115800800028410f890201000d07074002c0000031245040c0382c020b02c003041c11180703008007090841e04611b403a4421031034554000181541c0c00c2d0012350400c000d482140c290900103010314000d1f1003010032141150207404003040c00904880d1410285800c00c46405401130100c1c0c05400e000841c0d010501a036410440101c900300366040e030007800103071400040d9065000300c45c640001c0074002000001403100c80c90000d4009940102c484072880c0910351101c0950142a078800c60060641120810460030044162a0312980110301c041d0b03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 95378741 1250 95377491 95377501
    0xe0c1e03060616051e0109020a050105041203030f060b0f0c060a02040503032b05041a010602070f050607030e030f10050a0e07061215060f031409100e0709110306090c0301060f08 78
    0x10502d0700640700d2090036503040c01040151070341500724a6007580281c4040a10b03d482b04011680c82c4110300407281c03459418240800041c1c030950000340942d80401c1d0009400c0e40310303a40200c695101c3c1c0b0010044050126100300e01c000184290781d08001d03081000c5140c145400c01180d201c3c0106201c081e003c1720005015408415403024540c9200c3c4201401c000b245010300d4500c40b00380d001c0c245110a0a4040004a0810700018000c025140052828455a480c100030410740354000c000840400143c90541d84ae691010402e9500c0003980744c000d0420a0007002e4a5002c075070008011036000307410a0840c0003a14000708400c03003501c400780b5201980305245040c9002808072980f00d14102c0c0801e0742d00141a136800809140049002c0c0d4092080c80c5134003646903000031041d503022150360407a01c240346280c40356502c1035009a45100946503815981c2200000722040501c0d0040303001d0001040014514001072043e5000242c03032610b509650410200234400d0403c0d400c0c001c10b0000c0f0f400170034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 95379991 1250 95378741 95378743
    0x6120920010315030c15020a020108040f021c030503060f040b0a060302070c150206012120041104080a051603150b0d0807050109030201060801060602100c03060e0c1e0306061605 78
    0x8040d8604043c081c160a990f02e14180c1000851031081e402c040c4164680703044100d07c04160002d0b0035030140d568241c9070f2920b03210b90310420301000007241d000ca10311201c071101d4071850740e5217424035000b0346072203459207040d00500c05980d283c0c0400c54425442c00e00c40b241c1c140d84585552054038400d2070016103503802803804840d002e115400c81540c0b60b04c0b280b076003081154000f58a0307050300d0340034803401202900710360416010a0048030050100020007501c0a04403201202d0390b40c1030000801c0450015400b851182c10380d40070740c201910320341040c1c50f031000b402400c1004940d1140104841e090303541c0f0b1911508501103000100d410516140c0401403075aa9940005001082e0003176226a6909118074103240203100081e4120050350800e4000030700d012040c0314030011501c250b0054003d001c1d03821080c0d80140001c0001c00300303056446901150070003c008100c0e100310700c40c0242a5443c0d80f000207600500100100c01b000c00c4108004001f03a40d00d03420140d4030300d02000840086015001d10740a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 95381241 1250 95379991 95380001
    0x703080309070807090c020d08040f0605060102010f0f05090f07180b0409021008180c010905130912020a05101b0302070302070e07091a04030b130c05100306061209200103 75
    0x804101c0c803034004c02084100080c0d00181048440f43c08a40400641c548180d48051080f01e01510004c07060711a0707000b244460f0043c41d4414014400011000c120080b0700c000c4072540c030100c2c483d181e582d4040040f0264108a00d0302a003030348100a0110350315100a103800c0601c21a0724044c85621001284010740715138010603060340d4000d00c60070300380702c445400420002003160b0081a5a040300148040d044020500c019124410380d500035000c1d0414003402880c580d080300101456a40f42c0c0500085600c0e103d9140049483e41d01515a840301421b205161110069100d1801d900c0c040c0d00c1c8011002c409400c8405280318100036032a200242010b0342032003c698480000d60b0a0001000035440c2c0c002c07000030969811603108441c2030a039000d0a14a80198003000300314158040200761110102840840e0061003960030b02d00d03041c4c898002c9030000c440e4546540100c0d8640400348a11034000a841c00e079120041400c018800702c5442d810342040e80e24032910040c07045c0305104802039101e5002 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 95382491 1250 95381241 95381249
    0xc1e07051c020d030605030c01140d0609050103030f020106050d1713080f010c020105040218190c0509010305010602150604022d0714030a080c09120a06090b0711070308030907 77
    0x548a207003400c4000d5080c40100c0d00710400040c050286072200e4540030340301c0c8105880020f0001d0680041c3c00d0015036900c41c40440708442d10030709110080c0549000c1c01880e029290105012589501d1443c0107400400c462010b542903904180040c4002e4a50b0094501e60703036001803041640c201070145070115032141c04007074407600205003c041356040b8000386134420800c00c0c10007003050f0140d07000308031b013240c009880003584000200a1b482e45c0000c0c1c0007a450300421200c581d0f44168501c0482c643c21a20382c10300003008211701103002146582c0610525004141d94000b81c80b280e6020f0f06002c4141c040281820300c100d03800700e542d000d8491210410180e4040d103034481030341a0003403441d500300c0e0f80024a0441c1c0c4c40403200c1603400788440106c281c515010440e1105140c5031100340607421300b41c02c690380241d000355050010f525002c90400840001e1400741c3d0380020309103040d05101170b00013001844907052168811210440f603c000450000712a0080e480540382e8403050540ca0424000341d01c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 95383741 1250 95382491 95382493
    0x80a0f0f0807060501181104050f0103110d0504020112050601020a0209150a080a05010c031e0c051615060b0a0525020a03030206150405010f120303090204020c07050f090c1e0705 78
    0x180d64010400184c1c000740c166035001c3e024002900100b07500fa13080d1031000c440c0c000e181e0000d00040100d41032800864202c0e050505000c150b05401404101d800d401c00f010340e15540303403200f00344415542c00a00780b0000e00096031090015262410010b99190103800c0028010960140040d807031070340703070b03a403040a6620080104102541d2525a581e860350015800c1c1e07499460030441c19030322030092017580481400317a1424110402d00c444105c8c000c156050840007030080400220b403500d075100002000c03407803040d50410800c01090b1220011030b5646d4000c103144400c2001400800c540000030b4034020201201038041c504e2692000e0b404110040c4e500940015804601108168001c5051441a1040582c0c100b101c02d00c80108415038000b88141000710503003000c1031208480700021150400d010b418041000c0380c6903404a01243e10210b50446150401401071000c0c0c50101c6021070b011038120307484400ba041c00e180341c803654400d0000026900310065019150400224103417611560010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 95384991 1250 95383741 95383747
    0x120f0f0507060908010506060304050a02090405010905030a050712020c011d030705040e0d0f0f081305030c06070917060103020a0b1315090e070807080406020a0e0301111801050301080a0f0f08 84
    0x80060b01c83c645074011182c1550902d0009034242c14004142d910860b00b0800410540165400740218894054000c3e1625505d40411785d0104000300010914041c0c0c1c1ea8400365130f50704e40c0c1002c4200304483ca5621085401107905080981c0e4006203024041154580c47c1a14690b11300c0060700c1c04001e6413100d80c100b0b0401044c0490381c0c2000c61008130421040d20f607500000c51440040b42d1440c6a407032040042600440403e90306031060151040c45803040c0201ca1030541c124541501d8a0000c6401400081d03e40c1e03800e0049007250700b40c20109000140041800d94155800101d10307811900880c2220a00460504440c585000101e8010300074529240c04070407000d44000d007101641d02a050000ca551030104035160310903050b09100b0f650b50755409006454030303680d001c080d6008025072010819020354800c495074088c40b8410304441007040540d80d851180161480c240c03011140305050240070b000400144501040d615021640003502c840e80d4501454803034554016000090300c582408 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 95386241 1250 95384991 95384999
    0x12084c03020111031312030e03060907030627120c0215041d01060e010c02010306052205060405071b03020102040b0705010203040506060910051215040c061206120f0f0507 75
    0x192245a094038001c0e640c01d48005071440e60940d581c415603031442c0c0c80741110303002000780c41c00b203c501c8000c2c64420714114002c080b074000080c3c5008010f55007108250080351003081081128403484103480c07510380c3d0403440c142c60041559005692000060701b5070402d01e61a14200b881680340001007507004043c88a0561480c82e40001d980040c02100701c00e0403181180340030f01000158650480c0c045035140916003101c040111291810044100d050540707808020807107988010f1800725900d00d0b8042c984000c01c1600b04c04050700c101810050142e0328000c00c0c4600c10b503120f480400d198440c05070508008442c0d01d402c900a100d1075000100003031020070b0300820400190000c502079030284044510300e803548000c100482c00c0540303000d01c5041030b0803000c110609042e1032800d4180245016a0200040300840d4200342c00112001c59080d00c1d0040180401c1d03030040d01c0d050050b004d025040000300c1c100694014440a40c0c00040c20980d0005c41c0d0004224003410a13002032a4400241d03603000ea91 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 95387491 1250 95386241 95386381
    0x1207020607030b010c020a09090c09050a0906050a061d0903120a0b010206070f09150908010c030506030d0801050a06081f0e01061d0603040b061c0f1208 67
    0x819141a070020341000c51070142c0358401d0041481458004080340e00c4940f601c02c11310005c081c41c0004480c1400382582c0080c802683c0d00c10300f44100050320020070389058a2906c50b0440f6001002002d00b145084024441307110440e01d400c248880c0641060f6454898901151540c003d150041c17485802d45000c00400e50b044c4c3c0c1004100342c0c1c00f0b03022a40c464603400c000740c80e41540c03903c04c43d0000e08003c8040000c7d078554451f15907030754024209000910384495080e407e4405240400c00482c1d140c00603c00d890030204802e060b85840c0703103070264043d4101400208580e0b242c4c490801000485804143d071424051b03855802c0d51962002d405505542d524a1800343c2024840e039008a00300103000003000d440004250010b402c010000c61940c0c4c1c447d03444100d401c10240c0095000344501e0700002c048400d030104c407800d050062602902d845540d140081e0f594100c8540d210400c007000d81800000501000324030008140505401c078407280c210700c1c2c541c24003c0000d504000001ea40700c2d03801c1503d8 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 95388741 1250 95387491 95387503
    0x605070917101a0d060b0a0819021503150108041403070c0905012903100b0403050105010e0c07150504080d0c1701050a03080301060804020609060d0e0c030f0a1403120702 75
    0x30020b0002d00c04592040e06040300040c10003a0030750030883c40158000010042c5e0300075262084024081002c4035195907816142100d500080101181040724620075417070001c0007016005800c101040ca94a8144d01c3d100030032004d0380e02e01e0b05001c0904041409c00004030003100760b0f9103071b03017088985904250402c3e242c41d1005105e1402d90519100c008150002800c4500c0080d04d081d44150f6640c07800ca010940c150b9100074100b035081c0e044024003142182551000740020f41c01000042059410140e4444001c18042c007030140d807040801211000402c3d801c3c0189a0550071b0000260b140d036582041540d901c9007070452540285000342004146800c5194202c015481c030f83c001c1402da07252020302c5140c024070300010380101024001003001521900185502c6407020301081d08000703ca4000c01c100b13401c184540079500d03496070001610745c0010084003104a40440c01008078109001c0002c0e1030311064000549140140c0308030009030384040045460304030154943c500342c3e01d08200e00a403185 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 95389991 1250 95388741 95388763
    0x31b0b090105181212100905071107120b060402030403120e0a1b06140a030b0604090609140402060d0b060705070e04030809030a0503010509070309050a0303150b0c0303040605070917 80
    0x124a02c4a0540c440e1400206040d01c2e070524104c203480c119084009419842d0002e0100904c00e00014022900e2261800390b240a05002e44a5160084c04115031508000c1580c10005e01915010344142c00b0900001d045d540000c000e039001039590f2140e0400312403525100b41e0700d9103514209510740f50701a800217540564035004000085407841c00d030050424140c0c0600c620400145011910310b00e400c030f01e100521341c01d5081d060000d02c060f06d00001c550380390000da000541d41c681d5120708201c14007250142041c21254100f011446140c103a0029545c2c0c040c43c82d40340c082e42d0340c070010745055444070400c45007004c1d0080c0454061656400800c480050212030031000680c5850101d03c010380000f003682c0000e40070762030351400c580c01d04042c4140c080000b0501c60406448989100c0400d20601690049038002d94011031002d02c52007003c01625020307440078407810710400110400b49030100541303421540c08100894603031929201241d41c4a25a085010100c0c2c801004119081c80000c0e601a45 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 95391241 1250 95389991 95390011
    0xc01060b03100806040f060b0a0f08030a03050603010e100e100905031818041101050706050a0605090702070503151e070518010521040203030c010c08010906090501080703031b0b090105 81
    0x35501d462405480f40340640c1e0085c002d075010070329040010b04c0c2340c00180d020310015215404840d95000c50018020f190391140d0500c0e0000521452341d80d41c1800b032194440016802804221100c0d4200c1d540c543c0f004076081440ca942da00c0b951b5000303106000404030401041d40c2449880c201e400e1141e22076224500c4041394101d4250543c0c001d061a0b010680c036055010300300c1845644d692500c0307441c10f58001c005070400c6800c0025600040c4075125460041c0c509820000d20241810f040c0b1070100303000340405042d580141010002640c3c0021203000f1203402c8002c00343d040d10b4000280e00c050500f07081030161600c98000708540c0301e038094090b24451468008101c0300010450054445119200348601030303494920707050711488544c20240b80c005202604a070701e048000d11405003151520f48449000440040040004101d50b0007254040c00540030200170b5545403c8140740c1d034415074030004051040c121310a28040e00325051403070400d508031003c40c42c6807030b001603070500800e8100c420700c1322 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 95392491 1250 95391241 95391271
    0x101103070501060f12020d14032503080105030708100213080321010905060a03030f0e0316030221150702070803120109240902070204020c011103190c0903080f0c01060b03 75
    0x3000305d10318961140c00e900540614a010040d03118000c0000d8041d0390710500340300412211150203a1110030b2049110040310f141c400140c1c03883e0050480c0e1040c0c0c0064405d0f48080024050480d0205500300010341031140140d5926865002c03820741c207802d500254240c0804540a0506050302c1c460102c03414401103507648607070300c071020f00c003c07520306035005904114400b10910000b40640e290600e207c0b0281003c6441d0003100b00041c1c0340c86c0700b8404803002612410403c0085003030040d448407000b9401c83e0003041d103404120031581d8550424440341c1c9010071315404621160300074008140941003241c03d481d51603c0403090b800030140b0130f00c628481d41d03281c00080503120044c00e43c0d10711001c100c030761300a0f805460324440a000c0c1d040190b007179078000c2e401c1014400051007442140c405110300d64103c2d880f8600301b02d0b42d540e91001c4c0403101504078105105020001d034002040f80540351b024002e9a102c00301403400c0e0406005001c0c0355a00c541c42c2c07040104e85c0f10011005548260481651129 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 95393741 1250 95392491 95392499
    0x303010e16030c0e01050711040617010b03060408161406070305060a090221100e13050d0f02060408130902031003140307051b0f1804050106050907020a02101103070501060f 76
    0x10495005040e510002520062000003030346c0720b00c0052901c180540010034054602000050443c2c1c419400320041468084028124150a01684030200b4088024105071710341501c0d071001612400c070303202d1030a8a502e240c560402140c4d1100b2403ca250542c1103440e10b18058902500516050303441511440300641d000480c80090b008070741c03600d00c82040c21060503240305405000300602508002d504024070002050010550266510690001284030701042d024102103080031103282d481000c1001100080c084036400040e03468005a2113440e04c0d030750343c44040742c0c0d00d8454010703003000c15624000010311217000200d4120030151380c0201d0001c032000e640c111450740c1d00d2149003801402608800b51130303241c0e0101c10b004402041c0b4054801a6503109800010b03d84440c0844490030354a100030600c01441824800c43e8058401520300805070305020b1006982c462030304000a200d98643c040342d1180c103102d0101501d000e42c40b00102c944a2846180043c0604118081c0444440e070b1020005 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 95394991 1250 95393741 95393747
    0x11217030901020301050109141e0f030d030f0c0507080703141209010b010e0103060f0504020d060504020a17010801111c090c0605090909120406050703020109050d050705010f050f0610110303010e16 87
    0x4080d00400380c00c0ae098010400c546440c1011703108941c00880c1c5051024161401d01c2008080c00e581d40e40091380c10403c1000c00d08a0700c081d4010300801c5024480c401c0010301d400201d03040f0940609004081c08201b1200580300d2003400500d00d900501d40d014480045415004038401100988649001100307400046084550511800d180c01d00c10700d00400c4141041c4d401001c01d03640b954004202c01e922000802c01766801080c09038005030300c502880c1a8602c80010341409000204028860080c0015041480c0c0c01905041300c0d00342100c4800641c0180c4540c0049455640161034801240c0d0f20600a84141c03c8140805c0c020306c4a0310002d0100c0e9800300ba400c21200c90440418241400c01c3c0d41203030903811401045096650b01c2942c10081401000703280d4040046582d075640c0c80384180b4005003502d80250040300c54078188020b020301281040d441c0d5900803015990180ca55440404c111a0782ea14941c60403040c0c04000001700d1a41005200030b071145022041c0d4100b440303030b071110072 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 95396241 1250 95394991 95395019
    0x50702011104170708030f0405090c04050904030305060d02040c031e0203100614071401050a0b03010c09050f040b0901170601060c12050304060b0405150108150108011217030901020301050109 84
    0x40d02020010401030040c09040c5800010100f024070403a609aa01d400c0341e28a107920507040340020241c0442c04000c540703000340100d684038124501e00f0f41414507107408940c0d60900900024207050701e0742d001540b19100c0c0d2100030901070b0010024429140c0206021b001000c902c050700c0c0a140c613000e4043e003100303903d008603400364103410306810180746040b40c11956912544185d0420540401895002c40d9801e500c3c68401c645c14000011541048030750001103d44030a6014084c0c0d0400c2d600007065038201c1c030f0580c201e50065816641040011000500508117421000d80c00800b00001144800d00080205400c104a008580c12641c894400b45d03203d4150710300c01070040100300d01025695101e20050b6170014880c002c00725600041e800050103480d01150358042010000ca10000650780c0305a80e50340051110b1250a500440b550008000d254140904c9601032078940c201c030100442c000c884180c43c40131501151b00e0f4100f84550b14081c1d4028402c20340011030b2408041041d6190000c8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 95397491 1250 95396241 95396261
    0x806010e0d0c0906061d150f040303020f070e0103030e12010612050c040e03070803130602071e030f0e060a0318020a0b0403140111090d140303090a1703010602072702040e010303020105070201 84
    0x3840721030341c5c29441080b001441e410301610300c43c1d10500c6948c00b10000d90001c0e001442c42a0041c1140400000403140382406960200b41b400c2d40403401000429040311080e64806801d44101c0c0c400604400e5081c05001c00740e00c010b42c3c03040444000070034000045081c541000086405011843c3e03480610b650341d00451700054100007007007000c140034004554000c0e4205228150150a203c410349a8003184602d40719018448800c0d00f8243c02015442084140780c42e40f00d0804051030100000071403410701501211009259442d107200100752a85552080c80650040044088903200d001c8a40240c11510040342c65040041800c1d1481c1018041d07070f0f0401c843c2c6851300b82010740f01e8041148001c8501000d40b0b21003072a00d4440d200000520080d0320440c400c100800075080c2c207281030310881e00d141d402581207050600062001d2540131400308111113080c100c40303000c14801050703d1981c20190b40b084030080d10004002944a80c0850202d04903802500200030315950202c0036400c0e900c1d0300d00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 95398741 1250 95397491 95397527
    0x20a0e09160b09120d1707180306050711060f06060705010e030d020a02070608071d120a05010b011128080f0406030603020f0f090103140f0615030c0a060f0806010e0d0c090606 77
    0x1021450036045420709551250048c901040b03007240c80e042103c044401500103880312901c981c2085400c40c0c2054034802000c4900d030043c00c840c075080f0040540048003030b0200303118a000240741428000250003003080506070800b643e075110210f141120080d4041c101901c054021780100041c0d00303001d12206803141046807a1611441683d82c1140b020510000516901895800060780f03244400c20079060b0b03071441040000380710072441c80058100d031003401307804440740c0c000c0910321b1803e600c084810744411440710340f4031014007207460964114000d8a403651285d200c0400e0015443d541908050210f0b4026990320010150f044180b1061000405c40c054000d074038038004000144810380d48074442c0c00403405841400b441440d000d03041180590755180c1c501c030740c00d0404005150520903a8003010b000c8842003407040c0b4001010f011a03050001010903c40c803540000c245034081d500d91a40712400601c0d100004040b8a000719002102d4011074540d42c2ca01140892454000d15075001c01c44c800301 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 95399991 1250 95398741 95398757
    0x3040f060906090e130f1208070306050a06230405030a05030a17090303060d050c040c03020c0106051212031e010303031d010b0a05040207020402070b0f01060e0d020a0e09160b09120d 80
    0x5842d403070090400f500c00c5840101081b04440418401580303424003200d5030340e4003021030810480003000d0ba080c68000522800000b01e00f0802203401480b41002d400e140d4805460421003148a01024041d6912868050203100c802d4010444040010010a002d40d200c40990004140d45041c60b600200d45288450740704001190b0b05181860940e44014402c50440d07142c0d101080102c0c00b0340302c2c01081ca0010a402145a0000c040c0a0182401400e810364200c03084010f20050b4654817908111401d030000c100101003112800c901102001ca0500a101d1140651b5030345002001000100c0300507020f6481061010030546040c003880000c40401072022804505040402c80294001381041364050383c00c1100700002a441c44030b55202e4601c5040900302985002009010150704846840c0300d00f442c04501c2c030044c0c0d14102c2103c1516801000807129545981d596403070456508009003e01c0d2090360002100f18034034005200380c07802510a101c10444200f0b00340e64a6502c0507840011a0101d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 95401241 1250 95399991 95400001
    0x7171605091009020c07081504120c08090406151814011d09070e1203041206051504090b071d0303031b070602070f021c0203060a05130503040f060906090e 68
    0x390412030300320741c40702c01c107103141941c2d103910908030781c0070b1811207089420002c0100a1074405001e07401c81c8901c1d004205400e49071640d260082441c140c3c01c0c52041c00b40043e420024004180180c0389004405007007041019114070b010f16940003611500000900c103100c0d0300140303220320441d070421550201900100a05840c1c01507403e04c98408280e0b0505c000011460703000d50702c010115006854941721024070042c3d030300500000800c2001101004d51040004000d801492071400d5545904104001050b444211342561007004e1058010361190400007448140820111501e01078030441d00d541040840b25960580400100408241d064000340300103040d4024002c4000031049140e62803e00e021010b5030380c10200d03006107030182c60b9803104410480071800c000d080304280d10100e80010640003076541c006640e40720010000303840035481d50081140007090008400c10198000141d0751903980302c60348001c1e508010302c600b2000998011000540350300410341002600c80c003103043c107419518 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 95402491 1250 95401241 95401249
    0x905040b040b0c07030903080c010e1c0306060f020a11010e06181219020402030406090c090614040504080703030e0705041404021c0203030711030c060c03090901080f0a171b07171605 80
    0x8143c00d81141552148141c0bc02c0340c000344181d282d0215141191011413008000003421909150850700174030880d0303440e1a01080d00095001000c45c1e00c02c400c403244400903001218030054030502c4541200f00483c52a5410303141002c040502e6005484900f200c000c6c00000654a861450f000500c000180310204003504154004550050041202044218503562500019507165114078155030381d40c0410f00160b072180407100c254500071a030502603804c02e0b49034404a031103000c900400303055458040c3c034120a400e00c0517000400c0020010000c100719040345904501c421a0228400d8003506000791f81400440303900c165180e0050000d44c1488461f540d841d4664a042c51202e905214000c0600760b04c5d581c0400410001000754085c5440e030345c0c41c1007840040ea4060704440c40350340000a405481c1d00b00042c80301d5850b50041c07031122280140c03a501e14450710031080201c5031204c80c0c05020306e001c040018030303808032203d0300e840e0040300c1d46d02825562251441d2208041402c03000f04d0802242c58 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 95403741 1250 95402491 95402497
    0x1032007050f031c0608010c05030105130f0204080307060b04140f070504090207080901030e07240507020d082205060d0b03010b0d05010c23031308040905040b040b0c0703090308 78
    0x120410450320751a150503030143c59500708100c12201104c1200950080e041203020707020041045000900c0b1007204298054114001401924010000000d030200200317800c0e0400f0004000200e01156610380ba03900403502d0342d121034030a6540b2410403505c6582030a0a22a1603504e134000c00600c195900c502c4042c10f0b80b140094841c44c1080401e0102040100d080e100800c01d40f4401e400c040c1d43c80045400141c00e1303800400b0100700580020004004a142041e402100190f036080c02d4036401c0c28000c1d0640d03182c06040780c00307034111405034004810440780c14000d04460001000e0000710203021040e90b14025101c0c01600e4106409009003c90640c0c1d0741c01c004140c00c0020008500b03c0168404120b404c00d9050007a25a07a441d920b180c0c92064100390848c1d0421410ba422000c7c0d404400e1248a4500c005003c1c415041d0100c0520009d000c00581030310041c101610003840281060301f401000c3c01d60680d070079a0030011540c003041d4500c8941c01111002a45616071a0340c0754070310740b01c4c4080c0d50 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 95404991 1250 95403741 95403743
    0x709020a050409050c030f01080a030f0503060a0b030406061d090304060302090409200406090e07140d0c1712070506130201090b040f1a0909010b03100f150e01032007 73
    0x141c207000100310303011240200c0d0300c02c41c04c1581c070940341e00d0918a040102d200603440000b9903080407101901081d0b10100d00322800c1858203100d60790752144408103503400410b03800f118040c0004400d100c00c101150b0008012103403102124821424000c4c2a6014401d040d140e101c242c2e48200300421816000760041c0c200c500c40140300003410030158881c0d041d20801030000540e8030401e00c1d8542540d10382441041c000e041d100c0e6041084104a103401c903a280d16070b00525482028030404d19800d42e0707a03d9689518141d000540c0000300d0358960206541e00d482c241410024024524080081000308041c6e6803200d03045001000c3d10b469400100340104501c41d42030b41080601080424060301020041000300107202030240254a80892052031909400c11400503a030100035852084e81d030034411605440c0d03a2000759aa13a1188080c900340c01c2002da000042246032904009844d0060080740c201880490715404145200040110111200320742c2d00c0b01c043c0d00703042001c85100c0c1401e000d04051 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 95406241 1250 95404991 95404997
    0x1401090905120a0507020a060f0e040203040512190306050f0d081b0313051905100f020c21160e0c0c1006030b25090902090f09090607021204080709020a 67
    0xa000c01d00e0700d24200c3e80c40000003001190000400004508142c11804020010380c81d09031a01c07000684000c02c3c03594240030040c401d5801001003014842d06018041142c0102c002040d40c03405002d004205804030b02090703002103032400000090908282d00182c04041d4001c014900002041d51191003070740100e251102040407180001e90356080c100003c040c052064003003242e603540340030f007004034055a03c1054440e03003045510400a0703031151411300c40014101d017405102019074a03022407906044007100c80d0311a980c04c10307030000021160746102c01c0160744c4065680403030f80a031070860488441d00c01c00280800701000140c40c84501e201620b090903091099078031210b000b0042c0019110940c20946030b02c0c40328410b201c00504104030729960205031040441001d08140e402420366020f0348070703009916030002000a0f150751000071160810400812001746414000c0180340d46400c2100d115015110b44c510450305160314400741c0f800c0352840001049018202034080300030703400c004045414 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 95407491 1250 95406241 95406253
    0x20319030b030624030118020d0f060603060507110c0108180a02030609030406020d17010909030c12020a0302010c0306051e03070f0602010b10110d140f041d01050102011401090905 79
    0xa40e42c080c000140610054650307450100c440302c6418100400d5800250b109a01d004140301000c240c1014071010280c0441d103044a42d00d9605040f85c50200c1c0c0752004081c0c52034103e0100810805030f020500a1015035a083c4d904410b107604196140c80000c2d5941c0851081c0340007400fa20349402c4164442100002a142481c94907404030f89040c0054a03108000e4202040601c20760741d040003100100c0001e407620605546400030b400b0070142041c0980a40c81d503d400c0f50805260240d00320351010b80d44100842c0c11142140802900c91003003210880041d4242016811401e1190013620155500109240406445007240c0c05444840350348040e01402120400105810030044501c01400c045c1c0021841d9442c500c20042a81711120080060054100c00610224000518164070b42d0403030a00149850b400031400d0810b02407203020001c946d2002a000c0b0b410542414800f4070040c0030703030007040d0702d03600d5000581c240d1701c1e00780f11000c40801d44801005804c80d039811540d6050700980c251b0361 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 95408741 1250 95407491 95407511
    0x603040b250207031403130605130b07030512070e0a05090a090812090705060406050316020a1709120102030115050a0314070c02010f030c02030409110f07030c020a1502031903 77
    0x1e000301c00c001c0c040540c0201e40200700744140c242008203c01c0b01c4402541ca02181052149001500b40c0540c0041100c080381310940c5400000300480a80040968180c60312407030b00c0c1c018003aa126502c00c0c000005100045580180144441140e8442c0241020007003810702081c0a4003141c010401203078a81c89000d41c9011412000003440d00e00018243c10f8210301d4960007040c80c2c12907a9000c81d0295a041004001c0e80358080c007540d4000f105103600380c02256409608914188030a14090f064046c0c1c018400c04103101c4038000c04158a040c1c402500c0c09480080d15800c03400240300705140102032010400390310b40700300700804031251541000141500041e201102d0304104844103400318107907010700002e560300034041e0500102d0342d01e000d112858202c04025164021880350805c41c680b52805040e08001d08000c1c1c9001100740f140bc10380311081403d0081c42d101a41c001a4010a210400415200c058078407101008009400862600000c0603200000d103521084075007c050381c80c01418 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 95409991 1250 95408741 95408791
    0x3020a050f120615030c070308090c0306100609081b0f060d11070605060904051209210601090e030406090e180f06060f0a030f0b1f0801140c0403020603040b 69
    0x500d080941041d082c1500e0544148802e800c80060070680e50032082c4200305e005801e10080701c240a92600e8003c015844030b03400a0324001401200a41c50b0044000b0001c501403034518520444010340d07560000c1d91340d2002000d4035140182d041801d0344140708207000041c2444c0e4a0000d00c0c00c1d01500c00b81c81c0c0100110040d0071241404d808250340d0f040000c5c09014060329001c0ca40d080340701180c00506509080d69117669070704021500e200d1085002c03e810704d0075a00d0030300d41002e940c062a1104d0038181c6540d0010b45030b4209025084045141202c48140c00c00d001040c2e9003903400c242c070f401420b5400c225510a120ba0010300e140c4142104142c1d0400380358061100b0600705064030014105400d0440030410358003c40818940549080402007002c500a0030041c09016002504603030f25482c0c2c0300c00107250010104d44000b404808110000b103485c015170001401c0d401d400b0310a42241c0750100b21403980d200314070010754098428804900410680d072081074001c1101c414800d219220071000f0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 95411241 1250 95409991 95409997
    0x6040326070503031902030114090414070f030b07030608060f06041503060203070909110a050c030d05010f060809011b030e0114070302070203010b030f0d0c030c0c030602041508010501020d03020a050f 88
    0x441d0b06400102c203105900400301c40464401c5881a4194155810240c01c0b01c8214003551401c0d00c500f42881c003140500030100c000551b00e074940000d450026403030756098240d120007071104580e41d042620003d10b1040c804e10803241500c103140042c2c43e50f51101c404200800c400a01190742c00f698445503d00250385a805c90401548503540140c0c90740341940010b0706080c0302d40c2c000b11b01917003070a2020046011000480d070380fa14803800c0064440100000242c5180070740d00b84080c01c1c40c0317010000300d4124642402d04040fa5080c0e40d5044450b621070803400d02fa00c0e0070b0b400c12419041d5507003440300e400d40170360020043d0a40a400001d445542c070755510200c01000c2c0c0355080420f03800681d900660600f03010f000da15200a1380140301c03141402000329a80c03000802c244040203c40f1445108042c0b042c40c00d18003040d08143d0780d40b55252a420000b00941c09441418250f0303401e11241140c4a004103d080c3c1210700580280c225000c81703101c290041d502020b8010200035040103500a1002884d0107 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 95412491 1250 95411241 95411243
    0x8070806090d2d08070e01030e190807060e060108120c060c030901021309150f0302090705030415050a0516030b0307030605100803040b0405040e03030408040b0702120d020114010506090604032607 86
    0x113041d0190400b000054202c01c1d490480314101420840c85814510340082c003400416038421286580c020300b4108002c0e02d01480303000402050510081c5450b842c1c000550764140d42e02142510980131038070303202144601c070b204801001d6801040c0060008040724020399840000d080002d481e04280314148003101c05150800b08085985003020f054100703503180031030040e0071581c41d0003a040b07040d500001c40c240c1c00140b4400070800b000000a080111a00b101a00803031840c03420700c070a040c84d451510140c071085030115400000c29a403442824803a0164202407800a4050600c682c1551100c20103418000d000d611040d041e10400500c030041000108020070420300e085480314100340c200800c1c0c0c0d80c60081c0703074220b500500a110209040a080301c080703070805a44035a030f0701d003e031000c0340f40c040780410780d151b1601030f184081280a406401595400245080e50207850780c0751401c0010f036001e05008160042418041400090303068160101c2c0600a40020800301c0c90b10b0b04240c08507401190 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 95413741 1250 95412491 95412497
    0x4021608031e160203250c03150b18040b04060608070b0702040f0506011d0102070b0307080603120c0a0308060d05190c0f03030509040b0a0902040f08070806090d2d 72
    0x40401102804800b0041d00311810112401028072083e4000790359000f9905100254184100e068208100484030000035943c48031041840343d542c0e0405007141050341000d114003030304000c0640460700d42200c0c080c08008240300028131544490301d4032911814010800c80b0943d5803840d0114144e141007200034000c10075a00d07801d545480510500040d260101203024140e8140000d0110b56078002d12640040b0800042d402c46502c1c2503c0100d103000c1096001d140544400000c1c1322405601c48000c074030851094080343d601080701043d540c1c1038451402520f00503000030b101c01002a208440305070b00071b140102400400402915054100f03449545800088000881c0b041c08000c1d51010b428001c003071211900c0c10f61b601d561801b420314443c040f11288240e41e6540207032181d42d541d56880300900f0340f01c54110346a948074060880030b04114000c200c00d621480400054405002504522a40c130b02c00c0507220a209805044e2501d0650590ba0044210030350304000300301c04502003484d00100340381c0e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 95414991 1250 95413741 95413771
    0x3030c01020901110a020a05060304032c011e050a12020405060a050c0d020105040f080c010e07090606030b030a0818010c0602121006020312070813020613090501060804050a020402160803 82
    0x100014002e07414040381e43c1c0356034000a185e1009031b03440304031260840d0b0082d102c4c03540c0c9076140d14048a503003140c00181341d52441040040950b206148070f02111224080e203919081c0c125480c2e076510203243c4041542e000800400c00380081620841c100c80c1030000c011030244c03c01c0d49460000da01600040c80120019030b0114a00ca09184c6c1000715242c4510180005c20140c01c141c1c40d104540c405082010f00f88001c00103180200e00c00c03d5005e0a08820aa070544c0d0005450380140c0c2d0240055208000009003000a0061103140102d480c101c840c1d404511640b07402d403406258059807001c90100c40c140400500300d500070070130600040084104442d01c1021234a088003640c00210805e070444000c661081c80300c580c082600b43c203402d810051038100708038295103009140e29100600e2000a42000003c10a60110b80c6451009001d44840110500c004d0f07803980012074510f030342118040c00d0796004a01030030160600c2d500618580d003080c40003e020003500e44642e562640141c1d4500e040040301 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 95416241 1250 95414991 95415007
    0xc03020d0207081e03010303140a050d1d060a1406040f0b0607030305091011031f080a0f0b06030c01120c030b04020705100f0209010905150405041b08070905090408030a060503030c0102 81
    0x740c0704201e102d4071310003500c60440d411510300034000d08071074102100454000440b401c805005205559000c912032200f44003245100039025114003000411a0443c480c4c000400c0110081c1e006180b000a41c0410790041640c9490402014002041c006110340f90b9a0641d46441c0c3c440700001c02c03903180642c80216450034810111880c2c520303032000359018246008500c003100c1c194201265004040c0b0345601445003149421400003c3c0640e01c030317080300e1003050160000c0060f6554038814850190100f0312660b9109014103448200c0704015078001040030196024000160b0300959075801c80d40790004049800e02e010500305e0340a00403e9805604c071105100180301c0502800c84103001001d0b056080c21000310020380902201d0103900e1280c48103c50003481e400340f134801c0d10b00610000b00f06100901c505645242c4a074020800342d00000c03441e10000b61041d0044141004480000e0401c11651f0394549030121036030805001c031030003c6c0e00d421002030303030751340801c041e1800700600c5000517551984 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 95417491 1250 95416241 95416267
    0xb1e0c1c0204150c020a0b03090109140106080a03050d06120c03050f0c01080105041d03030a0507110a030203070303051f0806010f0501110606060306010c0f0c06121505040c03020d020708 82
    0x80c0c01000300c011401007000f803108440b00b2640c501910300078180341070384003420f100082c010a030070381010082d0103011082220109054001e81e0400d4029103924081d41c00c903044044c207030780503402902c01950000b2921000a40b00e000100350f414281600095006d440b25104103001c1c09520064905901924051052100503c502800c50041c0001005015105000030b00703502c105125217407046030740c0c5207032140d40c290100914501c0300f10101900d90300c0c0351240c00c810040100b40c608000140304044d40c1217080000040b8590701a1705500214105901e90741e085010342401800c4032040c0c22090000c0a1461008070900701070100000500007a41c14030032100c45006040d0701190421144007040012841e01290254120200f95615070b076075901c0c2001a40d101d4200d4100400820901c0801c0c1d09002803110100245c452607a144240d10100884bd54180c4416a54400100c4c500040410951034160f01c025041829070070090b040100346d083c08000c0740c124650586107008006600d96031841 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 95418741 1250 95417491 95417527
    0xc081005070503100312090b070602070b0f010b030a36050d090f170a08030f04030912030f030e19200402251a1303030c02060106020a0b1e0c 62
    0x290b4a841811840c00c21205034404ea01d510014100f10705001001d811640b04428001c05001900340075555a459860000000c0d40000c00c10b4885000000200f0381d2640200d60a50480b5480c1c0116802c6131104803410000300145016242c0c0b07115405045248012410080d0610b00c820080b6201407240c0d0b418231508011100050804010008406110a07038a0014480941d02c0002030b60b2900245001400d01d070245426011703140740c1000c410080f0500c04e0500d4280318503c0307030f034810100541c1c03a03801011680a4920003030100d625500c21900041c800d902c03900c0203400e09021295003040d010b90000703003074039001025580d882c1003c041482400b280360450441741c80a403030031480c0c21842100822076940c00794401ca0304c4401c0899540500807180e000440d8486d10b150040520f0415820030070124800900c2200440d05020305000410300100c0c41c03a049808940240c848440d181e074980f03154807002030441c40104180802c4800c0e03a5400c0c1c0303049100302c00e0f6181c25a0f44440740d140d8a18495 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 95419991 1250 95418741 95418751
    0x221060102010b040b0d081b031902150709090207020a03060c0504031a04020102060103031d1302040303031a0a060f1214100905100902030405010b040f0506041109060307050c0a0c081005 82
    0xd0805c00c00d040d964441c05501e5240700d800c85e5000d40c403600510510503c205160f101e5034520f10000c285400a01c0040202c5420380d0002d40880315a45117800240b55250030807203080010402e006000c211035071168000f821441c0c8000c00320180585c076030362848100c1c0c6240f00c01000081000c41d082c810400d038030364010380070826000401e1107031425a0000b0b55610050200404100d9441d201200810041100c0700c001200200f4521400c0301e80c01181000750003500c800d0300040c0c00c000c425000020b40d0521052004000b8011004181c2814419079000e49085111802c02c2401032440340140020304c03030312110401072110508141000c1c164128030103a00d40141d01030910f40b10038814841046084c2404841d00c0c45c03070144c1c4a940b942052401041b4071403510307400030304040c24600008000c0d07014078401e0008490030010040004400391242c022500344035040700c000c00102d0390721405036019100000c2200c00711001d2403a2580c0308884c1d00a5070307015501e2070340302050036850583c00e801055400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 95421241 1250 95419991 95419999
    0xc0305130b03090c04050c07030e0109080f0d08180a030809070906030503040806010501020d080a05040804150f091401020304121113020301080114060f010f02030d06060e0a050603010305120c010221060102010b 92
    0x190030880c620607d140303d015401018030507582118605039000da0a8070000b0140c241c00d48200e11180c000564440c0400311034400084c0803440001c41031451a0860302c46019204003c1038800c1e04c913507040c0c030299000b405100b1240300c2d0300302c0056281e11501544010318441e4006c0d6031a0381c07030070480f80d00e40241030300000d05640103081d0b900c407040c0d482000258003d1900f94081210788403414601594030843d009052000602a01810082d41001216880302010b503104181c0079070b031300386142009000c0400d042c01070b0402c020030005401860940004203009091410300d176440f08001030b080b4925074041a0703040e5004001000303645070a02c00ca05a01340c80083d42070b0245800380000d41441c2c501d2400c0c038184401454001207403071003002a1681d5415240c0100111134448001a06e214101c5019510a8400003800718107130900c5815030f812694080010032a00d240054800e20640107441c1c64481503501380000d02200e49a0003500b000d114002c004940941030040009095400340c004032805 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 95422491 1250 95421241 95421251
    0x80c0607080f04060f020403060207050d11160e0910020703021b010302160206031e09161a0405060318070b120f0402010e040b0310050c0307121107030c0305130b03090c04 75
    0x8195011058543d1042e84400d0009031301c001140c1180080c01282c102420f99480407542d10200600010382c100e140702151140c0c80343c00311a00c034242d62010a03a004805000c05980300b00010a811004030350403084031000d17101c5080d80102d48100f01c0c0c00c401410343c0160b200e2980c10060b45c0c01c01d0701c2e4040611007841c0552600d09400b0104001340324485009004900c0000001c643c91241c0000355a118194511002141050700c021a9510045015010b03506441000043c045d108038000c0342681e80540c0074142441d24040402601c0d0300010310750781c950780c1c5030714032040c1d905002d108a001408030f0420241e1620085040003101c10340040414601d00030704810320001d81c1e0807018414a845080701c02040b6803040360042400c0c98050b070f0030790354558102401c1c401c42c0c801000c0510b20540050b0707589540c5211401d10442500c440e01d0707001c3c0402408202d00e00119209902c4820520300030b050281c40c0c5a241c4a0380300d40704c0038075070240c80303024001300601000c1c1d0003d005941591004544c1800 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 95423741 1250 95422491 95422501
    0xc1c0c0e010f0e040f1502090102100218012304090617010c0210050606040e04060b100810050f0409080c06010303030b0607020f090a140703020319050c091e03010603080c060708 78
    0x7000c4031860240d444280494000207007081445402c1024259100c500e010440c100e0b01e0346c420182d0403200c40180940108001d007120103010380700f03659130042c110744a0000c80307140700700548025007120f01d41d00854032002154200341040703800420040c0144440054824503007480002072042c03030398403079801e0f904107111075091650004801000141008001030307161240b10000d00180b0440d809000072480810800080c48215407000c5202203094906e10b0004860120442e18840115290300b19a03074141020300140c10284090313852184054800a0055000d86440c5074503048441a4130f01680000d006000301549030003a24008071f815102142042415400a001e403c01441164021042a0001038451b802e0790842c031141034410815035a0750800c40300080c0031b17520480704003101c41075982548190b0303000c51007210301c51103114403007508004064080020644912203010340706081a179070a000b9503000e00c1034000a504c5a0f60203999440b400b42000c2c10008024503810600070a40100302c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 95424991 1250 95423741 95423759
    0x50913030e12101a13090c06090f030f03030f050f07090503030f1c1d07060e06040b030a050406290918060103080c01091208010e0604050403021b01020c1c0c0e01 71
    0x203518500040f40030412213604407070198041d086042c0a40d02c558400740016100d036044e03000010303890068040300780c5161a150f050f80e58007514896110010286e0108102041240311074440482c443c0c940814089000322841d0280c8400307603003501c4001c070941705008402e50400356040041800741c0255003040d40e00984600c05000d041100c0004040405444070326036502c2d81b2024503940008a09030070389950b0328006549071014000d40c2c1c0810b914040601d1b8601e810302c1901c04954503032070080c0c42d40d522403091074050940540103cad002074a4008201c070140314a4401201c42d4107100c00c81d2003950202d030070014031900107410b880344850200135640a202c40860454107480e085042c3e00ea0350900f265065005200030100503111074045411070801550100b0158126041c8003280405a11018200021100c0c292002000350740300354954810070b02c1042c000030800130140181c0700e402110307101044142d1a08025400455000c03d0303d407040102d61150040a000c0c00304072105250704280801c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 95426241 1250 95424991 95425003
    0x1e090f010c0b01060c03110102031f06030e030f070f0c03080910090f03030806030a05010c03020a090602240a020f03040501051f0602030a0c080922060b0a0e09060102010204050913030e12 82
    0x410030415105c090a045c540200c02104055485400031582c03464000740c105090507244050000b008104000050024070902804403042600b030f024600e0f1200d139181c522584d0f44070712011540080da8007030003030100710b104801d80021405903040b1130342ca00f44a0100107000301c01003a0707542886480c501c00d1101040d9041d0800a40e035050800354800d85815000929007070060000600b40d40c20f103892480a04d5060300505081c40050316003d01032510b503281030341c03a9000c605a031a000d003220000000c0c152070480d01d080d00004941c10052030140c04144c110029030045909a510ba0746071000e101c4282e034444c0c010f00200c001290081c0c80c0310309002c0025201c2c4a911716120030403052541c00c1050050000860f280a034000b001c01c1e00c02032210144002440d09001c1199140340b03004e00c0011082c4042c000c640c129120340c1e407403544184d4904100541c510000d00058115942880085965254411711900030111a40b1044503c00c841c07030010691102206c445000340d10004000d90039800001e05 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 95427491 1250 95426241 95426249
    0x60b04120f080c0303070903020906180a05061201020c03040e010e0606031602030417060414030c0304090216060603081207020d080a020705010b090703090302070f0303020a171e090f010c0b01 84
    0x1110360124240c00c0c002d0301d034028031511203182d000010030301a04542145200040302d10985500c00c8079590082000407019100c00c4882c5080b04040c000b81c0600304503445130383d00c414000d06110701050b03284201400ca800c402841d40c50f9078000201800000383e0010b2681c01401c0110628009142c4680820442d01010f4070784803644440d0401c0032000ca009000355170140c2503004480703500244c0d542d12665100d0b4195420b032807a150b50541503000c40300100881b40c0354440c0c40001c0d8035151414400d04025442074503040303207030501046198000303080b5005480080d40615100c94455402101d00c40141c08003401c2d002c15035128600140c0290b030400305441c2d21140002005071070300c51908100c0c1c00f50401c070115030b900410f01c070100312a050b0513510480720180030313508076013000e51100d8415100e0800c5000c0a40964068209140002c0800c1000c4a20101702e400560605003142c3d843c118881840b000d4251450010a0602030307400c042042c0070540720240382003080640182c0b9070f001102410f0007 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 95428741 1250 95427491 95427503
    0x801110703140307090b131805070e0d03030603120201090c060c0203150c1603050327030d090c08120a0f051c050c120a0b010906050a12050601090305030a080604060b0412 75
    0x300251204c0d0007070060800400f0801d1015540381650151981303001c0445c041d145d51003000403d00c0c041c5032014444d161042e40c1c982c444a409644d00d504010408038a03140440c105529010003000181c0091601c40c00010640c0002c9a01e031300e646010105c40b4080e0f0014010043c0008062026a03000504125411088200080d05444e120341c2c2c0c03079075445000609002d00d1304600c0e61200701603000c00218440c0c56412080c40750020f107244008100001916042101d034410301c00208984095030010121a01c200c0445880943c0c0b449401e0074240b010100c00000350700030890310143c980207400315100c0d80c490300e001031501c0c200d003c0d5030642c043d00c0e15610b44002d60325400070b4480503946048920044c1c00c003008100780c4c80e2500d403132405000042001c5001510a1500141107030041050340d41d030b9503041d282c3e804102c0e80400d8000c010710b001004c050400c000c5600000100304144014032640911750303150b1130185010028041074035055440f1404601080000704540c544c0d2661030841203601203 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 95429991 1250 95428741 95428747
    0xa05180601140f03070e1c05100b010203040312020c03061509070e060f130504140405150702010b1002060a05010f0501090e0a0b19090c020c0a052404060504080111070314 75
    0x8082d1100740182d41a45441d99000402d02c0312540e007000580402c0c443c112125101c008102481c0480340d10060001051b56005903074408040841c0e0300300c07840081042c4101c9080aa4986540301960507003160040503070407078003010f0b2450806000441d44101110b024412926800c40071506100d00105424100301403072000c0d44096940100300d89a038003078a0798494503203c644459400d92202c6102c0d8522461400c041d14800644050030140b050350410701909078503282990a0b250100020208800c6550740c0d85140c170380e42d40c2d2245900003606540c0c000c0031030b81b80c8510340e101120301c1a001003a05001e0100c0c1080700760f84c412401000c1c2c0e201e0b502c140d07200d500e4056048002d4040f030320718250305c034240c02c0c000c03581c500302b4407000401c4404500c5c06111001e003140e001d980b20701112100c2071b000020b49905200034141500e20104c0d10a0340028080c3c41b07001203181200035080703900700e4000144000707800c00c0100340c2402684c4800c000041120702e00310683e0b501400317200081e03030060700000005c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 95431241 1250 95429991 95430017
    0xd020309010f12140709060207080f0c0d0501060801021801111506011d040507031e020403230f0a0605060316300609030203070b0a150513021b0109020a05180601 71
    0x580251300321129005006585041c0b1003405041040035005840c014461007200180340040003c5144a510742000a8400211180140088115414801d4880750349589002440100900c02400d650301501340c6c401182e941000010316210134860754814550001078210002c2c000d504910790030a0342402c01c0509240000d001701740c4895214280d0b50701c54904001c000f56150590826248901c0c801e48810540d820314014501700d0250340000303081c48110000140368175080001c5d0742288505281150240b0400d4080c251400d030700500f080310300585903c00d1020b0f5040c1040006690600d403c0c007100c1c002c0c04d1051341d5101e00b00c05d505040b0780c00318140c0b091840e40b1202c4102c1c0e030043c0e042441400000a0f5041c040d640354049141120310300c000c03000049424002d03104038809042c1402e00d000c04285002c0400508042004e0800943d55080000000814442d4107074000c0c1000d01002003036201c154010003890741c030141d010f540501c08030045c2c4d09000c078800050540c045001d00740755a4045071 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 95432491 1250 95431241 95431277
    0x31908070201090203011d0601060f0516020a03200405070c02031209150406051c09021804020325030501050906060901030308040f0f110f030102040506070f020414010608090d020309010f 82
    0x40c400c045c0d00f5528200044041051745100f110b14100100b00315041a40c0c3c846080380c1c41401c4212442c00164103101c14084000c203401c0062145000801690385e094407034440400f03041c0401c00e52108411018100026170500d4040e60340c2c0003034130b410440032600c15500401d889812030340c104c0404800024444000740d07148141900420540f481036074445807540702c042c020354005261105418a10004200c0a00d2140a001d0350b15a01400801c04801e0032811203450b018041d10803030f0305008151848003400e0030104c90600320700552500c4001c0f2491402c00c6801c403034010700f045010741c00010411407140c48003040c0b80d045a0741482d02c0e01c09030341d41e03040040469009400051150360600000402d0003404e103900c4407040c81c201c5a004212880004140c01c0744110310480d0b80028092001070041504d20603020b1081c2d0001c0c04c049843c13411219075941c00e450981200e0040ba00c034000b8440d02d03110070400b8100d500b8103070004501c3c0042490001e028460001c1002041148408000503c424 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 95433741 1250 95432491 95432501
    0x5030907030611070311071805091005070203070b0a0504170a1407080304050d0c0c0902090103020c07030b010617010509040807021309140c09040c05041d070b0304020f03031908070201 81
    0x90042c1e820842d070f120021054840381d029801c02d030005050740780790030342c100350124000c030072985140c40c0d0941d614000e96006014120041c41901d0901504a200707a0300c20050148500c0780b007081c0d001c2c0d40d95100c2807500d030b1100b80e000380582e01c2c0e052403e410040000c0305904243d60b184807449401d130300c07031042c0c0008407011007815210400700c0c0404961001042400c402540c0154400d001360780b4070945d080e0b800c861032030800708003602d101a000070801030300200b680103000d00d20040c075015142c6800b00d281149040c08580c0222620b400b0700740100521b691001000340202e1040030304400c6035141c000000e030203440c0a40054842700d00001d00c50115030780c407105150084165541404100c009040034084003100181d01e81c02805101c00500c0645054040c3c0c6104990011141d5030942c14a8180401400c2c2e10031648040d80c1c00500d40100f01004010003002410b154460a55a1906205000c41d90781d00c0c00a26009501c10300413800d180c7c00c000000109111039180c45a001d0b03941c050100d01500e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 95434991 1250 95433741 95433743
    0x3090d0e03160909140102070210080601020a050a0b090c01140706020d06090906290102101d03040311010306050409120825030906050c0304050d050a1e0201020306010212041202010503090703 84
    0xd030300c042c0083c604441e9007140503020300400e26640c070f05100c0e0b90310070300741d00c90358034002d510030b44001015050a00903124107410400605c12904000d059540c0ca0b0b280258030082030f644403201d03008110344980108030201302c40701e00786082842c040c07106840c240e50340030340c1c40300415641d0081501440c1c400390b9480030f0014207034494140500303002030800a0042064041c07200c2020301543e045810106525031a0020078413707402060801c4001c49031100500c03100001d000819462190000032140c00c0020300003031400b07600c1070109908600000340485100c1d521050180b8180350080700819820052030000180605041c3c8195461940254203030f26405a0412509002d0710710390140d56042c0d000000701031142e07170308120b50b889020400000740022074000b4010b500a02200701c000f449000507143c0012181414801a00c0b12000d800c0006e00d00c0001000603035010041041d99030307041090b8140042c03000e070300b5850282080c1d07a101c011150b008010781408000000720741c042c1d5007003007030300015 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 95436241 1250 95434991 95435023
    0x30213060c05010c050a090b03130503070803150108070819060b131d01050d08071506060305150406030305090111031207020102040e0f0c030a0903030b0904030e0406090203090d0e03 80
    0x400d440d044040c1c15425002000e991a40c44c0c001103020481c0283c040710302d0b00d070032a01c0320f04200b49040d41e1a10594002803242e01c403582e10305400000500c040010b464000d12503520301d42c6038038000703c1c849070a0f0048040f0340d0402604000340300a40d6081000c4941111564400d500170850309581e01c0c01400742d5510800c4041800509030903580d002d032021400b52101d01c1c280720b0301c5880800b0074405140d403e003d8580d201c0c01c121511000244208010044a84103841c0c0210045080024204443d860381c000c602107900d070002c1040104c104d501454903c10100c404000541c20f544006209001d000c00030350501a049980c4401c01000708160352841106880c409800d1070f0800c0b000b8040c1d00544113005181100c80003044800740e079014994882c0c021040404d0550f600c410301c0d80c02520310100140d06044e41d814075211251912030f81e05100c1d60117a2214640c00c24040244001c0700d40650003900d1349071052081c4804030701c000c039080c02c80913050f00e040b03018a102e50001904001c0b105080c0b4102c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 95437491 1250 95436241 95436277
    0x8030d060333090f021207080c030105010b04052403090313050d0302070e19060305072c070c03051b061506070b0609070201020c1e011a010203030403200f160f030201021504030302 79
    0x61b400c0d000a451058409400c00c0d07600c01c9182d40c007850300741c0b03c0a01642608580503c4140201d05004c0c1c00841000c2507805218148110894610710550042d2111681a00300191030340a140b000c40c2202e000303010586114001011300c0d1002900c440c40c0d4000c020000711047c0100d42c2a050036244c005c410f4084220410810703a5900c0e000340c0d11342c031034402c0d4082100e80700c14451440803681c1c1d51000114580c11040301c640ea031010b040342c00203120724048041c05400d002d8600c02c0c82c0140751a4400f50141d900500e0079040101c5201c81d444444c43d5580d104100c2000b03c4000940d81c40c4d44160800410340300c00f43e041d10f41002c160301a0042c02c145410354030a224111041c0d800d4118061002d145120003080b5402d0403100c400140c80c0180c12441c090303882000410006440750790b4684540311a00c116203206054461401e040030744124458650f54489a142d11040b1102c0c05044000d01d00002110792451856001035110f0f0242c2c00211281003510001030f082c1400794040320221401d890052507 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 95438741 1250 95437491 95437519
    0x52d12010f090204060608010506071103161211060c030a0c080705190c060207060504050d020f03030a12060b0309190602090a030b04150b06180a08030d060333090f02 73
    0x1c05288106134881c0b820f103c4000350301409102c1a038141c07031300034000d5454605152580703100d0124910720540c043c4030f0034580c04d404500308002000a4081c040e0a50074500450030000392540c0f500c808a881140c0c100688040900004200d842410f140d00300154001810308190f9610b000d00200074025005175682d6000341e0521400440c2014803403540c0c80401526108103c0c0c1e598003a0040303d0100300d00304014031403450002c8800c02c560340300070305071003c0500c4000800e055070020300343c2c440410381e4640c2800d1000312078015000a0700101c500c040c15860845041a503964100381d01591030942e249115060141c2501120f10240b406000302410302d40c0c074500000404000c54064900260b4030008540c103000074000d210000c00010b2800d0304000030b820a070f541c001a00000c02d41d100104810000300b84100b40054100011a10300009126281d400c102600901403900e5001c3d80310741500480b101400c400128401030120600040d52407401d07d031200244540c000c010b9441108054842 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 95439991 1250 95438741 95438771
    0x2903010902060d0e0f0102120a2a050310060203070203280b0403050301050909060402100509061c091a091b0a09050906041b0605070f0302010b060d0f0501052d1201 72
    0x40b4014121204503117010440241031800c0780224040c55542811501c0841c0c0e5000f019080041c0000c180422007104921202054080211140344100803a8000c01000700e280450007841c3c00406003400614034001195000980740c514811040c5211160742100c151400c0c11080404d401c039a00090401d1607013030500300034219400900c14248035501d04000a00321400c040341c10340c05194003514849a10424030307030030f98240e0047c42180d600142c0c1400f03a005159035000241c11148400680000c1840560800da000d9107200c9030703842041310000d020f0000c4a0381c002501c000761801090001c428074550740005210301c09039446044003a0a140500100c1640071820600071407154046d00003480c900e104040802c0d45510511000c100c040c0522400310740300e105880b052921901c000100542d64000150207508803c5164600c1c1e690f80758594126030083c800c450140504171106030b0600c0790040342c610085070340e200b41040e000184020003d0364a400c240300c030f0707107001d643e0090002880000a170 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 95441241 1250 95439991 95440001
    0x3070309050a03030b0405070c15051807060806030c0402040b040e1308030405030d0506150409020f04031202070f06030b0a03020103020703020109061a09011202060306061b120a02060a2903010902060d 88
    0x240c5c1b14a00d040003050159000d11380c0f84a49a07800010b103007100f880580448005c0c900142901101d90450303c1301c42c2c007000107000389405405180c40d540c40030708100c428540750901e43c0303c15a014610402c024001d81a4250607503084074801030080d1031542d00c8a20480c844804202e0040c900c2801000f80001c001d07000c4042c1901d01d01050f006c000a40c1c902c81040b48418903410f545900000802083c07141031000d400a10807014003021f10740c9815540d60318000224244124080141c01880041c441c14451000460060005140505c002041503002401c040401d1000906042e4009051000c0500039002007040380c0d042001000004203034100c10b55402a441800c620034001e0074000710303040184c0c1080d1805150003070050b90842d964007091101c13991080d5581c42075038905001d09035203580b04111340000a240c2e034510b10b80380c9000c4480640741400241800640c2d43c10000500703044046000e02c81c60940e441280d18006444210100c0d0043c645140041c1d0480400900c150090603d9009 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 95442491 1250 95441241 95441261
    0x3050a0f090e060411120405030a0f0306050a170f161401050c1203090712080703090623030a0b06040801020702010806010c11042a020a140d080c03070309050a0303 72
    0x14560080300a0030226006419800303400c1c148a02200800c8540c107181e80041d035803130340801c6114545094600741445080c400c650485555000185201c035156101403100601c40c200c2c1010b01c101814000003803005c2203180201c00030004280411011450100524076140703402009a41c410848800c0341c5241046034000c0c0c0c43c103981152801c1856512520480e1040421800901011400510140c1a0340d05c080c211011600c01d0382804240e00202c034044098640c03203a19080d550700802d140140008001c0d910000c02d00490302c509242000541e0744258886252075850ba40d269540040c05000b441000c0d28683c20034400700c2d011580d41015801880c0c1c00f030003601c1e841d100d80c0d00c10004440c03945598100504007041502d908042c0d0405411101140041402d4000c00451810510f107840b88500c03440340041e0b10141d0145c040c81a00d12282c0c040d801140003420b40c1e00c480c194090640e4170003400f00f40c14060000000340c42c42e403196001c60350481d070200546a5100440c14004d0103881c038424 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 95443741 1250 95442491 95442497
    0x20d0f0b031204260f1221040503070f03091205061014060f0f09040207030e1002030901050f0c15010308031006031b0c15050a0f0515060702090408070b0403050a 71
    0x102c8840b03007442400c1924100e4480440c1e070155080300d0251030b0011100c010805040d84100d241c5805486400d001007a45800b410300c0c200c2d00d0300c50220004041c4c04946c440128620382e12001d110201e00d001c8102c4810350340001002501044915040350041d407550320400c00c407401e0301c44800c1001000b2482d1401455071a080091540c0c40c2c07101d408500c6408000703950301110421440070b40088000260081e14001c60105080210509c085020fa0b40210421400902e090906020528048488081c49003291000b941451840710011700075105940000c0c18000002c41d4035a0300020170025084045403051204441d035a69144c810540c0c0c0043d51078407612001c40700046060346c400e124811244620b060242000c024118056840c401640020356100b03001e091076440404540c0107140c040c0401d42c0c0d000420050340000301c03080b5080070b881c000305e81c40341803d6441c6659a40b4103441580b501152400581e4640e4580200c262050440c0205140c0b02c030000c00c410f00d50800040c02986c90540c03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 95444991 1250 95443741 95443753
    0x5011a01020c0906010e0d0f0c0609060f020d08070309050319020303040203210d0509010f050709080714060301090203071106040503210613180609060209033d020d0f0b03 75
    0x40c08011100d002103904500054400d0065500e03494910701407191f0b0750260308200d404030a5502c90038501402c130740105001c40c0c0143c3d0108902584103101500c410b001e44058844002d803850028a0707681c015202604060310340d4080428402c091041381c180f920311361103036131a241405001070745a0300110303011f910a01860507880c1d140a44007180e07410038000403102c5071030140b045504d2402050702410482d940d44da82d051640710700c2014414039000e11034a460b44c01d522841c01f03c2091500a0f40d8003c0a5207506070003c60307105444031400e13241074035111240580c0702d58aa140032107030003e02e8803140246206103c10301c4140080803000b841c4680c030564407034802d11111041d5240f00c40c03041e9505500038609035402824501e05501154011802c21040c40d01003070036840313130000e070307044640300780d80099001550710042d24007009091944060840d500019a002c2c40400c44004c000025031031801d501c500c00d181d40e10f059a4111209100120000c010303048044506038024011600024001d100324 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 95446241 1250 95444991 95445013
    0x40b0712020f0d1a0901062307060903021c031a040e0307021c0209010b0309100504060e15090d140a03020d020f0d091401180311070812030a0c18091805011a0102 71
    0x1c5d0143c1030f00c2083d101c140002010164288620072030142d4611444003d00811b000110300740515030300603000f68010141003c056501c4944e042e0740c01840c8003030515107230061060300d800c2e100788403580808440019040501c1a4024114814503400139030141c072220306aa0303000081f10a040300540240d034107908a80c1c8a0420004920090741e000001d03600103d20124004d50342d800ca99403082c81b5a0003c9400e84440410601c5d02040042900d03035551444100030020b0010007a03071044810b01e19082410583c082404503d51042011141c01c05400141d081c81d003103402e03012036012440360791196980b0f8001140c84001000c05000840d810300100084d08078110301402041a0440004402003030000507580030786091110300a455814040d9080c002000b036401d0094050301132407844581d40e04e1038608440c00c129400c51001c0d07400e00580100950031340d82030004500c1590700d00900040c805480d40b4100b5281403540720010104d6007007111001030750741a03410213400c880c42038085400e020783d4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 95447491 1250 95446241 95446249
    0x50c0c0d020d02040207050c0a081e01180305070c0810090b0a09020f0d020a050402031312020d140c010209030109030e040b090f060906060721120203040b0712020f0d1a 74
    0xe8501942c03092019403100007514082e401000c031140708800b201d9581103000301081a400d1564082022900a8038412003045006900380c0421481680204440c9148904005122918200180820001143e50000c1101d404200005081084111289140d611032950003a082c1c40808640d040310003008203490751028001c5210281d8014031a000d6615400140b051307030610b4400a0b03901815010000038035449520080d40100c0341d14654a40402807410000d0a8071450880882194449001d003100541c3c007200c80e29402c803030032040755a1220040005070280c003038801d002e03a143d4688050042050b8100e82ca03c9011401510280220010441000740500d01120540c5c1c080300b5980015243d441d107007080a078001802044181403c86940354060040e402034403054158403141e40c42d002e640e400c1844a01000a8a40705610f10b1400b030351358440d110340c017a001c4001e005c2070062860040c0c015405030742503000d0300c601c1c45850701080403200b40903000c03d00701c1b032603000141c0040e0314003418 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 95448741 1250 95447491 95447509
    0x301060311031005040c030902090414010e0304060c08031506210a09050703020402070f0c0b0405090c160b04171c05010f0608150112021b10050709060809070306020406050c0c 77
    0x40c00c41d000140f420720300b00921003d48038400c244020165140242001a500c07042d43c0b50046009071404a0700d254104141400c44801030f0f41c421140d0304c2840b0410030b00e5446401640d000b40e0008449450b525414800510340109a094551006005c22400c10f03a00503040112520f0f0002c100d19003164a9940c43c2100f1900070b0078025206800c8001c040c0701509290b001800454440c00340b201d002d4841d030329174030701e50000c0760851040c5d40c1c0700080401481c940445c0c0c680d00540b17501e4940d0702d09042c00d902009881c8601c0c8004161080e1303e00000c003804035905009812003110301d007072a520b20220600c020007580c1041c428810501d810300101e40c44668403002c500f030b1006900e500c0700589070403105204d41481c8500090400550030340031400b1a185002400c14003540000089030030300c10310415820a25200b840d140c0e00c40ca0401003050030380d88411000102c401f1800e00d0100303500e850728001c1c245615070700042c000318000140042e40607032100007841d0361003807907003a121041d000d0700030403c0d202 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 95449991 1250 95448741 95448751
    0x1a1804020901060e033003010b2d0412020a0503030f0903071202090705030a020d0f060501030b011103040b07050f1509071203050406080604091a1503190303270503030106031103 78
    0x54042c14413070f003503c0020b41c502e400c01080c049040c8900030380d00c0f60006d22640240c1001d0048039001c100420910140c031103040c086190a16144090140240c10101a00070340c841d0380c41c0b440705442900d05544915100748003500c0040d099030780e5203040f0144d8502907030000d05050700074130030040d0014050f1611001c1d4030055900a11251054440f031100f16120703000504041c241d0b82d403c110008503400d80780310701540125000400300e0090320b00800581180d0388041542d06101e121070410011703000201c07c0341c0680341c150380c19680310394040c20058a0485a0f01c034000641c82440c000c03011f040d9046481900c00d003c000101c448143c0c44e200d06684002041c3c80040219100380800e000d02030040d090154070040c00b410004018000c0c0d15580c14504c0200f5510a16450000500c0514210500203c2401c00254014016113030101251010800092005010507582c1c481320550b44061090300015000b9885001214021504001d626a44207200c1c590102e403030254841204c4180c0340c1a64820 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 95451241 1250 95449991 95449993
    0x2010b060906130f030303060905150102070501110a06051f08030a0215042f030f0109080315011e090501020c01090e070804060f0e030d140c0d1a1804020901060e03 72
    0x78203080c00303111039a00015109001081600c0c030204038a41c40701d080c440114041e070750118000d0321b0410800200d4030081d0241030719805501d03003601580d03000240c00701215800e190560003007401004003404c00c1e0b1150704c0207098a0078501480031030540b05008204c030422010024030102c0d55890126a40c1c8200319031040036822901000c00304d030442020041c2e2050058007140d020600c009007040000c100034400028240326207800d144036003020003a6201299100008020004007521500c0040c000107040c0400d00344c018503001d41036480b0300c0141540e646001c81da00c07804100220050405141c901925005201d1201801c9031988503005050403121174101c01c92054461343c00443c1c52030002042900d00c4c0ba21046601000788291146080a00c0c210300516100d0300b10a00d08402d0f540d03000c4030441c40842c0301c400d0200c0d07601800c0071a01d075241c0804000403544000601d070f5404d0180020215131001b56407010402c0c41e1180700b500c500c22442101d80d25116171325854140c0c0d40c84842a020703a01 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 95452491 1250 95451241 95451247
    0x7110405130f0303060518070801050901050109090e10060b04031506030b0f0405010e07080c01020f07030c0509070e04110a08090a120507050a1e0c0801020a0807050d0e0d0e0f0102010b06 82
    0x2040c090b07900740d40c6490291401080d229222404140d0140078101c002c210584008108208658452000e070b02409080b02c0d6075019514010000f40184141c1c080c20010b81e6642c4a8035004820401015071840845401807001c039035a410509199005403100b512150f1081110044403d0076200b4101074a42c04094600c0303980303821640c11080c120040c812101e5640e500c13000c0030550300030008000204600c070018414a041d4600090919180c03170b2840455920090082c400500d40c05126001c0d0742d0151a00100c40d40d4112040381e03004120114550840d2400c960380340d0409200c002032038450203c0c0c6820910340c2301c4280490b62120031403005012000891110b01c1018441c0c001403502c035019408480c5410080e44824103035000040d940ca405209114540c010881c540041c00004d22a520085051000040c0054220760009001004004000644071543c030903d41c08084c042c80844200c1c1e0182d1109800074140f00e003a50302c280d100d2264180c04558030762050051070003090001c0e051a003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 95453741 1250 95452491 95452493
    0x3081e07081207031e0506040c03091e050319020102040e1303080433090501050601020610060e0d06020c070602210d090503091314010e06010e0d0c0504110711040513 73
    0x381c1ea8400f800d50010552030702403114250142080038010f12081c0c2e4000a8942040c0c410403040320598410b910902d4140086080460502c03455841c403031585541d5903459441c249402c40c107502c135004011849609107030007460340c160705601070030603515103034050483c60711030803070328046100768a0005001850410002d00000c0040b035072055208410302507a00039403400764140c3d119075004941d6495880c1e5401306041401424010b5640000080c0083d00d506d00b000e049090a400850084406100c5200040410341e180c15140b02d1200e80c00c440d045403601c0701410708030b450741003030b100c0da0006119211142c1e851440150100c100e885014070302c28a06405800400081e200111041c0c0d80303400103002d40622910b40400e00381440202850000d418050f20426901c00d90042c1c1040186090503020005142d03003010103640c031018111030319403c00403039117042e102849403904516042820100e1007101510484050302265200e00718a8002c0c40c100b4060000322001100e202903d81d400d40d980320 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 95454991 1250 95453741 95453767
    0x70f0308270d0f0908100b19080303010b03070215040615050105040b040e04020409050a05070608090606010503240312070203010e011104151202030f160306080d050d0608060103081e0708 82
    0x30a010360f407030500c0001d2569400d8081d003004421541100242d4a80402d1902d6241660b0040fa5203001c0185051802c1d0501c4192917407400140120420113000001081c030b5903001b0132000220000c461802640c61a03d881c000010b480441d40d42640b00f250058013169070340c01403080e40c050740c07550000c1e00c0c1071901c0e041503250b022001601c20b0742c11558907003281000c250140300f40b0211601807001840f4441c50080028060440127105001d517410030700902c140c607a480012260800d482070640030118205055050705a0030000460b40c0c035204411492400b00f60361005071030560f000f1402007207204404200f0314241d40c0f06049114000d14200014446008080b003500128103440c9042114502c0c00500385040f41d01c29283c1440004001003005014000c51090b1009044207240900045141c4150255100e034421a91304c02d004011581d101904890307032000307004000510480c4c0903544c0d80c2c1420070080d840001c3c1d01010b401d42c02c000c11a00d48170103003281ca41d15440040310345003d030490400 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 95456241 1250 95454991 95455007
    0x2030303070f1106160906030b0307140111070305060a0b0307080601060507051c03050114030c09041e0f08090307051f14040909030f0f03090f020d08070f0308270d 72
    0x580601c4140c1ea8034484014007080805c0c4504441d4a224031448520f07440034060441d2680000c1c105404c2c40e40116094078003080c0802141c203814000c00c8040b0480b401a81d090040d00b0318200184541c030000414442c000601901070003000004100904020341455241c0e40680115040e43e0b11017001000042c0c030880c0209003039809801641c404a60300750000c00c04860b144000300010382c4400050084034500404042e031410110018000c05c1400b4001c00c1806200900c061b00c111081d00844694190802c40800303e03036405481048110100e15010210340c000102d0a4028400da507008038441c204944002c5522a80c0041181134002400c1c0889211800100f508906101130100241e003100a0055810840c0300340c80d905030030080c080700145044a03140e2103200301801c042c440307004605100c01d908500398041d215640d010b0210f00740b0b0304041c8201180103090039218a040390600d9030000c0c2150150f00c21907000d00490f01001d802440841c000720504503560404040d03206406d0282001c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 95457491 1250 95456241 95456267
    0x1e050114040c08100507020c100207090e1501080c0d060213030b07110d0f0c0204111207051209031e070212030c07030302011d0312041e0609030305060d0203030307 72
    0x410855040c020509501a094408840d11011884103000000f800d22a0401411a150041181d8a80b00d070000b95602a62400680200092424460618805d11800025000c000b00911040e88004081d076074405100d203078410041c1e0f2084c004501001d0201c2d01040840e07005100b01d070449607545400c1d00039070203003a07446180712980304004009006004403a00c00c25683c5c880012804540350080d08281500180004004200394282440b54004a6a040d5503405407000140540b0108040c0000e100b03510704c04106084050030800000c3d88407000f02038a452062034070030a03403290201659240140ba1507900b440ca401510182d050720300030040c040c00c500040a41810160300568117017960701400346400550841c074014070a16409004422005044d013184170300c02c8100d09221b80d1070740540050780d184640c2500119092081210101c6024201e180794030b440c0e00b40c141741502c0201068041200440c2c03c00c3c000425078503105068240c8160040d002e185155034080c000c40d45031100400d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 95458741 1250 95457491 95457493
    0x801051e090106050325080c0d06080102040b030907080d050a050c0307021e03011a060702150d020f0a090603090320010e061f0f23010504030203010e060103030909091e05 75
    0x4852081d58a014626000b0401503c5580c3e41c0d0512084c00c000c00045010341c5511814801842c12019a01119080d0f200c00744112541c3c0312000354110704040e1840f603004000c02e41c00450041000c0c036440c0015400340314000101c603200d559075006a0780720b01c24800711502040d0140000361015001e034000340010810841500d103051200c0d40050055821034011040c45400c115244216080c00d00c0f580541d110702c0c203420f071260142c0781b0000b12540f150400c000e000ba810000003000348414070342561012060500c055460f07403241c078408409500b00c1c00524000030101000040c0d514001c0c4550842035030107643d010550b1240f00301c240320310400c002c0d0803182c542d03a60301e04948082c401e10184d030041c0800550244000c6d120405e120030034031705800010903076000007001c1202a9a40384940d5151084d14000300c5807219160059602d4095940701039015402c1c4100400c0d10007010824034141ca10a45400203419201e440c0d0900311090b5980c000c1440c09034260300783c6040d270584060342005110740 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 95459991 1250 95458741 95458789
    0x402040302060c060601030b0409021c030207150c030f080108030a0e01050c03041e0b192a06050a05090c010f05030c070614040b07080408090d03020708060115030e010903080105 78
    0x75000c14015800ba003030954850f000790061108960340b40c09581070a2404550502a00a1680000760595422100041d0018003050391004250090243c83c00030113111140303d2300300380c007041d000c0d0145845600450006480325a206806809041c815042c1d4405800031804e020f48100103450556150201038140072060045c03450700d0100304002c101130400300d01e8081c100e00492034180c0c20442d047d0480407843c002402100b424080b07441050100c00c40c103244c4a0f02c1d4070f81104800410118030742c2140901d03928907080b0070501c861500300354082d00e0303e00030412082d82c03101c40081d1240400030b48540007840e03188a44040030b11907005142c0080d501403110f03141c0a450742e58401110040400500142c004100b0082030190501c8000c1d4080410700344a5024a05030361440340a10501440510900c00f400031b00080c588200b207410045c1c041d80d0b017250725950715103040221001da0800e11000282c10042c4010303808006010b000001c44d81600c0f04101d036400c280070440409405000119008540 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 95461241 1250 95459991 95459993
    0x1f08070306060c0b040c090501080a140f03091309080301120506060307060509011d0406030521040b04030204111b0304090b030f0d08090f0102070c03021003090506010e0703021612080105010215130204020403 91
    0xc3c41481d008100c22b0000b00320001d05860300240d400384402d010401c9401114035102211070200032162049412038a500c0290503403400301d0002c0c80749a102800c8a0004400410200c1138640c0d2112034901840840705507943d02400c056a424207030107401c0005205026442442d401002c084000021078101c1c2e0120000c1c50b40442c0c1203c41c03d91082d107940e488071115140c0c54050300d103003004120904039454070781170038005010050b1207a840002c0c040c40e507501c80610081d0402003030361950540d140d540d0500c0d90640074016542d4101d4055000410701e0f01c4409500d80c0b4000ad0410b0881500c1c0000d820501186402a03d622030003c0103000349006050144849020a00c028241e079072107980e00711441811401405040d043c4a51840d0030f05181c109814045680061001e044901c1c1007184020760341d8294003140070703004040310981404000c10503c070402581c4200703410724400c01d07500c10740e83d603a8840c012a41e440040c10303134822118082021404403042d29104814650014102601c0c250f03413 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 95462491 1250 95461241 95461259
    0x1080613050c040518010e01050d02040207060c03060e01051c1104090b070206100f05010c0b0903130f18021c11070803092a010212030a0b1f08070306060c0b040c 71
    0x20482e0b00c030340d502c400081c0c01e110310710740b01ea0303070b0102c030344400c1581041c660401c0f4000f00c990206015084c030038031100d1038000442d0b0302d0350101d41c0c1c81a48070006203c49120b0441c09405032441d801031003580380904d000442d070750810b200410180f074000c1c1e40500080072a51503601409100d10500342c0c01644034101900031407a081c4a107402181d8a0b401425645851031420f610340290b81c1101500c100d030500c0400c15a80e000304110343d444d4004880300310944070046403074594495441321507000e442680002030070407400c0130884101c69124003520b80d05001d181e00f05040b0700c01c0300c0135026601003020020006c0241944007c404613006d403010f078030b007007440e40350059241c00803116900030350f0200d40103405070000d04a4006149640f40120f100c100c44540c0040d40b00c08444500c0031540b800480081e049201c0c0e600900b000d90000341120308070000344000810201d400c0a8440042000c540108500c2442813107400d040301d0181d039500c610500b0360365501c1c402d008040d0095402d01c590f1765001c254150 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 95463741 1250 95462491 95462501
    0x6020c0c0303031603050f010e010b0a200a05010f050403050712110313050f0306370204030606030506010b04030218090a021207081908030708040201051b01020d050c07030e01080613 80
    0x10b829001480f580e2404c007801015560001c0c802a0881201030042002c40c4901950906682d019244140c460303000364412103403641c05c0e145078580b280708043c0d00300b907103500458604e05050140300284248a16559000c060310f00513580240050405c002440101d000d090b94031450003500e02c0c103e10700c02a003929091450708a006501084030b8145801c1005103081e545441141d034054024080c0c03845c12180c0c58020780070000601012000c103407030307180007090b0502c0d0303044401e06c02c16411500e5640364100500104400c0c08201d4030383c4242070011880c10034010658040301d500600041c18a030004003942c10030b10000d0542d501600c1040d4080c3c0c01a0f43e0f01601c9070581100000600d840b5141c081c0d007502e403c0045000203081d0051610f0600400c1e00c400c1101d0f4800740600304079080392954801200c440c0301c0d8140d01c0d201710542d90f16000700c40b10190014200034402c5130050101ba1151010220070744034418004020034820904840254000c11506610000013842d002c0c080380c1d07003581541a10 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 95464991 1250 95463741 95463751
    0x24100f09090c12050a0b30030403140c0a1401050d0902061611042c07180515010519030b150f0301090509030a0801030f080708121503010203060a0306020c0c030303 72
    0x2101160b007180800340301d12460707500c015803010074030910180c0f030b0120b0798490702443e01d204480c050039840101c401f42c080512051249207812a50b4507036403030034015202d604141ca40840750141300d04001079031410020b924203a80c0411465140507a0100064800e03074002d24401070030b5078481040c203015907524030203000a400c1801c00c1031004123062a1011641c08000c0005109034a006600401c0700c1e412080001000d05624010035a2a4200c00b000c1c6080220380c0301d600400c28080540160f84003a4002a01410b0040c003080e80c5821003000640d1180600103901e01d441c0d4010b6140e4005038829040141994400b1f04150281001c03420242d0540c0c0c000081e01d83c0c0300c03000100403c080759582c440d2640c0040100099418040031020081c2007240620019048001d00708100c000e00002c0c01c1101c820b03691021a40b56500c03481201400d400c5002c480518810360000141f44641c1018001c03284103000040000032014119950b490094003d01d2a015140c1b0410303040c0712050b10100020b43c065 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 95466241 1250 95464991 95464997
    0xb03221109060402030712181e0b060108040206070b13020a090207050c0a0803030f0a1b08041103060705091302070206070602090a0b0f0a050913050c0324100f09090c 73
    0x45800038040c0101640c0150103680503034410800c0001c3c2643c00901c41400240d10303030020800c20918048040c244001030400f400500328581840c49040b1000c400c0c0d05030510818030b07102c10b9500c031401900c5130039040f1800307500407608120007400102140d050540c082420080880070755400d4010031090728081c0c121105956000038407000340141007000d041c5200044600c1c1640c241440082034a900028011805401e1581c000c260103100d079801100d010f2009403000810b0a100e048020100b11081d54241c1d541d14440c82070340c0403401c0100c1c0c803c0c4241e0303582c2c403014940300740365060040701241030940d5514150300303104190041c2c0c0d440313000b840355500414015850300902c004009490754913920010050004110f01240c0340d154400b9955000c1c2d242c00c002e130b1980c1203040400d62004804a0300e2100502e0401000528212500039500070300c821207034507040c1440031030640d200d22012a4016400071038541024070280c855039419080920302c0c03074941d00040e640c601c00010360b18070800c94008 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 95467491 1250 95466241 95466263
    0x708180d092909010c03050d1a04050a05130308070e06070507090c110c010f03060801230c09031207050114070203090f010903020907032d021210030305040b0322 71
    0x907281045540e8400005501424a0b1080d00c1c4910140c1c0c0740309021600c2d040c045101d0206082c0340c000c0041d60500403d8000c24000860780e40034501108107500451485545410041039207004680310b03013445a4910b408200501c3d5807504e041c0c03452034000b81048104500610203083e00d44900c0007800c142d910840c010300700c8178100040d84040e02c14854191040100180100d19803401c00150030300384403820300344041e0ba05081003088018001d1900507a080b5800c1840960b01442005814030341000c81d28642201501c0301c0c1c8000100b8413440c000c0b01c0c2d2550003086000c0c103020030600213240d03151203076000154150303000721030b400550f00445407040560000319401d1807504164000c002401000d1801140f40c505560008150318409000c0b4000c056650048401141444c0e0036041000003044031400c204060030013460207907122401070081c20b030242000c01e503001070719920700e410340380d058403020304040c00c00603140039030341006244800c0300e00c1210040302800740b0081e0355451a4011220302c51 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 95468741 1250 95467491 95467499
    0x801260106080f03041a030c040e0601120603050a020a0e060d150f0c09031502030c0a050a030e0609031b010c1e02030409090b0610020705010210110c030f040315050705030708180d09 80
    0x10f2007024220082c2690608000304941d2310441802c48043d204001e84100713058642310012940d814900540c0b4890606d000c2e070202c107000e00014030b403070114401c640c0307241c0c140d8490f420103404000c1134038641d400485030214400054441c0c84503000600e00d042c8001508110210300c0030540d048015040081400072000b842400b2248990300d682d00344100e0258039506192403c00da0f03038420344c2c509504120011804254041c829041448842000400c462190910768051910390307000124900c140060344240072401030040c0260210020b0603204c0c6d80304c1d5940c042824034041242c4075481e046010030032001c6400045031068000d8180950004841c6180202c14054000704100e2158290760008000f0401681d0000d5100ca025894907408610344042d0400340b1000c1c040d000384181c0c680800b04880321007628542c00362084a02543e4642c1c820b80060300400201c0c1d01c140d42280000c0ca0802c0000e040711b01901e141c5802000a000c0c0c0e854082c1150009d501700f01c071030384007400000d0003818100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 95469991 1250 95468741 95468759
    0x20307020d11180f0103020d030e0a03050102090307120804030204110d061206050601080412110102040b04080109120c030503060f0a180b0a06020c01020304090507090503070801060509070801260106080f0304 91
    0x11503981c4124a4103c981400707954a0f402c9081444001e228020500b8190708040c80382c440b510a900001c0c02d0080b01a44914109010f5042030340c0d018002d1140304000291058010807910403180c010304910311301401c580030f0002a10011031400c907528420440741800305590710440c2d00505d6240719a6109117035078030300030050354000740485d4100000d040611003c074020281d1402d0400b02c17401d0144111546400e10b5029008a1307011040110700400c0c005565441034201090092003000c121015040f01c000a0701c601001002c09000550705000283c0b132420520140052090014400185582ea640441c0f204540110b03034503007443d07146c0d0600036480c10100d0044024100500191810b01001c8000035a44e000b22310450102c2515400481c1406020340324501c0030b4180603060364602c54031765028a003e00b020b4841e25000e42c0d0154000f4203030f0740c846c2003c1c03130503201400702107055840d0100c0b80050b003801900c0c0240065581c0d003c0040c01c60303420405912041440c0700510b4907246403031000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 95471241 1250 95469991 95470009
    0x30504030801090b0303030a0b040b040c0306180920011202030103080909280b06070209090607260601030e120d060e0606090f06070507080a030504140f031c020307020d11 75
    0x92801c2c84c285040d1026696000c030540c0d0703018074503160000d11f0f1059180018003800b49450400e81083c64802141c002c960305401c4002500e58807103030454a900b1104101080700c04e00d0070058030224010208445092102d0a1480541c01c14540800c1900203024000c0481e8170030f0740300316911000040c1500250810629495000700184003007411000b01c86010140840c80002c411074103990341d0b4082c40300740d8500c8241e42d14507070040c0061003180b80500c000e07555440c4c1690000d010030b102c03604c0a00140b2200401100c0c04036014245111601c072400150b010749503480041055000d42400140001c0000c0040d1102111000001c0b0780c42c0e240040340310031000080e0000e8040c00e010040b1082507160f900c881c04c0301746015101507135180c00d00c0c00d165040c40165003241040b07000300408581031540c42006403007901c040c025050100d00003001003001d0003a440c1c00705501074201042ca40c499010720700d00e0820500d15401500d141c0002540002c044088200782259041c14007221889036040550740 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 95472491 1250 95471241 95471249
    0xd021801030621020a0803030f011a04060c0201120e120306010f020106050a0302240403080a030e0c0a090507020c15040306050105061e0906090301050a0501030209090c06031b040b0a030504030801 86
    0x810821942001c482c0002c601c1280c22401e6000a01c1c8243e40c11912130a10a9008002c1401a40e0322820030b0b401c808101d000a00c52444401c650031a40c0c050f0040d6041214100d4495407121000400c03554015078051420388030099210760f94030700c0b6207082181400307000250001440c4079a505c1c604007002520307500b9100708a10441e850000c00340104e803280300006d0705aa80403100d1002c401000805900002e241c258600940d038808100002041088000380c03030a2801500e0a003e82d0984541890b41d905140c040d0303a602c528180420070580b1800e07841141c1100580c81a07400344601031020070700700e888441401c0810100014100180703d1b8901c1924090441191880c2c03420071282c0780c10403e04420f460301c0400319400940110181e0340d1008442c07074208083c0080c04145044089040102001d120a0307010b100018000303059100d002c00c41401c0d8140c0140124210344400c020354501c02c405055000d000c103001c20010881000d42d030040e203018020f5680101e40c40c40c05c0d24006080481c1032340 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 95473741 1250 95472491 95472497
    0x30c020f070f0e0405160f0f050904080712050904230c03010806010b0a092c060f01020a030e0a17060403140403020f0f0301110309010204030b0105100e0d080706020d021801 76
    0x101c00d0022980060904040302c0d0300c1030103507900741c0b0340e400d007982801d089030b00c00c030314145141c04005405440b440c1e605085a43d1011011035040c5d5420a120040c20b080f1402440e10b0010800e4500141d02c11010000820f66807420a040292510216040710b07600b00710507400c6405008485610544114070540c00741c3d030104103d0131949081541d84c0c3d1390606001d04100e101c0082640340c4400e1281d0400001007240d40f2842411955104a0701c08141155010300314403d850400038078a41020000c1010003101a801040545c0d070b2614204d80c19141e00c3d008507405040c040300010180c044421051007525080e000e007109060915014040d0541c5807011080c0c108140410000343e602c20f000344480c0407013520000400c0400b00002070051018410038410904044103110801105602a00580e403080b0310100c220b9803500b0811040030740b80440c10700054140204104c4a080c103031700b81000326101c0c90400f030a00c02240d507500705a8000700303401540560702081031142d0b0505400032008140c0d0a007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 95474991 1250 95473741 95473753
    0x6091005090d0801051c0501110403060c0f0f03090501020d1a190b07020114120702010b01020d03050c0d02070c03080304060b01080f060306040605090c030a062310060f110a03030c020f 81
    0x2e50041d201e403c05200d09845a1954002ca9103000108100b013140c50358032800804c0090089911500c86420501054903071524002c0c000c0c002c81e004401a14420040d0f443c3c00c0300203010128110301610000204543c43c1d502032000100848082c01200300c56514803070a80e07450a401020702820300d5400070015440711808104004800400301185c480a80a1905405906c044140010688500c2540c9101030508004020049506622074003929100340d081c0c40f040004400110207441c4d040d1089460103808024044420005034000c08031581b103490b04500c1030750f69071144500790304100d505581461311901c0f00500d5692000d1038aa00001e1000034902d10300305103001c41da80e4880240010b10056603040803440e241401c0141d07100342040202126140c241070314020780544880d03a8a00392100d603925030f0314200001503181a01c14041c0903602c02c0c42c20300c1d00f84100c0c1d00f1110052041e043c02000078050135088414080c0041250080e1408505c100398040000e141486204141495802c60 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 95476241 1250 95474991 95475013
    0xf0102030405060403081b030112140f06040203060c040b040b1b030409060801061203081501021c03020c0105060f1806060d0e01020703020f060c090d170307080108010501060203070b040605100302030609100509 92
    0x1f480549040d180d60042d0f12814218914080d04103100803501d12030184604401290103950000d1128842c91090303058400c1a11a4003050580d070103107010745c006555007404103000300b500b160098030740c640141c9031410850250a60980c2540d026400110110340c84850074402c1650034060107009001d8002c40041616180e28007c010210240114042e06801d03034994860380c0c4204860a0151041101d0004c04040d00c40c0280c0254081c2980b07203059401e00340040d94500e0002c1500e000d46101505281c003048250640c080043c0d002000c55600c06401e114041800320184107089822040500050341d40d00c1c64100a440c140f4400c401c0c02040d03205108118101c0c50010542e00481030543c1d02ea805500e440c5001d442c40d41c0cdc1080800012034001c400c1200c01c0f5400400581281d402c40000c110a980780c241c101d0705d03845000e80291440400d2008680064510b070300407076202050141c138000d10b42c0c895000a0a00340156150f0305280e0004904034103a03000d520685803c100f074070004042111113 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 95477491 1250 95476241 95476291
    0x5070602060c0a0305040203010b1003090b01150e10030f0c051803060103150f0b0d03020c01170702070e1f0303050c011401030c050f0315070804030905030d1d030f010203040506040308 81
    0x20303d2000340405480e43c011408540b1b0035009050342c10401403c42000c1202924010024400d003941030b5503016810b800000ea115516001041280ea10350783c02d07020081290034840411134031788000d01059035400781c9007103c1ca418443d25140145035a11942e40701203058001c8240461444080d01c2a00030800400000300d03590318496800001c1e00780440d0745540c00300c2c984000c20858020729000845900751208040d800304d00c51640c1c51098880060070b00e0414000e90100000300c4522000d60300909090115000c1c410f121350b40302081030110301241c42c0c40031001c8080c010070340c030840100340003240f0720b94119000e0042c0fa96000da17201e078040c242c1d855910b4a151012003031056901441c02c00a406144c0c0d1024004100d103140002c10303840060403d000020072100084800f0380004141c1040820303246008139408061884594500c0d503500c000e600e0566903501440c071010703810321035007080a51403102070020350302c0f0b80c5c0504050a80c9150609028100030801098842c10406240c40c501c010b00f0b03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 95478741 1250 95477491 95477497
    0x40c020f0c010f11060c12070f05030606092b03020d031a1903020616020301142401020c0a030c09060501020d120911120a060e0c0f0d02040f0203010e010305070602060c 74
    0x90920b0b107a00180c01a84080e580703544c51880035811401000c0c00c0054107501a0024982080303114041c00042e42d9940046a180300c00d0300c00b81000800800101e0010326050303010300b4481800810b081000b0300c4000d6190203281954041c00c403d004c20b8180d840600d038061080d030560021a0806100d0841c81c244500c1c3c0c15802c0d1186513100e1180c40401512608040701060080c513805483c440d95000c4c0b00c0c040301e03010b00c03034203604a100790708043c0300d0132180c000c01c29114068075440c400041c044000c0d0f102800c03940300142c1d1880c118800e86e00c0101c420382d00c40802c10020749c011144828058141007130981a20425007009042d940f0902c0d803c040c05501050402808200107000200000245442c4885a0400084990003c2d41180d03050041101050708612248150740c00c00031038255402258641c18a50b40039544211000c081c1040d0b420301d1110901010701c010000103100c00009101d204980081e001119000d80b44001481002001c0002c10080c208600050859240916410701e0760301c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 95479991 1250 95478741 95478763
    0x60109090c0909050c0408030f130807050906060309010b060a090f0f030b0c0c0309060a050309160f060c03170a05040309060302070b16030207020904050102130b090a0b0c100911040c020f 82
    0x15a1380000420840d464415600501040c1003540e0342c9402e580701c04080d0307410080c0300a03030b000d45005e000500d005000602400310350780602002c4295943c2803c021041c3c10042071001295281c6500884d41d039a031900402e2503c059071580000d4500300f60403030014040c1e94028500c0d8595002090000c01c80e0140c003141e00c107564030015980d179494406054114012608102c2c3c019078042401d00d50950002e001e540f0450081044070440c0110081c000120074683c030071303088108034a44092042c1403252014161541c040d0805400d03048010340c0000301c008044401c1300e0b1160f42c2d038047c40201940700e6000c0009214614042d414164582c070740d801242000392440d008c3c000c01c141e5100c8030b00e000c0e0701070796001a0020710212040c80d090401c10b020394404201c555441c0f030a15008655034400394151949004080c101b140d81c2410b206419030b240d8840c0a800815200f040c000100c1c19655000384000603210341ca0441100240e1001c1c4030a49000c5200340003035400c0702580f44050703500051100507030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 95481241 1250 95479991 95480009
    0x606050c1b010c0b04060501090506041a04050604140901090b0903030420010c0204050a0f0612030504030b1003050a03030605030115080d0c02124201030303050429060109090c09 78
    0x1e00500340180c658114440d8020300f100c6901c420001808001d510050485621880912481d03540b00100003c550003000e20001095411010842c51700303252740540e80c4040040e0001a81f000311b00c81241805030b00b29081e99243e911101810200010a0500740c0c0000384540250f08604199494110f00003011b4016400e036901600c91180c41d0b8412410780310059000f0308100082d05003401241c001c0c08101c12009040c6060205c00204080a010200001c0d6091764400e4181400c40ea101c02a940300540031145907405031101102090040c044d41c04128800e031030003d80c40c0d28000615096403540d546200d55075001c00801c020700c1c580400e00c581301022510301000e0400b0140f0000c0e0a10600310f2082c000d40c424003098074100300000807a1109002c0030300b140300121410045000c2c1c41c04484044c20002d000c030300010800a8000e03003007142c00503c40c0606510030b010f09c14490003107519103041804500203000c2807003111758112443c80c015000c40e4505204581172041c001c0c2c0f000465108801d00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 95482491 1250 95481241 95481283
    0xf0e0f090307061d0c0916030b03010603020a120b0604110403060b030f030c0a14030a1e050c030a030f0f110a0e060903010606090302030f0628090b10090606050c 71
    0xc0c100e0184200d401d0107501110800c03419404c4042034604000c03006501390103100340d8101d031100349000460140324032021385403414180714080088001d050701c2e0080c0c6030190b490344008401640c9503c2c880e0007801007041094030039800c90030300345659080940000d004a1401d0b4400105280b01c004990540b50091808604a40c001020038600044180d0141e00c81c0404244101040c50100c5c004a0321130041e80700208070300d4030342000e58580c4240680000410040c01104005074100018026243c2d02c0b402d1803800c00040300311260540e80f0603503002c00001c0d900c20000c8400c000900c100c2d501400001000c01c0000416200c12807680b02d000c00103001e01090056070041541c5450480e101039102800070301c802950346802030031040301804100e1180c040c1400c0303d00a03900002c1d0003403045050100003240b00004170007801400f5480220f0454142c1c079007802c040414400c0700660700941302d100e040703680c039171a10511004503074140d00071030100034080051000401002402d005031228840f00304030b0f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 95483741 1250 95482491 95482501
    0x203090a080f13090501050a0915060f020307082a0a0f1112011103010305012a2d020601080106060504080a0818090c030a060f08060a110c0a05010b03070f0e0f 70
    0xb06000d107400d0f22001e207003d50700104009043d80c21490489500b07603218500715403030b0203510042d28142030f080500711007102c104002d0f1b2446598915440c89450054920b0440651507071911907202c1c0e80240e02028080720100d22041121800e9034103040c61801512055406960f00e58080c001c1140103840e42045155000c03031a921410008510a0144002c004950f004c600d0940035400c2484180c81c0f135407800792001404d500e02400762075007000c02c1001d1040b5916522090360241800145910042e408120145082e4090b803c6040b042d400394009003000c2d0302d000d100740e09540f40384d0048810441c3c1844100002c01002960713040b9141d000041e581c071140100d50f6404074000540026a110b0448400d001404421000650003049003844c01d225594940259102d2041c4600c60701055030f121100241d803450b0158860345842d4003003103607145400c0400400600e031030400f00e4241d910f43d644a51036402868100f003140001c0c1a80030340c000c402d0f46018030807502000300811852040c1c40f0381d070004c0c0c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 95484991 1250 95483741 95483767
    0xc21051215030312090c180a020a0507020907170108070b0f03091002030103121e09030b090f0d090801051005010e060a0c050d0801090b01020604110d140f0607080a0203090a08 77
    0x31840035002d8216511183c00715100d8442c014140c95901980c082e00f841ea9a8504200b41d80001007110b0905255258a4000341c43c0000e502c80d45400007044014440c40005985188001d40203445640d82d540e805080200b0000843d2410380c0000380076404017004004401c28001640c0303817011402e2100ba120f54455190341e017421201e101d40303030b2800e04c000008003c10a051500b00380d880340c16500d24855880603141c1c00501c550310146903010400603d01000003a100001d034560049501064540d003c0c2403860303080c6005d0b0000112070100d50038410510031060240720b540c0d485444e002035092250318080020700400619605140100e81c00110425064045c1e079044443c1d5a202c0101c03212003070198001007010000b03005040409041c00d1f90301c1903640c03001518034011508119200d0114502004201401c895810111a04c5080c60050030108400f44009008000001c025040701d02c0d1031240200013003001000030360500d10620074088070090000b04101c041c0d520120340c9030b030380303104c0c00c0d201f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 95486241 1250 95484991 95485021
    0x1050f0a0b19060f14090a0918020301090b010611070509040305030709080f0105040c0602011a01050d090b0109050412021504030f030f05040303090302073201030902100c210512 78
    0x26040180400c00009202640212460072021103a030b41d20001700f1581081c280c03607204295545034866020f8109110415096201c1c804141820407551080103c90380441d0a60781c109906940b1456007a00400006421106d0100b540b01072901402d003a50800c400101001c0c0082e00c00380c10010040006011a030161406074040c0c03444504541d03090014002407406000d003250100c0e2000120040020081c1c014090540400140060f2441c00c001d00001180c5503001a1a900c900c15210b03103d050204041c0300da160301030301d0003002c0411103242600b05024490310a4101c2c004560140d02c24509600b00e03070200070b402c254145000510300556580841c040e00302003051b221068580024401015055407103007078110310903000c1c7ea80e1036a03100110040d140d2000700035030414035150074080204809403c008091a01410300056000e801d4000c2045204841c0750900071910006840c0280b00c501000303106003410f490700400c88034000500c000c0241c061241400000c101040c0402c3c086d40341074180d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 95487491 1250 95486241 95486269
    0xf020c15071b050105010303180303051e09060a0503011a0f0301062f06060109060801050d03140d06030c181e0b030106080d210902010c081602041406030f01050f0a0b 73
    0x505602c0d040e00d0300309207000703000c203200807404248821405004400080b9000003200c0d0583c40c4c850130452002e03500d44e0107615684c202c0c8103d5070104407184841c0e40b0300e8017400441e00c0955030b03203071658104404503442800032440204186001e101803a40181a00104c80c1076410310b1900b03801700c0c5407003c41c51041b12010f0b03c0f900c4d45104480d400f8891820000f500c1403042c1b50991b03c400245695200c1540e08840038040c250f041102e40016401180c01810b13060058410030741c1440c50003035807010300d000b2144140c104035070107a140d8804002d40c842120304a40c00740640c203001c2001d2540000d842c2d00d07140c5000c0204420a8552840c3e82d2195800e5120400800c441c03410340300b0001e804400204142d100c02d0b840310030b1024048200b1200240e51084016841d81a100e003080b800c920b40f2100c0054120500001c0414032610401005850300d00821240e0800f03041c0c5d80882e400c2c510f04050070591a0000001ea6a15010402403012282c004441e00b09420340e00c0055070b011a080070501035024070340 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 95488741 1250 95487491 95487527
    0x2040801060b07051b1e0604030c090b150a050702040b0d06050a05100f030f030c1b030f020a061b11010201020d0e100e071a030606090409030305010305010f020c1507 73
    0x1d00014000d24034001004010702c140d013540c40c007204102d00494485a00c541031a0010780400001c0d2025a000a064406100007803900d414640c0c2c90f52088403441030f54220041107038584055070000c2c280320401024020b10304520a05041615500030828003a098019100755240c00c00700500b6101e4002c18002c4680014050100d45040c00c4d81801400c0c0030b4039040390010b602c03000002c24041c00124003068030390000400681100a440c1150f03210b136000c0c0107841a031501c1102c0040f1407224040c550003184102d00c5641c920303030340d4010030281c510198031140c2480b04190480410480b8410168206940401445444208000100e0081c00340888c3d80389000e241070119010301c0c10004407440304a50fa200e040c800e03161411216a143c949a01c5040500108015166550724942c0d02851384036030301800e801c0c20240e00200150176600c0d1400280c0c0420359500060091000a009a0105405015041d8a4103000720002035403a02040110880d50141902140d481ca03c9510280301d5405001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 95489991 1250 95488741 95488751
    0x703050c09061c030216090204050303040509040c12050604030f1d042f030411010c050a030f020c060f0a03060503010e0c0105070203100204081605010c0c031113020a0207140402120c0d02040801 85
    0x4503000e5075911100604d01e01c2e207061688001f60861541c0200e50075200040e000d142840d00d0201804443c42000d001114080c11003613010590311201004003141c0c034003500040c1000d0038a130601402c0f02d081c003000502080101100c801c003078014609044031b491001d90f0000365140d110f054031034420204221703c80014a100d0b001c80c00003142e500185014500548101038484407900c015507040040807001402c40d0055102100420300038aa98151521a401500d50040e0400e0020301c140d44820f92040003c280419060903903035140c8180006086c055000300040c0308000c20407035507001620032050400c140020030108545050119003070906c405001507417103036261481207032035034a076061106440351030b0b1500041a43c07107182a440c2807070308000e0085180d0704540302c2404800001d071089411541c05824040b402c032a51000704000f04080e400307005010f04055440d000c103201202101c1c421401484842780b4121168856604002618015507494928034002d1010780615404282654600 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 95491241 1250 95489991 95489993
    0xf060201090c091401210203100203070f090e010b0c03221e0303080a0c1709160e06130b01090f0602150a180204020c12070606080f0703050c09061c 65
    0x1500001803040c07042d02c5808449480ba441c100c100d0382c124010480302d038140c0d0010000007190301c840051005100451081038101500800e1614140340c0344112050381c0007007040005640306401080a404038509a20034a2074102801110710040c000c1100d20100060410407211040003180c40c1500300b8248140c40c01c00003400322500100c1da109070751029001d41c004c5400140c640b450941078960549602c0303016160f8961a00041c581400303510f09218800781513003845030b45001d4041c400d5620b0002412081d00f62440044141d602e07502084503504580c0511269544001002e0b102c0c4240c668000340d040350640c0122802e41c550b501c064040320034944007007143d59001c80d4841500d808402c0c43c481030303210948500203c8049a000d5004c83d03c0038144040140fa25030000d0005031450741c00c560202c1152581c2c071040f80d018102c00c4802c66038031602003000400c1070102c8204185230304058100b5514640b58a40c035100e00c090160312900035840050030320b42d030303005552995031101700d411900031490b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 95492491 1250 95491241 95491243
    0x301090b010f1e090b010314041110210c0c08030709080106050603150f0f0604230603061e010203130306050906010f0503210705011e0f05070801120c0f0602 69
    0x30a004000030000d060801043c40707100c055200ea0300c0300021421180070b5151010503c000c041700340d03449040586580c84030f40a22440c103940c0b40618020b442c8401c1601d418410440e006e2801141d113070902c256041024407a514a0741000c2106020010200720407581c09021141d4400c1ca5600600e414000710611013500e9101000105a42140c0000c00c440e90700c900030060140001c8401d121011003203010700c4000d0428141042d400031024120608403100c8a0014550b508a500300d40a03640407c1c4526200a1044080900440d02680c1e0b003461170400501080c0c44400720400e101051140d0013102c8a189d208004136000301c1110b0010001c103d450b0725080000d00707421356440d03c144c8540400842c1c6283c403c040002140d40c0240108a4411075540744031010b8482d09800301140014040003001c22400e018000854100074004940c40031450f251000301d8000f24200c9030384c0c40ca8801005841d42d0041707441c0b4155a928520141c181c01549807140b08000e00d508a0742992400300000180a50 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 95493741 1250 95492491 95492513
    0x10603020a080d170c030105060d0b09072a030c0b07090909030c110a0e1602010f06060215010909080901300c0e01080c0307030b0111070b07060608030306030a0213020405030109 78
    0x212a50340745000075034095480e0a01e213041e0b480d41150356003080108141d24001c002481204042540441c01c0c009190002e428008111055030100e0001c29a061031084540028040c42c0b10740400003680209035180200035080e0214014000d081cec00b00854013003401003580400030209043c040c041410540303002444498004011210f00c000e00c0c0d6646503e2801c5100d01041e0390130034204508036034034034840d0640041c4168106c825556034400c1e82401c02041d00910340901036640003054929518005428668016802122000c0c80c0c21203c4000403e40012100a0042464002616030340312111784031000c8910104d541510b448504451042e003960400e0a0000c1180c0724101400588030055400a03001c0b80e9150001d081040041c55541c042d90110044030018540008401040c01c0258a0700c0416082100030201c040b4000042101e50b0003090003a0418201031b49c1541020400b090ba108140540288100301034081c20300440d145034191001030070014001c1c86990603074108044000e03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 95494991 1250 95493741 95493763
    0x8090d060f091502070f0809150c060906070207081510050d0f0201080606071505130206030f101401050702150d1802130504051509031215040c030b010203041205010603020a08 77
    0x2071843c41c541e05000618429264038540008803410150f0441d0740744501c541c45092110340c0617841c112a8000300c4440c0019001c030f820150024083c5040050201d441c02d00c0041c181000c40d40031440a0081c410042009c0d65030071060103a03503103652070304040d100400d91607412040d0400340100d290011b20000341c621040c214000c2e01c42d240d09480c1c06060110521491501802070304111440400742c03507843e84250383c0406007003500300c0115280c3c1c0c0003403c1a030043d91600c003841150f0050050903100381110400900d90f8161040020507220f0000e00b260060840180c400c035a461202c101e0800b212080720040110050708010910109041031500221448164010500b6040e07000350300c2d2441c412a401603420400030108400701800c142c000d000d0040c8002800d000911504c00d880f40030551141c0141c801c1c0c107082c02019040402c0c001152002c01640040605180390f0a4075660044105d906889902c0705a880c515000d041490160205900c02504180404000582e600020488001c00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 95496241 1250 95494991 95495003
    0x120c090c0201331701090503070503070606060203071a1801020406030f14011a070812070c0209060d120f0e1008071106010501090501120e070305070617100308090d060f09 75
    0x442c804181645154043d4240c04880c12028010700000e4a4100261206100c000020910700b003070351740d01c5046404c0094101c400e40d0020440300c04010046c0900710103001c040c4021401c01d101920b888241d04000030300c6948a03038041012078540d458a1401302040d0351240020f559440e503502000380104044c3e02c40c1414640340c061301c0014442c5c8100d145040368210b5981e036107507007c040b1000146a00c5107104503400c0004000c0b5280e000c490b611850b00c10003440c2c0b182d6201003000d0040c805801001488144564000c000ca680000c01036500495495260720f807060310704440007802e58906451007074070f0358000602d0b245946803580c8150100c1c400e0200b0359a00301c0500742e85050640d140800c0c01064081840c8480c01c0c4001e5204a030000e8054020f1075001c01c908541c000c40f0350800503990004d8505030001102030088603000403c1e20310304403101c44642d8103441d0081001510f503a840c0001000807000150324015691103082802d100e0750000d1082120f160180004801130454a40c12206 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 95497491 1250 95496241 95496281
    0x60309050307151b0513290f040f090203070306080d1e02070305010f0218030708031e07020d0c09110a08180a0b0705070302010b100806010e1504080606190f120c090c0201 75
    0x550a40e541d1251364207c95800d0007040c9030762a00c003000f140c110100c21003400313070f061000044406002140f0300007481019001039481c20520401025183d8582142c2c4495001c000f4103400154002100580c5685d50000c00e1516016524220704040d0941e0000d40f15600702003444400c10203660040021003124040d000d1a01c2c1100249a220b90240c818400d60390400d120280b49171300102c03a800b400f4000d4841081c500351041c1c0c00180324440704a015900c01000740c0f01803200d0081489444610301e09030380502d0810940020017400d4030001403600c1c0034800b1040501d601d481040040d031491940c000b40050951400ca58018201c1c2c0000905500540c20881d0081d801c0c1030209940e078840e030301d503554180191b46000043d01c0c42c2c40c040140a81200d4608040c0c640b190b0580013410191a03420080c05030381c01d2650401590003150303103804c8a11007600c0d104016484107006414100c840d124603040302c00002c0d003006c0d070080c41c859100c2c400203800c020710341e0250341d819404a01e01030050f40802d82 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 95498741 1250 95497491 95497499
    0x70906050a080d0827030703030f06120816060903080f0105010507080d0209180709031106040b0403020904050307061a09070f05091320040f060309050307151b0513 72
    0x5080d2020b48101d0015820500d02040c800b0300c04c402c42603000781d00300071190405420300c012510003c1c10210a01081d00045481b00405605008210b07007143e00300c0c000e0205030b09242c044140c24a000130003c00001c400600513021010b11115892015044081006080340302d0501401a4204071100000c1142480000c00c035907002d14143c980098102d02d446080520f00200d010088d0701c04178440ea07120100c0746c80c00c094803400d040c3c000e1250000c1d554002c06549546002c80c4200c41204000744546814001840100c0c0c0768400d98040b650100e540c2e45250b20b8504109081d807003030b401d0141925040a503941d0007107400d2034806407002d409a0310042c0c99a11f030201104c225950031922400a80d04011054091406407031780030024108000000d100d1000d03089810403035080540350054400045020170070a103080d503c0300c008149078101809000c000d60340355510380c0300e080c0009000c0c080394a02c082e1500311a038801c0d6503481074210109400141c050015040b600070310206803506014141c040707 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 95499991 1250 95498741 95498749
    0x1030b040210020a0804050f030a060e0d0f0504030b0609041401092f0a0e0c0f180a0506040f090f110a020f010c0f020a06091103070b04050103060605042402071707090605 75
    0x4188580c0200da81e0341000c7c1041e080040982400c095650305118504411010814500c602081117016000030948010308060150090215001e12010f011051204002088175084c503568017840489400c2c0142d13459290000806840c4200144150700c1c00c9609400c02c800b200075440510140000104000000250b8502e24840c008174281c012800306402c000d840100301c10190802a0303088414101058006c58200c160803040e9420b142e0080c06103012002d041c094240e1000c1c0506880440c9020f05098280d807040c0c0796449407400b459901d2041450100d155813200985140e107146a41d83c500148a00a58600900f0722030280c039442e254945002c58091480710b00f6288842d00903150f260302c039881e1000142072460003035906000d403411500c01d070355052202001803d1035101454540d41004001000c0302d400340c01440030320104110038080c440500000c40c01d1090200320003003008040210490819541c3c0d40182424440503080c685040804982d110680c0c0b5140000c021083d543d600704 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 95501241 1250 95499991 95500003
    0x110f070c0f1401080604020c0102070f12050c0d0e030118030f080c03060d08030612060903031602030a0c1b050301051017010203060612043f0905010e01050c010609020301030b04021002 81
    0x41c290300c440c406a00b0030b502580501c1d6008400810044c10101d1442c5002c2c2680d000b040112183c440a900013020004800c82441000005241c2303103003003514076031070f15075901c18070526a400e000c015402a030302d698094006110001c0c00b00e0441440c1000d0b4034010741130314040c0b901200864151000600081c190006507072040100800201d00f0745410b0f1551105540040c00113604080c2800c20740300300703240030041a0302a03c803c00095640b860f01142401c200880100e04008540080190710102030707200e040700c83c0c4240c00080d490100e00c0d00007140340300c0d041c03141d000c180c05500344410070907445a008000e4045400520070440c0d40d195a01119081b4807080b80d05c60f03404041440014034030382410081540c07040c400c40070a82c0c10782043d4402d519210380c4505103000c0709030481042c4c1c00d24001c2c6070a032031085110300b0406160380c24200080e14110804500904007c008104521140700942000000b44a101411540d03540c41e801c00c3c0e00107c2d0101d40a900075417410600c200103620004403 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 95502491 1250 95501241 95501249
    0x2010e010902010504060309060209090708040308070804050c090a0e0f0309190b041202060705010207050109020f090417030903091507050f030f221706010303081503061801110f070c0f 81
    0x80d8614180c10400280c0c0180300c0640150727100c03542404015240d40b0340801103070151a180d00d40c14083d00d042d10780203000b174000400003010804880c0a020010f500003a0840d03054004640086c410307601d05900c3d800400d100610a00c0501c504841c0250001e1b010008001c000c134241c506a0804402400010b0000c0484c0301da10a20082000300308040c0f031f009080343c204c0340d1000f0003140c5801d07090785a40e800da0b00203c006413010795581e4900011441d08503214000404252041003951802c1e480d00c44c2504007043d06076441101c0040081da12071400d0044515414000305a64001600746082c04002c6d0040181142c49200d001c0034401440800025924400740044032240b6060400295031002c0f54009002c00ba005490400858041240e29400c02e2103480c02006001943c5581002803c11b071026110042950301c202e01c1146646004c200389038041400c80d070082c401c6100b000d2081c01030440300040307007802c4004103560b2141001100140f2480780920003000601e512228407450b05901445 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 95503597 1106 95502491 95502497
    0x303010905070915050304030e0a090c050c101415061c0e010b041b05031b0a05070308010906060c1514090a21050901110a021302090102010e01090201 66
    0x8078120044c028030a02c5a0110500c100240481c44042e00c00340c10090108800350282d1100764114009009007030342045118541032000b01180c00c00710b44105603004500c030300c0c40950207502403040c00c0c8800e642d9010704c0b500c0d41c1e851b15001c29070b21380e482600210180807103012040c0f81e1001c82c503603022fa480045206603c4113141401c403655040080c4c8103515080380c43ea40c0001d0b43c0e000c20080450740c100f0694a4580914004030710024056206220200040c0c04541c0b83d40440500200707813182c2c17150354403030740ca030840c960548409004446c0040c403200c4400010511040654001d0f020051001900071185144c646072004120307041191640000c1c0030004001c02050312100035505520307007403403a160303820b40101144101c500c0c00741009120140c03035490080503c035039802c003a0700416103403114107042051070294120203061809940303802d0071418400018060840301581c165 = true := by decide +kernel

theorem cover : BRFrame.Cov 95323741 95503597 := by
  have h0 := BRFrame.cov_init 95323741
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95323741 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 95323741 ≤ n) (h2 : n < 95503597) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
