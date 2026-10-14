-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0437
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:48:35.984647+00:00
-- url     : https://prove2.me/submissions/baa4071b-a0d3-460b-89ed-3427f4096cdd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 78417267 ≤ n < 78597124 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 78418517 1250 78417267 78417289
    0x605100e1c12030f180b1f0b0c0111040303081302040f0606030228090506070303091b03020415030201020c0402090a080709021b0c0f010c050c2d09010b09 68
    0x1d00152a000741e1078200018640104556001d140da14040501c811001015540202d48a0a00310305041d030080710084158080d01030345401107102c3c071084d20740c916a61101d4200718182c03509100328500215200d0301d804000c0c0300507420300c0020855044810303080c054602503071202a0105600b80005001200c0600100c0c4029200401c0080c2d6050421070700c400320781468005900003940070440425201d01010341007003580b82c050b552421400340c070308010924031560003114040d0402050550800d8000d40105d0f410581c8181500b50500c0c081c0e41100031081c4030701c400c0e44101e040012040d04050101c01050540c1d806034003a060521103202801f01a600842c03149030480481840003c0e40e900c00d10002025001200b005030340c5141c2d160000c4010080418600740c2038208041030f00b030594411842440509081c2005003030480300b820078505000c80750380010b4120420b155401590000316600100554082240610404243c4148001d8000074008c061070200200040c6185152001240b8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 78419767 1250 78418517 78418519
    0x30c08090d020a270b060304020f0d050d030911091b03090709050a05040303110a08190f09030c020a0611070b09151b07050915040f0b0607240605100e 66
    0x40c00102890703001ca080e840c01c1d6030100990815440094042107482100344c0e44107251031034188030301a400c8000420b1440060b100900c51038900070100101c2c1c480b040100865a04031058a416075000540540130b00340880007150001f010041c8011540b0f00103800502541114480505244d1030061901880e4405400520300d841801c800091100c0203000d228490354003d40c0104842c24546000b0b01520004070003500d51003020f00c00d000e1010b41c0420016030000c0001c0300c698400b5161004c10004003102c540210503e0f007410b0307101043c95046010006013078801c0c3c6003040307682c0e91090100e0381c9a1032410a9460b136007040108000d0324200102524089000914900c4d25107289819032000349e00075015403a0b14002001e9500401d038080c40f4820080c07805a9200203d1b1804100300890705111000d9581f085659900042103c0b40700e40c0032003540c1801404c200d513150242d0a000c10024a103850f10200d01000510ad15180c200a021703810458001030a6a070703a110a22405940c0840c1c0c002c105 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 78421017 1250 78419767 78419779
    0x7050f0d0b03160612051510080606120f07080603030c0a0b090708160306060602070b03012105030c151602030702010c080d02310308040b250b160903030c0809 70
    0x344080032950380703100062240b40c071540c41c00c6405d01e8415042d1140104140c4011403001807111081e201c800404c0c10a50380351034026029610f4000048680c000e81d00c241042c02907403010020b49551040300c8038010170254440c4199540c40710100755803031141d801c0807103d03600616245030005076948460b50300101144142c441294580f20070b18500351281d105004241c003000c00810502c1841d02c02c000180c03000344042d000b198106180100580700620800da0202c1c01c81e120b0601080c0305041428107a46d10009880c5c0d100020f0303500b070b075540c85083c40f60b252125107100400c8040d5000700d4050284807894003d14204400c9800540303044141680c01d0b0b03004042049624101c0c4a0b9100504da680f40e440581c0c2801e030a081c05100020b00000c82c82e2004d800b1100040c004a0f8000003920f00b10f81e25641d000c0c0d502e082a41d00c40c050407140c40d81c085a000c4550700d480041000342c6052170322883c50141407404031201d90204440b6580c10b80320280200701c003002800d001c10031280003000004000313452 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 78422267 1250 78421017 78421033
    0x80702010e0d15020a051903200309030f0a050909011511010b0306011e030f03020d09062c010e04020409050105100c03050a0f03090209090604060b0a0302130c020718021207050f0d0b03 81
    0x706007c1070300421008000383c0c3d100c1c04c5407009040070091346a43d1081c400c035103055241c0059555524840d11f4038286160714045103010b0721510038801c898081c2005041000903595070f0300505010044400c0600224100341e07031545290303505216103400038000400602c1d2503443e0940e0581c0e120590900d44d5a03518003880040049500c07100305026140c401e50042c039031584060340c024160b881c01e0b00046c0c10000e000f80440040c0c86030100b0107010005413a040b2150084000c0181c0360300c1c5012001f00e402500201b8001601c2a6550113203040b51401c3e150321034103e240040450b1005407665004020500500c00d40508510802c134620030310780e903801c1c00200601c003500010584c400441b581a1a5030002c001c0208200360380c0500400c1c40f505460940701c0500310340c0014001390603d40c040c00d01982e0f505806140c01d20801004c0014a502c6140c1c0050440d04185040a507000400407410102c246d00411032842c0b0410807241030140001c00e081c100b504940400016150a000c1140c0c18819002 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 78423517 1250 78422267 78422287
    0x311040e0a030206040b060d0b070809101104090b03030a0504030609050a0609050a0c0e10050111030d0e03041406070807080903011e15080309010c0311010612080702010e0d15020a05 80
    0x800307211524040e800408207882c140c42d240001400091071140030360301003121100041d44420f6850b0f0842240d00f00103045030703141c5462a01e0641041c3e005510542000e1452109401c100000d00c29078131219800d120b10300e054001d150b6039214030700c0070310009581004100041410b80d8050341c241c80c403820540d0015200c0e0f890b13a10035070b18002c40903070b551f40044244500304861201d0040044c4880070100c0302a18200b581450b401c0d0580c415641400200304c086002001e0500c121081c5807001181007040e8001d42e4190f41c0c0e260400e000d148003661920100c1801850107000340c80146030312018591030401c0700e5680c1030864100c0480c4c55050342d00c800d0740000010801c1c81075050743c04113003000034138400403010141602074070b64031040d002c0d0410040c030035250368409107000003160103082030003d40000300311140c010300c1030340d0080c242035009445c90020880407000030700200e8000d036900d44c25a8500d5040048140c05101c1c0100740714545851200340a005402a02110450341091801c00c23105907 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 78424767 1250 78423517 78423523
    0x20d080702190b0106031406030319020109050f03030f01060306080307150e06240405040b180a151409030a0903031b0f050708190c050108100518060310150311040e 72
    0x40d0403200083d041c8010700c54694584076107000c80300f4075030303c103401400c0103c0425164070035803c40300000340750b42c2c1484107418001d4020740111130b03203c011102c44500800b40f06480350015146002186412000014494840d0042c4c03820b90b580391011707500c0d181d503d039190b50320043c000080c003480c070740c440300700f45458001800043d208001045c42d03003500b10305a106010048003501c6545220b1840c05043c0000701d003a0040f40d950001350004841068112200d00030302d4000ca15200074461280007182d10b41d40354a58202d03a120b00d800380450803040c3c0314900403940f030b800b448a96400140e820401040820700ca0201d9003021031700700070210a0201652540790241c0701605003502d00d17030b00c02d030000c0041c600c04010429451003800c7c1000700082c1c0c82c1d540ca42c000c240300d100300c9040000301808500d032603014130750007002024002c201e6290580c0d039030381c0e603a846101190000c1c1709000b02d01020224807d64000c107001407100d4003840c45a00d085640d8021546a081d05c01074025548248219190300c4c20 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 78426017 1250 78424767 78424813
    0x90111030d0c1b050601120807050a060906060909020105070f06020f071a07050405090f0a06150e03010606051c0f020c07030308010f051905010c050a050303011403070509010303020d080702 83
    0x10701e00c0400d003456002c0010380100e0300c0500c2c40b01c10304200e950140200b040803800d00d040d102034200c0e240c84244c0605044600b130141c3d401c09051801642540c500f00006540032214061003040c2c01d10901e03541e10410f1044074591803029012813000c02c6440c00003143c8901c0c0c100c2c0184103590050a2400034008285160401a0704542c0743d400080820204105045030940c404a5031504618280c1840042080f0701c0700074049a0000c58400041103a600310342e0010300282c01402103100d8200c00022004140e540e8603844240254641503000c81c44d64030402c100c51812065140425041c00a940240024400c400450251b2f075803e100c01d0000c400d0a0004c00000c42c003e58480001e5410603920b501c0460b50b560120303114440e07a80741d004002c1e0650056004640c000d0a080d60000320710b082a506104084c03000030700501002002003120000c050f118462110140c084171801a1a84240410320000380000f4016038030595075400054411303600c0380da0001c500d00c182c0d50311410724145242c90101c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 78427267 1250 78426017 78426037
    0x106170a060b0607080d020a180605070201110606030705120c1302070605250c021f02031b030412020d1b0b030109060503061911040324050a1401030b100e010b0403051c0f0509011103 80
    0x3340c120b09641c0c0c041c003203426000054011b03180508080d400030303544800c6403180341e000c0c4034a003400e0520384000b40022813044d040035060840120200c040c0800035844900c3c00c80b0901d24000c0070803210310023504605006101051404581d0581c0001a01d040d000b00c0000c03030740303c801000d01d00d0401403455a084020200d50300115140d5102c8245080e0141d90318ae403580e0250b100340010000180f802d22080800e5405542141000e0349a0401da1040ca014a4100d00301c000c070040001054000c00340114121004040e00b00071141e200c204141e00c402d821740781442070003504c1140b0001c2c805650b00850059810603d002c2c5425600da81c0c2c0a1025440000760088115540f1003d21380c00050041907070051031044100680104900321500250701808080c11420b10000001c103a400700c0d5a03490058500c10004580d81d42e59200c0c801a640e00602044640e07005000001e8801384514050a241d5103494a907206c1c8410070900403146070300010061340c10010041813103814508107000070301c0c41d916 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 78428517 1250 78427267 78427277
    0x4050a120203010b030a12030f0b04050907030308010510120b0d12020f1c02032b0e0705030c0d1203050a090f140d020304150806030106170a060b0607080d020a1806 72
    0x1141d0041508583c8560030090003500030382d0a4800050003805c14101c09080d5050006000d5110311002c2c0060a0408440d60003038a440140324501c0d00010307401003101d00c01c0d0346891050782c0341d0303003071081207028065800080b46280f802000c00e8002030f00700c9000c825022302a421001d4031070b240c40c41070001c245045409030300481c400460a81c0140081c0c0000009503014524150b11544000e65070310030721324440685162021401050110002c040180c0c80d00300030700380100303110400c131107449103160b100702403003481003411318001424404c80c604c04040d00100070010034440103030280c014010040c02d032401c80d95964140e1000800032121411407078029405169881c05480782c207407030b281c0000c0144040d54402c0c0000c12000250308508a10903806180c0070903c1e0b11114003080c090109908640c40c41c81000c8150b01c1d030349400240c0e0740c520500420003840801c8043c818001c0600c680c41c00075042103010803003484c0c0e1000940003804d0303a0016107803044841c0104096480d9030355450b004180011 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 78429767 1250 78428517 78428549
    0xb0301080f030a05030a05060118170715090e070c020a0b0c010b09040b071107051806031606020a0305090f0909010f0c05091e01120f0b0a0b19050f04050a 68
    0x500c1006401c40301c21651000750316212500c1d00160807400300800e0100003944443c0080c00d6644100003280d120105025110040ca4440e4a03503502c2c25400f410009003849000e00004081d4200c4583c0e100c62140c0f62907a2145070700b003100da81c08001c2e00a200701c0611490108440050f11400c2d0902c0081c00001089903e50311210481d6080d10282414103200302156428800030401022100e80c004143e4208000c1b44180002c40c0c0c0d0030100240d0242c1c1d0710107403000c40301544800c3d01306100d1080c4000c601351442c00450800049003260540201001a44145403010002e4000c0000708200c0d130008150400708907081e80002c0da1100121a01c1826945901303020340700384010702988245030814101a82851044404214000128031840141c40c03c02c8880460316402100b000869070310610f0140300c40035103101d01c2030140041d148124090107404000144e44a000380c181d03080b8000c6081192815015014219071941041a100c10041010000001d803540e0360030b5010000e00065070055008 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 78431017 1250 78429767 78429779
    0x18070219030207052818180f03020f030307140901050f070302010b010206070c0b13030c02030604031d04060b03180708190212060708011211090405031209010b031b040212010b0301 79
    0x1100071882c54250f00d441a02842c0200c4a50000c03030050b12100b43c0d050344d0541c1d8046ca410081d00e00e81c07074070121601c1e4151010003842880c0698000e2207001340c0071a55002140c0c8031440d2f8a20003103507614001a00a0050088200418010464144141f40180c1460103005031440e860348a81700c100d002d0703035403464402c0c2c43d540c060100960109183c240444c9529032030f1a0b1040d1890300419643c84c0d002500544010180512900402560040c045402924151034007405083c00780c0c40005210b40c2c46110038003146462b0147c101660709a542080c00c5459203008542080c020340c170520321900920342c01240070141000f0702101e0401a20780d41011000324014010800b09800c10702585400400070070502da5003107095681156000ca51000089185040c02d003030f0b080100d4400741e4052004014441803042c004040c00118010302e03400ca1458581c645020700b290039148465426401c040300b0304440030651403100c0c05101000d08090f02e088428800042c201d042600488101c00000c401400a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 78432267 1250 78431017 78431029
    0xa0602010207060e07080d0c080f03040b040606150c031b080f090f030705060405012d0306080c03010614010e01030e011b0f0c080306041805011109030d08061807021903020705 77
    0x9045651001751a2040c00c2482d01500d500700a00300c9001c0c4400f030014642000103140c00c4031b20030350500700f21503140c1c20700b031600001d201030030f1381c007600d85608104001c5244410001e0f00940d0703608985500d1101e45460b0b5040c0c030322142910740c0e103140203400103015000c55401c0000302510342a4240746e07581c1d20111802c1080c0c403407036851154000d9000440c01d101a4a80504480940301c00f400e21100303100c203912501c80f50f42c00d084e1803200000c140c081f0800c501d80d015000ba03407c1d0b400300d40c1510000304c41c01c000d050880c1d29a2042613140c0c224452104c07040d5004094803041c0c044180350104a5050700d0703205600395050359030307025541001200c80e01c80c11a40035001c07890701d402d035140850144d1080c1d29840414000548610303c030320fa0f601880c803c044840359041c80c2c202e90240081c4084a0600c007008419008003c1c1076009000d008034030707014140704060140c0304100080c0070b0007819651100b041c1d01590000c104000398882d1103c004524216558401c910a200f680240562030802d000d000d1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 78433517 1250 78432267 78432281
    0xc0602010c020c090c0f0717031603140402040f0f230105010c03020c0402090607020301090c030c091503120c0b2509080a0213061a090f030f0a060902010309020a060201020706 77
    0x300319040365900342c049544002000707030040f0781001c0c90768640300d82c603151b00b07503038411400003c0100203040701801d0741281e1040507520800351001840c80c0001041c0301581501d1120800c2e038550601200080d0061502c0d9005060400603180300040194000200008032100d080741142140980c0d52010240c0710541462030140000b0f02c2c0015080703019030703406592030b2100c0c0d100603c0390390003045003042078036a0401c0e100581d400800070301414801c0c1c1483c9460000d203000036106003840c50401305001c0524024141c0311460750144205440c91a260b0f400c0715400b4423080e1017081108800a400328810040e69406401c0100a5034513008151210501c124403045402043c0a42190104251800801c0020303082e601912024405903401400000803c0d01c0d030494540c0300048200900310070a4079026000d00307041074234203030650010354003050366510f0041034000b8141d12089080000440c240c010405062060501003181c0d0300503400035004030007035048440180e40c040b40c0e00040c410280039050b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 78434767 1250 78433517 78433541
    0x40816080d050a020a05040905040f320f07030303020711030d050319092001020708010606030b0f030303090604021e0d0f030e10080703090804051e010f020610150c06090c060201 78
    0x14a00341e8036100241190041e2300c035004d0096690700006081c40b958040f400e03400c80d80700c51400c46d03c51108804071021059029901143d1031502179889045030002180d102d4194100d0041180718559601100a507000680803a00c0310040d081044640d01e080082c011030780b00b5030312060b80360b02e0a041140b80007440d0300218818907042c0744030300010420340c140b00784804000000d0002c5103028940140d01e042c91542c40344810307600c2c284000401c1030341640b04200c102c00c01c903440d001055408007096568042038400501e1900484046001480c00b40c01c1c00807a440c1403000c0356482070b0340000041090203440f03401d541850048044c1c9040650045170310343c40c2c0404585200107609544001801013600401001c10f069640d00d4800c113000496042d0740c010507000f0304c0880c5444600000e041d094100032403241c04500c0044000442c43c0c004190f55200e0151607138006100c510300074417036516a10440d16038040c004010149004254280030385400a0b015811080007140340400007406c4500c90354ad40 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 78436017 1250 78434767 78434771
    0x3090907030203150f040219020105090f01020c0c0105031308040608070305091504030302160204060803070b240d0c0902030a0905070609061b020103060b1201090609060b12040816080d050a 83
    0x300c0e0000b8501c1c11131620034401d590034103000c4200c0380400c000f4030902c03070400707080204c0100410b011075054010b2480b44810381e0503611139680b00b400550a0b03009040809500d60003003060040745500c1407001c1e59124911205034071400c031103a100d41190754466009500000e03054010000d5141d0180a01ea80009000004003805a10a00c1341c158006c0007410040805400046001c842c3c00f9a86442d8070440e0002d02c01c00002d6500c020f103a6a9a2240703804035a03149011000074840d03020707041c14240d030510180c070190b000d15820703040010f014074030b03801240c54142c280c801241002c45071010390b01c03c866101d4001110036450803c00d1500305154004403c000720024248074242e03000e04c4010f81c1034a88900d0504d00403007840103074050080c6030403400c4d03800030104a1890610002d000d59048034800401000069110007103513094a4482c0506400c415041100f0060f15600070811a07100c1d000e1144d880c2002030b404d03d80600001103030f02c2514a0000480c9640c10490b0f548a15600b105c0c2200003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 78437267 1250 78436017 78436021
    0x703031d06041202030c180619060f0e0a0807080604021306060206010e0c0f03010b0a09050f060403061806090803070806100503040201080901110a0e090a0501260309030d0906021603081803100e03090907030203 92
    0x30003040c00c19500c140c00704100280520403201e4a4dc03ca514000d00340b00741c01d03120007c0e140c40d0b042e039451030211006d901c594601191f40d0841c4080c2e102d8142030340d03600e501411050f820040d072004100c001918030321811000700f01900d01c48459802550182c4000c81c111503548100644c01060700085030016031046a081700701402030380d980c10413542240c1d80600041411150341501c0156645082070203880d25007840c003a081085170600003180f15484549a007821900c1c1d00741486000f11404610002003030007000450050b40c000e9400582c04002c000c0049080b01c02220100d0740c680003c005003000c0764826884900ca8a4100c0009a000e19050410455580342549606202d00c1080a81c0d108080340002d08824010610071550242c2015045032039402c10894001c241e03500520401c00140904004030480103900810501103e03004142c032810241025410710203402900c0b0100d0b498410200240d400c41c6481c0902020070111001540c2c50f10451014045100030081c90202003500c1041 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 78438517 1250 78437267 78437279
    0x901080c04090f0204050114011107050d030c020d02030d0906230f070201110601060e040501080604050a0204020d14100e0f091b1305090703031d06041202030c180619 73
    0x1102014428110350104902c991820300300942480360601a400c070381802c4c008a404a841c1c49001c00100c0300b03036a0420010708100141742c803a81035000300c03075004490000a0011a2182514001e90b40c002000210000e0a940c0082d01d001c891950180103d2807060003000080d41203240920b190040c0c210028100585064194040c03181014113000600c0114800003564071802d4600c0741091081d003155015619074034054210441480514441c3c1d00f04400070490300b030080360040c0510347c0f007001001c09101d19400c11019401c40f100b05031010341d640940c103810300000001a8011050036884a4549050440311007440100400d8000034040078402d00509000000e1107051280c0c2900c080c0100c1d001c035100103400c0601411910740010b040000348001c0c96030228241003268402d80f10007520340c20024040300c01b1044003910580c000740a0204000350400300c0c90710064648010705513044080e000c80090000d0600c9000c016109020208003c898149402c10701c8100e4241780c881140c152600d8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 78439767 1250 78438517 78438523
    0x2040801050a06170316080a0314010909170c030d1a0406030803040507060c020303161506080c0406052202070507120c0e010b190e0a090204121721070c051506030c090108 75
    0x320f00100300087c002a05007000d4884c1d44580207a0f04c4140710f500c92075075111002c801401302450162b85004140d9a6448121268801c613081403003448050742c00c0a00311800d00d8024034001622111901c01d10b44041702d1951a8421140514420b0f0f4040b03440742054200b03d032614009401c40418806049a9440580c1d0300105032184904c44201540c11099a0714101c4580043c041c6680e104d40c0c100f0102080700100418040d440c4001500c0400196649400b00960340c4410306114084130740b004214100d002c1e480e002000124080c40031110840d0b5920b554901c001c10341c1b40c0c103035410034544405004032440c52040c40c0c0144210415030b41020407011000b840d91301038148000a002054510184035116001c040006144000046455594400102d4540c50010320102d50180500c40300000135201030341507500300300300d12901d20820340d09443d002c0d0161001030010340030b000c1030305403075800070310100504103c40c3c4001000121505061062614213040e20440358850303034120b00140041c0c4400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 78441017 1250 78439767 78439807
    0x1b020a030b04050316030c12090608070311071a0f0705030f06040525090f0b16060c210209010807020105090607031a09101a07050303150402040801050a061703 70
    0x1c1a074503001621946051441d503c1601c08848625240303100e20302c14075801950301e0720124007800601c0c1c08480c012104541d11401c0e40140b0000c505600049512103110307a11036402c10401090b42ca150280c84e4862900d00e051801c0310015140500d8100601c0c0c02032058201c0e0441140d08150741141880f118047c0c5000d80206510f000c1c07984c600000350480c4825541c803000b12103a03101c04400120404000b00301452034040c44981c035030185c10009044d11850101c6a001d120901c14440c894a10351f6107002410082d6118410041c0b0302c0c00510300301e000061b06809030010041d0069580031400000b60a0100c000c081c0000d40e454101006203202c4c010490302e40c00481440e00003a00c1c514030803d04005240700c54444e82203104002000315000c2480080e505507a1704003407908031412624800d800070b103e003100040030350300b003800456044512201ca000c040000104050706158964448c1400c54508440c554440d13500c0703280802141c0d0120080300c030b5212140300603524000454004641803004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 78442267 1250 78441017 78441023
    0x70b0409050c040b1204020306090a02060301120501021306030b01020106092901050c03070f14030c0a110102011e05040c1403030a0503041a090f0606010801061b030c06020c030a1b020a03 82
    0x100c030005040c800300ca804840240c43c51303490003034660031800410b14080e4011a001c900912421010414080000030000320301070340200030b24a50381c20801102421811041c2c100c0c2c0d699000e10024280c102e08901142c044c14540d41c0004e422103100000900303442040d0702944c1218907004032240181801d003115121404402d500c0300a607044800122030500c6001d007440300c140004030703040003000240400070310340e9409905860548590760a5543e160300ca0300541c642c20b0382c025012040000d080c084000742ca40814000010351410640d0040e911000805003440020b982c0c004000c2003103613044a4101801e541c0705840d80444a0202182c0e0760701c656048481848404000a0204503440600201600c5d07403004a4915041c90004a0fa640c0d83c0c022084c40140540c000281c840e502c1500502d04a4055545038503054060b0b10428200c41c0a089054040083c130150600108e00d681c00242803000070f9500460b540c40c03100000a10084d5040c103030340c00c0c3c0400c82c85420096500c14000d601620f030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 78443517 1250 78442267 78442271
    0x910050c0706020a0c0501020406050408150112030804030905091602151b0702040603021c05070603090203100522031101060602010e0606040c050d0e0601050f01020105072f01181202070b0409 84
    0x5440310040d110301c6010a00141b440d800081c0215500790311402900850b50094215103090b107487c140030070145024003c4600300c0f060301d081400400e01c503150054002d4040c1c100803288a0f1100c0c0402d5600d031088426943c1c0d18001184000039550400a82000707614030350141045042c4580010f036420a043e00c1c0c24130200d00030801009650750b0f81d100070029036005000e0702d000481a4944128801051808e9171140186072001540c24001d01454100d43c0e4000c010f860015114842c0e00c000389005400c1511aa080c003c01d61039842032046020500380c06074070f840083d01c8045000c5401d6401d65007003c1d00b16410b24030607084074507000441c940c21503030848002c940041c4a40c01160240505a2040105030070084594007075500171507440e060300c901380d42981c100303040075005a00ba940e06440010005440300d58500c10442140740074140940a650b24200c1c2c0d41648201d00d0030354860045070072960003010300c41d00c1000091070000400c0320041c0042d243c2940761012280c014001c6125400e102a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 78444767 1250 78443517 78443527
    0x1080604110c061603050906010b0d0c050705030c1c02160905070e0a0603090203010c09050d0b0417040806011e0e010e06060f120402090f0105060405190302180910050c070602 77
    0x182010680d00098400c2e001c0752543d18124081d004001e030303004607482c00300385081e001c40c100400120f036482c142ca0705c00c41c01c0d600d0070040c0300442c0000c0c5100041542046024490f00000036028030041c20b1200c4480010040c0b5000405180011a280000d0310190b61080c60305118002001e06008200c43c00d0399400075065031500000d541125039400390741d074003c42d00c190210b001c0d90542d100c0840c983c0280c00800c5032604044050b05d4000b4580501d075800400d00f80c58030001450680c0ca0740e486441021111400d00301840d01c1005a04a40c01004490700004014400c0c00e4126040c0b280c510486080ca42c80700f464000801003085042c080d078031040f449034000885940740e00080710300203402c940740e1990310402100450179694054030103c0c450081c3d0070200340c41800d6200e66034180c500041441d443c2c14908400c208945a9000021290210366000000541c0da179115452122418810010b000c0c43c04e5002a82807828403045e1041c400c0c03500d0148856408054161b81440c0d510180050707a903 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 78446017 1250 78444767 78444791
    0x1e020c0c0103020c150f0a050106050a0c0b06210a0b0a020304120c03140f09010806030f061302120a0302010902010f03020720010309060c050c0f01061409100b07030e090105030c01080604 82
    0x1091007411503003010703145041c015424000b0035014821011f01604010356602c0c0c5404840c14810b503104030300050048010301000c92403603080141c2100c0c00500000030786c80d0719400c4500d142e800c07840010407500142c1c41401402103100885a200105d18404c5156140c25982c0b000d80d410203010f600c0c200410b07103e0030070403d0300600c682503040c242d0400320313600c4658090800c3c1503640403500042c0094a0200451400d081c0000d0700c08a1144e4030016044039942c030400303072003140540f00c0c003079900c0002103614415500301030151061641c000d900208a580c0103000240c08020078580c2c5170105441048010081012901804200c0d0008808440c4054215004074064054420085c0081d03251205003158103070842c00401b90b002000e015140f0160160000500302c3e403051058108405e5102040b082c245015140b4030f07030101031110080205505d1704a105001c0c0c1001c941140403a51440c05001640b0b0100941c0d03005007401c800810380000c0f40360009006c3c42c0c2c09015580103644440d80b075100c0d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 78447267 1250 78446017 78446023
    0x3040507080609012a0c03050a0225050307120807030c030c0605131403280c14010507030b040902010f1206051504090f020a080c13181e020c0c0103020c 67
    0x8000400480b00d81d4107103100214000d1400d148408211074002d03c0c120354000c42014070744080c2c4d1883e1101da280e088945c8050311141d00c6407002c00c003180100d0711141100c5046c6245031314408080030170740f03080030700304001d05185c003c00d07400110b1202421170080340003608000886098035414a0b02e050b440d1064a010b9400c0c0848134401803e40d81050108800f08404400c0190828003032400381025129110306035850b44210050142d94420030004903000394010401a42c284c004c0d8600050904030a0b1501103c400c0d403401301a00c942d440b0028004003a625004091022400700d40c200940440356002038021a00c0d480307504248411050101c03260a143c3e40a03030010300b0042c0110324a48041d05880b000f0390b10078020500601d2511038100b01c916014401c2c0c07207001189484032841903c8401c503a089030740140d02c100d00c3c00c01c1081c0c0041140540440c41c5401c03484550408584011080301208542034020307140800b041c030501c07100d0303081c00000401c2c940c03407042801c0040e03851a40c4c2c890182 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 78448517 1250 78447267 78447269
    0x42406030b130c0909110d050105100e16110307020306090d1d010e010f030b04020406050703080a05160804080421120f0e010e0a050616020907020d080c0f16061a09190203040507 78
    0x15007c07040342d10b80c0c800e0007419080184a02c08004410079519100c8503810209842695107c0031190700c070a2454405010320060004205900112810001d8544c002031502d80201e5240c3c100d0f030440c02c0000300d203a4000e45210118001e50910100c2003002d180001c015294402005040005074188001068004d60210103c148043c01c250354583d160040a0204d0b0b000e008200c000032a5071000038108410340c404d4600603000c0c91f100301090b41e14480e0855000c07a0243c0280c4a030803003000002600180640703407040081400320070811000441c20701602084ca030010380b10a000070223001c2d05245a0240a1883c1c01c0024280340ea1036441c1140803c42c003519136004a5001280056003981c64400c0781c16500340544200c4001042d0307615048102e0311032030001c1070180802d045001007988000120003a040c0201d00340381c110306100080e401c8044941c0700c14029202d2640e1101309240d110b94040c1c88541d1410103583c0c1d1308403400e080000e2141145a07440205032168088046030801c401401800 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 78449767 1250 78448517 78448519
    0xf020d050d020903100c1202030405030403330501030b0112050d110a0f05060f06060f030606030601030b0d030c03110102120117120304030909060527042406030b130c090911 76
    0x80c00c0b50040b1541240244001400200807412101d820f4087e94010300840c0d01c2107038044003940c100340c81d5a03921703268840188449521201c40003000e0909104510800c00c681100042c08145d40d49107040c41c200744201178102400e14000d060801005c51400901c1c4080c0b42042e00d855050440d54038400d605100600000400c00024080210300380000010814059908080304581c0c230f4850100704081c074411001c4c64650f40da0107000023012480c20748095984200181000f2401080e000c0004100074040003084001c2034101c0d00c04000c0c10791007500c0030b42844082c1d00071072410000445000ca102c0c0148280399201410424450150341c0c2403213858500d042c150115902c1b0f0401d0300d000307010641075000b420881441c0c0703e4005810314043e48443e89002e4101120301090a0a1800500d01c1c04d006109660700180d10440c80100c41030b9031102d400c1c50703e1000c00011520b00710318025001600241c1140c440908111015000c50f02c0f410820040302ca42601c0041c04801c18508000c500381000340c01 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 78451017 1250 78449767 78449773
    0x4020c031801120c03150501090e01031205040b122e0b130308040602060106031103060f09040c030b0a0f0b04060302030303010b0315060a0504091401140402180301020a050a0f0f020d050d020903 85
    0x2441389640503049070260039a0868142c1e0b0f01511813004460f24841da1150405040d0820010000300f8010001c02ca05d0407200d00d0501d00c1c00740c4440f000ca421380e0080c00810310402ca0300c010020241405051280500c007048210340b0381d03000074068441403809a00400c5074013040055000c90202c8041020702c021640031300601d80b9107540d20302c0a511030b0303024418100403034206400310385601d01c00f0040324071a070001400e001f1032000c7c0d0b005104480344001c001712004100307294044041510420007a226000740b9202040d5080a0903544007500d801080d29400f4500b4100280016500401078905480c00200344075129541c69060450074459070340029080a00000c0a03401c60707074041e0062056400450081c45071340715201100008074000d10034910007050140c039006062500d6001007100000c0c10300c41040c51070101d4000380c00ca0380301c003200b0300101300000307403001050f50000e50350107500040b030401103095001e0310070107901c405112200c9020031800080b07611a1000303079416560040c1c009401c03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 78452267 1250 78451017 78451031
    0x6092406190906021c120b2e031410030201080915040b0a14060d0303020a03022104020306132a032103050c0702010e04050a1409030405040b04020c03180112 69
    0x1c1d24403035141c00f07003400602034151816081880c0c2d00c03445d00140450750b546482c81300203210f003000a013440c055059102415103582c5014040709a101440001100000c0d0544042280b01504407900400881c1c00800c00000700300301124200d29a004894080c00d042d01c941d03490900380b5050903115000c40c80c074400900284824001420a02c0d840f940c003d040c00c0140080507105503204403011104a90b10030906032414002074030a4018089180103400c0150400780c1580b00501005d850040e000908034190041009600e403c110403a0011070b95210004100c1068854548900010020210b00d03e41c40d01080889209840030b080210b8019010000c072220900f961002c0704512094040002c0c1440b01048820050700100c52815a05850308640c40e0041d6041c4805000000c08400380c259a40c0c1d141c0440442c7c003440c00340700f407200d07801075592107040004000443d00c4002009000341e206101c0c81c00038807000003c0f41d2680c0d0f4000d1b0b140c0380c6d001c80040101c40d020020145260a6820180 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 78453517 1250 78452267 78452317
    0x3030f030603010b0d05191524060f050304260c2a0604030f050102040e070f021603020d0b04150c030f1d0706080a0b06070b06040506092406 62
    0x3035070141000700e000707010900c0c040c0700f00040000c01400280460b042100100040d01e054805c82c00e1183c030440c103000b80480c940ca945d6086880012800c1c1c000c2c80c1c00903001c0340304e0021101000c080c14040c00d28200e4a4800c8c00c00502502000300020900c00307080449002c40300c2d10070030728503c40412601007a81c07101242a030a0f151000c0414000010b8001704624001e56040601c90041c00c0c1c001d0302007410149591182c0310b6030740031b10205840d2550300f080089031860051007110b201711100d4071000884080590000e14001c1003503003503007141c04030620503c0140d80d8030b003513081520740040414419454a08102588480d1201110740d12847c01d20700d0344846805811100900e000048100301d40c81d004d40f03403040076103026108000341e508440d10078081c807809402c81e0394106c080c00c4c8001031683c455201003040c81d13000320b000740d80400d08182003000c545054014950700c502c05903030301252804c14800b000e00b0140042c01d565215503451951520a03200d1038103440035001a02c0100c1e4402c501c01c2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 78454767 1250 78453517 78453547
    0x50103080a1805010e0f01090f0605090108070201050f04060c020c09041412030c160309080a0803190e0c060c0118060902040605030307080d0b0f100206060301150503060c03070903020303 82
    0x1c81071404680050344110b1800ea070980250119841a12285074a844100402440503000181c040c10321449030000300d0104042e4805030094482610b0303456555500394000340042d60024002d2007168100030801407513503580980707540c10a034413150100d00141495000e03410121510006030b048100201080148210b4698500e4024816000d48440b10040c91030043c2c075105c1207520101c44802008062000140692103200b11402443e000c900181c0310300002c0d023488801a8140ca000d05c1c08028041041010382002d80c2c841843c0c0000c00028445c10100340d295a408890710348116000700340e0f0f0803620303402e40000b441030786140415481100c00b0b00e071986c01070902c804164001c524041d00429142000011200c0040e00401e04500b803444201e5004090203400150a0704450542c0036207103d0345907040e01001144070764005d00058030b4007034149401c541c1d0aa0400c806e030003820030208859200820300c81d42101c10354501507925a249581038030803503903940c0000d400d84000a401040c002000e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 78456017 1250 78454767 78454777
    0x3070914010201090308010b0c16031103060106030b010c060e03041205010917090a0e04020103020d0e0609060f1303030b04270c06080c0307031a03010f090506060904050309011101090605010308 85
    0x484000c0c0d000442400482c00c03100c0d896002400700e44c81c01c00501c19011900041c02c04078800000316a07105180f443c46100e95a06684116000086c0c004284958a800d01901b4054986858100505d450070030000380b8505a500025290b143c1d296558240040c080c070848001d07002076140324841006c50310f4190300900305508142d0b40401c1c41d070f40d802c6800c404441200d258003001011500300d00c0c1880c644007031110700a03208a0606a0800000c6030124407402000020810000502411b00d02600698180040102003105070002c00e02004102c0c2000383d100072509800d890001524101c10b404203004180c0311107940340740340603803070b240ca054440e10201c40c002c148a402000201e0341d4402c4142d032001d0303040e102d07501c11a03004d00025816138400c0c1e0200303440b14030a00c030101d01182c610011a08540300c0c0008100c1054032441c0c21010f00c2002c010440d0004002d0710094401c1c582604d6440e00d0b800b030000901d04000300340150000d022025080320b0203564000c902080759580d40e14280240384c0c00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 78457267 1250 78456017 78456029
    0x1b061305070b040b0f0a020a050105010608040b0601030606050315030703140109032715050904060b0d0b150706050403050403080c16080c22020c030d0b010806100c03080a02040b030709 81
    0x5118000b29011048409403022502d0301e45103d03080c018890204640c3d904465455011482503424100201d03800b40039484c0241a03a460707016850516040001c0303c0300008040b40e06150030304008100c1240e001046030303131105101903420110300382c0300f00007400c0ca0034680c000303419804132001c910014a010b510a008061294440c2c08142204807a08134100f0404001c50051401231034042025030340507148002810700c82c0c41d080d49031601080020701107405c41e4100850321440803c070045081c0092241030302d4500100c455002561042c21880d00502c10450014003694a8101082c02c142c0a602510061640501042d0700c0f81c1c00c0440880c0c1d00d8650501c00f000c00b44d42c0300d200058044000ca40e621010314060726110606035003406484808a108035034103800d69082054a141140c00e2001d064291580303100440c89014860004001e42c1011744928813408a02c0c4440780348942043c0e078003c0b07a981c1030800c1d01090713990f544204000e002c0e650003c00e030404000f00f0040d05a9002c4070300c20036514 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 78458517 1250 78457267 78457273
    0x7170c01080702070302012607030b010311040f030602090604080f16050d02010c12090f0e04060506010e063117060901020c0c0d02030c060c0d080a0218061b061305 72
    0x11804011100200d05550300e40140c2c00c418020320255214840300890f44500c4152100710b0860580d00e003456100444041001039a40d80d00c80019603418000c603192284114075007801e01d81000000c1034004102c0c88014100c0c0e5000802c151140ca5840655000b064000140c60181140d070907159160329252a09100449084001084c00d1074680d00842e40d4940694038500b514226650341c600310300101241c6002d11056100000d40b0000b5544440080c022840a61704e07141003501d042d00548402524580c10700c1070140e00d207100b64071504159040c1144480c1d04076010240c0c201060712503410241ca04c00c2c1a5050400881c6001101401c0c00c1c03c0180d6400322003990340e501942500300d0043e007040030919040141440c04500d040141e500707040d070005054070100807410000176013903400350301ca028a42d0801044402080e40100501780e000f80340810540c41d02e424030310001e070145102101c1c84e22586c00031a8900d8034003401419106141e0b420400c0352542c0c108806101340e00600ca51040f42d00344 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 78459767 1250 78458517 78458533
    0xd08090901300f020405071e1e0e01020703050613110402030421032403050606010212090d03120e010b0a06050c0a0803041104050903031b070b0c070305070501020f1c0504030206040b0907080717 85
    0x7610510b40420300c6410382701c5602d180f803500a003c5542c2e11042d00445c0c11441001c5004c000b054007880081d011f00b50050618401ca40700d46000d025050300e80c0202c502c10340c8180108808201c017a07108511030114243c0d00745041554103c04e500900c41e011002c03c142c503400220884100d041210181520300540458107255034410049a607200140c1060114036014010248181001d040c620560340c801c1c24800c4840032501a45422182ea03032001a0702c90791140d5200070381d814020420000341001d858810314207588400341d03942e104100c540003000d5a000000103400e100d030305104619410300042c014003103404e000803250b0752500191180282e02c01c95040b04c00f40c1070b40e500c040355000c6501c401c07030001030361b40e800c041d000c6604944001e9003840000c01075070001400c01c1c401400380c1072004001985441c00950050141100c0054800c44286824144070100c1d40005440768000e600c003038160313160b6980850f018241036417544407035514894058081180303090f503c42c407440380c02c140d01140c401c2d07 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 78461017 1250 78459767 78459827
    0x50301020306180c04080307050d14030408031b0705030705060f0a1a0d0f0c030606060906080405102004090204140f100309050c0d08090901300f02040507 68
    0x1d11060b58902d42c040340070082850f80c40d00065105901c01503141c800c50605075612003e5003582e100110071a20354126000317103504a90087c5559000005082c684e50551405584070541c13032201038900703040700101e4000042c50b0f5280314101c48443d58404c003070341e4594215107003240c0c0e070741010381e189084000787c580080c540300070324412010000611100010b425001e0f905000f040442c11005a840c442a80080740102d50303c020814001c610807500003c0b076901c2c040c0c2c02012000c454120704100070048007032102041000580e8000a15100e00004036200d41d002c261048203281581c8520040340480c0006043ca200d901400440328a4044000c800c0f012a040106145410000701d41c0000181c0c5904009031080d4007100c0d03580d00c0f5400310340d0050103a400003402e01403290000c403a0200005400c80080c2001d00610b801001c94800f19600c3c9207605640741c3e060300790012040f02aa400106a2042c484022519004a0b401400810850404850007441d00c004035080070002e03035113044c545000d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 78462267 1250 78461017 78461021
    0x1d030313090203040206041a03010e090303070e010e0307050a1511010212040314040b030103080705160e130303020d0e0f070f050109050409050f010e01021903061202190f0b13050301 80
    0x4404840c2204014050924a0810080d0400780040c0e0b0012403e0001050b034450a01160f0074000780c14200030341704c0d031400241244060005000980e207810a2060182c272030342007101d0601c41c075000d0074941c0242034030401092610740766a01c11580320991a1002481051000624003018500e540e04170300707001c0c224080703800d134070030b001c120407401c1c0d541c00000d800701c0e01c101070581c90110602e15092400b5a9540380c46001c1d0801e03041500c6008002070481c04100c2c0c1000820564a0003010300f0042c28908810101010001031100000da0b83c11003281c82094804d80c1250611004100200b03c0700080c006102e544820343c1300c903c4c4403445050004a00098924407060031507405030f5030840041e05240601c800391082060455441c07281e5550618900c03001c3c012881d401640c02c000586520090b07401030342000605a9103814185406014804c1c1c46e0608040c1c0d22240d01680e441d00d82e00351980d8106100c0c00b40360700100541d000840e000c2142c81c43c0714014401c000c00a910030f1070b4182c0398810142 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 78463517 1250 78462267 78462277
    0x60b010f0203120403031d030d1b180303030b030f0a0605060f0105030f010b07151b03050c040b0f030403051218010c050301050f0d030e060409020c0601080105130303051b0a1d0303 79
    0x60861185000100001c0c403980010f40a90101f01b040011804610006850f503044240c0c00b110241c0ca032840141504d503c4002d14030303d1446032404104a0200784c100242a04c4a404003408043d00d134080507041313485c20410031103c130308404200c40d103010040c1413540040c0029a100751151a43d000c1c0780c01150b109205907800b90b03d0711091202a40d2074a500840b0380c2d4058001114880004403802c03c0e10205442841c04041132002e1540c0e4191680c04014200c0700001c00107600040140001c4c05418607110a0340c00340592034a24039901c2d01c50741000c0e5654000e0000b403009404c0000200302a42d80c0490301a411405c5c8800240200024047d00352000d00090007031580046101200c040f4500d8000c44020345170303010b41403140d4042d0128010410303c0d442070308036003011900041c003511013a508101442c01800b1880081103142800c010031518a40c114002500301a2204086900e07922102d140c015810704004a9907a6440d111001411310711554001071641c6001c602e240e0054200801240d0f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 78464767 1250 78463517 78463537
    0x50a0605211e1e15190b01030c02071802040b070f060b06041419031e050c04200d0b0406140f0301050405070b0d060902040602010905060903042702090d060b010f0203 73
    0x4203204010050042600fa984000441c2c0d51040030b00c009103900c4084809800341007400103000c090030100c40260181d41c1482d0101d8109440c00c0d030101c10f10750740854020103440c41c4a0704038020240384040003020303004580000c03148003400150390040004440500510030f00c40c5400f40720040d80c24007000b1241c01b581c440d210354400540300c40c1100b8581041494001040154012815131300c4e41c88281c0b0116103080346400c0207003507814200520400f0441000300260445003030080100c082c2c03c446452100284207844402c02041350840c9004540001c9480031000d4001c000440d9200da01d00d00e00035900390b03414000c8030010414000d904040c05610300c00d64101004003841840c0485040483e845540035155440e510a000b00300050240024030050050380d001041c20f211a007001ea0038031700003404000355a40200810854108040b001c100e00d814070641d480e82c201e41c1c1006040191003400032040d440002d641c1c40c601008810340c040804184281d0703078140c0345a13032140140c0c0d40f84602c171060 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 78466017 1250 78464767 78464773
    0x60b04061b080a0509010224101e140105041a0706050c03042d172a06010506160b0403110d020c0d08030a0915200304030f03050a0605211e 61
    0x400110b138025001071a0325401807040706d00301e00308005074a40ca00351079840007480007000c0b024010020326000307150014100085c10510f11560243c13034030800340410311912140f00c2c00855480b05c0f507800340c4240e40040c00c504c11107100c06120508a00a55171200008803030f40f6103040c1c0882c06001101c800c0d28480c0d44c0c494483e9185070000c40c003980c9440c101d80341815180015444100014504213490490a5483ca0080391030303502007540601c120030880c0001203002d612201d25050780c8400684541150300590300941d8691101141000c0c480c4c01c10703c041c241c41240707000d100405a00c1608800001c01c003c0c02d464403106010402c980301c944e100561540102c00b0b503000c1005c91454030080d9002010309400280014155071080a0309000c10080c241007030707540c4204104034a030965011061030100043d01d20b103240c9558054420000940108100740d51500000c5880711300d584103501805005101540342070700711085540080c80c441d202c0c0101c2c0100c00c20721202d0a2140a10609200f0007006 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 78467267 1250 78466017 78466027
    0xc0102030916231c0507050f030613030c03090e0702030c0714010c030809150106020d0207050f012106090f020a09121a07030204050405070e030d09080d03020a12060b04061b08 77
    0x102ca00c0c00884290184d8421055403c415609000301200e060f16403044000d041d10515050400c000d24813180c2ca514043d400030001c00034070540e80c802c500003035503040c103005004020604045910044503041441e004140c4400d1114441d00080684003860486049845071601c0e103003442c80056411a0103404100c4035450040001d0082d0690350740b041039182102c223091400d114841c11440203900143c0541c0040c481305d0021641803190201818050b20706c4140035095100081c54a4a1b095080c0f019070030800c40540c280d4442e400504c0107140030001072240318001d40c1c400000798031004002010844070360300050303d80301030550f410160360480408240300303150309074841c0c0e0400010b00c00707410142d0802011034155514403400b402941e00d0b994090480c00301e10145031400030986012030034440f05990400204000003074101e82102d00d481c026031280300d280d10540e0602c1000301c80d180c030903040540125420b07640c031024104031506540c81161451036050162050112454054070700001001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 78468517 1250 78467267 78467309
    0x1e060311060a0203070203061e01230d060e0d0f03060f05060f0f040905040b01050f030303040b070f0903050a05030315060316030209010e060c0a0b1f0311030c03030c0102030916 78
    0x2e0034081110740103072403500405600085c10400215a8444000c0b2006102c6c0c91219260f140039015020f8400780035900d8561900040743c2d00100e851840c031030b62841e41c00c0303820070905800c07105583c111082160000109000080e0500d80c800c090300002030301d0440000340d03007a40e2030948000c80c0d0001d000145804104c0214201550115840043c2e2030310421001030468641d2068520641c001c0c03c01c1b000320750411081047d01801c0b450001c2c0700368424001e00001c00c00c40180a0f40102c501d0912542500010005903440340f016070028010f805240814024840040f00443c89a00f07101981d241400046003040420300007580d02e8082017200e032440603003440c005d0340108100341050420011011200d0000390450b84110090046604541c80400400444034441c5412403084e015250301d541001401c03c581515a01c006030418a407825940c4443e1810300192680072400783c01d03a9680d00090003443d000c0e50081d1a003003400c0c8114240462040d404001c1c400544640f10b11805141460b00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 78469767 1250 78468517 78468529
    0xf0e18040201030e10050604150e0601031a040603080d0f090b18070e0103110f0303090d02090c1e070c0807060801030b10090e070320030a02010c03030f020304061e060311 75
    0x140220b0500d80c0d10f0702404002ca02c100401d400d0402c00140c00b00d818500035042c0300688a00038002d0388000c15050050250049205545500c120700380b800240b1500c03c03044885624484066580d000352801d6000310a1080070401400c0c1c050b46020144095030010401c00d08680281102801154420340811400c4155249004202c184e0300111184181c0300e041c01c04d010002070340219000c00004035040200e050000d100d104004084000d58201010040890240e02000030020f00c00c4c43c100d40010202d0a003141514504010341101c01a030710700c80310b4000b1882c1d01500c41a6240000c4050003d000b0000003100c405440003690b608076264a11740e00c0c0350300010050030f68001c2c04501c00c0c011480d56060701c20399500d15407030f0009014171403030740c10a0700c0c0c0400c041d802d184144024641e4124681c4000400c412019030a2802c1628520282002c500410b000203103031a407940000144001d01140f5007201e80701146081d203003840001095151004c440441c4401440180311f0440340c282880d00c4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 78471017 1250 78469767 78469771
    0x90c0703030f0c050715050906011707030609080306030712081605011b02030a111603030f0c08030f01090609020703091703040e01090212090a080403080a03060e04030206070f0e18 79
    0x90501003044028a002c60042c0e508091010000520201d04101444446d944014040c2c2c4005020480707030400c07903481c54441805016020fa07224441c8000d00c410b100411080c0e0055030821400c0010040324034102d41c2940c0250f400d540329105807100480c0826041c150b0095a47c0c3c891b00701c130321f04049000051682411528240c82039507071f400c46060b086003003022500841c0c165a01440d582d00c3d4405002d0028200700c0306040b07042d0303c01e5903900c0c40029048250010780741c05040024a00c101c40703c00721004004070324010a644008414020701410359a29079040e0b400d80e800900c01d241c1c98404003130484c001c00d0006400210480c034208240c14500b4125181c01c0c4010055031302e41034a44811030030005085c0e021400165002901c1c40c4508032404140e5080b4641d80040d090900303a1f80c07520010f0380110701007e801d02e500080c03250b03c91400790740600010413212141070018a41800c1c0651a9070007203944801003041180144901e0344101222414141d00600720150840c8107a40749202441c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 78472267 1250 78471017 78471023
    0x90318080a02130615020c040f20030a060f0b0901033602040609020c03030901060602070602030d02030c04051f0f08090706080903090603160e01050712080a090b010915080c090c07 79
    0x35031400403404803c17980e180203400c0070907001802c40401038020b1004039a6000700000f43c00f0310f0041444110700d84c14064441d07090900240c142c0ba521500c803d5001030280d03901c414609401608009144203280000e4401c4940c240c070100903400c0c0094a00d00d803a45055102e000102c05040000d980605441c024002c150001d400003c00c40e03160b002180c00c9a00c445130800f102e0384040104000c5403400d0050b007011700708900c0940149403402e20041d40d00d0090303000502c9071503000310000d0018072a49003610300030800100030302c07031011024081c01c81c3c031021240d1707030380010301541100c1c22078034003652405003ea02100000c0c103600e07150590071945907001900c0500d1a000c20851040c080d5a1400994001c3c0083c1211114503644c03480040d103160030046072107052120601c100c1c0c0c007103000d04400390104226030501880c82c3c5c1c0c1d51b0305204003c0c184803100401010312400080b40504166000703406d80c099200c4502e1150707072620400caa560341203102e0981d12010b03010000d408044190302401e1560300c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 78473517 1250 78472267 78472271
    0x2010f05011802130b0d06140a0608070f110a06020309100b1c030207050a0b0a08090613030806060d0504030f0e0d02060a0c020d0b0103050109031215290c01090318080a0213 76
    0x44c0f658070005842d445034038031b504803a4071100300380903994040d40c40701c104000132149440320925140000d4001200104114140000602c58000c0c2e14000c89006004154600c161000d9103594509807000307410540d00060a442905909411201207215101040c2c200070850850181c2100c0c11203602c2a0040c01282180110100001c05480320008140500303901d100f4162503074451030780180340c0c490040c280c40b0698031038800e000a130520312141001d010380600e0607840c0765848001040d1148110111915035501c2c3c0bc0070801851b40c4080c40316815046070356100001c03407d1008001c00ca107011200694404010001081800e01802c00040f00c40d03c0a04103000200482d110411034000907842034030141d4440c04403408055000386e4104030100350147c00c0084c60044001a007030b14100f4051041d060003447e40c00c0030002400308004600c44044210540d48442c0c4000b0383d40640854501280411034441c42058141c16812000098403440c400800010b40580c08001443d5403038154a0700880d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 78474767 1250 78473517 78473519
    0x52d0a0212010f0905060d08040306020a050417060f0108070513200d090204050a0908030a0e0c0307080106030b0606030702030a2a050114090607090306020919120302010f0501180213 80
    0x1245a041c442c0200800341d50310724800d2411042105403032004005500ca8040c5415160008424205550503650401c00c0141c4034520050f040e28640718540149240c104a0600c14841074800242503100c1d100c0030402001c6a6a18400c0660751003d90080a501800e1010041c2c880182c91780080ca041c02203c0c0311034024001420b90100a5001080703c00303600e0b842d00d130010298207090281e990081c8103180100002c8240342c4527205c041c000640b0052403192208105000c0b20710400066605a20007411303551004d5840d102c1d0745c008c0056100448403500f140c00080c0c03252a00c5401c0c1d0b4810440c07a000385203003880f910002c032800503103420444040085c0c088040d04500000000800152040000080005006030f6800e600c8030001e003007040300d5002c001040880c5601480c0542200d510031000b58813840943d0010b201c00510480101050f14420400500107210b40541d00d189800390b00208410300c1c40d6031481050302c0702402802c44520100b2001c80c40f00355158014031089940c18a600002 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 78476017 1250 78474767 78474787
    0x61d09150708090c01020604080703050a0e09010b180f0a0e0726071107210f02030a08070b09030903120a110717120c1203040510050c0d052d0a02 64
    0x515001c1d2550300000d4061410404108001c03c2141ca0010302400104900c1c68156a00b40483c070900310001c04021000c00c8141c4842d014072600416240c00500300390307042d0b031920a0451281c00100540300d0309101c04a01051a0424507018180d079100600b0360001c031414500d6100204d4070141c881410006080025100e18110780b0039042e422a0b01001102c1c14100044010180f0362446030390311803604848801c0000c1ca80b00030b04000050034031121001d1508660906000e10749485902a405002d2000c000040224504c014510580b04006c0682e041c1c807541049a507070700480c6e40942d01540205000111001d011001c1e0007240f000d4900848501c1e007100b845410042c4981c030442c18441040e0442404031010702c1908845440c130350015040000c500e50326a514101c1c000407410360400080403c00380b20302402403085c07140c42171609008504002500031030702e42c0480740c541301d018234107800305880c0712003203496422003000310401074400600b024107092420005818003166541c2000403c0013 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 78477267 1250 78476017 78476053
    0xb0906031501050c10090201030506010813030311090604030c06021608120d0b03030706060509010801020708030610110a0b011410080720070e010503010c08010e1b0706022803061d09 80
    0x405845100c0c0406c0701c80540c800501502c1002d00050305000ca8102045000c02c10a404c016895815140120321544818941015449940c52168101000207000300500144009a1017156203a600321460341c1a0080800b000b00412f000355a20f0741c000f40440c40705090410080c040c03118401400183c00002900000d18580c07000301c0480d2181e45030403040080d880c0c503a0740300340140303400310095203840a10b94411402d03210040c41d1520504009025804451064128194646052040303400760384003800e02480809007441048602882d0401e8182c150420320526080a8480d45408000352507040701038036801c21004034900001e042c20721441284104005207030060001850400c0f555042c84180750035145005426000d00c11100b004110a4103a4200c003584120340007411181d914820090000a20602d1300141100d40040b8031070700c001c0603065600010000744e010030050390110b52810f4003680e005205d02c0f4081072209005e10300000034000e11591068007e41507581415240540701c134 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 78478517 1250 78477267 78477283
    0xd0f0209040218090708130b0c040302190e060103110d0b010c1209061106040201091206110a0504050f030f0706030207020607080301060201020c0607080105030a080706021318060b0906031501050c 86
    0xc05500f000500f8141410a90226500b02e203407490440303094a4000c25803201109810401080c2c1901c4900140c01092600c0c2500e018513401029a440d4070740d2100d412a24004500030603142c0e580303210114030b031903020344290080341400c004800c0c10503030f40c41c0c407150083c003d00e00018140884201d140000521a0055001e841003030f888424400d0309151004003103001d80214520150701c40418032003d81c0c0c015030000210381c819080b0b440d8890070b91400340c2c040d03c80c441c0791808a1001051141d64940c0080c05041075910644442003064030550406980d00c80c40401d61540b9040500e081c0445071003a0003d06406001503e4589840720941c1d610f001039109910100060354007051800d002101800321541144151900201a5040600194841108100c0240070780c00010b411400c0000c503405032035a0007080080b4201c01c6a42e4001c9840000312032400c01c40180c0b5103440418404006801d680ca201805002035045540d002903e85c034800c105030150303060040a0003d50100b4804109000c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 78479767 1250 78478517 78478537
    0xc030a150b030a06090b060403140a050303070f08090a0b0105040e0109080409020304110604061b1103150910020f0301051002070302060d140a0c08150406080a0f1703010b0d0f02090402 81
    0xa80c2c82c5449800341c0203c800e0ba800c115800780c14900300310700c84e580d008251010342c1e4000b1024815142e10180305444d08c1110340700102035000120820801c950004045150701d4105c0d10b5010041e910044055265824140010b0403259010700500160400d5401560841038050000400d007a59840b81100e9410590040c0e14050300001048204505904000070012041c2e81c0c03942400e06085028040f4182d00f100002411001e40300c101c00d01012601400d600381010303090310000002e1020700c050b08641101e4501c003610455002031341c01d00442c030841346030158000d00740d0304607400c000401880c050b030000c0003000c502c0741960100c0981c0d01d5034001c2403c00c0640c1d000041610001d030381002d00410040c00e080384c1c1072400c07200da9903c076000492983d00210031001c010341c0c0450140001c0050050740c005003410310401d4498000c118144111036101802503124010b41c0050360900a030500c024055125801014452443d12240e01d800044010900c0c400244c00c02c07204d036000c601240c0010b01e01d1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 78481017 1250 78479767 78479789
    0x62d1c05061201020a020d030203040606050901060309020405060a120311120a05190c020109060c2f0f090c040b0f09060a050d0c022107020102150403020c10170c030a15 74
    0x72140e5031925054038070090740804001d40c109000d080006e521411444409000d16400000240070010380e54003401c058200241514001d5844d85402001014103102c103e028501c6c2c036001c20102c0c503203600340d42c0841c1d04042200300419256035044070390000c15041800544078101810740900c2421000c1d10107658155a01a11410070f0109908410590302c0722500303200600301d90b80d0250340c0c064004000d4a015041100d18000e451030010760000d40c000100b0340103000000b081c000c605a445e103041c1451402c07103402041307401600811661002c00e0b42c0046000804010400c444c50401e00a09410403240b006181446174503804102e4540c003480a00c1c0c00558000b60440d000740052262141c468050300c010b02c0071004200100002001d40e003001d200c684004907404045a01c2004240485c100b11121941c1606040c54060750710300c11f0401184c0f042a481c42d18400051040c2d2102203103940d46211240381c0d0301e4103414909941d00142c40d414440b80c542c8038410f03040d000c60070080300800d0f0a030702c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 78482267 1250 78481017 78481021
    0xf0b04020a0f0b0d0203070e030d0e150316030915090503030a06360207050313150507050607030506011718061302031b0a030b0109020a0e062d1c05 65
    0x104501c499003500001c2e200c1c092250184821842c1600341d4169480240c0e0040c1d0369158039a098030a542550022607241c441e00c841220640d40c40580b0072101542a21170141800075501c042103107000c02c5400e154201581c59005c182544030750055030700355000e402c001f0500c00340301c4408800d17500828019280d540c0000144140d43d90144280f1009003500e1103a041182c0203002020300f005084030300221816540c0e512404017001584c1155152030340b0500700c80d0f840001e8100c81c00e003551076101d090b4401c1382592410050a02542c202c803100740d03110000d00310503540d00c3d03800e078001c12007c1e00580c108416291070414804291500900070040c410b5510034a005890526250040c028540c000300341803418490016240010b01402088600845521030072800021440754003950340043c1084020900004409900350b00610400c0000d41e18507003800324070f10521001c1c0c4507103081c2141c0a01a45112808400b6002d01240d40007040842a45400f903100d0300203410010004840e110341d562030007 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 78483517 1250 78482267 78482269
    0x6030201020c0405010e0402010e031c1e020703080418140a05190b0607060915090c0e01090209060d05100801020a0905030f0708071701230f0f041106070303090f0b0402 74
    0x72002c00480215400c2c4103541c10003205441307100020340002c2c1070001d035140f507030034035603003800161440f18244804c584041d09000000340b54186442180700041900390003071400c85d10108000b000d507500840302070301e800d14042c2c0813208070401e4610715143c1c5540b1048044070224040645010340c02a441c0410b09081c1040800307030348900001001c143c60300c2d00201502a4070b4880c2500c0b92203403c02c0c00001e03d840340c1d003080d20f034002c8443c0903150442d12b02500c010400500380180c5003550038030161280f480c4e0321040c0c142c3c100e10400b20030680c4144248000c1c06c0124140e00400e43c891850844070b0031a66944034168207a0304400d003000045000305405100320709080140182a5044100408a06280c0709045444203210700949280d0801c840101e103008109400c9103034007008011004980110795210340780c0e074084c01d91340068403101400c0031030390352a2640d5180780500d0b040a40740d01c4c0d6040303d008010759a03006c04400c13818141c448017050003154211030b0081c3c000e80078690b41c01141c507141c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 78484767 1250 78483517 78483523
    0x601091d0606010816050c1c0f0807050d020706020910050301140312070201081f0602030403060605030a02030c041a060309070503010e0313060f050c010f0b0406060c05101a0a090603020102 83
    0x8400c24810760086080010700e80e48581c41a0304440265098441d180480c0403c907aa440f4a00d0340c03a440344102c4c141c90681d282086501310000006a981907080c200c00310b0b0480d100352050312604001581031017219524003450b030051602c1d6100e400700601d000489800b207000c0400b0350806d600825004401000720b01244a03216180f54406c60180100c2c001e4909541218064104080c1c100722880c1c00280c003880104d1902d120003c00c000480c49499640c0c00c0095a9a02600089070004e0510100007081e040015142c28a1580100500301040b45001032100805a0640c0020b5041c54030b01080700c2030310307038000940c0146024005040001d0a1070700f0b05080d5491000e002da6541d004102d048811140021000c0176109145850885103070301850403211402600140134495207003e03140a00d5400301c1c0c1c040b880c00c0354140e070280030160342c8603000e9a03504084032014101e074100741c010003542c0245900a041c842c84d00c03040002001700c18000f0480d881d80c1500b01515031544d0340720900641da010 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 78486017 1250 78484767 78484811
    0x90a0201020c0d052523130504050c041e0e0708060708060105030412020304030209090309010e010915210c020604051015060c02040b030d2303010f0b0d0b03060109 72
    0xb655510450f807001c4d901c0d40d03030380d254210140c5007001500e07480300310710040305800300c0051010a4072040c0e90000c031008074107118804900b041c030603034848490000201d00da019451245070003030081c082c0030b01ca000921010344100d0066030f089085404000c0d03140006489585040c2c01040001c006082c1483d65052178004050955414801000e0800c09507030f03800f0044a41c8240c2c80b8505d0307281000240001c2c0e00d90f0299800c003c2d44018480108000070000201800988500b40d0b1109081211100151034a50303090141d081c61500c40240c82c100382d40900b040d1010040004803400c04034020030180383c221010411100c00607000700d428003051290401a005810400c803000b00b024002000c2c0c036111a844601c10403042c04004207031402075548540c0004540303600601610107000c683c0d0f01c0105030707410001c502c8030130803110f030816401e0280880c145d80c181c07a10300654490706400c0041550b2070360000e860b540402910b422001480d510148012802822800c401044080b00010070780000194 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 78487267 1250 78486017 78486019
    0x9070f0b0a030e2b050c01050106030504151b030930091a0d0506030a0f051606020f0a021207090f0b0a050f010e06090d0c0e0703111204030513030605090a0201020c 72
    0x280903200d1120390000c00d490714541318514120700140054169114011511040015481c010002490a0301900300c148a0b51003500c0643c2030001c00300031742e41103501c5a8078050705008444580481c0350b01a62220300c0d2079001d54007001034501d010145e05046030600400f2000303080f200c9007500070b59030448410000341a103168a40a0065158808420b900600e4200c1e14603a445401092158070f0501c0341d02c800c82c3d00140b80e1f441c1d280b141e00304a69200c11a50103080043c501000020351280f020880d250406241401b8003501202ca800f0810742c041109000c11090140d4580010751050a11406100340e006040100340c2e280a50b080208800f001d50145000e889403141446060780d112001c40540181100e65644070108a40851034802460744010328240c10007a0106940c0525003525120b92001d5400340402c2100c01030b003150500420311481c00d1100c552002c10000390040014003500c126000780311040035030340c0d01c0d8a01942c000f0799400d03045811005104081d540c0c10700c43c1005e4031078 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 78488517 1250 78487267 78487273
    0x50c01030c08041110050910020109141501150207170f0c0d0312050702030906070311010b04090807030809120a1d0a06090e0618190f09030e04020309070f0b0a030e 72
    0x3500384c5a07460311082619500d4031a00f0180000241d8a0141c4152848030002819005410b556201d02034001c048840b02590300c0030030030386580c61340100040d08007101424200741c1606a4a48110000000c50010540f42540184000850941e10144440010a162a0040c04064280d0841c40d003002c5642a10501802c000c003058404641c1010f24950f12110120000401c0d03510300204a0850142c0c4505540c05000010f02005159200d500f41d506605040020080c40c144a0704000c21120b003090020700039081881003102090082da003080c0e2024280b230036900c1020701d064201c5000c2d80b2845224010903408668030f2601551a00078072820a03045d9099861107007406000750862000f8424101c0301c144a0340028400d485607008000283c901600961071402d01d442d0310501800c030f03440b032202c10b180340c0b07002006292030790301910b14280d405480d2590306031a504e040c013000e988010000100303131050000000701c801c1030068602c02824820001074480f02c031141c0c02419200700c01c0690800b64 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 78489767 1250 78488517 78488521
    0xf0d0c02120f0304170c01020706140105011e0504030b0a0509010c0c0804090c05091203120a090f0f060b0901030803061005030603060105010c0512130603060501030207110405090316050c01030c08 86
    0x100381504031600c0e0b000c0a44503507200ea071203103095080480540c0c41c0000820000c54403a400041c15006020441c1c412101403150328681180c110f02e4880900c620350018030326501182c9440074160b0001111981b41ca0075a10f003a807652640c1306c200005480d407016059485040242c0f02c0710030310410342210b02c03601d0406a010641c0d2100d0105015a01a2100540c0d64070103101c46640100211601d1100280040e50b0211404d00455101c3e0440d0590311003048500000441d0340c003031440313480f0034a5480034105144a189403178868251581e01002c07030b09103175286504002a40c40810143c0250322410415541e450020180900c4204c1e0183c1282842028401e11840383d9011415a041d11402c1c6042d96002941c2e0801520348841410800c100c2d5030700140030f000a80e21059039200b6500d103900c05100f11035880004404900c1100c00c05070400c0b07000703090f01030340c0e10700354200b1382d0031100e41411641840c0491251140341c001c012012910703903203d0311010800d5605409031001c00c6200741460200d034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 78491017 1250 78489767 78489793
    0x504030c14090a1a040905010603020910030807080306010522030203010b01110316060b060703020c030d0504061d040e070e01140a05030a030c0203150705030402090f09030d0f0609020f0d0c02 84
    0x1040d000d0700d450f803a1038482c0001d0070381c05415034480d28074610003002404694090b0601900078034032400b040c0c1c0140c02e1200045d04403503160f00310004403540400c4440c94034541d44c551000c19080a403000e41000400c026400011144030029880c00310400d070506209451881050700b12014907141c141030081c40e540007200c1100206c1603d104042c5841c46008071192894400c00030301491450507880080421142c0600d9800100a600c50b0003e808503140e03055002001d4451b4002ea20840c0006001038441740c00490f030152400c62400c00c05070020a40c01e08181409007409a690007617a10076003200c004001a0080903895003900105640d1030b401c050031b140100c0e0b298804480090140480080d040085440800c9040d212401c200264402c90404a10090441c2c0c01034a0a03449030101001058805002c0300306070f400b52083e2801107240c8040d040c11040a040481d11902c8003695542d400911003007a0b00040030f9000d8960300340e542e222244100b16045030078142004045602c9082d451140c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 78492267 1250 78491017 78491029
    0x90c0607020d060902090f010312020604121d040203090c0310140c0a0512010905010305010536010603332f093c030601031202030c030301060504030c14 67
    0x4590107540c00b014403880d07420a00060034410034000c2d04600c1250811001034804048a8103803446540c000f0300941000400300e070740c1c0a0642c1d000d05044182c0714603018040c014011050129011041c011203c2d452000003800c0780c004039001a00343c1c2040000301c4042c0303824020117081440004041005601c18040e2481c07401c0010096540c0d880700140282c4034902940c1501c641c0507141c3c040c07200755038403844144003a00c0207200466140d070903c40420721030750300d044144102203007080400c2c21015100d4407460341030310788900c0041a55603c12010000c201800440c0f8082c407050310101d24540c02412010f13071031003803462800c0b620501c3c0c0ba006a01c0c05c1d011084d0a2005804201c91881c0c4800441e00911540300d440b2011340e221480c0c01c0c1c10b031915a88028a03100c608000c6100c401090100107c01200f00780440f41a035060b002100184001a02c122503128290243d2044034108500d110600380380d980207801c064040ba001007410010002100882809011000b046000022407200442c80c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 78493517 1250 78492267 78492277
    0x907060809030d0b031f0213061d0105210a090b1b040504050a06080a03180f081911030d090e1021080d020d06030b060a080607050c01090c1706090c06 66
    0x32101d134450144c1c1c10030741d40c100305050b10801c4424900c0305912044080c88020340c000101500d2040301400001540b50260100f182c04440c8031403040900750022004460a52000d9803c09000c10212652a50701c00c140581030b00c202010741e0002414542400d180229010082c540781002070100704020400c101c1c0b6066400711803044d200420a911031002101c080c08554000c0300307051007014860300915034410328002c54400058281e0305225210440c3e0341200070301d8056030300c03190f1028200c070f044444101c1c004440c0314010300070b03124003611990000b07007840400c0040e4000640111024820303000416800b030f400001000001d1061403414480b10b0140d079401079a810821814840581880200d000311020000c08401c11555a01e100781d025000f40301070301060341c44a00c1e503000500c141c140a0411340503190a0fa006084950729280125466031100b1001a40c075500d8804000024200b100c4030703001f4122800c20103201c0042d464800385000c0c00107010011a601240e0b0364005900c522007261 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 78494767 1250 78493517 78493537
    0x3091b0a121e050d0801150e0f0604030c0308030a0b0306010f06081003050d030e160b03012c0c070b06040908030c130e040f0b010603050f150d051203090706080903 72
    0x6001010306122000404034404480c82d03141c030300c03a00401c0020101d01001e8001c540c0c0c071504071070f0362599012001d042c9803002003070200b50740c517a1910b80380c0b034042155400728100410302c0346400c0c0c0740d60380c0072100c410a80c800c403030b00c80c1d000c400d00c86280c00c0d0740100560b8110941c010903003580b400060400ca42c20324072820052010210100d9400504c2101041c0651341050441e0004100484000c009101c0c0e040b599076907001d0447c1c404159813000e03941400700e510110300541180d00302a524ac51403090b10310116052005031280c80704c4240c1c3c4101d0140700361500d1160b141c982c20f4504003400302c440e0040000784220314100d162800240d103801600d03000441ca03c2081c0e00e8a05a6880002034545900080e0100c0c4066007040208005480c460060b1441000c049076140d90356502501500c030700741c8140c51800b0700030000501d0052200301c5a070036400001e04449c6e103642c0a446040c10b022881c1c0d2401140c00e03001041101c80c0504101403002000b83c1d00d810080f525040d0860780d200d002c0c601c103003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 78496017 1250 78494767 78494789
    0xa11070f080904050907060e0409080909070c17040306110310031401020405030a0c1a030106020a120306030f0c1a070b0406020309010b06030c0307020106050603160804150905010203091b0a 83
    0x1400c288a040c8080d11030304440900104401d040040c1c00c0d541d01c20242c4240c60010796450345003140c1e41028025010402e600040702810428000100126040014030240400ca4800c03c0d2501141044800304520f001c80b9a5050f900c60840c20200c06890107201c00d0500e03407c1c108284003401d98103003c20350890360440c0904444031903440c640c5029101d680d03c010ba145c400c0903101414031425018420403a00c034074000c2540a40a1030310031900e40024443c080258110644082c0400d40104804074001c17160b250002c1c50075141d5840404150703061909071000c211424040c00b4824201a20300030745a2400d001c141021075a644195820300e008000521168010001c18421a400d4010f440042c030000e09040d204d02d4059560a1a508101c1d2a0b10043d1300b01207000910342051001c40e40240034450f030741e1100144695040d1010b2601a1045813500e10f0420b04e4148000c5030301c512030496205600140e600d0030520f0010b0319000d1303002000030243da4400700c2c0780c14079a00c3c0c0b0100e100310380300e07030001d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 78497267 1250 78496017 78496043
    0x3140703090204060f1d0601030504030c030503041a0114010f031503020112060b070302030a08010515040e04140111070213150e0a060b0a09030b070c2301020906040807030b0a1107 79
    0x101d03010301815408043c03200c45d441c00c0440c03000b5062141d12814070020700903101d0380d5503610044003910713402c1c0d40150200d8101c9180c0d40100c0c2c4200700450b84280280a002c0890300b8800458035461000d074040c0581e142504012581503078000e075110310380d020034a01071040b1450000160842d0200e844028140212846994071550340c07504060001d10314542c00741e407113034401d050181d1258850400e603000104404004203a62805d1151580001c3c0c40c0590142414102421004045d90150042d11125110303040091400d109005201c0c0240c0c805010301c1c1c0342c0f100c03071061084100f180700d040082d5504004280051509540d4102c0480ea0310a8502800e501c401d4802c070700500304d5402410f5140c0c80080c0d9038091a420103403440c11a44200b14140715175450b0f2104483c2d240b001d010040c00036155070303408111206143d219030030121000b00014a050070500020755654131a40c40b03202c143d00310380c1041040c05401050b09901640d410800d204024804940c143c80307203d1600700400c0c03180503080f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 78498517 1250 78497267 78497269
    0x1002071104020f0405181909110a14130203010e2e0e040b06060a0206070e0102070e160305060910090203130605090a0b22020f15031503070501031407030902 69
    0x10306100e290401030411960b841c04044140c0c695813290203440d0140c5002581d11310710f00140ca035294824514910310f40b41c04030820245101502643e8000c0d40c81c19003232229100c8942e625401d40005103013140d411804492a0000e10446070703030b10248e09030840d206200420802000b811804d501c542d0380401c40c1c400040c0002200e0001140c17048403000d13501125400f0400314600544035020b01c2c020030340101d1556030901002194070500c0c41850058216501141829006012950180e401401550300d003940790510501c100e08c04030750211010412114040780d568251140383d0f040801a514a034103841c0c101e85011000b480d40c4a2540c02030380c00400202d92151001840c0100340d0b0000050003542045150250b4407001c0c1da80030f0381d003665034202190345188101b0051150720742030041d0441b100800c1d0200044450f00c3c04d8002d07003044d8841090200759030303004c0041d84a4450521022140c51219003070503e80740c80c2d03400107410701d031070030b500c9002081540b0106540001c0500e00890100030313902c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 78499767 1250 78498517 78498533
    0x5100608130f05100204031b0303020307020f151216020706050703110705060d0e010b011b080309030904020712020c09190e1f0603150207020906010521010609030201120608100207 79
    0x2a4000d0700f140220b2070883c0d441c11041e0010021680900c100f4441c0036030b604050b058182540c40001c0260340200812001400d0001d07149041007001801d2004415112140740030035808054616100000c900070058440074800030740030801c40620060440c1400c2143c007400910403000d000e001c4c0958844000c0c02183c3c20003401026100c0a445982c07100c1e11017000202030003000b0400540781d42006c0e176030983d030f510803c1c0703003043d510800d170012001e003070242c8900c20709500241100085020800104c00340d500e440c001014421721030500c1b5011407a02900090500344a61a0240704c0c00611042c0300600e00c02003031725060360300c0003580001c030f244c9000394041c80c04181c601f400480c09180d81c0420884c00159203d1002c0300d0280005100f5a07000b184603004038030030030388000c1d0b102d030552000c44c2c00b03548540082c1c116803040d00c60240055048040d54401600c0c00d03400340300050940001842156448200380070381214100c014010700341024456900d540211085003212940410300e042030081d08 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 78501017 1250 78499767 78499793
    0x150a08010621111903050903030105040f02070501021803120f25020d0302030406030c080105060f070c0b030f0402100509090604110409060b0309070510020d0309030302040e0702060106030510060813 87
    0xb240c001c00ca00f400da07180d104455048900c4000c0c03a003440b0704014a0140c064040c66104480f55000f8510710380c28403003000000d000c50300302ca0924039424000080081e1091000b001282c0ca01c0b011025481c03142c9080515000340c1c083d411030b1400007030200d108100c094405440140f51010242c40c0001c0c92803c40381011206130740007030740c400e807101c00e001c085c590040002c0064407a0342d60140501a040340341980c207104280b0039650007040c01c0200280c0001300c0000790040602c84c0d0015443c10355601c01042d455001940c28a0340389403600144000c6240921500007808110f080141c103029251000800200c030051000703001e151a100541e640c15505021280541100f40e810403003261070b201e040085410855407062a4030400b00007148602e0800884440d41c4a107a00500d40e050703401008501502501d9021402d041d0240400725030b414058445510902a942c010155503142c018000e05988026114a00c0c00c40c1c0c01c0b6061081c070381e00003030341765024141941c0d81d0044052854120072046203 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 78502267 1250 78501017 78501077
    0x71802090d030c23070909030e1216050f240903030f0702030c0306060d03050d060f03080a02010f061203031814060702060912030a0902040605120c150a080106 70
    0x888441e0804143c2c21051a0395032074000c0030860380340a03103100d0448030400c035684201d60b01d0b804507404004076959504041d0b00c0a22915000390341141c0760000c581001e90010510907950018486070260a12001a000007050111800c0d001e42443c000890303210030914290340c140365245a446d102c60034420302161106540038007162340d64140c00b0544e550b1a00000d008a210f07015960b00d12815181c00607056000c0c010003000ea001d80c8041e03070303415100c907030290a01c0c0c00c0302c94544000090400b454140342c00191b015a03500faa90310441c0d0300080c00c480d90909448441071030401c090120074039011406038042c0d07240c213001426402400040c12600c0e01030400404400d10225602034000f030108055000342050307003c4448986075000040c1d21100d100044000d40e0710244000344c2401d240707400004a860000d04001986a2100049842d80710862050707805030b4020074107280320f414440180c1001e802480010341c100800f980c03004001005c10b20231141041008000480480750105608402d264 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 78503517 1250 78502267 78502279
    0x1031508060717090c010e010807110a06091b032004020d18050d0f0f1d030a050105060102070605130302210102041d060f03071511070806010801060501020a0507180209 74
    0x2c0c0c000710080c8041681003003c00500751600104125a0300040d100780c015505844084480f48040c0046070a88c1000306101c003004083c14450746180c10502ca00301c070440c0030b04e8000c0f0789202c00f810840c1560000700715004451444000400215000940d16013501002805540d07030400c902000802900690029184140c41e00c5143c8007100580c0e1040102d992158007942ca25202c04501650104210700354403000c19a0035450b920424403a0904000315141d0103800035480d0b881d071012902c0c0c800d04084c1114103a5403682030103a9581c0400024000703000920f0901c1c40c04000d042c410380d2031030061100a00503600061002400d88049441c40c14212203c8002c640b159541c581500e0211100703600001c2c0c01a10002007810782c1811010448407200140051901501d803500000590304195003c104102c0c24000c000800b03282449610010400c100050105504081d201e508460041d8029815940610322540008202041500031916203d4100c0144040072a406001c0c0c45948a5258805 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 78504767 1250 78503517 78503521
    0x1e040f02040e0c0a03050709030b0a05130501020a0903030822080a02010e030a0c0b0c0309150903220503101b0503070212030403020a0b160e060313120c1502040b090103150806 77
    0x10b1044800707864858a81e640502c040d44481f001514031800a00000e490b0740d0300840054194041a006240c1010003e41d1a2581a145449050072a0050202c50001444180c02081811341c4044410f800018615400101e1b144e880d860b5009404540310043c003407032012505050f514001e502582d50fa440da001965500c80c50000014207450f2640c20449041c8100720105016081a4041e40e10880c1040d00911108041484011300984010900080c42c88100020210059171200080202001460f480c5109003010201410031440b1403008140c140303000c0c4046c1d031008020718035940006240c200b06540fa2110b4200300d0400c80a00d10035200018008240420181c0c0041c1c80c400b0350b401140c00c0500d03501d80b000101e150002a0000d0380000b00020154005031030040021074105030036032600e070401ca0381651051030b0b090755a00c0540210700814005d20030300603491902d076a80e014246046150904000f5003540714012a20a18105030391020f500e040b0700900f81205002e410304034100d5a40d4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 78506017 1250 78504767 78504781
    0xf020307031202150403050912070b0f090102010506030303070203220905040308180c0102060610030b04050103060e06090304030210050913060e0603070501020105040b01092304080a08061e040f02040e 88
    0x511000e008210044c410783c16036094a42000c0c001c503005507490b03500d051801c1c1e100c100300440d00604119400c600d006080d400115490500000c0044e1a502d2603016113841d9400300281c00c4410062099029030010420030001541c04805c40d020000d44c0c4600303210078028208a484043c500b504640541c5192005104c141900004a00c1c480d00f0f44000d042c455201d45074101d610303101c0181e00140940d0000012555900c1d0007550540323801c01520300040ca41c09040002800c2d00c000380e01c185c8803e0f540d070180401b000c5040c08420380c003560b004025441c02d861035020440c05803558030000c08010b00420f01040643e17801c000108002500d001c2841540c1d1100e8100744002015250a8441d103d5544001502c0d40180142d82c0300300e0b0004c0300341c0c0a50b841d105428002e0081000d940c3c40045181046105d0780382030f155030b1401980502040360b220501d03013074090080200075108600c04d480c52a8103c464210034070003000902801d0310081146e8003a02a0103011f8021a040007086c102044200485 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 78507267 1250 78506017 78506033
    0x40902161515080a0b0a0c020c030a080409060501090803030408031b180901060306140d02010504030b010608070806090606030412030f09050f0706030203060a1703040e0703090203010c0905030d08040f02030703 92
    0x22040d18001414030b566403044165a40c0b0000c4000a00c100f980d00d002604480c0d46130f00c118a10b031140e00507148039410301d4000904161091008580c503090108050140f08010711622028000030708003100c400d03081924003070707490200810040c100c600002c00a990a062000740800c5202d11089050b00c8040b0f101960390007546401c10f260181c0c00d01400040c00724801d00481c4115042050a8901b00c4180d000b84400c0801ca080285d0500c10b042100100040044806034000c0103a03699290b06410032000082c860000544840d1061031010103001c0d10341da07901c3c2213a400030b500111841800d03103541801e070003814890202c211010f1901c40e211090281c00304a070700301d014000301901d81d607544030441901280400d603000754000c080b03550b040c05090450611400e000404208483c2000c0d9140381c41c040c04001140e400300000e480308055011800c4c03d0107000104800c2c0e04103002d6950030710300440d0340c4400c4060302c401008044004034040c0038416422142305038026003514a06501ca04010318 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 78508517 1250 78507267 78507281
    0xa1101200c01030e0c060a0311160804150c120f17010f0806090601080606060304030c0b0106030e010b04110306010c060b040507021c0e030d210f0f1406060409021615 73
    0x2c086420000c01c0a005407010610b4403441e01c00030405400d00380700c090110300400c507124081c01e000e007003007012045180458140000061140f2070040c0e440d4244000f60104e118404420030520030041140d03000202101c10300503900c0343c280b40c040e02c0140030180850b000d40c480d1160f81e14180d0000f0002c251451014106400d907240c032011a00240c03110340405540d0300091080c0401c83d0841c4021403510b00d02800190f4106020f443c100c560354082d5102d2004031882a4045808a40c3d03400240b58501d4017030040440200c1d040303e007001045019009041b05202c024081c1d810041c1e0349030780d0000c001155201484c0752402501c20003851a0041e4040d5940c011141c01300da03d45000070b418401c152188860303a0901e40040c002e00100403003000195800700486145a140c14441f5820302c0181d890b074490815030303445104000c20580101071036001228010a40c043d0085070481c00c01001303031a12003c89089912003e001691010000c002094113150b07414001d0021851101303c03450082e0740e4108030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 78509767 1250 78508517 78508519
    0x203090a060503060312160c080a0b0c0c25030813030209010807061b1104050411150a08041202011401060305040203100b010c020f03012409110304050a1101200c 71
    0xd0085526150241c455010841e01c1c1689640b1403540303418003058480c098411814600c0c4210a1003290340c4c3c8896212645401c007454a500c0702d4a50014029090581f030f0308503944040082c50101e18560944e00e40380c42120707a00c0c11103040681d00400400781e20340e02c0000c6420a0350940c4904400103000c810740000e1200381c6c41001e400002254180001c184001143d401c4d03210749891b00540780701200c042452201c1980c054941c00e903010306948a43c0103441c80b0790311940013182d140c200d5004002c0703100b106643c001c08081046c400040819040f41d82c003a0030a41000510948403950f0310101d01400041c2d820342c9a070f14491000081d80c503010340000b4000d510031000c0c2c4000f0040c882ea4281100d224100c0c61b40018184190740001d0f003411105060352800203000410814420544422007140c2d03419084201c030b00781841084071040900c54081c200c0c031205070f42803850070540c550305d0740d915052134041c1211060b135440701c003568024100001c2e580707900500c84c265040802c500a841d401130f96501 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 78511017 1250 78509767 78509779
    0x60f0a080d030209100509010801140a09050403030516030c020c010c0609061107140307080d020903010902150a0809060601020c1207090606090e060a05060d09080c1e07080303010503071802090d03020309 89
    0x1720b041c0f01e003d901030303413040c20040c0e440620036841c11000c5550700d2658031140750000301509001c22852424000c6a2103107000c0d0314003240b41d00700f001c0ca441540b200030f0701c0d203400c041c90600303d003131455030120b0041c0d049202441e0401c9c8110360f90820200070401d104008211a18151180c098018280c028016460190780d03102d0280e599402c3c00c0da100e01c20301000400b0940100b00e414045201c580c041c21281d90701030000119421640c2c00721b0401203070490820002280814a602070380e51080850b9401030303034400544201d0070a100040c1d0707501d044062840c8034a008a0303e080040381e0070000382c1c004001c0d0401c2800310039074419014002c080f01d8004c2040c8262110001240707030030000700e10022600050080c034a8080080b8080d0000e042c07400084418003001c205100d03401008000f840340381103044850b041c1d24061008180d20341003141d8004806500140300422941d54007103001ea04071410120003180841500c90290024424100d05980c09400d0300c1000d014554004007401698809445d2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 78512267 1250 78511017 78511039
    0x90303040806161106010504020a0c0b010e0a18020d06110d150302091f0b090102010908030c0c07060801060c0210030902030f070317071509050304050a0b0a0f110303060f0a080d030209 81
    0x800c64031000c02d0b090f903080c69400f405c010081e40c03c190303000701020768561800022414040c5e59110251900b80e011307107010883e5a040c40345031101c5200351410301d0000e0448140040c200c0d4046509102d002102030180d5587c0c4150b00601c0d0000303c01c076200e03181c0d00a010002c801e01c0a00c3d8410501860005a01480c201e0000a030046101d4800c0da030f0b0382d0240d941e0b0800c0b0305d01c0d003010a00039a1089995034110b5480311510780001c0d41000145000341c4500b9a000d455003030015050385001010361107901000740c90001080b0701600491081c1036550152000d41011544401c1038016150100f0b0094240c441d0000640d0510f2003c01c082041e00d10441070303d42414804140c249041c081e8120117040084407070102d40902819a20141200784108240c03421300795030b40005030007211160702c900542440003810b00b1a1a91000074506480710900309042485500000107550f400300402c0d481c0218154495141540c1c2d81a0a54000304905002c40d1024103a07110014065040340050790b01817052881 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 78513517 1250 78512267 78512311
    0x90303050a06120f0606080f0c031b01050a08130b180d1404120c05060a0c0b0703050408040509101502031803072411010c0302040518010b1603020102090303040806 72
    0x100030071900303440f01118009a040e21882d400700d1060108aa005035600c0340080c2c10b050500501d001414842e0150040c1580074040c117052509844a90722158034185280f41c2d00d81c0c00000f0345020040e1890700c145c403a92400d58103009c43d1200400507003540b910750100410fa08001c490b4418583c034200980301400b10780c08041d5484c0c0d418041c498500c003014042406412201c20520700c1e8540107114500c001071341c2e040402c466a0100d0190000528001400000d02641610043e0890581d26080000d031405856001c510b000b24084c0714400e080250100b00744400d600e609902400700740c1400018210428030181d41da0b84201144010f0b10030000c00c0d42a10314003c991441254201490f18440844610001100d40110303035814050100904100700059800d102d204030000040c0c0300183d403a4141820402c140301da8000f82c071851811a00140240c101400c1079600c00d0310508200e0b0750500709031a040e4068000c0d00030709501484042800105001c1c0010024091800f018000b0a01d1712105 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 78514767 1250 78513517 78513521
    0xf100c2607050a03061508100f08071406070501060b04050f010203040312050703140316300b0d0b040804030c080312070f050d14011401050909061c02100201090303050a 74
    0xc00c5150306800200008a615010300002d02c20320300301d40341c00104581c6424048650041c3e005801c00050854030805c004240e5603110000908030402911691034584404140d441c50907000c0c1e05e0781404030801c02c060fa911440c007541c901640c40002405007540340c0d60302c400150000c7c41440d1182400c44110182e95002004650540750014410401e214103424141c0c1c0b00d40c0504000c40400489404034907100c1c03200d401840c001d0f5103a01c59500710020b6440c000309411241c043c02d40036502c0014a0320054008041022018400c504e00425915080000240800c030603e201a068024000c100410007030341600a10590740304413188101940c94543c0541ea9000c1c040503e11050601d401090300c1a000e550ba01e10645058607140c0d00d0030b81090700260a446101081d010b012a05000521898280b032700040c000c800c00786091420052110002005144081d2407a0f0080e400503501c07490a0640800001d5615000380900c40d0380c0485000080c000c00125100b030700028a02004202100c80380c1c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 78516017 1250 78514767 78514817
    0xf0a0501200d111312020102070603060b070f03020c0d030c14060103020d1106070602070b041403160602030603030714070815010308030a1e05070e0a170d050307020f100c 75
    0x952003a81c00e009040c89010020203620015020210003480101e251001440c11040580311061720401500e4452002a00d0800140c00000c01e05d41018400d0101c8450041940c0216800904490140116003005c2e420318600d0280a87c00600c014560380a060708014041078103880707a0340400c0365030704000c0c407241c64400a02000b980146800000001b04400908510440100800107481c3c12900d59031101241c0c05614101c406803524010001400644580402c0c0024502c001c1c61402074001c5100c800740c030740d22900420265011002c0f4000e51400c0064500c0b0300d50101140400e003649603d03c0d03948040c1403044044134800c0c0081038080d501074400030390491b0b40c000c483d18296107483c0c10780d030040c1844004503c0300c81c2d5010420358a40100d8055039000e1085511102c02501c412020300001c402e07140c01c2510840c5444400c0381c248000040c240c1c0d05110540780181c1c40b610f0701c82d422800d08400850062051141c1c00c00954500703099800018044820780342d43d629007002800101d00c8000c3c0b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 78517267 1250 78516017 78516071
    0x7051605010f0f031404030c0209091c050711101701080106051503090a0c0f08070602060408032a031014100906120e03040b0a030b0603040c0302060703110f0a0501 72
    0x19424240240e5001d0b0f083c0301c0c01c0003264100450082c0b081e88410100e444111401c0e400220390b10310241c190700f08900140e4100c42c074500546484206c0e000e981c006124103541c000d080160020f0142e040c0204200076502c5d003e0014180e248003081e242004000c200455a013403a4503954200014002070144522412507202602c5a43c039604540d0001019401c001c110320460300038403c050b0700044a0340000c801030918000024001410186800e2501a09401c461f0540d0302890900001c102d41400743d9a129141420f80a00f00b58840e022040992414028503003005000c0300303001c0c540f03103281840f0068801c1c0504041d400500c507802c0100d918602201d21022500e0103506000b40c52182c0706682c010b5560030310229690020162052a5070b11992228400e0760010845090640d454000c89021010848505055080c03d868000a0008a01c0000d11400c00040c00c102054094140104540682410b0381c00c0072000da4105500c034186020304480325442d041038004008000e00c00002c039000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 78518517 1250 78517267 78517277
    0x601050402030a02091002011407020a030c0f140a0605040b0c0703120c0e15090a05040207081617070308090d02121215060c100f0207020d031b0b010b0705160501 71
    0x128200500009500c06091000a99000c05c5528880e4a40140e0302d0843c449550000459030f0b80071400c60003510001c1c2c100c004541094400e480441c1e44620502c404581001c165482460549800f5400b5210424454400e000d00c100400070700c005030380f10900c1140550f03041c140e5582c4407444041d00b842840401400309034440c900700d1185201d0f620000704171301c190600c02581032201d00000c091104d040c3d03e86140a200198840c1513041c4a01c80400519050320203600b020059a0380e889140504a040b045803042d00c000c40d801c1c0403c220b00342266400007604507030303201014100244284001c6034480c010748911100c0b91541840000d40310b0300142110751030b50420780313120911110040c3c058a0030400e6044890b2041041d541c2c14002c00d00440840c000b40580c0c01c020014100341c030980382c0000748440c418000c80300036889810201c0308107030b41b602d08082d0880d40e0402d0b45410480f00340b0042c00d528140400410022a90360041454600600860b06d0800c1c103000340403034111850103041c0c0010 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 78519767 1250 78518517 78518519
    0x5010c0b07050904090209010801020714010204050a0611070f030614071404060c0302030405191e0506030f0c16030305180c030c011809050f06010905010806030705090c0403080f07060605120601 85
    0x70384a00081c107003e0000401c041034414954000034403200080c0c0100040d030758001035140403c4030f0f86030050107000241c0000d43c1000d160400040b17100c140780c440d06060101c07030090010156024041140506201070515020b42e8590a0250081401e1985100c01408040108404a0103108031003160060650700c280741c00c1c10142e08841c03400749a14104d00354441404007060303d030340e007402185400b0500450b8542140c5090301c4089840c203004514110a408e854040c0401c0d00c854085a5002c0f00c414066206915100c00a881b144208001c500c00820044003100070940d15820103400f6121000ca461140707200c2c00341e101c2d03d4201e4610f4456255020701251085075008201c000c2001c84650302040f8043d83c3c80c41004161503040b980450742d0b0fa1404200a95903030804401e6000d05000c1c6001c1902e0b02d031072404a5540e6030a8040c0c2441100460300040c80285190200e801656001d0112a1943d0f00075100c0640d139005214119610313070414101243c02c1c2896003203541112010310003403d0316 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 78521017 1250 78519767 78519781
    0x30213051003060815091204030503040905060d0210020f0d1d040f090510060317120f040503043b0603120306010507020a06050706051006140c0309150c060105010c0b 73
    0x1041a1001d0040c9600c0d03400000750444180701c031038218117041c508200180703040100e00307091041a0b2810443e00ca41407100740702140b800002c0ea400c1e6078401d840000d07142c035250001022220b071400000e51058240a5201e01182c2c01b0034020710050302e80b41207070214003401c2e20030b4030507160036424040302441189540c0701030b2420b07030805030279468405000520802c80c0e48030a42041100048506c82c1d6880f0380302001044005101c5400c001d50b0b03242098100082089078440060014284804000c41000440c0a0101c140105e8004000491001029208460100c0300e18038004c100c0d071444140e802d210744850500000b106110703810080c080d01d00540240712040c050742001d0001d50400400b8004100140c592200d05800380280e519196105e0030039103040c50540320024172101c1c0c1100306920800074944c101d2901c06542c1403022000d41c4851600c07812514500031410001d034446811000080403480404c000d1910a4818042d1100c9071780b10001519a019030003401098100c21100044403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 78522267 1250 78521017 78521029
    0xa060b0a0905010e0f0105040c0c0303051510020705041505030a02100e03010f05040b0601020c09190207051506030f0c010905010309060e0f030309070602210a020727060603021305 79
    0x4002001030a5114140d21607011100302c8078241c02a840c0c4065480500c40c110a1750a02c131703401050f0071101403002d01c1c1d020f0744c0144000145000203042c1500c41020500c0c140342c020351708000d604060280b06040c400c0306802581c17146180309a5000e185403403080700d442c09009401e80183c99020b8010000e81000703609000851140104880800100031841c50265408ac000d80c503660b01445404146418141025901d01170040d00e428150b600c0380a40210316103035000d0b207070350018410f40400e801600151450000c1c0c468081d000307095001d0b40201c105104a4011481d00960055045030407291600090b10380d1780c114405aa0301003400d02c074003040b043d071090300074080035841102e0100f440b8100c6000540f5140c440d29142000d504003004104a400c0708200480041802d0310003499070020242516480a5a600c49059400c500282c40c0e0180d40c003c01c020001441c1c8030f0582400740c0e00103078000c501ea03403000003074100326400d0040c0002c0c1030388640240c84603c012040c004150307529201c20041 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 78523517 1250 78522267 78522281
    0x30310031b0902040e04290601050901053c040b180609040c080106030b030102040b030f0601260108010c050316030b03010f1104140d03120203221a10080a06 69
    0x24040c60440c07070210300c0c1039450002c0c10040011380300c0b1300720794245403400b03132500341c02c400096400c50081548003085a4200c90360030303006007082c01c0c8907a5499001004071aa803040d80300307000709840d13044010342c40009240400c0f902460b401048001c1e21035102c2c00300c5d130b031481103208240e402001401110709209115003031204049008040501d8040302c113011400340c603002102c40011a554038010040c05c1d8144c0150000715070110021842c090402459883c58080030304003603031001c0e40f2000500c0990040c5d411a00d400406603c2d5030f0740000d1034001103000300007406241d10950034100303811081c0d4060003d49000b080c02d40340d0b4000600c00448202c004100c00c40c02907a00d9034032800510341b8100907200e101c940c019920b9550303542c0c9040400d1407028140180d0500d01a20011220502090740105250116000c40001503625140c43d609112061145803040000000c100c50000c2041141101a892100040310007400d41e0f172070600101c0d80e82c601c4e1281003036580081017804000380c0c0030f074003110b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 78524767 1250 78523517 78523553
    0xe060703180213140105060a05041214012a3011030a02040501030b03070e060120030a030c031409030f0706061211010206010902181203070506070306051203031003 72
    0x107011141a40004481110008041c800e6039982c4905a1501c4070314103046000d40320075103c2d2440d099281a0041c101d118070310840e003096451482000400c6003141c90070320540c46510007070201000c0051180118910001e07200301080401a5110685010f001d0768a5070211903462402000c0c140880c18070003203102c104400324250741c1d0101c82d0401150760302540c06080c5000005841c0c40c00e00b070026080310666218a03121307070301c81c0303104001a991140d510341c0d00c0326007860440c1500c01d19445802e01c058180b1100c1c3c00e180004100402616410351110b85a1a503555080c40100a0b0559800001070309460790310b980d800400040c01020b1101008200042c4940c00010f0190b54414103450f062000d481c0881d089201084000035640c1d0400c40a805458090003c600d81b0a440c0c4600c0c3d103041c00d94401032f005098008400014150501c00d03102940c3d009800d82c2c0b541d1629200080081103503004081c0304804844070450440400410b0304d01c05d40b915107101c026103003903884111200e84010801c2e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 78526017 1250 78524767 78524801
    0x501022e0b030a05010c261504090201050d06091a09070f080c070f080901030e0304084b07060905090c0d09050f0604060f05060f090703020409020f04080c0102010e060703 75
    0xf010008100340b24400b004010399484841d12041c0c40718801e88440c3c110349031f4000d250f80741d00303001c0310012440080b01a14011100090162000d10069509000704140d00a0b490301d040000600c0719034039001701c0d801401c080f18040c1918418003c1051044043e5510800074080105090311a130213140f0313003904048074804141c10824281c5d28600403e00d2004102e8440310041380040003542c040c000d0945003000311014500300343c00c060b81a682c80c4500024440d0941681c0341d41a80401c20f89448520800f003540f00c01810440303081280c803a880c035520707500c6207403098903400140a881400c4003402c3d62001400800542c541c40140c0d100303078024100300b40d102692040c004c00041c00802210320780b228054040d110030314040c20700800700c400c00e8116103407080c10700d4200b00042daa004091841588200d07204003403526000c80441c002d00968201c00f0fa000e20000d2905e0741c04005101600031140ccd0a801c450000d40c06000480c01d031400311408072859400000400c48882c000e0300461802032206680d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 78527267 1250 78526017 78526033
    0x10908030409020414030d02150712060e15030606030712140616020705090106090b0304030306080111041a0708040b0a0c0203010c050309060612060c0904090c0902040501022e0b03 79
    0x16003419039000c0e030710081c0300c9640001c3c00c002e588402ca04110719110101c024054580d0440f0010f034580341d2914690400f05100000a50b000d4044c50f0402924116a0b400300111505c030341c80011b03804415544803000c0c841181d4404040e240009149100d6a00640a407150516009003036610780c00c00c9008441c20360440da00f860010b0f804020285c891803021404d51408050150081d041000030f400c9203000b05805001070104a030041c00000403a900022040e039207554a0500314000c000c503800a0700e8a500340364442c0000e401000180080d01c00110307e03411541d1142541210600ca400d0008002d0f02c0180301c10050b840c0590081d180111060602548080300d990000c0e00710340310042100007060001c420700580c4a420821240e2204058800202c101d1148216503034540005049510214000031038074102d4075a03400982d105a030003c0d00e15100c5458141c1780e4007070b40042c002c240c01803142d50207001850b041821404058280c10700d200212400ba0003d00028100544500f0f40502c10701903 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 78528517 1250 78527267 78527279
    0x4060f0513020f03070c2303030402060d090c0305060a1a0a0b1c060b13060206090a021c0f0507031218060806010507080d0e0d020c18070c08071103010507050c0a0308060109 76
    0x7140301720016038482e09040c030903140409200e00c50001081c4607010175403841c2e481541c000200e80c0c11030707012106035842c2c110000d1603001815100c903005001c481030510002c1080000134055000300541002880401d04800481c41160841c004071a03001041400401140c0c80c40001084010038520b504503080d9032010988043d11030540c00070300740240020380700000e02e91282c0303a0300240803c0c0c030140c216420b00481c09980e07060043c0340a4800d0700d00c03084c94001011034184082c420b40c1d0180703c1ca0240945414065142d40d00b600c410744020200301c2030007000c1446000145d880201d400103010266041c042d007160101c400420113814030100700207203004a6924000350906041c0c00b440803440380f0440101c503081c405080d00034420366201e0b030564a00313039545400d00c186c1501012948000c6d80c1d40c4203070803a079896070784001410b80300300091060309120524001071000d1000b40d0003444161541241117030a4400d0380e0340c00680350031016029000074810314249401800500d0440035041d1120 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 78529767 1250 78528517 78528547
    0x402120708040501110c03070213020412050a140d021009050c0901030602130b040f050904260d061203050a05030703060305030a020a0201080a020702150d090b04120e04060f051302 79
    0x140d1404041031000c0e0811041120034080c03200d01001ca800707014180031514a4443e41c9029661000b44502044441501c2284441c0c1c190360041000d2548800c3d042410700b025902c1d08150041642d1807140ca044456168800081e1008900000c1d4010000c1c15000c809000060029920807140c030301925040406580e5400301d404d000e07502441c4016070760380801c1d5070281c0d800131690041c1000c4009200401c250303030340f45401008503030081d16004019030341c5140001241e034180754001000c95904c00549c44d45610301c0017601110764000000c000e81611488140000141100006c00086003003000c0d0104502c40c03030207550408244d060118549031255903c5080d6040311118100690000031102e0556a014089a41143d09880114500344403500411001082c0a4000d03480780c80014400e41148840e41c805c500c15a0080321601d002e081c03038900b60108282c0314520000040c41c030280c0205918081c072078030023150300911000103400d1500c01840b41d001070102c0340c02e1110f41d0030b010108000c1c003030b2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 78531017 1250 78529767 78529771
    0xb070303022217060906190605060304030503060a0e0c09040209030f070308270a0e070203130b0301140405070c1e02060706060501020609031c05040804090906060801050a02090a050f040212 83
    0x100111890b280c01d101c0c40e000700800240141c0c0c810b5101c4010301c081a180851010380001800d504007540c0c01254000f01c01600d0554001c582191001041106066201000e58040d1000301d40da03510207075a0f1034030748581c01000c0d00d207901d100404001800036031815600403c00d00a0207819100f20000030480c890034801940c0c002d0301c4460000410b2101880349240200d20b032340301404980d111181e94000719428603c140520051081080c0c0460680350003002503a0b540340c12100b040d018543c4503000140c4941080c42403440e800c4188050340d407240703014054684100392a40e500302c12021552104d1040ca030781f800904801c0305049201601685960000b040c0720382c01070034007103090f510b0540020302d400d100411f00c004940092241510f24901d20401071403200e9054808a19900c850a14209920a590100404d280783c10300413010040709421907400c981c41c900007005140d403400280d000361301c44c080540c0d611140710903045c4100d141112412052490160005007489101078049101c0142 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 78532267 1250 78531017 78531067
    0x51302030303150a050a08061b041e051306120b040206041d060a050603011a0a020c0604080f06010b090d030831050c0105271206070306090608060c040b07030302 71
    0x4420103191140c10070000130002000709445498080d0701d4030807259200e0070064000e0b40c080c1489444000820303d8902510060106058164500300040009003002500c1d84119402416611244c5042100354031800b421030700c2ea4042101000c460b130355415480341006000320b07071100b403c0c040401c0e10840031014459080200d1080e012a09101c02000809100c962046102d01d004100610881d1854100400180d100d4039005456805440e026030504d000c1c1000d5070b800c0800800d00290b88400001c4407492440404103960403a629a29604460300c100000d6a400811149036240000e2040d030129a01028000b0785e40b40340050881003480d254074024203540c440985115580511a05008100c041107007402c080c0e15061150755003219594104501c03900c00c000d00000f040460306c40014140b0301c0c038001070540d4401d181254005c0d00030210b90050000c0c5614001010400240000301c89002c1e4001ca10040e0810785008a44001c81d88400402c030701b0035030203011014034076210540031504c40034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 78533517 1250 78532267 78532291
    0x1009021c0612061a0d03080405070509250e0a17030403150c090e0f070c050a02030a051c050f071b0e010b04090e010c0c0b0a200a0906080106080a051302030303 70
    0x942800c0c81801d90303400d8481210700840080c0a00c0e0b0a5840d0900c0d41d2001b540b60400182c90f03034450802034105801e82d40a00c4d0442103074010070a20703050b2580004498189030071058a4115a070404440040c0c1250030503401495080040c041d40a16503071184802407070008584c82d1079201d58501c0c19174241103504900d601d8807001c50113461a00300080d20054031031241081ca640c40c03e021440a4541d0241660050061581c0701a044c800c05001000900e9006421680309021520b816560307200040307440300c5034044581d00800c4892145e422181c45006645035141880c006845450381c0d46a590703410704034043c1d6408006400d040c410007160007440d80c00e10094903107107030030815010741d5061140d1542e641d150645d10000c0540005081d4103098018800014070350321075100100030003a6110103802000a1024048101203070f50050a100487d075494100e00341c0c0d501c0003a20510780a00400d03011584120010f40701304081e910107035000303104100f4502c00003001d4012a0031070380180c0d50310000780313 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 78534767 1250 78533517 78533549
    0x6040e0c030f07060305060118140a080a0b0108010605010f021203090a05100c02010b09090a03080a020903070f05120304060807140706050a050402010e06180103090602040801060609060908061009021c06 89
    0x307170940300c1c06c1c1c0c3c070000a080c69403074034452003044c00e0201100d0054180300490981c0c42005902c84071910400b901924040700c40e078030114241485a5002403003020300c198200500400c84d07510481e00f55210690b15002001801002403484100c2e400050000e00c00b4480e0440d1200800c6d420000c074010040031040000e0420b0b50020024207540c040c030055070280c0e080f0414004030030313000a01103019503003619004449460310410301c00a032003814640b542c075128070007010411049000013002120022a84e81081caa02c0a071115260302892003807102041190300095002030003400703d81c1c20824181642c5240183ca503403a801200c0080d541441c0a0f48e4070020071086581000c0098001d03d4201c40890070040d030003003146692850100ca150405407640410800c2045a070155005030103050000d000c034549a2000610140070b510482c800a05001c5001580040c00f02d049030040d10114915001d1a0070105d140d0041d41c0b0040c0220a4020a4090780c1c10040f15842041d006d0462941804442 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 78536017 1250 78534767 78534779
    0x60702120706110705010306120213200a020c100e0904050313030c08010b03120d020f0f030103060b090a05041106070503130605130b09030309040e0f010203040b07030c020105090606040e0c030f07 86
    0x45000d07170f0025814541381c11014400164501d40e07800c02140e0440f5840c08030456038203140302500349001d06072010f400c00c02041c1a54201034000d090212019401c171500300303103d00c0801990f58255042c1d000403800c60700c51041581450442250f005018a003201d180c140748041c8903468051070742c01034440202c1d81500348880882030041074040c400072401401300111405540c40c0714030070090042c0303400c2c0d80002e40e44c0102520000b994241026840035507203035070b501d0421034040d10ba50202144a840403000044202c02ca80c800c5901964201100c03652039000c04081c03020a91080005648074441405200000d5015440000140200380d03a49a101c2440b12a0303035000880b29001070030010f0050220f010030b80c80020a894084800301c0300491070f0080c03c881e841c20694035040c0e48a50303500000400040c000380c0b04040340204d84c20b680030000346040c000c0880c01c9135400d560f03080154010384c000c1003e40c68660800e5944203460410703200b081030900002890710719101d07440040703900001020000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 78537267 1250 78536017 78536023
    0x40b1303030305061008070509031603060212130b01231306060801080304030512090d0f05030901080610050a080c0d0c080f070807080a0908042303010518030906070212070611 77
    0x1005d17034943e41141c044c20000b400303000e401010a41000004901c541140c1e600b007106003003d24140b41c55070320158803420850b02a5000c01c415084400b20b00000c111403050340348040e020b031500f040d41012540d00344082c800840300c0622004aa030700003070340c10512039a201c0c503415400211802c400100c032464100302403c20700c2c059001e44070342e402c14801080400c0c40895100e803440040b14560ba5980300b0b80300040c00118a103540a044080000100001c000c80000141140320090b01d4240c0c250751542c04201030b0542c0d4a40c00000100e09201e07007031159006050b1650014101a4024100510220070b0310880303841482003400107400005228001c00300812803900840d8910348104c0510380b41340044c240d242c2c040c240c0e00410b9500e01400013803050719016103018010b2000b181c2c04041d00c00f142d00703002c124000c1030719100b03502c4c1601040c0c0a0744650030300814a034010001d10300704038120702088942c3c0c0101c40e090b82c0042002c1143c19030103100f40b10b64000381c00140c40b4244100d00b5030418520b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 78538517 1250 78537267 78537271
    0x131a03010b01020c0303070209180703120201060902040513050403030605100e040f0e0a12090b040603050411030c0a091a060409020309190b06060703050c060711010e010203101a040b1303030305 85
    0x106641113020040c4140d2800302c00c80c2d20362601030720580c1e0141c80c3d01884c2181c0c2444041c8100d014003c1140201c00c0040c0700100200c148201c0e4024130120f519252918224030413440b42e01e5101c80c0a101201c80f41459400c010f40c0305000c0d040c00180c1c0e60351000820903c07803220040c070001441c07100712000c09203868422070190000610040184034a1360100c1c40e5251035080c0050000802162507034801441860108041d108081c80c0c540c4665440c28080c001c0c140503a01100c0601550b41c0601c0603003400134002001540040c0001199032802c0c1100c0c00a20f500f03230013002d02c050951414401034072040d00402c0100b110300c4e0016030701d18000300c50f0f82c1046030f040603a101c00721642d191080403a0f5280d51860b040201160401d581c0c82241c50260340e64401c83c400c2c0c0710340e0300640042005030380c1c000708090542c42003040280314421004030001e00702c5c84100c4001000002076801407040e04003c0d41c2c00d030181c20f003001c00749242540310f04110342150008003100822038801c0394180105941030164079 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 78539767 1250 78538517 78538519
    0x3090d08040804060509030f24010b0a02100f0b040905060402040e06041101031107050f0703050601080d12021b030f0301031b0e1501021e0312160210050402131a03010b 74
    0x1501828aa501c480c040c3c0b0891040500700b0001280802c16a82e051100c4228810148100e450f11107c1c14200b4000304030340d400d00f03452804a4000000d41210310030444150035801c2d0f010740381c0c0000c2200f605004102d211034581c0d41c070b80e07145100e2203191078030700c03840c174542d40070388002c11251a1601c10001581c1c034441020030b4a40104050000044050f141e0908600702403d020802d01444002c0303000314098020701420700e101d03211440c25000d1021407100c061307138010f10586003240c0c1c81d4904d290707407845840760782c81c0000c1400d107035a0742d02c14869000d0311880e141000150440700312440c94a1640c4c000d841600f40d103100c000010001c221781c8001007444841e82d9004600541e1405007055442c0a00070241403180c61040c56001c4168402d01146280038801d91803c0502c0c01e4800304503940e40c010111000208043c84086070080541482880c41c170700c2c0c55401048030100c0050180084c101c044c00882c1c01002542c8090402840780c003504500261040c146040c54190104041c02e584488840b1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 78541017 1250 78539767 78539777
    0x12030310080a0201120216060216050d030c0e0d08040806010b0d1505010e010c05100c021f0905060403113324060703020f03030703020324060d050603011503060203090d 74
    0x440043c1d8108400390080c1044000041e1a50300d19507c0e0040c40c4101038004001520000b041e80304c101c280c41032280759134020030484594800f00282074003241c02d40b4440101007840358421131024a000421440c40300c1c441c050b5581040c2c2c0c1c84001d02e1402c10300303030803101c0d1240c004941d140301e0419521400c542c0c8214001a0000a4908400a0301070005400124100031154540d003013403040410079590181d04100303080006802445009446c1c450a03805007241c0400300345c000030540d84a0041a5010750800f01910302900c035940d00740d80014401266134050300408501c08170302c050000c0040806070307030140344100114046040907034000005103002e6040c0402d59510ba03a010071808082003e0605452195503075480c0e007008d914040c0040300340708003880000104007000c8e40c10f030040c60145041100d40e024582e01d0425040041900301071040d08144180031070041e44c1c404c0d4102c1504a0320140001400c86009100407401e41001c1d0015201181c0010500201300001c0007102d400d43c50740d00c2c007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 78542267 1250 78541017 78541033
    0x40f060f020304031e0303330902041a0c0703060e030a030f020a020714030106050a23030f0312070c08070b160201020403020307050904020418110f060a170903091203031008 76
    0x14005d004050a2407014060039080c40c0e1000c040c000c1c2e0080e40d001e60481d032026200d0381c410b035042a69030400748190105031400309000660b000c540c0241d40c10354002e0b0071400d25100140c3c0b0030310fa00340c01c00c0303c052506104080b00000450581d1240001408640c0b001d9035451118100140c160780c41c00480940300ca10400c448982540e02040420035207401040e405210003818000a0151615811483e03102801e05400200030250095141c400b203d03070018154aa02004101a2501900f60a9020035041003080d4003641001d000c00c1540702c43c860800c14544029034441c0000f9400c00c4d034040354800c100006200c1300c1194131441e44400e00c3c0764802549090704681c0880e4550801e881f400d4040c070103910218046640d250002c1c96034410342d079208000b4004900b40803507120004400c0f0340c003889030584a4540c1d82030800440d451000310b5146c4c1b03140310380301100c02c1e448118000e00c10340742404180085041542c0700d102503960481124025031720f9003400b15103000001040e501000440d44030100e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 78543517 1250 78542267 78542273
    0x6050915090d050f1b031c03060801060e0121020307030f1502070317061c02090a020d0903050a0f080f01050d03020106030b0718050a05100f05040b040e0a0b010306050306150102030f040f060f02030403 88
    0x1a051f0502c034000401d0100049080c4d410740180c040380d000130b10207500b0100041003d02903501018120303215a5000001c0000005506c80c59030650400a07401d900181c900b480800c01040400f000240b25000029500d69a030048000b02d13041001304078000350b20300001c0c89007441c0c07514541d5000340d0121110000441031900751181c10a0b121310081c003411641c000159082c00690540b900f407440d820041c0300c0480e1626008069900c00c51441c00030a1061109040491081361024824800c1c08040315240c0d090601704042c8241000c421821992030b9200400040d40e00c00800d405800262038845280d24101d0f16a4080e11890f00040d01800d01068200015582c40c0a504041c00311030401c46235401c458001114240725030b130003241c81e448001a0005499401084641c443c0c10344000403c50700000000440a6030410300c6040e5250f030040000c03a1103403d0603845106603040500403a40340003008500c803036045d003065020413940d0203440c0040200c0e9400048050f6054518800f9503c1c00c2e003596 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 78544767 1250 78543517 78543523
    0x4031110020d030911040501061709010605010c02040b0303070c0b130b03040b0a150e010b030a0b030303060a06140d050a0f05090f0307030305060105040909110a05010906050915090d050f1b03 84
    0x15240b2010541c440c0009020b01050583e072865000f4003400c140071039170712146d000d082480c100001b00400c0c01100700044115906204480650344165140144000182c081101405004d10259030500040081600064540744c46100412a0014442e280c1301c3d0031054407030a480541c421244100300304100400034000a40041c0c6c0280d15082c001005091b040542a074080250882450241c0150011030410441409584030703851341d0606000c60000700090507100d000035a00e00d600702c0b0764500140b09142c082c0410301c0e00d607010b00001c0c07410014a5000d08040e40e07401d8461001c215541c0039014400041805400d07848401e2400401c200032001140726601c2c8203644c0081d0400d5502d501007101c580c400c0d4111801410307090b40c01c2c40300000c07a042010405a03c40d021034440c1034003150001d0f041d401120a841260701a8484500303290301c2100340300840d414540031040041c02080384980580e140380c41090140e000c0c1e4010f02840c00b081e1503d510f043c16681245221480712110400b080d5000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 78546017 1250 78544767 78544783
    0xf060109060f08270708010203040b06040b010c14010b031603151104030b0403050f030a0209040e0705060403030e0303071a0a0f0b0a0902090f030d0c1a16110705150403111002 77
    0x25202e101386480e100d04403000501c841920703802d840c003c2000000b110641500030318040ca018058000c040e032101d030200403c60300110310641c042403034040e060010a002c82120b0500107408000410350044007000a424000c0c80051a584c5649003074040c414030650320800203c10760084410001071110304e0f00788505026600c002030800004500150415104a0641d454400000b903899140d040000148001e500072540d01e134016440c0500407185034400044140403100098140f618090440d1411508034040c4034174070750148400c02492001031003a6141144415440110211509222400070305a40d608004150b8441c01e0244070002ca50b80c40241100b1a001040e006a81d26400f9000ca02d21950400e445541400b46006e40751160780c000d40c41d503842c1031140200c0c3c1108074250024440c41e00c001c0c0c6501d21030030600c2d4581c2d00118000c42c0c0285408011130119440709030f46000240440c1c2c1c0781800401081c00118080003040078140e6140c1300c0240445141024160345d500c000d507a50300f0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 78547267 1250 78546017 78546031
    0x603211806050910020102120a0504050105070e09060409050708060702072301020c090703140405030901090504020c07151205010b0406031107050c0402131d01061803110d020103060e0f060109060f08 87
    0x1903c07001d6550300c1c007d50480e5940c503418404002d2501c0c15060b040001d10044800750360550030f050009008520039519240960300082c00324003903849840c1440010700011804071070500c51a8400b00f0b003114204009807060700e07564014002d060503c80c18061408090111440040529802031017a0380c0214141c1902c900982c2c642c0c1450b075400004902800d00000b011060b076004000780802d02c40e0100040200440070781340d502c080c0e0b5481c1c007031004034401c0300030320f01c283d41101c0014801d040c10301e80c108222078082e107080342003001c480f41c001c0c0468100307034040f620144002170200401e6416000796400304c0c0c04041480d0801c0c0c590b40b20345071030b0200850400d20482c1d0000388207520441142c4090003621000c10461016180318040300302c01e060a00901d0003081c0d0090103504001c540c0e032032440c2620351010444202c030300c0e1042845194119043c080707050540341e00300442e030104403000302481000c0035084248641040c8002601460403500310308200202c0b01d00c05050540c0000701c0c4c1e908482 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 78548517 1250 78547267 78547279
    0x3010b1903061e020706090314070b060607061119090506090907030e1006090501300b070203071202011410081f02090a03030203180f150d06032118060509 68
    0x10415019400f0315003800881e804500c04103040d02440300b503502c4004024445c0d2200390448a4600b00301640f4043c44200924100c445000101607007408005005410f1081e1781c049001000b903904d11040b44c20500b100c07030440091450118155603c003040500514007524040d00c0e203141c00c4e0105000b0080100300d40f00f41500d9980c5244240741c03c1240c0c020701c075507502d000c015050310b80895402903c03080c4580d001d4001980c04007030344c1e960401450702c0440035413a8844001d0b84140d8510400140080c8040b09501080c04068080b96120b1129254400203034000070703030030102c3c0d1504010040041c0c4000300e09040c1c03500500c400100003c800401415104240507821070841222010307100c1e041400740c00600e01c100000400d0380003c068242c42c509071503d41c04022000d82400034000076040f0040d0b01406080b0400e07030002190000380f0580441c0900800c0c400c1d2640c9401036540b016107001001c40001e03e00d007660840d0700465044507050700c1503035030700340f1441d00340000c103d03000c1d601d001c5108117 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 78549767 1250 78548517 78548531
    0x901050f01030c0e030f01201303031805041b030c030e0606220207060203010807060c020a0b0d0e010509030a0f03021303030e030a0506070201090213090f11040b04050a090203010b190306 82
    0x24007598604c001420010115410b0790000318203240a40281c2040b00b007402900013911791101854402d0b20004140c28820702045865502c0848001b000c6003070013020510080b43c0800da82c0ca460256155101c01c4d00c00c02c801a02c4105401411640c0350f110003402c0515059408032041c0b004940300b604550300f1904070101501c1c04800110b0f108254038808501440001c01070100035440d00030354100c2e010b40007076800190340c81e0810765000d000746500a40c40035031042c080c00520b044101914600d51901c0380042e1902c1204401c508444003078030f01200b180e001040540350303258810340304480312419160a504060300800302c3c6100e50b0301400000d00703000419000b40c60a4a040007100c2c542a00b020484040f800d100d80041c4c000c01c40650309a028810381c1c2201c0340054554007821aa03258010101003401155071105842118448103040d800f80d1242e101030240e6a4500030b0a00030442c03000002850241071041500310f80591503540e008440d00c0d2940c03d20007540e0281d04085940021001c5502 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 78551017 1250 78549767 78549791
    0x120203060a1206090c06020f0627010e010f0f060506030c090105160c0e01060c0b180c030a0302030318010c080f1e01030f050714060f070804080a030503150901050f0103 74
    0x380c03026812804644290b0340c416001c0c49010381000c5440c50040e12045100c3d92199803c03611031440c41458101d40d4401070200d40808407030784c94100000100c1e03604a03000c0364004041401d581c4942c0c00041c1c8c03030707446548068803480c05204502c000b14180c0ba08100c0c091810f0b01044e002c0c040201b20f01c43c7d102c004034400d82207034043c80c02c44100c01c001860303442101805103080a1040c400b4059424040c1c0c102001045d024000c070104411941c10010081803039480d0444898010918080f0303088900402c544c4a0564504120001e85907110b0b401440e268a40614030306140401c00d00e00701420380c10945400715542d0403007199500240141c40c0400356903140e00480c003004208141c1441c441000e4400002880b0b00f0b50b02c4101030900c41c0f010344148541c0c0b0b001140054642524440e80001b080000300e0040c54040c00030210303030b03108815450400795036140302c9061100115040d000f080000040014610031522110410802129400003c0d4148004640408803160a0718113155552108800d8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 78552267 1250 78551017 78551029
    0x3050106020303060f09150603010b030106030b0f06040e040c09020415020c030a0209041e0f0602030613060e01060f1206080604020a080703050a0303180f060c0f0207080604030305100b071a090c0112020306 90
    0x2190300235000030350382d59541d44d107910103500900c59100000d1030003101000515040140c0003000c44003d000c42d003064201072800c1da41c04400341040b12100450303040000d101010340041d000a042701d02c68440303020350101d006800d0070700302d01d4010b10940041c1c0328440140c0e10703003400030f030030907045041c2a18600c800520001ca840d9030f402c0c05404050241c90b040b081104940043d4440d00d0f058582c5038000030882f10354410b8a010303003e000320301840c2400621a81f4070606400002064a02d451151150401d1581c401c45115802c02c0072203030000c800304015428400d20180081c41c2e40d400400031645140c580a444902c08400241011340310921004a680040f5950f140c581d048176020004002e01d107003141c01810a030202c04046011284510045800841c0b501c048411001c0070700312903591941d0031401082d0040140780261015880441c00482d03920107084514468070480b15808209129030001c1d03140140240c01c1c40e07014001c0340906036800300f640f02c0882100640580c89484240003d14 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 78553517 1250 78552267 78552301
    0x30b01020c0a1e030615030606170c040507170406140108031306030b0f0909150105030102070f110d050d0804020102070f080316080c160e0907150e030c100f03050106020303060f09 79
    0x79650400b0146c038146052030780080d007141c2c41120304120301079075842d11400d000700101091100d50025000c000b100e0809403c100c0c1d018606242c035000808200440104d5408140c805850043d43c5022021861010079040703405010403500550510390402d05a291518040c0144400c040d00c07031007981d2840c1c44d105180c82d050000101450440e06d401c00c200c0d0350340c5080a070b05100c6410445c00000b01410188200c51040760000480740c46140580c9402c204007140c0f091031500018640e49080118000b4054030325020300b1540d4003851405d060000900d05142034010026074641d0031000c01c00c8204c000102d44421117034000700c902d08152410069164040c01c116140b140c0562003221406619070203400c020340d4a40b071000c22068035010044d5540b04014014254034100c000c0001032a18040c0403051303103c04000701121500c3c42c03050086035000640c030380e50070081184125506840ba4040c02214050072007031000b181189001d10000780c1c4400c0c0102180d01030681d035008901d00c810414807200e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 78554767 1250 78553517 78553523
    0x11030c060a020115140d0b0c071a1e010e0411011103040f05130203090a080d020c03040b0a0f0201090201020316140105130c09060f051512040305040501030b01020c0a1e03 75
    0x19141c600d1008041d0107090083c0807604284c411900204074071244000b00c807406100949800c40c09a00783d0f0311124501c4003d40340c2e20242e50140700140c0050740c00644400c090041140140b42c074100446000c0905a404580c5c00c0003802c018018440c1c501c0c80300e0415031250300321040c00304c0c100f604001641e06a41c00c003062546d0340000680440e011400414500848106440d0031100c10241d2803980124001a20201d0940d00300c1250340380402d01c9540581014140d140c801840c1c6030704894980e2540d840b6034010141e08030089082c91915800c80b051aa0311039890000344412800b941c0001e4036482000562040700b40401c0780e00003131040c02809140c03c40301602c02002039060441490300d030b51649203002c607000618028080380c03040003401108220380c0d009844e02d000a06100401c485d00aa1024030009401d0521030f02d90350700c1c0a021604d010714000c1c1c0b50240e41e10309240c0010290f400c0540c0060541d400940c1c15034030340d107a400360002100d8135002208409450000b200030480103562003d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 78556017 1250 78554767 78554779
    0xa140a0c0e0a08011a01020f06060904031b06050105210d0f030b030105101e0f150c0f06050603010e03041d04140d02070806010e070f080709050a0b09130e070311030c 73
    0x803d00c03500c1540401c03424811100c044d50401101e070012680c4d00520700c012400f54014a001c0750761400c000da40c4903040362290415000001d1081c0a004889200e10790944d001501c9800410a40c00c001c621101c41d01f5101c00c00550034401c50807040d0f515100d00880c4010050340110400c1510b00c03a5100f1191440020002d02035400c0000800507009102d0040744022143c61010300c0580903c0013180c41104d540054100c0241d00d043d81d01c0c40c03501c00507066802409205130b03070900040c0701030082034201e500c16600042c407810400141401c588030456003e1050303008100c1407042c010f03800c4140142c4100d8540301a02a6035600c0c001051844030b0300114507034403175005e6610b4802c0e00402c401c0d00391a04a41180c0707031a80d0b0f510b925402c1c01010f480340b2b00401c1210300e07a410011300c078001456000301c460030840301c0300b80e139100401e101e50940e40c031107045240702040c00075140c6010b038042c90101840038414050306510599164540e14240320040c141018a000b2035085d443c123015500e000c040003026 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 78557267 1250 78556017 78556019
    0x130204080609010c18060c0302012c0705010819050414030408060f10060c030c060b1003060303020c0a0b09090405013207080f01060f0c05030c0c01080a140a0c0e0a 72
    0x145950341d805441c100400e500b000c1a0b8461584250074082c0d64001030000f00404900d071507801d0b00c80325a502800d800710354841c103032140407061410610081a020780700c04010740700b40c507081c14182462608a41c1c10807c50509001d80041150f080806034100ca40300050707562107501e001c4169820251025541d03020108001900c180081200c61145103c000725080a0307403054100c0e0701620540c002d0a0128004403449400f19200d0400d4140845c410741000400001c0580041c01c43c075816880d810000741c642c20305000b0143e060003010628001a607040c05c1d014140340101c2018011b0b0325606000c2c0c580380000506221007500032405000010060f031090016180d001ca0303007251842561101590240042038000c3d1040d21154403500e00710021040c0c2d42d00341401120600381030104031081001c0c0750ae5a1000ca40c09000800107050180002c0c402d440c0c0080024200c008010300c3c080025250a8140000c2112311454680c0311038070000000c6c03020a2410182c40c003441c0086800e030080c141c1c0300 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 78558517 1250 78557267 78557279
    0x206010b13030f0c03150603080708070206130f06090f050a05040b01090306050703021312030f0e010e090906100b16020f01120905070801050c0c030403122102090a0b07030503060f130204 82
    0x11319415203000b1480402d0340050890000140e840e00c0c400100399800c01c01241c0e010030010009042c1c4c9030320041c100c62501200f5065081c00001c0c03a00f1404405401e00c204114458001c84482d004103041040b944c4102d1500c0300184081c031840c03080c82c2c012904c1d48041a141d038442c60307100025541c80141001075090042c8014001d41052400f078815401c900c00228000c0c11041d10315200b41d916981c1e12203144074501c82100d100c08030070f944c1410b110a9a44c04901da03642da000d014450680c0310300410083c9021120740d4040103840c2e000b00c071040c03400c0055002405411158101054042d2140400301200c180120f5901003100c00c80c0202074501552401004070109840089400740c90003440f8036142e9581800c0300d0311907035510702c034150b00802c0208000b522044d40f200f4034a407103050040d022411071420a600380c9100b03000720f151076030004282450785001c088220150460409190500351035540c068040d10001d0a124480d4050110702036040e80e60070441002c00704545825500c07a81d03110 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 78559767 1250 78558517 78558533
    0x90406090c0b18151b010b060c01090b0a0509030f0c1006090c021513060902120105090a05010e0a0b0114030f0d05070c0e060603010e0925031e030206010b13030f 71
    0x744516000010030031040715601c0d08501d500d0f10364413000610b500d410700c40d070302c0c00074082440c03481d0385195501c508000e049a80c40701c0150518040300700011403200c21512301000340c004014408030840d0715200500a4251001040d51481140c542d4840d6450149a0b600c0745172a44d5216612003840c1001400304484a10350480030b03040c2199002c0369001c118800307142c800b07000304540741e802c0e03468224100c138040396032500143d01550001d050000d202101302601401d607242111214002c0e40b0141c907407401c10034240708142d120741120024180315003d681d03030350f4007554041c4900c0030b00070074409882c2d0655600340500d100f4200c2d0042155010480030b24084e10715080108252403000041400040c003040e500c00440c40740400030000d51850f820a084400035050250400074588551078800c001c210b1051708840c402171a041d0070781401c0745180b40242c01e85085c50b00c5070704082c018500031030002c0c0d0002030310341c1034a907a81c0105445846084128628003441d0340090407070303820380c9000b1061040c14 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 78561017 1250 78559767 78559777
    0x1f05090411040e28031e05040315020901020d0302071407060f020f0102090d12170a02120a0c02070302010f140301090204080607021605010c060b03010c120c030902030a02090406090c0b 81
    0xb500c09000c0e0240904015840d620480040c070900b400d5900180350340d10041c4e02000c6414440d0030220b080f250181e42a0307841912000440b004100001400d00502c1541d441c5400310120302401585003a03211b00000317450f0710085d020b40c4103040e0040303142820006840c100701400e4a010301240e4449a582400400c2c0c3c440402e1280701500400311910700809040c022564100d03030250400010380f032030790b0b2121401100054400c0810803000c8400c083d10280422060003603045130009a03d9044c49040011000400b030030311081a46803000c1810071a40120303241080700c0e02400c080c0b00d0600c0e40c5005840c2d40c41003011406151400200200b0001c030741d83d010300103482d41036003103447c20360b07441c40f007a80e403030114280f00c00c21411111020040d0750b10a0200c00b038414071880300410300480e01000300e400d5540240e4040080fa410540e6958100b0785446030b282c28440a250038400641d460300440d0700d0380b8041030702074029a10940000c1c24400d4503001301080d9a0b0081421f02079039075444409055800c5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 78562267 1250 78561017 78561019
    0x20a0909030810080a050601030b0c22140103061217160b01080c030a15020a02031603020109200612130b0907150306030b0c031801020c01020a1103040e1f05090411 72
    0xf982d0340403c0048001462402c1154010004c049076401c64030b0f103031100c8200030306a0300000d50400105076103c0d10300d10002c2046c0c8022401410190510001d0030002625040032030415103044020000000200c0e621883c0e5508401c0888202d5600301201046100c2c0f41c0b080480700c00c14043c0b0204200110160504036600314040d6440d03494200c00300f5865150b0043c021700840081c1c1c100404281c26039004029980050040340d03d4101b2024504104040540003580507075955444041400003000c50502c11822111400e88005130340b4001031068002c80e940d8288805401c400601c2172a82004031811440c0c014582034000d14240e0541c0380d031001d150140120107009581007503281170081c09140156075101d030300068560b80315079590409400040002103031241282c08100004001e10040044000c0c0000150351450b40c10700151050008450225440e40100000c024003401c2c20101e07074108401060884600d081281d950f0b480d0946a04500c1e0301041e60003e00c001c10003000601c100042c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 78563517 1250 78562267 78562291
    0xe01030b041d010b06040305030a11070503060109140601020d0207120f1a011a0703020a110102030d1a120f0d030b120609010c030c0807020705060c030c0115030201090b03010b16020a09090308 84
    0x61300d605000340d5014a1000420740d5000f4000907420034000d0210b001303081e408404658009550360300103860200300307a000a9050788c3d10300359411078580c804061a03000ca001c3c002000c14115031a4001c3da81c144510036107c20300c4a41040c80200400340e01240541174100140081c04102c4800d2a100842d003880740e01e901230305048030a06142c80000503210784d5a0550050500360500b134440d110b44854100c42541140010410602e00030043d10071205002501000615000d40041c14000c40c07510490640410346e1003e80c0e10142c1d004001882c210030324052501145c9608143c0100d007280c03640d6288d400c01760050108004003d44154044840c0990070f035010700030f117020003c05030791009064601c40c0040e00610002d1015042600c0109140340194040740e1030150080b50701404c44090301107408015401c04020015136034040f5810014040c0044014038652401603044650310031801e100074181d500c404000b0642d91054070f0680100a80c007404c0c0303d8a50340c0d1400419000c011110000111 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 78564767 1250 78563517 78563531
    0x806010806011a1c0f09030e0105040b071101050f0711040b01081501030905030f18090f0f0a110403080c0a02130501080a0818040606120f020a0e010e01030b041d01 72
    0x3140001c880c0e04039440c8840c00b0350034105246441203154851386900c008440c20f410390b04891360b00c501c2640c4043c50041800190b203201e52400801d0225056442e90412005000c10300400104e00111b91481d40c2c04840546101006e40060b606405003100c4101802c1007c0340c0c0c3e10a01010307504480c04900100e80070030041c00380710f00549180c2415901484032000052910316554020350000701141e00640c112810310f50248035081a6070300103a0000d405c111004280e100c14108096011342005031071100c0c1c00c10340741403e40b81c0e601e41c000138a1a02041c0d02c407a00010707444402411500a160801001070741c3d6404032543e20b41d210020310040340a8a40282071030344c404a94070890f8180d41303080d0007030b255800d4991160b10303041e0810300703801454010782845e40d1300302e0350341e0710442e0000c0403d501d035910740c0740c803510301c0b07004650503034051802c0d1900411008040941c029060341800c042424021020100140120003d201803514560403e1030440529060a40541860b0701100c0703200090082d2 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 78566017 1250 78564767 78564779
    0x2070f020a0b12010504090c06050304030e06040902180607082208060106030204060e12030f0702060f0703021f020909010b0c030c010e0610050102070e0c0304050a0b0f040c060c0f02010809030c0f07080601 90
    0x120010318024008e080910700500109110300000c40d00f0038000d242c8124541007000010345a640254440421036600190900600c44d028440340c281036001c60f01641022a507440c1d01003548600052005540e41c208002c10f000800b55141b42d02400796a0119001c80d030b12000050001c0d8400e0007140c1c0411503203e40d10485280101d04001000d0303840001d181840c0c43c0720600c0a09070400c440499000500344130101c1107258003000750400c10302950003008090b0001500701c4640340c540750801815801080344420944030404440d04441841000c5d0b0b13502c00c100034510b82140101d980418065003030294800803000005150b41c0900300c0c1465400713407641c2c0d81d00113982d10115880348203e01328201e4001400d407019031026690017801042661200c402a9440020034107080700d00c0d47c2c04105101c148400d10070580584c401506060822100d4002c4503181e2040c500c840510080c1000041d0001a004210510596a81c080d90808954a922070380902ea43c50315120b00034808284208000007400c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 78567267 1250 78566017 78566021
    0xf090605090c0d03210207060c090f1a18090a090c050102010606080a0e0c061c060b030f040b07050c0d0e1e060d091106040605090405060306150402070f020a0b12010504 74
    0x802c200c010b116404603034650740d058809240001c600c4491020965121042400c140001c0c41000d20680002441403816032014040b400070790070421407404039580074019191041c0c03034489880b549405081e1200710030200c510760f40001a040315002100c202c00e11452021b6a000300c0e440d60310441e08411110b44a4004901300d5010f80729240010700340340049600d109640d030060080c51940c106982c00d05c1c000c240451850b07801000c40900d000d01720321041384101c000d8483c09024102005e900c42c61410002d040e40c02240c00030748007601e17050401d004980f0040c020700449490380214019541d00c1420b0b600082c04521a04446500800c012541100222505c030000300e405640240043d0910590a98502c010039040c5030482d0b400150010040f2a5075400018000414680e41c98940d240f4490381880281d039400380c0b165000758081818865000b030940300401480f48290780040e110350483c14044180c6484840180d0003091080001c202001050014034602e249800180501d0f6039450510003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 78568517 1250 78567267 78567283
    0xc08070f0f05030c210a03090206070c030302071703090a0e130c180f0e06040b0a02121003060c020105010308030a0f1401030f02091311010c061508210412140307060f09060509 77
    0x1081041040101b0a03140650300503528240003401c03290500134103548560801c0d0b4030350401c1d409640b00c100100040048908080440101c2c40702a60134045000c1c0401c1c0800110302801c62902ca1000004052088840204000035007002507641c00c0c51b59505403459a142074082d0100f02400c005043d0b100d480280106c40c83c41010400030481c40e40e580d01e038200b0411018002039a42c1d60200300c2642d80340d0180c0079017030143d8980304a03010340501c0c42c0341050407120b41e90708441c03d590400d030041004c40d2180c011f0703d40c03151341d6010100c0d1900c2d03c1e10a0304008c02030700e290300440400e0400048207001c0400001c0f1021482078840b072005465220003100c130310007200300041150121154240c2c0c0e55200d10100760801d84500000f05290b0070b55200141d1c140341e1600841c05540c44a81008580113458a441d03040106040711207244c242058500c04a030640c081c0003038040302600e80040302c1c01d081003046801c0c59030494030030000c0d1800010020007922000000390350541c02c14001c52101d6001041a034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 78569767 1250 78568517 78568573
    0x60e09090a0809031204060801050a0504150506030604090c08060a061a0f0708040305011d012405060c030405100e030715050901030507140a090f06020c010c08070f0f05030c 76
    0x109420740281c0d2541c00d107500042119403d4003620345024003c42c0c022015002600c1140c580502540c1080c1c24400002e0040d80420300c282c1c1004c0d5071080140b200c005d07520580c1d40541e5007503940e40c2c58101141c090460040001d05400f045e407000209540007040141c041ea032039080c04e0040513680d00c001403400001c505c0030070401c2010844541c800c40d4080040080c00c0c480c40209050a0b034075200e940c212440c6d401c0035681c82402200400ca001e0003031080a41910034114030601510b01c420030380441d444c2034000c01d405088001348000f56604100195001040300401012908171369100081c020a00d20340564000e11a110b408a4800a06c1041ca8030300b40c400d13640d10781003500e81c030011809080040c025605100c1d00184103030180a1001c010556091951a444115850001c20603100d051035070018045400491540070300daa03110144030341030754124003001d031508100d0a080c0708040010344014041007040082d030341045000b0010f4200300c9100d4040d1010130074610300c680900b0300030403101 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 78571017 1250 78569767 78569773
    0x305210906030c1606020307020102180306070e12211804140a02030a15140108010f050303070f030908070303111507080c0a03090f0606030506070e06070b091606050301060e0909 78
    0x7061243c2803805030950f02401441d20707500e50080e4581c03008aa106440070f80050750006880c040340b10404009110455007a00142424a460304e00245030340044440680311303201100d004c50203034a081052140ca000c0c7c542c481c048178211201104c11a501c640304128114581011489042c6030034410310601915031300d50201c4542c0c541443e0f20081d072000341040303803080d60707101620a02031400744602d001d056005200c05092503420005000340005034003110017a02d10700810301050304c01105440c1c0141c0d0101011040a885180c1600c54045582242416209208001040c180c3c0b06440c08070040d138010988810b05050a1031454440003100c400e0046a900300c0850012200040180780c604601d184c0040c08581c0c40d17035180e900c803520ba6401d4034400d8840c0740030701c180182400300540260040c1025910721600c0340105901d0b0144034005003e4111800c001115441d082c041d2070f21402c00c03d1112903409480340c401412580084c081c420002d2440200c40100c3c0c1010500c80c1d000d00b40407802 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 78572267 1250 78571017 78571021
    0x5010302160c030804050f0a0f050f0a030b090309040e0d0f0e030c0604090b0f01020304061b0c0b16120309020a170a0f11092d09030c0304030521090603 67
    0x650203548180d6007009602180840d40c404640c0b4020340401030b43c811350b00302d40c2d5189013408202104c012a244a4407e41800d9402c0240030040800368040343e00c16a0036a041e56146400131302c440d40381d68005004041b00000300445030030040b0003400080740072141044071212910b8466640c0355201070040200d05450f01140003035000300c0b14008503640c003d046441c01c0b40048042075003034125078400b01d48551103075400d41c0f03170b450b26000fa001d01c28000c0c402542080d141400080280e0701c0035440d901081c424106010501500c200c0c450090400d00007aa642d55640d50301080340030140c68000c0c1c0341745418102d01002c0324413a004a0f00c1d0709030000c0003038019a0604444030082c03c6041c1c6900036a11401d101440011401400461414050100345844001c54024801c00100040c619144040303040104895084002254040a034a0f40003a054550726101000d01c3c5100742e00e00360000b480b0108000081100028003861810a88902c602c82445140882901401070395602548034800b840 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 78573517 1250 78572267 78572269
    0x110304020f150d020d0506030d0c0f030e06090a03050d02060a0606090519080f0f01050702011503060203040213050a0902010212030408030c130f060314060109051003110d020301060305011d04050705 87
    0x1d0501c80484034031101031030300380c0a40f500d10407a4000380c40001070342d480710300300b0040d4a414404a440d18400e81000c0a030292036680d030b503c24014000d001003c1c030180144c101c005464200c1582c01d09000507001016241d101d080c81541c40300030404040c0103100d02c4000030071050307481c00340d03070100c95480e116100064100b03c108000f4405030840182d20340d05404000511032070411800c507440d46a280030b4107083c03044030000c83c2514002050708043d60f04000d10304010820744032410307088a030400001030700d913190b074400507446410102409100318281130500c0b0284825910010880e40300b6001c8403c01c90f05040c0c0c01449020884000c1c3c151042070000924a4105100504c601c50070b004821806036180c403030f5004014a80c2c3c1101000a0307a0320f4110048200072250160407a03000d0804e5600d545c607040010301000d40f82804102050b8403800700c49040c0315010306860010300c207004155142e40e143e010040090000340324001e0318070300811070440001c45038101c59010340e41003009807281c0f608000c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 78574767 1250 78573517 78573529
    0x40b100f030902040b03060c041d0105030303010501030b04020c1510080a020927030a050406030b03160501050a02030405060715140906010909020d0203030705010515060c0601030f02040204051e04110304020f 91
    0xc1d0166040b03911106a200c1c11340e424082c7d24800c040680b400ba4696042c1840e404800c1c3c1e04400880d0f14004d042c0c0107100300c0d0b80010035281198803d203000302d209803401001c0b070003a004080b94115140301f1300da00708807a0aa50b00e80e03030740316005d00106000415030b01d20307003681e07140509680650480c5180010070f01d0781300e098011080c1021500d43c401d0010788812105440c50344105141c00000d003004c2424000c1076450b005800307104000f20020240c084180b500b1020765501d503c5286c4c1440000034500d10041c5c000e009640c02864014207454484509040802580410003d40b18a091030a01440f10307442100000a01079900d010051406070300b402c100d18000e107070a03d41643e100c1c46074071500340141e4042005001861150002040c2814a1210100c091018005a52280409104400d0303420400503410341100c0e00401a41198240d0707001040082c0f10300e801c0740350008681ca60020888000d072100c0c1c0c0c28214181c400304482c0c42c00d02562001c1d40416075000b503000007448040b0146207412 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 78576017 1250 78574767 78574781
    0x606020d030b090c03090f060c070201020601050409440d0501211104060302040c0522300602040303020a1505010b040e1503160f0b0301030803010e040302030705010504080702040b100f03 82
    0x1b4800b04c0310058800c1030218600181200c40d44c005031000600e94085580c1845010f0040030700303540501c41032105a42d008410864074107004420100540315000c10090f031100150384280003070555500d01e9038010010034560140000200450402000256411218150700001c100400701001c484103540d0b00c4a810524106090340d005480d0000480541e030355105004640c216901d889554488c6050103095100d0112103103201921242d9040282e80000350604400c41d504030004440e8044035070710401604d09248015081a10215000c410190002040240680138012443c004c6000040d241c069030710074011100821400d200410092882031200c5805c81100c01040100c0140140482c0c6480700300f03001d00140e800d1500c800c0000c9018010310038094000821080d2840d070450b151070009200601c00d4400300e1680c5c00019050510901c2601c0549031f010001380141c0c107203420320080c95001424240e01c0745e0b280c00d103110320601e40650003c590004546035024142c0350b040b001d600400c42 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 78577267 1250 78576017 78576031
    0x10150903020303030c03010e1003050c0d020427030206010f060c0602030601020c0405040606060905060702100c0203070b0705030901090b16020108061201050405010204031205211b0309010606020d030b090c03 91
    0x19010000c00181e4003440030350700c9a25242111901d96240903810208460301034011100c070040e5200a101040300462801d44500060312036140c107c0c0c8030b2022174000d1020000005c48505122142c2d01d401d0805501034420b240280e00700c50090f600c881c650080c842884c8612800708404464100c0000c0a64004c2c6610a01c14015500c3c07003c64100403400340ea0088408031780c8155680c4050154580205042000e04403d03107000c0e0a203000c40c1c0c0851100f49004090000384000710441200719941042002c02808041c0c80207511040c1d10310f0815944e402422026001c103000240204012400d05d043d504140110700e80086541030300d40064880207806800103401c100d41092080c100d6009000c2c1c0c40c00756124900040c0d54074a1030506d400e40328000700c0000100f0504200e8065019061026410811a052402e40c40780d2030b40e0802419015159842c403d800d5008010000901811743c0007104640c425001c3d41c80100030b00303104900700d0b101d509070075a1090000010501c40003c00002e19400f400c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 78578517 1250 78577267 78577277
    0x10504090816032106031113020c120301050108070e03060a0b0102030910120b0613090b060910080402010e03011e0e0c06031f140105071203090210020a0501141015 72
    0x100c2c40003556042081c500b5404142000c045070003450310a107110402d40c8000b0341c1000150306680c5c502c0280c441840402d8464910a52502c0d802211981210703212840031040360a00c010811704440325800902c40c590109c0c03503540001e0400b030302413074001202c503000402600c5981d03248140a0010403040c03900c0e60451105200300c1a00d6111121802c03210040e50b103807480c1c442d864005420a0340c0b840c002c440c0c0220030034404c141180c00500e040c00d05070343c10200081508203401002c10440c0c040c031584164003001c600c0310881c841d80c0040406000d18001c0c1e840650b02c80050042c1400da0b03045069a41107030691050341c00f00d02c0210b07030001e00d0144010003035810000514000a000390400c5c1c0340e201c0030911980200001c028410340c0c4c0310080c111000c940c800c0c0000000080c20320b0203031500113003015403111a2105410320aa200315426075006150040030310120078000e51f50505d007141242c807507103440c5001402002c500c214512681502c50400070441c101005c05460452a17118641400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 78579767 1250 78578517 78578527
    0x4020603070c2a0305010f020403120f02030f040f050907030b061b03041214060a14070e13090305040602010e07080a020105090a081209011d0a05040506130e0a0501230105040908 78
    0x3e11010344100c80e4100032601c1900c1c1c0c01c600300f036800c59400d1000d4400e240d104000c2000060104061301954a80c60704001c100c1d0508603009900714450701d48a0302c50303003a00180c041404d10080e02000e081d2007003a24409203d6032100010b900f101d400450341540413006020300d156204a400c1c0c1c0c44900300e8024180e03420b1135651151161300001582007201c03c45d22240701c04124034410011a680002002c2c0d061050300c01c040c441451000340a01b80c01c08001480807258103a8540c400d4980f410040703082c00b00700700d40d42814010400e4115004c2c0c0c00040d401c1070301c0780c40903100010700101a24100005087e491106600540d040e500407514030f5009995205c00003440c42c4280003031031081000c050b00c2561b9903060f00004100c105204400034038010304e0700441050b0b4070b49400d900181c400a940024a0b6120300000644c045076201000c41800d051071180b48220700701003400301d4210700c1440244088400413008811034180c1d12412601041680010010384c0b400e500700c60450360045056038940 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 78581017 1250 78579767 78579803
    0x601020c01090b09181e071814011e080402130b0604090902120a0f0302060f0702210d0c1706060405010c060f02040510080907062f070e01121a04020603070c 69
    0x159000c4420000c1e042d40e2094240807412880038072540070a5902d010b10845c0c1000035522000000340c01010100c001c849c1c1c00704042e901940c114400420340c540c000c448580d03200c1009007210700480c1c0403405500c800002c0445903400e801210503803400245400d04041c02c06024000501c1e04a4069a11040180f844882c0880c01d00c40c1c0c56055025a0858642c4581420040d00d0031030050940703140039040030200186158003054003003041d440169a141000c00032520490346018040ea0440301e01d2400b000c2c41140768001444600c02c110300c81e05251141d0300c42081011343e000d10311a050104020044040c00189a40c2c42050b52074854840117007440e8a0790042491251506141404a20170303605202c0d00c0350782048280020a15450084c110b11107441d8484041d5008480000942c500d80080344000f00781409100081c1103009420341a540e9540352030001000c2c10317003041d61400c0c410018401e1a00d00003101c24821038003d4081440c50b162400d04940e1400070410954042040b0308061480f = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 78582267 1250 78581017 78581059
    0x406060302150d060b070b01090c0e041508060603010b01050708030403110304180e010504050c0f040f0203070801150e030703240905030c0f06190509030c010608030a03050601020c01090b09 83
    0x202400d90860303e480e0000c00d55a0001c9402d66000480e00384003e01c4000d00045064501da81581c0300303200b0105480c40300c12400d1310b4203548482c1c01c96002d810b013600700b01e0303c044400f006011986e00b2411030301944c990109040c221041c1800306c83c0000c41c2041402c2c08508120011600036110345480c0840135030800500d41035401c203412074111604d681581410218443c010b114421100400030000c1c0c0c201a50384960311014080300c80c0c014070b401d00a03c0129600c99200c00000030020809664a2402c41c0000700420000d00516401d01111485034404a106186000d568040a4020940c0074113684502c41890042000c5c5128161000d119100902d883d0044070281841200219114803140700100c1c00d040c415885c07140c1c190701660401050140f41006642c21250507480000d040d260a0b5089056204203240100d2a6080003000500c1031400002000f0400155508100c140c465a004907103941c00401c1c80340c001102d41005000c11507d10005111a10008184001a03a011055820 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 78583517 1250 78582267 78582289
    0x11e031406010311120c04051f030b0601020d050a050f090a03050f01090b01141f02210403050114090606041d16050411030f0f040516120302070504050709050402030406060302 77
    0x1030303140c110000410400c0100c0c1219980d07090221640114440c00d520041d03910102011102e1043c1e443d640401c2c030400700f5151a803400c0d42c1d01007401084a48a04041d0304070b42098404a006100340c0d43c00b02181031040b0299042303290700e603440c14508184010354842e90f03000800d50960040100000200044041003400c0101c0c14400000c90030012034140923000c2101607005200080c03a08605126a03510381c200887c0d07070801900c0f10540302803100003ca1401d10740c0125800d90b466803009209400d264100a0001c40f40704100a00a101015810110303114060360f80207a290b1219010445520702904406801034074407100c20080203090301824648180c212240704010680c40003401103003440e0080001ca40d80c10482d031891800c04565180b144603008016240250800c400720b02000030505c03801100d400480d1031422039a40301c626080718400c0e81c6204801600c52010005914202409070600c14000c68036034001440c544400e0001952008004490040d6a041c0210043c0d9401c1c803000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 78584767 1250 78583517 78583553
    0xa0b0301080d11010c0207061d0901060207080c0609181305030a090311030703020612220b061008090c01140f0301060507021806150703020a020409080d0605090906011e03 75
    0x11900c1144820082c03c250654181d0401d00d0b41004007000310300d5000a50380b400c13640345141c1590055446074541d0040000c203114a603022802e07a0000600321341c00502201a60b40c0c40040d0f9150580000805c87c00c0c3c402c0ca004140c200e0388031111012051105444c06031b01c51a9807a030120b9010190356201c1c1103030300c0100c803000881d59200c0140244090090410b030300c0c98003540123007501800c54000030403900a0039110841c02c508680083e00361502d1360001c130006d8131103000a54030401c0600e4143c1c0031003000c65180c0c0c0140300042c5074180c01446205a14040d001040c003a100072817003100110340c01d0900201503600003030204105e1800010110055009028a545071a25941e00307104010b10f41192039150f1140c01411014450290750700c410071100300317400f5800a50b5800103854180d040c007541d540040d41c407a1404c04400140322501c1c0041c00a6180c07040200003040d181c030304000c4d28034000d482c800510382c4081c005010b4070141041c45042681c0462024031625520343e240d0126203240c1c0700c11 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 78586017 1250 78584767 78584773
    0x108040311101d030f0322080a0f030e0102131502010204050916020607140a030b12240c07080702040b01090e09010e0705060703020c0f011b0f0b090303061c020a0b030108 75
    0x161400700c1010650104102e004040e42c5021a005e04092280c00040d01040c1000e941d0000e8901c0c00f12542050904140d001c00302649840402802500350708074031002e00082420417101608c1c2840c18822a1422100c107081c40f200e090409200e41040c00e49410100195942080082880d580f401c0782c051283d261481031101420040500038107000e03014000000b8011081115000c1160391000da034481c5200349400680800c003070000444000069016800301d0188034040c9a44103140d0907002c5989003241c040e4059501c50905214051041c0880586550303c01c5c0720b00001464690000c1c0e1110300c0501d406160300b9200c408181c541503040c1c900c180c10344c0d5101c8001b0101201481a0801000121551410075055480c0a5203840c95049a544603401c4450400540d0b8080c0c5100b880014001e0032a1454078014504088000ca40100039070354403080c0400140c00380e400004480c407a5201030b101c250701074080d2130303462100008110b04170fa001c0015000072520007100c90156008110311002 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 78587267 1250 78586017 78586031
    0x2a010212010510030e07061103130602010e010b06040803040b0c01150e0a0b03070515030a1407050a0e04060605160302101a091b041809050a0305040819050606010804031110 76
    0x1000904400b4000f1a81454100603941c0184100800c13840116a0b42c0c1c01d0071041009034030348580c103520075024111807110000501155903603055029034001001036008014a01040d4200001801188a00e00c40c503401000180000605400074001c40c0b00b041c0d002180080c044490320b8100840c0781c20040d040550074007000924045801621450401a070282100c1c40c140300101b0529065084000207148000002c240b400c0c40c568810320300c580b81424002043e041c440b00c000c0c40c5502032014900081c400b408400c00e149042e1161404403030680c1c0b2031a20b490090311071408513040c020000e070158007440c06006282a8071b8049c8203465180c00030704403190718a040c10452680c0b4054401030b0f101d030907800d11070121000d09040381c0540f0703d444880c4154005007081c910182c01c0040c0024102d01808800004245c2c00901410560f4661010b45591010740300040021b0b592286001d03099611241c0840c525500401150781c01901030b10704400d407001c031111b419103003165050b183d4008588d1016 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 78588517 1250 78587267 78587269
    0x4020c03070215040509071b050601180f1104060f050c06010303170a0b030a06052d01030501270209150d110901050d0c0312020c1201060e100303052a0102120105 71
    0x28820103080e05002c00641003d045c5404980b01c014006d066005218008046106510b0718104450000e42d2200454000d036854604103072134018481d83c1a440c003428405101d00c0c8404a0046041c002c4982d5000c43c2094944042210710325030b010102410b0100c108511103c0b20811304c05c3e14041c6010342c075444c2403c10b200c000322800d81d50003085541e1700c1d40b03041103208150382d0102c0da0903691604140081490b44640c40c0b0889081c4021404c8410b10703048040c00603074231880700e100c00d0407a400341008001c003901010002d00300310b446180803545941d00c0e5510900602c1d0100440b50085020780102404428045c00300725082a80e55041d111038101c200d85031800e1500d401a14054030301924403502c6100360b591044030900c2c0f00c1c00001c010701c910102c803181c124801c102100003d80020002c209003986c1d00c40050081105000c2d0841494002d4006a1000c5101d503880302103a6269540d07900c0c01b00c0c040001d60030b80d00e001048020324030ba240c500100c514003d0014006650884040c458103500d404 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 78589767 1250 78588517 78588529
    0x11112090102150c07110310090f0605010501080402090a020a090902040b0705011b140c0c0306041401060b1216200c130603020d120210020301090e0d0309080d0e07030204020c030702 80
    0x8030383c0901507080c8010081c00d0600c070401d9903440d40e40850303d0010082000b0019060104008480c44c907907103441046014000108001240740e8017801c4100b00340e03600c07040111503da60494003c2e401015460204040001c0c5500804000346a840c06031141a240c039802c40030b1340e02580c00414074090104408091207000c0c80381100341d00c02100c2042c200e848400015000268015501001f09c0004c03d40c800b1906090021020300f60008041c0d841030320305481c02c007074040c22082c00702244d517107001e10219039082524102c40a000d1889201c0d0b080c1d56034554001010540c4040c000200000c200362a80700040c08201407120003510b0014000303081c40c0c14240100718130241c0b4440341e400d04005040000d600c0c0c652802c1409034201021283c0c0031000802a464145460006000309100000002d0001c0035035001d0700340101c41005942503034080c41401c400380ca03c8041c0c090401d80c0d0402c106015480d0355805850140c3d280002e07035040395900c1c0c00241c221381110740d1100040e000000d0400441c42d0030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 78591017 1250 78589767 78589783
    0x20904030c03020f0607090b091c0f050d0201060b0d020315030a030203030108011406150c07120b010e090d021507090f031a01080d0e0105030c0d021602150720011112090102 76
    0x101303009203000c0c170305405c00420703030340f02807050f504a10f000160107a031b9600c3d454203880180496090361081000d042c90055125509100156010301a01c0319422855206001d09000c80300c09004503030a15a00b200f910009610140c045244a00a01c0304009152010f029450440d40290007940d125858440f07802d0940c0e9000c502d0002003000c400400090790b07a0f120b07081c50600310f11200c4980f500e0380491103a03d400c500d900490b01c415100c2c1803000c100310382c075118039040c1c900c44070240314a5100e21800e16601d151440c00100542c000040701200c2c0781482000f65404940b528110440b10341e94040e0030040b0071540c02c01c0d100040c581b21880c08035920603c0890041c85804000d22603090480e00080207050b40d400400d04003e800404a5000b00c4018181c400e148840c0000b1982c0784040203009111007240c420483c042c10400d41942c0d24804c513003007035a02c440e030854075042d00c2240022056604890b044101410302c1400b412080c010082001552000000401a10740d00ea40388000686042c07c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 78592267 1250 78591017 78591043
    0xd0507020604061b051b030c0319030606090e0f060103110f04080d0206090d0f03060f0603050601030f02160308040203010e01020301061106010b0403030504180e10090317090a030516020904030c0302 87
    0x3c544c940c80c0c030f100e83c40401c8408003940c0c03d01045c000132445466505510680351003050500c000308a9148141d2a40801c3e07000c1551758804100643e80e86605070ba15070400d2003040708100d5843c0001d18001e80c21070106078070000524001900c21002100207038a604040b0400717001c0300b00482c0034060a1000c2020071001d2485000414643c27604451440e583c1501d5030180e0100520802c1440e4414020b801c00d8005d40a40b444000440e910b075440100102800c1b60181d0000c0d0920210a0b80e0a04030f20807034582150561015074485840e031403d50709440058012030305503684d140708219680b07080c405035028140c250b03a0000c2c103611800c45140b40407410b070405e81c181c00003040100000307030b00181103408a507100d0000802c030010384480200100790480030929140a134141700302040d510b40e4040c4204912a84801c64200040c4100c103000790b20031642c850190b8400d00f01080860700807409030000001401828005072840d03804100880d005540031000b054040310507400301501071002400f5080d0b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 78593517 1250 78592267 78592301
    0x50a0603050c040216081806041d070801030305180f060c0c010809030c0c100c060906050601180506091c0c030302030307080f04030f05130b030c041e0b0307140d050702060406 77
    0x150070000c682005c81c1154000d11135600007031000410055000d0080114500808141c0ca59654100e0300a41c00b035141c4120b0790004c1481d000403d500c1c06048400d05803030b0141d460b40c1c1402050041501c40c0001c407214250310080c4038810880d40d640710802008501100c001403c118141c0d0350000d081c00502520390001c2e500300b0700100311200c0c800900080c0700070b02103800d00060301155809441540c44480b02800e00c0e4207040d442c105000076a000f41d8000c080c00e13070750300075a0445200300448021041c050503901400c100300f18070030380c40d000f144400640c0c990401c4402c5c08d5055940c0204122991340300b1030250b0400710812440640202142e0703401403213031000407828070f02560300400c1c98195002e21014002d021550306442c001704060390000d0f00040700c840d503890030115208001a0454411403141454070600346d052031030400d10480c12200f0b48a0b00500b161038122081d1105108900c44060700c4809004141080d5401c0c01021b0040c80d044c1c02414540c20300d420140162840c0807070307081040d4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 78594767 1250 78593517 78593527
    0x8030702150a080604050a1404050c0109050d03050d050a060f152307020405070e040906051602030c06010902161e0b09010606020a060b1207030308071d010801051e0301050a0603050c0402 82
    0x9400501c500e0713208400300c40004080d42ea01401c01d00410400d02c016030b925180e00104010800001000b840800c1e003600c4807252542d1703a10030003444200100700180042d1050007500424143c0790404d50300300c070410303a002c501c09441d04e0031002c0d0304403650b002c0b501095004d680a02103030b400c1120f0882ca0305403170b00700051049020321121010320540700001c1c0980d40d680000f0f10014850864180d100d54000e009005045490402e080945016101045504040481741c840c0c2c600001c100d0f06509034040242815a191149240c0207400c04102c010150a49401ea90001401a441d4440450b009401034001c0c1c2c070316040141714000c000b007031643c5a81c5002010b0102c60307000101900d2440c0d20000c0400c6000c2c1c1800402c040e8a00310461407640d105600003c010190081100b80c401c5091342c1d40c446425060b900040185850603000d0350105484000520003418010301180640b07400c2c0d0b41ca204c1d18021383c00801c3c215282207405c0c00c44981d4501082c410858148034a02e64000201c1d8194101 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 78596017 1250 78594767 78594787
    0x609010b04120302100e0304090609050708061203040915081e0606060901030e030313050d05030105180601020a050616030c03021207051309050109020307090501110c060a0203040f0803070215 84
    0xa03201d00d010314894022001c5030307002007500c00c02480599900800701407007001c0c401000b6964a42290144014650030400c020400416620569100e0842692841616203034402840041038100c031049010780030800001c1603106c540c2c0181c508100118a00c0d82043c2c0c50040414109022100c400034604501c00340300510b003400042d401d400001c1150306d280c0d03c0f5a1140141c00404011041c504240004020020074201c1d040604464a0145054401c076050142040301c041c4800d0182c0f5a10a02c4400408265901180c200c0c1d031184040c0122088a00301e074580500e0140111baa44060a080000d8682126410300502d07a41c881d070750500b0740c02c001410b501e42140c104010103407010004042004500a400a0b24050043c210303a1000c02003540c589107100003a500483c0d011010401b040d80015003548144c2e10b15011420a00242991110030010040c596201c140410304622040c403005c2510821100e14200030708a6400445c1d40ba2440d1043c0080c1008950344101280014045000f00f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 78597124 1107 78596017 78596039
    0xa0c03060b010c1a04060207060f050702101103061201090210230301060c020d060b1203071208010612090303110301030b0a0e0c010507020105250c0905060901 70
    0x80410181c0042d103011400e0107000303241d16115803404011000101d4840d8100b88a904094507060487d210881501d4035901500d501c0395880c4107103d00d40d6010005114440a0341d0710a00010240c007840264500005000364051041e070398440042140039842204030560080418401e550800c3d0b000b805503460800d11030610b000e2210a0180402800c281c138100c1c2d0b91991215800c241035401d003c50450b502c001104c440d82c5800082c01a9a922884c0d00449101500116182d2800e414820081c481006111040c44450300050044540c400000003c4030f0b480c0c81c02091518070b900d401c80041c94073b40001400d02c20088008800c200184242e140138102d130000c2400300c02d0330b89003210345800041c9005804903600f0851b0400550103480070705102000711000e00340d00c4504481070102d40140000445000c203801c4020302480109105607500a5000e84024031250b0600c1d080300b1f0303 = true := by decide +kernel

theorem cover : BRFrame.Cov 78417267 78597124 := by
  have h0 := BRFrame.cov_init 78417267
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78417267 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 78417267 ≤ n) (h2 : n < 78597124) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
