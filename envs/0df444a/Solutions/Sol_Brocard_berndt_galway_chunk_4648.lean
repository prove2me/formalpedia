-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4648
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:17:38.938503+00:00
-- url     : https://prove2.me/submissions/18652861-8363-46f1-ac7d-f0d0e5838fa1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 835791366 ≤ n < 835971223 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 835792616 1250 835791366 835791373
    0x8030c031201120c15210b10050c07091107050a0c03020405010819030806240a08011e0603020706180c030b0c0c1c0e06030903130f12061a130203010e010602 69
    0x44046041404c1100840340f5010202104072203101042d2800203200c0c0361040110141044042c4410b03c540060f02c0458044a0400158081020540c0c450044007802c10095204400500c030841c0c0d16400614441803031120306042c007036965585847d20500000031030790845a01c03420000c5040074010180585010000b400c569490400c040e110454005006010028010082151500c840d9910440450b040c401075800490507140c200300f0750f002d207018034000f8015400000300203030740d0030701074130140190301110340c069261185c110069006118280c46866403040d01143c1c201c00030f51001c0c8964494490001018039606017602e603100c0051400d514004200040701003140045204c500305c0071040c052640c0c40300c0809040710758004040341c583d00210b0002c248002500000054802883e140f00e000e1038090700e980359640c43c81c0c40351051945c0340c855407208a00051880d00310380ca0240110320116001e505800c001030b40b82e81d4a460305d440695001005100d03007a450002c0d01c0c00341c0b0190006 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 835793866 1250 835792616 835792649
    0x303020405042007020118080f0109050d02011503150f020301090506010210020a1718031605190308130302010b19050f06040b041509050603312102010608030c031201 73
    0x214103039441021002410007801c840c00c0b1141c47e846d405103401515400301107542010080d20300034000e25510300c05032687e1044999400520344140a038000c50043c0c98145210b0500e5a541d02c200c41c41e0010042031100d03150808100c40c5000e510282d03009006086000c20103041110001e13051404d85070050021034010088980956080b07480341c462200c5040c20648607944002031685a080d07065040c002038040000c070440e0003800c40c410507203418010000e030307400240c0e0301801c17001e0702c0c800d80c200a001c02d990f00d0008003c2c3c084280b15043c85800790002007040c010480021f042c10072070100000365240400c0003401282840742c1c544807540c400780c0321a4941402c1015a0304540030750711130454590f40760200c2c43d0525101e41d41103001814060b10f0701d0b4507402c0202c00c4940d02200d680084100210510100704208000c0c0083c030b40154100c40075060003010306d03a410b45842080320405042d5900c803400041c0450003080100a41c0355040c000d152541580c10310200407500690200150020110a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 835795116 1250 835793866 835793921
    0x140703051801052205070503030a05071a100311030a060608070810020405060912030f04090b042f0c010e06180705190618090f060e280506180103030302040504 70
    0x803048881c600c4003449113920215858007510b043e1050700596054000818a90360342a0000050420740380308003020070312024221142d460003d4101e420300c81d000c170310400c00c101280180002c1d010b003120203000e5030f440e400da41e1154000e5400310340c009103066010590400c600f200a05c0752031010203061206600d0309142c900011014043c40c01002c2c85118189000d054084d000c01c21160b200306012070340c944441e07a40010324000c01c22603543e1400b41d801c044584e00010380000000d03030f44400c10562024500d0442c03400500a410501d076110f441c1d9a0340c503c00848090400030a8030600c440c8020320030b0f20700c00c80c203502d0502c140743e0300407030007500103103ca0951180c00610210039280d07540752001e0101090080b1306c0010090350f000003101071602c41c1c1000d0b45203032504420305443c03107910907600e6511351010340680800308450007210702e10300d400001b5030085180c11654003d0002000c90610640802c810070340d078007084e0700803000300e60300040402007418580034206980e940c4030001c0c1d8a070b0040c1907 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 835796366 1250 835795116 835795141
    0x330306060e1309122c030d08100b0f070606080c01140f0426010506010f1d04060518090d1b080a0210110406020615031c0314070305180105 61
    0x42031520a00d011202030340810810340c061204150003403520081c540011101030085024214055801241c825900b9081c400c0012180c1410303001a001f04a407100c00e020803141c9504c05040c455614104440001d60700c41030001400e0300d00d081079400c59950069143c0030b41110032661021180d5004801c06180b5aa040310b4042e51680000724a00c0e40c460003089048030a1295400c0214007610300c8000030b43c00824403405202048012000700110b072074600055514028000c02c6070001140c0004020398010080324030b040790a00a080071421a0302c41d0006642119a0602421001654070030000e9000d02000b040c0181005820404218200ca401000c100c4410800c054004000090150b42c0907108000c004414140f6078020016085007501d801c20fa5400380c81903400601c5500c012914010901d1070f480c50036070004000b0300300d00608041d140d1441902d4045d02e024560744002802d000503400c01042d00c50116a540042c1c03615101016001d8152074000300f40c1540e1401d800c12400d0804007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 835797616 1250 835796366 835796387
    0x618050a09020f0909012307030f060e13050a0506040812010e04020607021c0f050f07080313091503140a060c081e180f03030a200706110433030606 65
    0xa507030421885d074400c01c0040c05003220f244000b01410550340b40340c8001100c07580c3d80707000d40750b943d0301440071185021070074065910354000c4010b625640400f2034020b1800c2c3c880410900e21400a03251905526106c3e0f90618004640541d500c4400042c8146c0c01c0c941c0d90102405017403041d10071a40d0b400c2c182c020500d64000e07014002c0c055400c400c0c0040e20b41140c04d589981640e4006140c00d0700000134a0082d0700c0c4c06040c1c1240c10180718460b404070ba00180441a211601015100b035503016240007a984003a02024056040300743c120078000c00800e0f44010b102204804210007865070519500c0d01104403a0410b5072078040000600a0002002503a10351125011404003041c40d1504d0b1a040c0b400341e00ba19000546041c410a840440c260b1000b101443c440c9468880410450948180c0711102e80d503c060142d0071039000304030b0714000512a07402408880002a01c4900f440d48507410b81502000075120b6031b214000c00c030001805601d15224508403000a0b1074103001c21840d1a5000e08580e000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 835798866 1250 835797616 835797619
    0xc06050904090206031f050a0308070b04081b07150c2f130603020f0d0c030b0a090c08060a050121140111030f0f060a060e0d05100618050a09020f 64
    0x20450016030740e503088085580e400400065803800c0540a101081443c80070100000740040c1000849242500196045a4104a0051034403640ba56240c030405d000400803183c90a09200d4101d0002c60145080014080d0000400d8610300b00240c14078114220240a41008095141c035030000d294000720305001400080c414603180b080040000303024000345212500082c7c0304040c00e200580036080102100d00988444e4002d0a4107030520003201381034680500010307601031003040000c514100180e84282078000008480303200e569019414203043d44168020703440b44080c849440c5451180030300420186000110802d56040440a4284c1410000e00064881e4030f440441000a4010110b01580141c42560f41e25003d54682c12031081035917503050603400c02000480307034245610b807403040d0344e50f60f1942d000300c0003030000300011002d210204a0b0303280070303545015005900c1c034091440908002c4044c5400300d84048940c20071039100401071814142043e80000142c1c40d031a40600d1103000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 835800116 1250 835798866 835798877
    0xb180304051c02130f020409060b0304050d0c050f060403091508041e0204090606090207032003070f140f0c0f01030b09071b05060106050307080702030304031d01090b0f0918040c06 79
    0xb950000504624804244500031800c2074034050301d507070071503000340280c5010581c00c014168036245802d09901044800400d5a801130703041c01c0016006104c003642c0b00d8401e10440380e204825001250410100b0342e0200e02040c64154188048401c1d00e01c0c3c444407015610306503041c0d1419071150318841c0d131601c40140480504045a4083d516a9003000301c0c800d400c00c0091204c030380d98602c4503000f507001090550010700d45481541d0390170205001004c0350b644035401142040659101c14441c485281012581d20280b06034100703c4950512070321a0a181c1480500746103a0407505000c50380740c044408504140c5450b142d1019503841d28280c0e42c0020349480e201824103600031480d04107100300c800141007807180000014803558000c00035481100540c2c1d922a1940701c1142c260713130324082521b004001c140e900c806924820050142900b80e000f0525180c03040503960348a084c03040c1d00051a0407000000003c3c09001401d00c0c00d0304403e1b00340e085400e90054a0151a051a100858000c1404028 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 835801366 1250 835800116 835800169
    0x20408011425050f0d020c0307060c05040b0304060f021210050307061107170a050f031c0b09060d0303020d0603050c0a06021f09060f0e2109010c030c1e0b18030405 72
    0x4001342610000050200c08542d612003403507640e5580d030810707203013250004d05040d409140f451150003524122800300ca2034600315203443d51094058200c1d02a00c0d003080343d007404400e4041c0c0103001158000e07802d003460900142c1c1010141814110550022024040031091005660300001409c008441c10041c0c6000d0f074110070905141440356410003d0000c1c862034102c88020000840140448008104040c0036100315003141415264520215a072101c0c18800003112410003400002c00ca6110303103001843c215410500508440d143e07042074400da408203140040504200e0484000f80c0100e0004001c031041c0000202c2e4141c01d10f000030006540c075100140104003041e0003141d41c1c55003c5c4c00c14004000020b07540782c1d68101c0a165011444140311104121803058011908110010ba55000e0724007820344003a10403144e0b5000840d0b103e4100b460501019001c40c6650840380e11800e0f44c01c2e0207003048450180159600c2c12400d00b41d800410041100e941c034103803189103408042c2864142c84 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 835802616 1250 835801366 835801387
    0x8010e100b0f091e10030f06050a0b1309020301051e01170307060204090b010e18070e0a09050f01061229041407020c03012004050108180102040801142505 68
    0x21820415803508a00054284030214824160340061a81c001c5000c2c0b181741d682e0050b0840050041c030020744220001c02c04c50f0089003c41c1c001c10390020b50a40701140b451424000f24450140040c8003013445030341d078800f4504515080c0074403070b000450502108544c0c010480703400e404800600c10000200b894144010305070b4024401d95003040d811034001c640f90707030b45c5415103000342103030b00310080c0010054240b105942c0f8228881c12060814038113011142c0d5920041521017600c0d1181d13990748001103000c006251503441c06180d20406500c0b18080465140c0340014000c2c0c680310081581c000d04158601481280f50203480b0b11162200b001041582c0c00d150109000304541a0b40210300f6000004104410790002110000c10405030001c21844550f6008d107515409001030000d6841c0080008100642c81103018582103c202c0789012202110700452500b264415408290240d440d00100748120201c825040c0c0d011141c1e80005c40a10186501e803201c10a44100c12010300102044c0103581 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 835803866 1250 835802616 835802629
    0x1021911061c09081317061b070606300f11010e180601020c011d040f0e0d0f0905220e010b100e2e0c0204110703031508010e100b 57
    0x228000c21003c0061240d2410007102651021030284403000c015280001e2201c01605080c2520703001e180500301c9520b408400c44043d01c0700c8000e801001400340a0079000c65198032400d40101785002d0500034014610010f8072114034002446013840c00014012000300c6e04011001c7d0410340e20221990040c2110170041e1618200c2d2041d05e900613a80200640750b071404c0c2144980201e000b6022a04440d542100446220121440840d802c00d01f82540c100e450801c0e402c001c85000703500c6030200300d00c00402c02c2c1034500b0380310505100008001c01007a440d929004110701c4007401d4182c4030300702074400e9030301c2c4c00c0c070165000340701d03203a48550725010300244640030350001800030703001048104805c407406801068034003010520f500c82c48442c450300285118120710f01c2c2205851030b4640303030010181d007001d4421022441c01641c2054481c1001c0752004002002880198860f4500161404410306010440c0c1075039008440345030f1508100e0701c002c1c88e00042032a904280070901003076034a04440461740 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 835805116 1250 835803866 835803907
    0xc1012110403151a030f030d09020d0503120a0b0109030c21140f0f06010302031f0e01060e07030c08150607020a0b07060b120601051f0203090a0609050102191106 71
    0x5080740000c0003c1d44200103030000121161030065040d0344a0aa00c1015225401c842c00f40c10150700030400e4249002041e003004040ca40000d18640c030030551504d6a508651040e0b111146e07001d100e1081080b090420700c81d40f62440c00c00c0ca00003d46038115600d4003084405400f50b21a19505080c1000c410742d010550491400c0d48140c0740d1804104c01c141403582c9661040c10040300380a01b016001d16050009030407030490790028010024050400b100c0f0f200d6440c4820f000140e00d071640818042c280c02401440020000c031050101c0a00c1e290300014100c0b00b440307070383c0020070011206001c5000204540001450f004076056030740d500d05840000c20070b2300d03903600090000a011030060180000c42e8007004080308103881032414080400030081c0c17100b9090007a40d502000e4101d40da88501400401300750411510700442c0d18218403130001032802c0c0520340c011030000d950060180410b5a051201c1d2490401e141c00d00540d0444a40d40c20703503625034203800d09024100c08914030815140131130030300e01f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 835806366 1250 835805116 835805123
    0x319090c030303061404090519140105010806102c150a0f050a080d090b090a21050d03060f0b220f081606050d2a020304080c1012110403 60
    0x405031a40d901e00500600303507502c541c06541c141c1a40d1042035081500902561541c04006004100400348000041c0038800e401503502c03240844200c98415003d10846020b0141c1400510040c42d00e23000e408810343d8035400c40000c0486000062002c0d542c4000d01c0d503d0302d000028046400c1e030b81c00201e95021041401c81981c440081507000840c014801c070702e0000d60700d05480301b0712501d8480c0ca81580d10704600c6009030014203040c0082000d0400400a020940c02c000c1005440c4c0399984445050644a200340c6602070b403489008400300a0200440240d903038a41c10103002c0e040ca0b0107081c007415001c5101e000120031000072000d0000035400b207409070320144501404041600c6090b1488101c0b1980150641c9116404400d68810003140c00305048070442d40c0d0321841c2040c0202820080e224a44542c0c1c035109060a40c149180c15000c00e00c0c00110f40d41e0b00440c2c84900d40980949450443c405081c06082d500c03161110184e0310007003000310036141030710200725150352000030055440380707a0015 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 835807616 1250 835806366 835806383
    0x3070305150d031106280506010e0a090507030506040b01020c06161e1101090b041e05091602060a0b0901121115091f051603140c070501080c07030203031909 69
    0x201504a001e00c0d50f10804d48085030010399a008004030619a101c034003075640030207660210909005138000941c0601c041c034001d01c2100f82040815050f240c1e542041c0e42003500d9504022516074941310783c0e540588121400c4c002c0303042e0343c0c00203926100b1a02c006801964001102c405600c000464883c07181c0e4807070b0740c502190080b480d41c042c400448000c200da00c1c0a11301c004260350f40c801d08240041d80e480d403107501e00e4146082900c20f071945c240e0302d4049505608400000d90f035030b140f4451038861a68401441558510602c0c001e041c078100420000fa02072900c520342905444980741d180c151031400140b500103c5071810a464a5600d04501c1c43c1c1c0064107115500c135460b200c10141990a009403044440303c0d05100300c1c1802d00800d60401000aa07052000d803000707041103040d092035507000e07043c44220501131100d90300c0c00364800101d465030344d4400f8008005035640812940d901c5400c402c6810304154283e03070000d40700d11000d0001650103130310031400c854004207a4002c44003580d010010b03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 835808866 1250 835807616 835807639
    0xc100206040c0f060e06031f150e0301050108070504021c11130e0f1603021c05091c0815181f090605150f13030c08100b060307030515 59
    0x95490310121412036158101e841e0003d640d0101241003800e65181e44c842c071440303003940400d11855810088c041400b04405007000c100959800380d55070f01524050304040d103059001070014200c6018100b403240260703d4900100a001000705003603082c0c400c122400b40c2c0ea0714800d4584202c07281d00c405004690380ca00028141500410703030003048003540e1070020b00b007010740c0c0310b44840625030b048400101c0c42443c40b0002d418500c00106180c00d1034042d040c014100400c00b80032605040c0c8450a80b036180755180140f114160b020442c012071401c1401442c50700b1040200d000303060040c06490540380382c000006035155a030f18100928006031500124115038542800314043e62218801c0980d07100000000114140c18207008100680f00302811500ea803450840090300305a11146207940908070901c0f035280714480400d446030045018400c242c12142c2444412030502e8484240c081016140c1040c460075501d43c9803d4070f03403100540c01d00098030b965054401024010321245141e01c00c03103a415 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 835810116 1250 835808866 835808899
    0x20a03150e070201050a0e150901060b1210050406060f050f0d09030206040c061b0201110316030c061b0e0415031205071b0e01030803070509040c03061d0c0901110c 72
    0x103089104200e00d500910086e15203049020845a203052242039641011040751001100760700038941020b0440300004904c0d0751031007400215084815410404100f41050003101d03420440d0303181c09000304407010003400f0315060f0f001d002038004044200a00001049100c0c81c0d0b03800405480441032807a502780700ea00c509142c000c1d1a180b00b201d08585141180d50041a2030344114000d10748680b0820194034818481d40041d07401c414082040380092100300024200c0328034803001311011910985400455040602d082d20944e4000c20040c04845490555030b80c282c0d034017140c942d9046000350380c0000c0d401e4407045181c0440c13885070005130807031860611241c0d80b180d02c44003d04c407143c0102c248252900443c0c800c0c40c003103809841000190a1881c0c01032020444400095800600c1c81c1041441c00680901040513a0305020070000440e60701c01c000c00c05640d0030240308038401d030b03443e0042c240d5243c1080076802c01e0150301640c0d41008089052400300c56801c10010800200c01401c0d002c82d0242c209 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 835811366 1250 835810116 835810139
    0x1b14150919061209030e0427050c132703020c0306040b0105190806070e1810030c08010b030d0e0402160b160216050904081902010609050c0c03030a020a0315 69
    0x12502c0005101a20300185050003842003000199269452074048880c40d81044058070030582d10a0748a007078407004030141154a05c081c0f4036075100781f01a1481d02c980b03004201d251070702440fa1000c881d08100415900c04505420095200700d18107000300102c0c02d0f414100e03e8920440071031038140c42001d00b440188401000c040f41243c40480f200107005e1034401920001c6034180c400c0032101d9104502061b0000c1c000d00c00c504850750302034440e030100701d0280b403080f10f80f00c010b9800078080190858203000b40540c0041c1c100151000e240248211012000840d549444100190041201100700041d19544540491710b07125030000e00c0003004182030400040c16101590311081e5000b8804031118200d00124940c3d04807040c101985800d00d20b041c045c082000c5000348101c1e40c0720420450004c80400030040c165441581f0b0f8000035a5900b4001c4e5403044a17405003070000820010701480705400c4c1d00104880c0d110380942c1000d030316002000c200780c0c0030b41040304c819155140c07a110040317200000b25 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 835812616 1250 835811366 835811369
    0xc170a060c020c01080604021602151206120a060e010e031308060912041514030a02030f0c04080d05090f0406060f030c0e06030420060c0a1b14150919 66
    0x16401080301d0701d003510041c0e9554140c1c032900781c04264154006802403820303030301402e5000c2c2410b4980c408051160700046074100c0e40c1007103072003844010070401c408904400010703600090980d00980410040b1804039643d07110484001c052030b460b00c4050396044000e4002c12004207007031003100d0b199024122010040f041c54026000240704200c00990309000024100e01c24102d80c82d9664a004d044c10003c098070384030003106000f4000c14458941c0a200c901c00150700c00c0001e140010b0b00d038100100a03503a400406030030701c1d104640071310090001c000041055001d10700f150800a0b600c1140314086401e50550b46d101980c85440d12000040c2c054101d02d6040a1202c10b40c0e00b00604260003000b5107140380d0011103160001418800100098030013950000c1100c040ea0181d0340c010500030001c1c080b0b9019496181803600041a400200042d003035900300e54000503901400070904065107012160f00540240744991002202c540142c0700003800c480c1280c0014003401c0c03804415031000180550305 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 835813866 1250 835812616 835812623
    0x1202030d110a08010315060e01090608061b1911060103140609011b050a1b060c02070501020a0b07140c0a03030c091d06061803030d0507141905070c170a 67
    0x100349203607524039000c5084a600c04125160320307403184d0071a2200340300c4404e0502d8000b000355850001003014514220307000e00804151001080203410001594148000a4502040001800d480f60218101a0240c41c007001100b15241c4140788802c008807840c2c03281031801003443c05120000310600c42c007000c0080450114004070780068031a5802942242c0c0841316803000b5010080d004c4041d0380c41280280f0312080103242910808080400b90603005040800c2102c03c1961810181040c41d0144400030080c0424000343c605c0b03182a4583e070180c2c64008004000b00070010f903035000d208034280d05480721048944102c645d207003240d1a01900506404000d100403e404140c00502c107080300c5030551171880c1b100240b0990b511040c0501602d900f045040f44c003850102c0c51404e0303040e02d00b08041e00d000f02c40244049400d0a2010018110724071160110041c000108200c0380c54005128180c0b15810b414507055550380000d0400c003560141c941c201d00c40800605000f20009040012003d813030901 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 835815116 1250 835813866 835813871
    0x5120129040516090e18010c090f0807030206030a0e011409070306050114060d270c090f0e060c0a17010602010510060815220c0c2d060506030a1202030d 67
    0x8800d2400a1600f0910894500042101d0014000501020b880e070390401c1d8a07030100c251034280c00e107141d801c0d0780072101c00d0743c0000c600b001c0c01c0000140c00040d00001309103034005056098250303004688a403100a08a41540b03489103405240d80209600c099401c1c04000703401c0000b07080101002c0d0312041188010340780e0905240021a04805d0303c2e20300841ea05004015929142840d4051405048554500c1c405589241e0f42203151880751445032804a204010322400542004004002c03590005041000ca82c582800c116260f0360000b080c43d040451381d0340285c1c5600040c9012145649044130b110841420380c000003c03d960150861400780354041d01c00540191254012280900f040703403858010b02c6e509290644608050b80b00d01c540d01d041a0311424684218107910082d140c5100021001840b07011060090000c5001541035074005106210180410590042051007003901c1c081c09882d5518080303882030f0380c100030b40f01c0e08075070107021504281507900c00030751640c004c01c407003060050 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 835816366 1250 835815116 835815121
    0x30503100e013c06051e0a0f0c0516090506131e0c05190503010e0106031401030305030c0d090303020405100503010503150414060a0b0a060e0a051201290405 69
    0x1103941c5000e043e209003c41400b14030704094080e0381500c0b400002e01d8034200d03046407142024030022a540740a05099103503180d58122084d0010349030f2a04090700030514005104050030031f030b03000385862540c03101031405007901d4219090241c205913501e0f613010002c601c1404009030440c580c0d0050740c800c503001c8801111004004107440c050303d088090f00800b000c618000e00c04411203a41c0194480000707440c22500b000e0078046417029003044040e410000c01c0001c80100302e040041f20001d0301401c41c1345000d0050341040d0320036070300100d818000107040c8000800060081309403902617512840302c0b29014040740040e410041c00030342c014001c142c010440e89840201c0b242c01402282d040364000f130001c1c141c082c1102c1c01d081d143d44028004541c500d10000c0c11206d260410030405000303a2203c0000100c0c030a00404000d403080c010303071003103003072000942254400f543e8042d41d010447d44291160754841c3c01c2c200c0030a00500074006800307104090f8103064442036840c856200403901c400d9504100a4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 835817616 1250 835816366 835816379
    0x606080606150a11010504060f0e030f03040305090114130602120f07060209040207020d0309140405071d010e030a030801051504030b0a0f091a0604060e0c0f2503050310 74
    0x81030100c039401d030460541e12245568580600080160481c02e00e005441c003141030f6180c2d0f081d280c055406492032502ca02481d88040c1c103d02c14982c401003540700461038545841000c1615000081000e001e003c40070079551100d9014000e0410030100d003504055841c0540d41d460324810380ca0303011f00001445044050000c0340c158604803403031881c88040b21418101d0980e21000070f54084012607812503001c0c0005c0c00140c03210310b000042d85100b40c40d19004c02e810000c502c98209100580548100e00303002c02d00c0b828035000425440c07402ea10b44010409151080d0041e11508103003184075801d481042c4060091641c04814641644d80490340541c3d105c9414821072114002c40c08041c1040b442800422008000c45d44810010348014102003130709100ca480740000d0080406900300041c03c03c0040054914180c401c12014101d100000700003030611383e003081601c1c0600440a19205000514494400327461000710034100003090035074114a8881c58000c00c50342080d00c030180a42c2e85000040b680 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 835818866 1250 835817616 835817623
    0x10806070212070510050c0705010b010309030503060d170a03021305030703121b170703031415190f081609050103030c0201121e0218010801120b091c0309060608 71
    0x46469078002d042c0d102e95182d0450941d07128a01c12103442c864540584401100d41c01001c1c030500b10000481e0700d42e101f900381542500d01896915040502e40b00307840000035040750542c3d401c0300b800d5900c940c202482d03141140703520342c01403031400c050000401c40082c044c1e8140c005002180c01c0c0ca0380c10000a0707840041c0341c4d407807106001c010001c01100b4080000140300d1900c41d40c1d000d410415a002c07100d100e46030020854036144003188810b0000411100381a094015100b408036410540d041d68a04019800391909544450078420441c804142103d44089a070003400713401624000051a07070b44211a550f035200c10002c0c6a80802c1c00c1100245100b05880703000d0480f9010707241c0740e011203026401110440c8607070003100b03052603840540c00e6031071619021703501c04d9045030a0010707070710902810003205003000001c0713660400c00c0013401802598080d040b0780400603840200f0a4183c0c03280304003d0706003507030101c0300c244400840704128110740d03068000c05001e0b40560f6040104e0b03a10b503603000e501c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 835820116 1250 835818866 835818871
    0x314041b0e1e06010909150501030501120f02060912010f2708040506030a061508040b13150f060314032a0c0d02040e0a060506030601090506010c0b0601020c09090d0206010806 77
    0xa070006a4100b000169030744040340c1c001014903050381002e0b200d01d0fa040840d120a80d01242c14440c00c1da00b40174039601441482e001d0200d105995821180c6c603a42c2c2d40c04181c0045000f401808042400d189a89408140d0302d2041130701c81c02440015019000c02c80140001341da0b98071030403c5200c030078103014164074540740d01d5500409006d240c9402d050a1025030ba101030092144d0941d9080000303400b10040040d07a48140c1a9501e607503160519081117003414002400180282c1440109600060607a80005044030161040450304144603141e680c010010b036800500302407800d856840546030040002d00fa00190f403550112002c080c18241c003104000000d108a0b140d11100703507042c26244c04074101075910320081000c01c0c0313201c01510780c0b07081c5030031850102c8486499400780840b42c6400e01c005405000c200341c04221901d00741c00000e2a150070308901030052650328010030200d034030030f00a1407540703400a4886034840c01d02510700da540d900c943c00400014000c4034004181c1080100307031a130 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 835821366 1250 835820116 835820131
    0x6181a100219051002030a0203090d0207050a060c020f040e371104060b0c0106050112111e040308030424110d0c110f0c01170f010b0a0314041b0e 64
    0xb0b442200009a0310720100301690244140980c1d0740c0c115110f400150311815014502507103d08010450926203031801d24120155040900f0900083c0c940c85841022580285050f104410756400403c103e08aa140701d160094200340c000d0030484c0f0300140050f0720780040101c00c46030003140e0324203500c0722603035042006c3e80d1034140c4c2c40c01d004541c1c044240c0c0d001400082c400940f2942e5003c40c00c207240c0c00386440e080d0594480c91b0821403907030000182015540700d100d0903c0030300410841c0c10ac16114510308070420704242e0b0007101c5504640d005440103180e00580f899a0b03800e00781040c0d1401106030441c60410450090801ca106482d405403d6405092820403414190400d10607405400030080a6003040807122071411030400070000c1981588000000d0611317880000001008281158002083e02d0b0713140c414000c41800c0f100030141143c40d4103001075101c0907001d604030090040328500100644880d01848184229100c0c0c22140005960600b40155a10f43c85001001d03021503000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 835822616 1250 835821366 835821373
    0x20903060105101205101703030108061305150a270c05040b060904110304120212030705160605041b0501090b03061207050604030803040b010f03020f040b030106181a1002 75
    0x10803032414038403c960301c012a2820310441c00040007820500b29001121940680448003904000c8010641c580c660407800b200007441c91507050180ba0b0381d0710751001e00042d10b03c064041c420000c0c0311083c803400d4000c5164040c544800d00f02241010702400302c403502c4543d01121042d0b0814180f0308101c0d4044003e5200320514450f81c41c00003048010706801d40d500b508035004200025041d5620b10418402c100341118554507420103007010340c040700039a1408015940003c2c5058801355246080c0c95002485141665446082c50047d003184800340600902d46404d0005000c01c005e100141b120400c0300401d09000d80550340e50045481000d90f1085080340c1b4000c201040c090309041003d00201500c010450b0204c130b030f0f00c00100e04150301035482a645400c020040c0401c10035052459030050030060b20308000c2c541503400080c4004c08110089200720b50720140d407502900e0a410400c000d114003400d0040700b610055452000d0700d03002c006050045008000c040b11032401c0f081d14002d01e00954002d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 835823866 1250 835822616 835822619
    0x120b10020a12120c020f010b0609181003060c0507050d05030c1e040302120607082d04240e0f0304120803070c050307081b060f0a0f0609150e0a0209030601 68
    0x2035079000c142ca103100c18104448880076548a4640307000d5059001455401003414218446c4501d08440103038440e907200d902e0403c00f5001503525140d009800101c0e0316911003090700d80c100c00750b10181065100030440c45c1419607981c003458200d8041c00301280104261000304040074000c80340c51008550b503490a110034000805810100f000705402c008a50540d1031815480350001020414401150b00c2d05910010401074100d03802a251500031080400740e02e040365100c0700858144140b4907010350181c410740d00050500007408549580e91000342008002c4082d43c6480501500817403100e034034a032240c1e0700042907240c0000101c42c115500d00141300001001c566900416a2028004504011a0414240120360180b00500c84540305800b996503440d1401d8420b549411000c46542d20f40c5c00807000c001020415040c145e911140031500003410240c40440c8500030141074003c1104285040d211045003106400c10070705485044490460b135a945070700b4035042e07108055242c3c0e09034014000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 835825116 1250 835823866 835823873
    0x603031b1707080d050108061b0405030312060f10051306210903020f190b09010507171b1b060603031e0d020702061305130207030903170910120b10020a 67
    0x2a0090340e00c107940651520a9410419085d1030003a08410b042c3d41207101804041c4d280580302c1e140402210494504051800001944a000310354407041a0303c840b00010740d66a42e2a0003810040c040142640c02505e28040001c00740d401400788414104901305001c900d090240060010003540302040c00d40b544000f00c0c108000c0c040c0c0540c12819886240001c8404e000d05000c09080447c929000d110310340403e00b000f286203503024001400c1039240c241841242a80070441505207856054a0781c400c2d1541c5004002d050400b6040500c58100481c0c043d03021020000803440203104102143c00c0c90310307001304040c0c40e44101d43c00c8650606402190000e13585c0144007500b01068082001410005075401192050740521440d03540c0100190041c8007600d01414210b2861130307039103421810304005540240000286010207415501300c1c1032028000c04400c0b045541d01440a0500d200746540228064212101110888c2c2d8090420180a44070700b861741415106160359401018407074100c0d01d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 835826366 1250 835825116 835825163
    0xc0909010902091305120a120c0c0b0f09030d061e0f0819051005011d010911070206091c140d080c0d020c010b22050f040b040b0705090901090603031b 66
    0x4c421660fa0141700e44200200400c00080c000da0800c54603887c815141004086d011180140e03134803020302140c1c08101c1e010a03880c0201980c0084020080100c544965541b540fa50180705010f0010700d02345400400c0084c0c035981c074020488038920001e81708070703160743d00d6031003050325400343d410958410441320001c013038004801c02040303011304140ea0021406144400a41e8800d800071000032280704601071000c504525031a00418400e481046154404080c000c035503c20b411003c0c1c030425000c00c2044503030359030703404040541844405807051f00c0c0c02458007080e400240451f80e11580604109440050300030b4228601c51060f44040c10b203407001c7c0400180094000d4400c419256513141814007840e1200700d403600c4000722150041030140000d001c910300307540b40244000303c0e1036400c030305201c00282001c90707042c0c002b54010314154181c0d8482c0e0707040b5000e000740b000703190b80002079000000e42c0c0e104c00d9001d01e041d240240c0c0e820f604007a009012071941da9814000a1001c000d00900702025001d80 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 835827616 1250 835826366 835826401
    0xf0b10140304080d14040b15090c09030c04061202130c050a0c11150c0c03070b09040902031f020301031a041a130f060b09071103180d06020a020c090901090209 70
    0x3034850038101401c501c010411030301017640d14514040c4020a00c010311403642c01c156031101c4065070a01071007044802203026080003034403107000d8035008154010240c0c0c0900102c808202c018100304811a0340e407024401140302c5082c10390040c4480c122800c0c2c0e0008602850441c8071082d15030300c1c90021f01200c110f42d00124100140e83c0e52085868006031aa9916003800303254082040325520780040e0050103003000740c5050f02c1031007648152410400481c040d81950010b00c01142c00060501031800440d00704a5101105610490030300c9904070303800e005a004d58140c030700403c1181c0c92038000c92024103010909030b80c0039044080041010300500902200e1303552101407001c1038941180c0c41d079500358502d03007035010131600d1a440e10050261b900f0008040c5900803010302d030103e080510365030080d843e4865a00869003880540c0404081d03901d5041e410b1500580c8a03108540d983d0b40300400946409038400818850716036003011411702d483c140102d8039004d400908800030b42c3c40e00317424078000c40c404 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 835828866 1250 835827616 835827623
    0x50301062f031204060b0d05211317010605010503061311040801090c080f0303160318020604031101030501170d0503130519030e0301090b150a0e0a0f0b10140304 71
    0x229405485000ca050010f0720321080c0d2204844a80e00f07052410006132800300c0c6800380901403401e6a80041031000071324804a4008044040040340070411040492003000c0c400c0c9a045082100081d1a4545408140100f14584003c01081351110300444162006440781980440d4040316140c1d01c500e25805841100c4444403018540380da50850a404c3d1422a4420341c1d000720490001c00018100303126440c00c0b079490070040c61552030300c443e6001003500c440c0440c80070141d842c2900454611050384a070303417150700241216140c580c1d914042c0206042115114002410300b0000645588503001001c500c0307103010080c0c007070003600c02d600f01e84c0c0780c10040210000900112441d000300d10103025003c107500c81c0b00b0580341c0f198190706028142c500c505c0700c10b41c060ba00d1700d05100040382d5a0300d070141d00030030402c40c440100901840001d14605d07a40e0440134003000207600780550200207034041c0c80c040c5071345001440b10034044004c0227440c500151218010429070300301001400a25401141d20511 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 835830116 1250 835828866 835828937
    0x70305061e0a1508070b12060d02030d0503070348021e160b130605070f1101170906090c030703050a1b08060a0606031119050c010e01050f07090605030106 68
    0x3982c0900c0c920741700c41940708100340b080004031a03014100304415107504c82d1050310f049507040f1582d40801e65901605000c14200080030000c5404a4880d070040100035011000486481c0040024010021402c1602080343d00d280c040100a03504c48015404d80c3d01c030940c024001c40440003506400d2000a20320070006401644091035010407023842020147c250000e00946440c0d101c02502c520b61070941091b028083e09000040c0042c0d9410301232502658040000c821091102006031461109000c2d4030100e22800c400300108504001a8148034480c082c00b01c60040d01e50308149034840f4040d000141c066001031100c44082a070003143c00d030074540c0085c100301084c0d0f941ca01d03160600c001524100c4641d9190201040a5a4140103500c64268810102440d01e5261241c0d08070360b02c00c0c068010b05000001c1182c002e50482980b03c56080300240000344101e2500c1601400a8041140c3c08000b050444101060840c030441c00d50381030b1031a940312042c5034281071090354840004412040030f01d46 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 835831366 1250 835830116 835830119
    0x933030303050c040e0c1930062106050106051c020315030a0305070b0105091e090f0106140a060827212706070f05070314070305061e0a15 61
    0x8810a0010300c1b404031070f03203500d841e0784070640341c44406e02034071400804000764090810358102c0c92902c0d20680403809894002404040101b0750090036840e0308c600e5144007007508840d070240d580d403811010700307201e1041001160388822041d105801082040f00043d80c1c0c48230105120a0315a000b50f40158498030742a6400ca03907640001d10b40261000304a0001d4000f0031107104006851800d05c0c05003400311030b40040c615013080d150b036407420081c418404d00308100002c00c00c07949003407126071540c00f2460020b120403030700e0700c40c8913039120b1200d0303030103401380364541000602c040c42001054010402c00400d0017200030121240030145a069130301440a008102c5000c0c9003481042e4407022048a100c021620307500c494802c03681a10600c121280741540b1000c24185c5641c60404888034141d00981412442d04542412883c1941507000113016111900d2980003c07000011610110f9101c2e504031000e569a1036480303240c01d41c000026a526180c441c011501580c296001404c000003501d120b03400c20f5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 835832616 1250 835831366 835831379
    0x90103090501060812071109130f020415090b010e18270717010b0a05030303012102032d0a050606010f21021905120408130803040933030303050c04 65
    0x4a171041c441001c1304000036926082021030568040320b903400301c40c940c0307151a1103110740c1c004484194006022152820094046540310307800742c0d80d20f030340354040d07048440e0311001080b0040c0602c142c10b60204850140c8003005150058022038041041a03a00c90103442325400214040311003440308107040b055a04810401780e0410109006003100d03032040164421200c25542120fa941c1d42d810701a194541041c0110344000085034115101c4140d03203442c09001140303205181c0e0110400940c54014100700703403244032661810404005c86042c3d0703407144994840000f5682e6044200050807078020b0b100148003580100300b806105482030900d4440c40168610b411400701d41c0c508900703280303540414203a520b50041b00000280421a0800900d0003403100c44100c0c0180700104000c0000c0000100d19040c103840d071898500034120441140e40311500d40080e03001900c51003110182c00c0700d14031042c4100b109980400541031106102e4001118195242200136200c010403032010390104000c0001e91 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 835833866 1250 835832616 835832623
    0x220312030207171204110604030609060b211002030a020c0f010e1c020709020a0e0604060302040e0f06090402090402030c030d180806010b0d200313020f04060602030901030905010608 80
    0x444049560060ba1850781e0701d491461038030051403200c2c640c1000e00606500b03c100c101c0301c640080c3c004400c6500e1046001c00150b40f485541c000804050901440c502088404d402c51521000100c41003044c120101315040030a2519074961811580800f541480c018143d5008540000304120003514000c0e02458651600c040801101d00c1a036440c101c0b00080c0c07000303200c00540040080d001c01100405460001d684021500501e040b051b400640543c4107401032040d1911100050310042e25155034200c0a0001e400030b20404c0181c200200004026550f40c12085100d110f0080000c9080c0e121a0244203444030010000c981512920091010f25901040806d101c0b4580380d0ba20303038560000310514030050380c050303022501c103a0005005020701020a0b09450b00ba406c210f03c0007800fa8080d201c041c2e040c1c1c007030718410070b1450400401d00c4901c40b8065621181039000352a1121048503d1090008a525510404005030414892402c44e58800d42003070512a02a5001240d2681c0b0340030001e05 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 835835116 1250 835833866 835833893
    0x203040501060e1303020f0613060b1c120801080304050a0608060a05090903180d0b060904050102070b0f0420090c0711030f01090b1f0902072303090112060b2203 71
    0x40080c04d0340c00402099410004862009280005070a80e810400708150307410020050040c40940c071030100b032546484050603d8602c02803030f148d03034900c10000e04040074941404980d000004400c01d00103e5030ba140002140c0440300090a010a4103140250803600404090000c81d0f014140c200000344aa503407240c0c2900846402c80075503a034000040c0b03081195084e000c08640201c20b44260480400d503400d103c00d07401001560301c08401c2d074039450414024407036100300034420800d00b02440a0f02c000384a030103104070700ca03045981080302850b280d2409404100c43c00350b4441071900004a80502d2007010300407052040b0450950408594002410400000208001607644880c04c0040c010450089030300886d01c1042d0442484000314401c0058a29004031188207400140340000c00c03440c28084105c16a061111a400704a0081c82a072254445880d1b00d002403024040b0100001c1c6c40d1241d441168030300b81945240c8110303014022868400d60418042c0f1190b0441d0010120350041a0f030301 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 835836366 1250 835835116 835835131
    0x40b0a0603061e080c060307170f0708130b160e030303090109020a0510021c0909050709030c23100e06030703050603070e0f0a090501063303020903100203040501060e 73
    0xb00a414020802d407211980310b850039003040c08020400c100313480402e1400f8000c5003540ca540d40d0740d48120040d1950308203459281044082c49003000703034980300c0d5541203000d52050b42d110242c1ea140d08064900c130a800000150022107550003045020506400204000706036003030003247c002d00c020010b800d5800442c1c0901460351a00507850851510b00780241c09801e080740c040400b40001e01e4005d503510000d41340c0301100d00074402c0c0401794078003a60606c401004c181409000d649400c2d4001094500d031440100c403c4120320034045101010082e968003d4003d91100a8061001604001448544103980d50920070b842c414010300f510b500000318404c00c100d407804941820000149403034200340c0e40c00841e190781410284005d030081c20a0741c4d504024094404a001007082c10964010074071a4400d408034040086940c3c90030050407903242c40e00010081c0580c00541c00035050f4168400c0a8506502d80c002c03c6162820002d640c0c051a0091300990000400c07d8460a81007501d81003501c041 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 835837616 1250 835836366 835836371
    0xc1203050415020102161e150b030d0914130212010b040609120c030b150901090b0f04061410020c221b0806061c091a0c0a0815040b0a0603 61
    0x184031241c608038000301c860300607100840c038203e0186c15041d050b000401e802002a00b141001c10103041c40c000360360545e00d0300504100400e03c412050f160060200d07060150090149010510000d4007901c118002c031103480c003259503ca5011410050507140411403121229402c0c0300404001c81b01d9850321b8040e15064210690b02e5042480c05808a03003036902086080d249101c081300042c5030050402d0480380c0c00101041d45881d0310314001d060030300e0400b0035038201000c0c0000198907a100d80000104080aa6066203210610030620090381d240e8041c1ca0305140c120360b14000c00d810306501d1040480c10500c1911322044068001480ba019a0031090702c86007500d407070b400380644040c4210550500980d920b040420011400074280303400051031244107540200e43c4d5262a0f40c2c0d02080f8884c40e0404400700299010303440c141c0502c4180d400c1d240c405000e124002005500740d2811140414915204c0310b0310740d9281d1612070000003034013800ad60003d841d02d030f030703500d154850030490000340030962000f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 835838866 1250 835837616 835837619
    0xb04060c02182a030c0a0c140a1511090d020d05030c010501060c02040e010c020d11031312060c05040315090303112a01062702040f030b010602010c1103160c12030504 73
    0x241d20030340250f400c1e00c0546001c00074080c46828032000c4900d03d0f102030070560900f03462410301035601d45440d07444402901a00e034460f02040b282c002c0c42c2e105890544001c01000d102c4d288ac0b06128061070b40050f41220018100102504e800074050701042d11400450703103092500d007044c80c252007007030303203c04d000c0340d0707101032074400c52400703020f000345041503035000700182e0b00740100c02035031940c542441d48244901c001d110001c540d0184112188034a001413440100d40d614044c40704c103542400b0040d544140380445102815104030121000c40f1340180004e00b05030840c0c090480102a8890101c0905654000640944800001070180c14868000c0e4880ca941e20440e02525078410035140c050b02d900d001403e100d2040c041401408103400c041240c041c51081042101c001c2c030541d00f00601d01e1680340400403c2011805000307050318103540c000e020034070803540d09403280c100c0100d1201e010340081c04010054011800611201406522031082da00d6980711920902c1e00300340d13010340000f84002030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 835840116 1250 835838866 835838911
    0xf0d0803090606041811120318040b0d03081816060e1e101206090e030703030e07030201050403020d030e090925030201021509071d070f090b04060c0218 67
    0x50fa80100155000d002070b6284144081d608490407100802e10091743c10100001c0d11002e00f5030b600364503a9004c595545056021102e248003e07809800e11a03401d201c05440c9509000c0500314030146e141c0c803039816688070141a2041c85c0850469a08140b00d281d040e002004282c206200c001c0113180c4400103015143c0d418400c0b422581024807001c500450a0861540c0701c250b03416803224028a40a00050132001c1c1c03a5001c0c0c02e450b80700d030000600704140880d060b1008401464028460b0301d0400c20301050307001454690340d0354400030b40411010302c010000340c1040243c0d806040d00c00e01e07144a0031992140095205401951180881d03406001d000300341e101c1c0c840c40302514030008620f1152180c07640d0300007952000380c03001d5000803002c150080752648404200000113031802c400400d010000e5140c401203210411600352001075040b01061580d18010312481d8195104010b10901e000e0400c4001d0751144001c440803038000100850900d10060340c01d0b15940500f01000d2003601d804910769 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 835841366 1250 835840116 835840123
    0x1a070e100305070816080112150e03210c0a030b0301140f06040b030102120c0a09031509033203190501080a0b0105010f1710030203030705060907090605030a0f020f0d080309 76
    0x780b5500d094101003c1c3c00250581003c04c1c42c2c1150010848c6600b10112464040b0000300101d003039200c4541821060040942c1c04400392041103550302040f00760600442550070070120684000d0407000041140c900c600e8400e030060003400e00c7c041e0002c01c0407035640e6141c4d100e01004130b881004840040042c440d86103014040c10030b001c14214029401c09401c050f500780144005040341100050010b07080c8003040c01000e228000790f82020419959410303001440e0042e10150307100b00c0001d59002d070642c0078903098000350721001240e214034480100c2c00c0d1804101d55400940510095110340040070580c500e0303409541c0c088c00f5000c01034080e00f01c3d2407800340300d0284c045c5c000d141803180c102510121250310090381c00840180000b019000d860f2a03c401840d103000d41c0000c2c1d09400f00084800920800064043c0034038001d10440b00080d68619802048640b640205a13040e00301c070708010003040b40311001d0719035076000070640c50340b5040c0d25000440d1010294400c0b51440004410480038541c1070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 835842616 1250 835841366 835841371
    0x81309110403022b050d0201021201091b030f0b03100f06060e0d061109100c020108010e0108120c031b0604060b06041202060706090203012405030a1a070e1003050708 73
    0x300105400d0606650000d045155004101548260381c14080c0c1d082401020020304c80c2500041030344c001000d50000203010350300201041c86a10302d000000190a201d522a0f140c003608030014610380280760311021006000c908440c40c403110303181d004408040c1c2c0c00340010000040303883e80000304940c0d4011454140c840c507900003000e20607040789040b080d485a40b51102440e500000005400c0a01c800d0085c090003424085a0441007404003209100d07000800c0314041c078001d8880c201c182c2c1e81c03103074429140402405080307a40e411500d215610305072000c2c0504210309005041c0c1c3d003011006001d621100e40078401d0006a688414244000d1024910031f08640520503698145800d041824001003c800c00030003d000300320000b110414410542d01c01031100ba4024024403100c0b401094502c120071100180c4000410585000100d51030005440407100340d1000d10000b04458803181d00c1e542d03a00090074202400b13901d540181480d607860340d04d0301d902d09a03618009110308103194001c03c0803100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 835843866 1250 835842616 835842641
    0x15020c190e0108010509030f0c10050a09020405090a08250b040501090c150e0603073c0509030d080907090908032202090610050417010c02060915010e13081309 70
    0x45c03c051046c0f181010003210130054201101e181e82e040b6800d00c071464100b05165200015203050244940c5800079000f0144e003e008450a1142c0d4071074000d420f0300c0e1100c00400501c00c0704104000f01600700c50041c1c600d0f04140e003590300160119141c41ea412024011241120240d54a00c80c0604000b580c0c0070220190080c0704a13425602d91101e000b9100f110308550340c0384108004400150041d1050070902181e0350303c0706c411000410030821070000c1480308140381c00c4c01060a842628400d100703000741d41a1000040080c01a644e90340c0307043c2c0300404086c0c016403450080c844085024603c6000d52081c41d44140070b5596a0722b440781b100b001203000c00c09029441d102014002015075103500c6003e07040f41c801c548079990200c16002c2910184a160f00003044039031921110100050190b100c034104458507025243e07540d8070144095154011400c1c9403204900341e60042c4105482d614100307500c04404c0b90b494508810540b00c0f42070942021090751840519840e0a000182c500e0244a890300701 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 835845116 1250 835843866 835843871
    0x10e0303160b0a140c030106140d1a030106082a030f0f060603010c08040503180328120908120a0513140a06080717040501060308030f0a050f1015020c190e010801 71
    0x8229441c5005e038441031041b0020810314061111411b00c40c5400c590240c404030400300400c1590440d4001010746800005100c0c2d441c225000900c1c032408102070290950507990820280c241d0b44058041c5144a000142c041c45005030754442e00104110540c0c15001c80d01c010200c07490400e0401d425121080310241c1004894801e0000041000003552030500c500120758102d4465030000c245845243d1141a02080795401102d500c0403504141a0209000390512049822299000e4034110200c0c071890015610040c042c0254040c800040d105052081c13500b1490070001902290342c1519940210303400d9940c180100703a1501d0400d02100090246082600350351614a00192450b0125001c5645500e180b200160170000203600010245a0190450391a802c0a15032020b4060003220a458810302c0c00d00031a0f40d45d01040112803050006c1c0303064200190a180076580c58500514114095120f811080f220540d1001000d2040001251410784600d203884404074009906a101802c280d2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 835846366 1250 835845116 835845121
    0xc0e0406110f1c110f120901051e040c0902030c0d0c080c19090b0a090f06030213050112020c0d0e0f0d050c012303070206070314090c010e0303160b0a14 67
    0x40c61000e0b0340303c0064006441080010308400b203000380141c508144075a02e800201c2038801510321000e44500c41d1b000051001c07907519400198200c600a540301800341c1c00521010344190001c0400680c0548209a0030241c5543d40c441030302130ba001614400034442002c40c80b00b0f0000c0700e078481c074180514549481d0031103003064190440640b24440141401c80c140c080307200244c3d80241c041d88002c21010031002d98a81c00c907d0014180032240c060031400c0c1c15030742000104940b09000b519284100a034080841500e041d006540f0082d2098014100c0340d028025071520341c10500c0000d560382569100d50b150360703002c1020880e00b54000c003803091080b0402d4084401003040010b025040200a0a141344002c0109203820012a0102c02480e5200800401c1004040c0d0106906018080d2928103002400d08041000414203040b41c0c4a0015403001074240105c1d03100340070541d4034034405406e40c0d2400c501036040c00c0c420750b0750701816280160110184120054140b00b425000c00d81103038002602d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 835847616 1250 835846366 835846387
    0x20304020901030803070c020909060601021917031302060c0604020a0902070c151e111c05030601120f0606090f0b0301080a0803091009050a0b010905090c0112090c0e040611 76
    0x201c41c10300015020400201c0056407460280f04540c0119400610350035803490070f1000e0694a40040f9800f0b401405000448000203046440000001b9442840f5489503110615910920f410050028050003090040c00b030258540300300030300404142c0d00182c9404e2a207070051004409550740010750540c41004554007003220066180d058508004445140e12200e41c811604d4800b0b0408041052103104c500901080d040000c07005d45101c1007003a284480030000f01c03295a0b07d400c8c0c01450100fa01040002c1c9a58841e50200d401c2581503640016004c0654415804030348082d0880303004180c218000340401c200d204501c034010904810102c0c03842d8113000260380c8a284c1114001c052120200100d90510028041a040e03c40030b15000c00c81032806092440e07540f046000d080c3d4000140c2400420900306a0160318485d0307420740b0041c800144104011114102052a5400c0846c0c4c2d451110002442c2280c0c8079004001e500c040c0045400c00c2d040207011039078800c0b00034417a1001042400040c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 835848866 1250 835847616 835847629
    0x12030c0e030a080d0f1112221101090f0f090b06073f0f030c0806030d0e040207060c0c1e05060c0c1e01230c04050d080c060a091502030402 61
    0x10a40c4074446546600d4132004200107044d1054160000e2401c0440c002c0c85076201c40c0240030403a0308210030440e240c8030009100180a2190954541c0d65252444c0c030012514003283d0036031541c0c040c5006400b45980d11001d05070850b00f5001818903d07442842042404258040c10014035021100c061401d0540d0740d0780140320224181c424140c00c40c00301200e800a0200f140c1507054411200006001083c0d20030082c04108400c81050100f0b06c1c1010f81c104581c0f140842034072030701c2c0150092220902ca06010340385c0f50b81d10008951700030740800401002a8060080b0501c0007000d481c1c500f0425810303c0c1043c448400c2700d00c80192280307007101060228000040b842d400100c01c180075a6641140c6500c60704083c07910554002112202c0b41d49040d42c03038154091510702c042103c000c05c001c0051841d01104100941d90400381d89011322040c0981d00c0d00300c149001e014844d0f580d0a14080e103841c00142420300c21030b5108240b55441d80d081c070520141e51800303a1340c1c0143c10411840d51506a00140301c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 835850116 1250 835848866 835848883
    0x52b05131502070305012a11150a09021c020111030f190903120c020f0301020a050d050903130e0613111b03040503070b031006020c0d080d110712030c0e03 68
    0x75144051015202000c0c02445100c0146030004002c3c85644050a2000000c00000c144903103440e000082c039080c1b65119806c0100b4848071798018141400a0004170300b0190b0006c0c0034141c000c2d41c0ca50000f00140d5074501c4401321103446407450511722000c0d0001610003464071000d00407a80081001d0800d011103e4220b800e50b4401c00d42401002000c4042121007646540008003189450b4002903041500410700507600c610071a00d800d492882d6105040c241d024020003140031442c2805400494080b68001300c1d44400c3c01c000301c0c2d041c558001d41ca5044003000e5480702140c18445018841e180c100912100c000c80c080c06400e200304015421540b40901c2603181e1030447d088040060481c20b03034240102d030300030b00c0f0080c100c50341c06440300c1c10703229154400d442034544103100042c0000c10a0020409003a90380740240001100c090907192035000703911181d854101c1d142d03211045c81e0702e0b07071806004e0b05d19580261000c10081603000c1020781102c180703005000c140308145207080f10701c0d54001030482 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 835851366 1250 835850116 835850129
    0xc12030504030c020604030605060f0109080d0e0d0b180f030403021507060905070b2106010905150d021803010e2d0309060c0a0c0b0306010e040216052b0513 69
    0x840c0e95a604003103601d0003068000a5100b10001000814404aa0825806003401b100c00c82480159207005458103011171160545c03070b03004649400b841c0f03806410300100440c40a04412521245944e40030709a030003c540c0440c804031284c40c80910b80600700030444d0480e504600640c541810b54001071400a03d4030004283d1141c0001c4600070001560045000c2a40c07100031151a95110051268150050030000fa205602d515079480e03541c1840d400300d4050f02e4103843d2030001e9410203080c0540916031019503030b03081c402001200c0701c020051000f4100d07240e05441e6040007100300c004150a44400456083c3c15a02813484001d000c0160340510340300c1020000c074004030024882c0c416082d07000c1c0e07900540c0d01060110322851202000300d41c8601d040d1240c6a412f070309503203c10303075110980410b440c46400101221004400c60400d54001d210f06244c510500689800540d6054980000c1081c2a4a2030a01314410548060315408020420b807950822900b800d6030405111104c000c41e11651 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 835852616 1250 835851366 835851371
    0x60507050a0b041e0b07020d02032802120c03040e010503030702090105041a1807020106060503220c152706020a020d020f09131112030d0b04110c010b100c1203 70
    0x1401c000404c001664030501800c049054800142010604c4080444100001d40200c42044411500c0401140c1c2c01260b210a840e1410f03903064103540d0444488000c08041d403140c110280c0c11000707200050b160f400303000380c01199510f0a00502c3e0240703000c10f90102d07020740d2081c04144016610482030300d054500581300015041400204d00000903070094000d03802011040c0c1c0c105258809a1042d845180550003e0042036980d44007142c4520045402c0455281c1708003103410a090007101a500c0240035014000746c017525403e45801c1d065100d4a91004201c0700080f90940c00c0640c4001190210103403140011349103000806900d8101c0900001c2c4900c0b1100070303410440da10214032a00210010b04241e110b450301c070718945481d10114100b5500000d44840c032201c0c600d802c46d4280c580c5040103005d181001d03400310300d88000e0300862060300d42c85511180031b1402e1400c6d00010342600501d2900128140001c80c0500400800d056100010030006a18a8001c1603a091b810300170400c081c07800 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 835853866 1250 835852616 835852621
    0x5031303091a04030209390f030f0a1a01050418090b090d110106050f01030f060e13030305010b0406080c16020d0c261f0b04020a0801030c060507050a0b 67
    0xc503519546504920720203010312410325000b680c440c0c00307401134903c01c0d1143c0c0040e07203078508080b030078010110120015082101d1030107209000316501d0f1076048222203103d070030520360001d02c50164100f1142120346a14103170412812141e24041c1400c6c1c201e00040ca044a0b225040000740700d44030701d0095820717400c40030902100807005c9500240e00550410111101400d01c1e110040e06d403206818413a00007002c4100c010501003040c8908c1c4100c4030020407020400303d01400540c00f030729010100f004001d543d12000183e80b80700742c07400d610480c1e107200705890704906032030050b088981c10b8000c0c40310080d041c0400d0183d250031102c0f02d90041c0e40003454586070b40ca035030000e410b041a0742c0c00c000d40108110a009007001102e4480304256584180f80526820980264006885801d106070b03800d580070804c0344010382c11184264460654036200851480706c40c1002c02e00780c0c0d100b80c0c05c80c400580c15500400504c0b00500104c4c01030055840c00c645000d040d522001d690384489603000d000d00010001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 835855116 1250 835853866 835853873
    0x6040903050f0901120f0203061f170a0f060e1b12010306270812071e0e01030b030f030a0e011d1003090b180f0a050322030b010e01050f01030c050313 66
    0x5c0031458804580030300c01200d00301503100282d042601c03101c0c010941401213420840c3d54509107030080c2540c0d0307605010300c2504504040800c1e00070b0441140e540c1e0f112040c054402c1c40d4080e0344043d01c00c2e0148a05203081200076004041044258036240d150140320b5410654003070082d15044179000b00c0c022a0004450308000301c000c81032101c506610b00c03950074202c10814200060804580380301d5201d045a500c244003601c000b0b502030201c2503000102c000304603040713010740601d6041d100d040c036000480310341c4040480d01d00000c0380c1030301c40b1035480464840b02181d4481c02c41c41c40c00900b8079104180c107003200d90b0f24044804907a81c0314451114241d006c04102d01ca03a00c03100b131040c1c11043d10b0f001c504040141c03040460901c062044c840c01441e00160501e64000b5404505a9001004525159000d00d607c09583c0342c007082720826039031190001000c210315081c1d4034080c202d09103d4800320b5141104000c4c99210803c2c9440c181344c20203801d6844581c1282c15030f0380c840915054a11600344070303c1c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 835856366 1250 835855116 835855127
    0xc090e0907080d03200703171f060e0910081c05091005120903040f030620070c0f060c0308010303030b01090513020423030a020d050c210606040903050f0901 69
    0x81110542c0e11605188500312913040d001082e0242c00d1151240d50450030200c0e14449105074003001e40807902c50100d114921140002c440e40c42900180b0703001c455000d0601001c400d0105500820005074150740044c070300c0c500901010740220040c120741c0c440b80d00d0b004035241c80e01030a1074454524046050a106090f000300200c48040c4001042d0310828103203690090b140d50000403003046600b081100096503c007000007102c1c2a507601d144035120291840c0d51b110050402c414903500c0f07240741301d426500140c40d8075014181d054420801c00c06c03032505020000403800d5407030b480002001841004080881d40207461b15054035054540812400d030310000607030300d000d801d0b071203640c01c1411035030480e9201c01c290f0302030415269180c4d442c80142044220100c0440281f10748250b06802041c43c0000500d071040b082541107220b035054032002c3d50b007800014800740518502605440601904209400050147c0e641c031083c00c0368100014402510010094056051011a9071800140f44940d5a0088 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 835857616 1250 835856366 835856369
    0x2040f0c093c08010c0207050609040c051303230105040206160204091401020408010c021204050d02180406050406060905090717100905151012080a17090604150c090e0907 75
    0x2c0e54080741040c0030185104801c0070b42d10a054807546030465461071940f0103d1b80200b1900c0c01080c250800071140100002451040da085007880010420100b003040190207000003117005901d45502c036031421000e810281000d1020105507450b180c01c020060b902d26081d2200d000c07449114112a50b05480400c00801c1581805880810f10b1304a8004540c1c054004000b95464007000b0300c15a001614203980d2140400e200402d908802c0c00148001e04000d546070118600042c0000420303161140b0500c1d0300d200503242642c00300d8640041100780001c03805010000c05110004011900c1c1101e0125200c50580c020081c009125003200b2003102d00c20400c0c5071110744550f004001e51241407600c2513940300e60a02d04042442d103a000604141150a504422102041ca5500e003501d00369969410b950b12032400c8200307012488580f9140350703034103241c3c09100d11400780003003005007058107010904244d54204103141c1c9080046242e59180e1155898084070100d04208407075031201c030000f0f821710009 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 835858866 1250 835857616 835857689
    0x10c081021080c0606210703080d140103031e090e06040e0c180a0c110604080c0a0804171b220905191203050c0f03130c0602010902040f0c09 62
    0x10920f00f0841c44082005401204100c030900181100070110200d01c0042044110306508001c3c400c03c08249000010201049107600014440403004030055031017000303030801d0300090000c10380720248500352042041100c0540c108000900c0c5050441e824400c8010001c0f030060b9110340c4152101c41c0100145021045c004000180c0c404d0b86030903508a036503044420051071402c11082c4855140604202c8601c0c00080000c0c1c05180e03201d4882120551142095158a1144111004c086104400500007410100311815005c400d1003000c189022800045542c0038030300b41c000700031140c2e148a0114030741c0c00009001d2892545120080d00204030b404030251490052003010b80d4034100d400160706c00c0e940301c0d140340c51184035202401c60450360210b40c004107007001002001510400380b8042c42c0e114909910044004c1303010756078401004101d900c03040240c0e45428486046190900030020503042d50342c6e04128034811035600500140d941c0c07080c96044d07100525201d0550503c49111409c0b5841c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 835860116 1250 835858866 835858883
    0x80636072c0f0402030d05030709080601060f0e0901062115030804240f03090212120d060b130302221a100201090b01060f0c0b130203010c081021 64
    0x64000e404035268641c4200e4941640c1c4000080444450760325142c01150040e000300300d403180e00c08082d01e40d0b91000c0c1000c1e003400303485240002d0781c8000700540d5010780749076900c01c04516030300c1038060721100c0400d28a82c4140303d01001070044a5229030004048411001c80d00c00c00703112503401d50010111100765022881e012031001c4244002000103008881413010141c0481460101055050324902c1c00813001031190602c0034140c510079003202c21070900061035a22800c60490300c1a00d4002d400d070442c52180408980c402e40411f4a1041c0c80080032348002c45807400142c0d000e44403004d00d45000007071054841541ca0700301031201072008c8a1341c2c01421402c00c1030b40c0c400c1c030007401340c2180749010610884035000c441014902c180210105176038841c4800c0d94036403d040c01038807413558050440003013120011403407001c60400c3d482607000b910204401c00691070940140342c292145020a14140030034a4184600d40a402903000100c442d40390b0820310341c403854100001c100310842d001410b19103 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 835861366 1250 835860116 835860149
    0x29030a020c070305012003040b010e100801090c06020705060901050d0c18080709060f120f03030f0221100f0e070917030a09050a12060207051e0708063607 68
    0x11301540104100403031242203804610003c0f060507502e1000301c40041c410310f00f0b40d0040111a051a280c0c40d004803a0040403454992070701c08007800c40e040c900003600c0c0c92040402c03c010030b507010301061014003c1036036050300d05022440007810910074840107410702d943d0b404004440b00d201ea0885048428009120031100750b0700c5020907680e070454001c1c1c0a000d8030b08100002e00e1111084640c086425200d07ea070f0b0b046907030703807101c00da01e03c407480065080c19111800c0c00305081c1c5074402001c011103020350724048404000507003900241c0c0104042004103015005011119100e4460800c542d251100000c05540d440f104407201c20f03503584201c01d00342075600e019101003c00f03c003402c441440e40d07450070503ca90792410001c031000b9502c140c0700507812030003505010802e43e40051602e60700800c21503544d0118084006401440c01483c010f05820100051003054001e000c0c564002000c540c28440380310702540304000c501007000c0b40342da1410401d42c041c0c9445006202e01e030010300d09007000c0b680c0d48 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 835862616 1250 835861366 835861373
    0x240307050a0f031a0106090303030f1e0c0e0d0c050907180f0503100b0f0103110702030706030506100801140907122406021b06090a0b030a140129030a020c0703 70
    0x41d040c00111684c0c0c030480c5601043d4120f02c0c2ea150304071034803540d80300b58503461610198001d01c06101c691024075120094000c140803034114030341e0b001100c01d500040031510520014004803020882c2403040c81c0a1003008003260001a004044d607030120b42c5c46c0380030b40b1095800c0e80c152075040d10480080b0440c2c00d000a59500129500086400943c00d45100f420014031400466041d178034003580c4007144112040303a95100358800f2111220401c10315140040700d8001903c2c00800352700c110300194444e01003100300c1c1001d0301659480e007071074141440c01c0d5043c50240700702c00b502d400002e802a0608000a56024451304006180000c11f00d4104102e404507448013005200003d40b6001c500c505502c0010917030f10001d010084089a0001190300e0b0364240c0c20000f9952046a0207540540484400309586c039a00e001140140340c2e408001548207101921b40078000310503848100800c200c1e49020000304400c83d000904220300c0403c1554946d550640390b0000d01070058000d13043d10a006011041 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 835863866 1250 835862616 835862639
    0x110f030a1403240102121c0b09100b1e0a03050105240d0b04060b030a050a06170c0d0203010230090d0c08160204230609240307050a 58
    0x940d00d03038800d1000800140300031910700c02920380c0c1540e9035210306010703110b80d4414141e44100b8014030542d113408820b1021109035404c00162100d600c512954040c44003105486006e20301c2d4001c0c0d415a000e40780c000d8440040c00214071a82c01005400914503c0d00c0c40591090021205000140c503246c08007908000c1c0200400d020700c1d400b4806c0041c10008100e030321001507202388003842c503681c0360150811480010386001c03c0c0396034101c0d844a501040d81800c030006941b140380822700c00100d5141c6641d880090310000e44c00329260991054040b81500008601103800342810340d100030b100000747c0b02181c024411440f1902851421084100c01030410240a40840d0658001d10030540c561944084d01c1b0807601c40c2c04c50119180c160b061780017482202c00f03001803204010b14500180d200d500402c081d50200d001c084000c1404d9807402c5440b1038606195500468240d411143c2ca151004100842252003141c0842c41c05040f060801550b50810551015100203401c480c4400e942d001c60265 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 835865116 1250 835863866 835863877
    0xb0301030803100b030c070618020d0b1b0906040e1306021803101a0d062d140f0a0e0705031213080d02210c1b030d09050d0b07110f03 59
    0x4841280c0000040564080c8150b90085159280591501c2e00308e58580c80100517404041c00840030882001c00540d540d00c0031007080c140603c01c040042d1400080103d0201075401c12600380c05e0f005e03c01e45005469041c2030f00e0030b80d140300c0040c1c0d20301d440f40c694007a0400c01844004181c1c030300006410022b04500240300c1c03220b000c203804440001c9032040400c01a07802c502c0c07840141c5869407003002c985141c1505035000c124062800010420003003d036000360070001d110181c0001440300f01003003030b0840134450b405249020741141221030500201c026140780b409807880411a80722100014905001d200e120000c00b402000c95001305814141c50485800c0360301d814045020140f40019401000b1510390782c80402c95001d0301c000c0c1c5000c0b03460032003800c1d0282002070150042c02907440c030314400c11685a680d403003001030065010381281054074015001042204015941c0010809500d500118040456000c1e07000500c0e0303960408101c60440008807882298824070400c0302d0174a901100906 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 835866366 1250 835865116 835865131
    0x30203130e0405031917100e4206040e010306050115080a0c05120f06030d090b0304020f010c02090420010e100f020c030f010e0f0a2301060b0301030803 67
    0x180342640c0e894824212050840e07000d82075810401000300703072009a1a0004c203198240c2400c1c03404403212151040c115000726252141c001c480d140a1026494000070180d0024020318802c0031070440040110303c0d01c098194a062041441c0c842d901e0200b04110700d601449005490161210b66641200a07880c40a00c81564031515000002c13848224007102c0c00307403c07801c50329051010b8071070007503034001821882c410710100901401407151700e81c9038008281c01080c0d00c4c51200c00c0c504196041604204603280c0d2403051148220041210300b206c0c1003603070390150f01224911410b122800050b20060b114000c001c1d4020f0100042104001e10042410101c07150a03c0c800415080380740155500c1511000c4079a200c130042a100000d2480b4049075142054180305a0b1784950b60400031078076000100700c020005075101c40301c101240c002080080300f01c0040310014000c240071174444d140c1000408480048d066618440c1304c8820398250400f100601c00341c1041c0b03540303685d60f08100c40c154000f501d926 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 835867616 1250 835866366 835866397
    0x15070606090c020c0a0308030c040f06020a0204110c0a0f050a051f06050f01080a020706090605160318020105072009011202030606010906090902090f04240e040c090f09050109030203 80
    0x515040c40060301c1301400c0380142010b03030000e0840e10b0f102540c0e0001400011305100800020072004182c0d200c3c8130081c125500281081d1405104101c03d0f01d14142c480c541440e8240494608404000740e07842c030150308888000e0300b286d01760804030700f132802150010b0080c3c400c8002d51450711003000d08071417484603100c2d42005619158030421045560b41003400d40080c100e24041759000041c0c1c2e000385141d42c450140000c038450150350305130940b0402c456901703001800031103000d030b03494141c000d01d500b0b00c610800040c101049076001030032a02503ea405046032860314218a2039142c90b04403440e50110080c035000741076a60703001900d451003908130102e019000d090040f41d41940503064200a0341c003d620788030100740c1800c116100a400218046074800c0001000180c00e8a03284241001501031401c00d081c580e00886103088442c909a21241c80217614000304000300381d004081c6016078143d55000f00c2d0907494106642c0203043c0014002c4d002c4e5292190300000c00d50000008c296010114055 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 835868866 1250 835867616 835867631
    0x3011410050a0e12010b0409050c1305010f2616061403060f1c061e06050109031502090a03050613060c11032d191d0f010e1507060609 59
    0x1c64a40c0078445400c004240000d0340e264a03403520f21541c2600c42036102c000200350400c100080c05a440c1710780151565002a0006181ea042101c0c1c0501800e001120038000740d4034081100300d80f650f10744551061035420448601c0e0744040c0401c42020303548048211800c10380e4546100e243c44455202d04001309403559652040443c1e00380071b4a109040003007860040c05000c10600075408903015481c40c40c035034112a03403400503125100714800321507106081c141c00c00c02103000400711246034001505120043c80c04000003050310190800031b0340400390158442d80b00d00c01240040b0665000101140114020419505445100d01915900410052141d00e02c0b03031000351041030004400c0e40170703600108841021201807803c2c91280000b01ea030000607045111000d14481d8114402d482d42460200c000c031042ea80d07100400d070442c00d141e4a1021851030403900062640d2030403100e96030501403a440b03405180e550301005200180002040566031340860302e4540020881402840a5245000d61 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 835870116 1250 835868866 835868899
    0x30c13140c09040f06050d030f02030c0706031b020601080a240507080727230d031806141c0e0303070c0506090c0303030117190b01150816030c020a0503030114 70
    0xa010440b040501f031501041480d480c11258008428806c0303040d44410001034502c650208100c60041513569000201c0c0000340c20302d13074002c142c0f640340e41045500a0005203c0c0321030200d143c0c69000d51000206440b40014104418080c804034000c9030300030b150808001c216034202000600c42c42c1c9660b40c050761000c00040f100c40020389207001e110344d05082201446404809030000024140c200c1e255020b07107030301000240300c3c240700150031400034501c01513580001490726881005800c071800c180b0a02aa0054042410300070000721010084100b81c000070105410750041c0780c0c6031000c3c42641d640749402c07900540743c480e145104a50500c20a400104404004a100d15412100601440c43c0d64a00401c8407243e500c0d403070441c001ca0240e1180040784494480d0002000da120700210102585020304459031003807040c2c1c820341440920000c0008019802440d40c20b6404a400c0000d840c0c090392070100d25241c4024001881480300000105207035294a818603101c0c0383c00c07220001010540d11 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 835871366 1250 835870116 835870121
    0x120c2412050906011202040b190501020d0905060306040c0c0b070509130b090a051803160b1303020c011b0b01090e0c10090e0601050c0d1205010b09030c13140c09040f 73
    0x300c4500b8180c010400610112811500c1c01204138001080480c5501109000400888c01105110040f15500c10204250350b01030100100c050440c7c00d1a407803007403401c0041a140d110041c0014403440e9a459040d510a0003034a400e040690820502c415500e02490003034074a9000740412031141001e0f6246290b00721450040d80407030a405428056591204e0a86070090031000d0104512a0500010100031880400107082007004000350001501d0203400c0c030798801500a0702503007501c5605045034000c40e030000341c280b021110a10b031000d81c041da5940b400c841d03e040707000000c2500c480e80d40001042e450300d4201c136128240c15025030f079031030242030100110460070b41941808109800b20406c00f0b9801d122480e5440441818494580b070000500581051422000782d0f0220f2482c044000d1260309511425014105a094481c94802c014001030356500304e90382e0040c480c0c0c4c40c03003d6003a646001342d00040e40e1007400710f41105090410340c0520795682c204801403030148d032802407065015030850 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 835872616 1250 835871366 835871371
    0x90607050a1119021306050a05240a020d1d03190309090c030b030c0f090c090d08030a0906060503030f0f1b0f1f060506030601030902010e090a1515020304120c241205 73
    0x50100b4002481c1005110400391301d00c1c8444c100c0c05e00d4ae10240300a12259000f8082e1302a598040c1016044002006d0720146900300b1085940ca03501011084540b4000f400104104280d2030003981d071b4003540340c201c83e4155260403042015041c4802e821029806400100d03075007104a060710704241c1c0006c14402281d070109100b543c00340101380846c1070b0b1080c41d8001c03c14038001505441d603182140e11340c680341ba88241e5600660a0341c501600051000ca0b11841002c3c20084028520b085032031103c40c802c9010b61b480341c0603000c60004605400f4000140c84103510445403041d2895140040a80ba4440400c0782802d903040305100c400003c0c10748548200d40071f030351008140c1411034595500460091a0750803049040c0311300840318584c1c50345c601c21070510078854503201213004075051500b001510b034258054607c825440200085083c1c000c0b05a40030781d40c040031000301a031414240700003840710701d13444428040d840d00c000d01140b00310001210041e80301034803050540e40c100c00e030400848004 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 835873866 1250 835872616 835872619
    0x9070f0f172d01090609110301200f0a0908191a010303051801020307060f1e0218190b07080a0801060c0b041203020705150402100206090607050a111902130605 70
    0x2050441035030035800c07002c03041d4602095000000d2040c0c25a8409045421081d81038804000e0728500805030f150900800c0000164240700c0111034450700320420180c0615020791001c000e0128405041904c1030720030a0040100608594500842601c0c00001d020180d106032140307070105071803030700030f00c90800014102c9a240e40c4003880c04040442c008121640d8541141c1140001c000d0301d00030403028096241a80d4140c840010414404400001c184110b085e020504500600000104d50b210300d0709001030702d1040d1007298000130a03224140d10b020f11500201060ba0f400b1804c0820300c580e80000d03003440d2130070351142907050340c8414003560300e0404010000d0104040c2c1c8005000640c5e40148002014400d003409401d00c5101d0361110f041034141c0b503681d4ac015454400300019440c222004618031a0320b0300142203181044030002c0d4440030010a62010300c100044e010200d50311503800c01003280d49150546a8031025010001294442c030794040e40f00c1d02d00c00311142a102c146200700822030b01c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 835875116 1250 835873866 835873903
    0x405070c0803060d140d11010b01020721020607080c03030601020615130f0b040920040b0a140d0f0303140601030e03121317070308010f050a090509070f0f17 69
    0x222401000956601402d04a607075003200c0070800300058041100942400b45a2640c4d00300c0c440c1015012308544044c1240c0d4110350003800104100f0f0010345044040f520b079014a4003542006001240c0e003446041402050010001a80d2040550200c0598011103090342a290203480e0341d48d03500440881902c4481d417009146480303a107640110361202c0031031101d00c0000300380e42c11450001021541c5800040d03401c8404201d1840181e00d83d01c50720300e96804201c400300a11159000801e000b030583d4090740c109054141d074840c605540e21824551860b0340042e0a0181d05024a0020041c003040700c40c85299402e0301000c01d00960090052401c8400305100460500c0e040516285203411f0150000c1c0340c60109004c000302240344101c01c00b0315540c032241001d070b88025034540181940e04c164044201d81c240044284130540c0c0b840b0002007121643c444c0495140c49a034089424000b0031380c09044400070144c00011a048086254001ca41000040529031204021071035240d6201c4629030300d9910 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 835876366 1250 835875116 835875121
    0x30705040f060e06190c080a021f06140603040807020619080a1b2d030509101e0f0b0a0602060a180203060105240a021f1a040e0c1804020405070c0803 66
    0x10171440320a801002c80c9440700100c492038543c16000d51000458a00680128030401900306925400f0400501a58400c00800b40381a43c1146400c40c030b84d00b0705115900001c0401c003405071032001e80c0c000705c0d0003d0505954442c8290507d0b041500d0031600c00c0490300180005072410040c2c400c0c041c0030301e00c1032000704062a80303500071199002d041400024865042521401c50100440c446003150034640300002d060500c02c0404e4a8414001606c4001ca410b100c607203420b00d07009800c4101c44201d282004110207028001e250042c00c0f034100c044d90002641d202c001000b55001a0b1540102284101001031482d0b0034bd03543c507441c01d0200041c0d0583d1001c40100850b01f0040010312003e123031103090090f00c03c42004458519403203a482c0b035005030701c40301c074015551840703d10350601c05801d04801c1107558400b010030309140403003005141c4a80c1c0d41d00010807440209005d48408a0380081c05094a124403016550850303000391000d030b0050b45800009090300340950307940c43c0312a401403400303401c56 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 835877616 1250 835876366 835876387
    0x2041415060901020709020d0608060c07030207030b0c0f0d092d0b07050c03130f060503010806070f1e0c140f030d05090c0d0f02010206100501050a030e030f030705040f060e06 77
    0x1c1e44122002070462040b0ba00000d01c004887c400f40008841000d000b042c0b403071606030424a0440007605010b00302804101010010350001804000c41c0d0f4880705500b2039035101c040543d420300940d40e11018001c400580c56130300c079800303500030030304503209041c8417411008400400c5105000002039a04140b40b0002c208041140701300040d910070164070385a850b2240700c950b01d0b82541c01c5024050701d0f00c21091000c0c0680380c6030340002c401904580c50103c0c00d5615059010399036040103020001803042003d848070100b40f051500140846000120f8000914083c4005204c90f00362842070700d15070070b06200c48200000c086840b054660720000190f0a16040508480c0140000ba000340c4992003044c07000c90b2541c5666a04c0c3c80c200f809001030100b5954a40000390410304001c01c84091134803008400d010076a00300040d41c1174680c140c0380c0001d40420100d016840d40c420300c030401c004034002108100b0f801c1e601100070401c0e10004010034000c265190815114000d1a03015594810b0080c800403040 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 835878866 1250 835877616 835877629
    0x91a250c060509010b121b0d1509020f090903041e0602030301062d030f050f04050607140f040b0c0f0712030806181503010b330d0c03020702041415 65
    0x441a0000000380720191030000806034001d8400203205900207007d030b02408070964100028014094580c841203225540d40c000c1000803546030014003507030b80c81007a419903e071000c03041030201019000e0780a9090950003643d50350843c0c419030301701b440e00306500b002044071920308008a403c80d400450039a400c2c0305081d200e0f4280550090380c0c2c000070400300c650034580c02c01c060840302280c3d00c0010340c810307501c107004080e94401000f11080c03c10180c18040002c1000030030950003180761078003611007402001c11b8000ac1c4182c0064840600f8081004104e1604440040c6504410407040b950f41c1c600c40100399454181903c174119081100001000100340541240d40c0d1250000780100090f040b40c9200b10210201960352100c0000d52000031050b5080910541b450301004840a00c00102c0030342c040d01c0508402d0560910420f035440c01c010310800c1420555010800a4400b030101d4214030354014020b400c803200981c8914101641c00001c08098190540034000a24090060b4201c40d02402030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 835880116 1250 835878866 835878871
    0xa0303110a05031306090914070318020901030b09150103110409080d0e07320f0f0a03080a170c0d0903120603060509240a0f091a250c0605 61
    0x40d40c0c01440c203400e0010320148000c044244021120f68406401c2603802000c001050300803900351450065500e00010310a4581503010841e860003042c850314070781d0a0310342020100c41c029007040c140000403040080d110021440f03848d030f000455480044204180c207001c8820322015180e88210f0654100c603040039006165014040c0400610300944175007000111024143c2178455504a901c06118040508018030240741c15401c41c06900f51046007410300c2c0c1d40d070311a0460701c01c0500300305103a403544990070074003e0500002c003803011040e640d050103112036110300300c510002614104a4030340146c9500e02c190046410301e180a00b0320f5256a0928000c0003d80307010340c1070014030342d03624003040f101e03000d0303100075521560020038a410140300c80e03890714038494000340309000098656050f4a0b2006a5641d100c2d004440128601a0f00b6500f24024100f8290281c001da04400e006868540e00c10001400b035910400c1d07011100500d240310240031070711508070703900041074002c1e9800031544540143c0d4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 835881366 1250 835880116 835880147
    0x9130b03101b0f1701090b2e030b04060b04080d0e06041d0402010309050f0d020c0a0b070305070c0306090303090b2a0c030c011503020111011a040504061e050603070609050a0303 78
    0x100380d0007100056501c06102680007000c815141c0c0c6038030740d0a080030070705190010040b4601c003d08c9008a9801c40003030a10540311002c01d0b59881e280c101507a070355007040e8002c04410503459501d035160700000b40c8801c000b05844020074101c1c2c140d101142060401c4030101e800c0c4005072520703101303015400340030300340081c009a040580700c0c850f4401080051000302494500e400080081c210b4411003c1e040448008440b0301c600b0304808104a502d5001301160b160641c1031405c42d640b807009281803508544070b03070000350885240c40d400ca800c00d601070303000800300d500a0024600f1907a036003c101c02d500a404140f0703055000c810b0300a1400400301d0340a4814001502c0079070782003400380311000d030854451500c0b100045055240820a658110441980108058000f0f00215002d4a1483c8007180d40004041c0a039640c1e40025060007903680c800c941d054a80c41d03e0f5110301100c0c442c4100a0441a501e041c403034018a0070000383d007401802c4d14000c0f1240540f120444a16548003070340c030320704200c0745c44 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 835882616 1250 835881366 835881377
    0x10090e061c2a06020304030506180a060203040b040b0a0b0a0303030c0e1210051b071203020702040c0e131a04022b020706050c0327010209130b03101b0f 67
    0x440000b118800c02e0b02e00c1c400e251118840905507440b803510008a81c0e807107203080d0b40003000140b001c00e1001c5189507200c41080d40c4000455102c25a40d031400717400c0b08000c0d0560340301109003c10003d030a00180e0042d802000f9241c101c1d160b96101f00221040543d002d513200501e00e8080000901a4121010b000a01c0c2465520f013404000403803940c1c000790304500c1040e00000d0720250142064410340d40c00c40e16210703203040da80d03035480703c00c08070381c490054050000e09120071006400303803280d01103503000c560140062201d52200c1d100907200c0c2400d0114030b4400d2101031000b401c484110311868810b56180000000081031880501009511405020a843c8100001a4450450f20000840500c00c1c40c1c0c00580e181764a041041c21140080c01030f42214808005100540c40342c0c02200b61080c2e54040c0003e84a180c410301c043c0203200d1050040d0300010400403013840c1c41c1c0550702c07060311184c086c1c050344d591040220700003048840e04011224814040032075030f602240301d208586100c40450801 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 835883866 1250 835882616 835882669
    0x10e06030a11090d0b06130b010206190f290102010c0203090d0204090b0108060f10032a09060f05120c011e020114040f1202070501050d0f02041706040210090e06 71
    0x4102d207101090800c0d185098a03005109840c10301c200030447c0504100c80c108804901c59000075261017000d0300900c1c081e000243c00c600071302090350013113840c01907840f410064032910595103034200104d80c14100000e800ca4420340c02950060140002c0c8100c0e59000d90700c0c02c20010300300a41044039103000c0ea04aa40d500714180054094030106010308141c8006110f545802c000e0700424500c02403151103c070301c0001c0104006200c4440a044245081c81c0304107008038408010920040300d540303c3d03d411420100300003910303840030314550240c0d103080c0c42c89500b010909038559901c400782c440613400100c0348541c10040d01e01d600381030600141103100116890784a142c444c0c850307810940b420340c2c0681d444052801040030320500b41d030010145001a000c1140340174000b80060042c01c80c40c4500740c0e21035640e54031441c02941110081e280d64100c03d018903403164011540c5550842d8120f004641d8240011031040c0103013a03041c1142c214860403459030740c40c0c909006543e450201920010b0340d444c8003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 835885116 1250 835883866 835883869
    0xf0f1e1b0309030c1502030304030c05010905011b020706020316352812020c150903070501063204061805091e061302030c0a0f080606010e06030a1109 66
    0x4980c0344901030395500400508500b032154241c0c010398080d42207404c1040c0444800c076000b100707999000350541440840129a82812800f4100c5d028004000303518180100c1d0480d1600040c404440c0c035158202c5039201e4803003e00340c1c4d40c1e209e042d5a0104c6002d000c0085800914200d25454449a42c103550030200c40381001054089214100901c403014000b1070940c036010401c00074407040f5403044000f86003020141001414054900e0000440d184d00081e850010072420803054540c0110350304080e11514110022948a80080038119125420244c0c0007401900c05001a10105800020060103845041c580c0300c0144440040f550000e4507040001031030200002224501c0c00f1440d4042618941f003404c05040081e1072000340c89002e01700c4410443c1141c00200c45034030202955a42d0f40201441c00001d142c20010440d050340b24100c068041861201403e800c011100c80c402150380540700d460064407a180a8441c0b140c0000003400000c0f0484400c0d08000458410700c00101e282aa1200 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 835886366 1250 835885116 835885157
    0x190212060903030103031b080a14090d05030c06090105010e0a020c010f11190206010b0d0e031b0714010206160806010905040e0106180509340906060f0f1e 68
    0x6458030507581010004009158012100b07920102d10382001e980300c4461035031440554040c0450441c10030440000402c9403480c000116041e05000030100e150080d91460065520782c00001a070f6110302039800441d078050300500415040e140990888126642c45800682c000e420145442200f5074aa000c40c074000340945c894802e07a401c2c51701d940341d9180078000884209184000d5080c1c110741c0104c00400001d54828240c0d0200b055140c404610080c50061407480c41c01040f88400c1d290000c103001c207c0da181c001800b03004070303440e40b411807030034295120059885103400c440070748200d81550110114144030340300c4d03e40c0c00300050502c1c200c11511003000c24200c1c0c40b80300110134161b41d6554180b10600d4055011824031288420500c1f25142500c840ea0321010886881d540803100410348000440e03425002010000c50054007902c410f0743e903140d200140503144218804203442001000d03166118601d1100040038548450f242e250f81c00c420080c016078460000380402a4030300e03402e5480c01c17000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 835887616 1250 835886366 835886371
    0x2120c0a0e0105010201050711030a03021c0609090507060c0b18010905120c0f0703170f04030b1518070c1202032a07060c0b0f18010507030905100e19021206 69
    0x24040e1078166040500190840300e0140c000c106100d906208518002e40001c00c88100280e50b05d0b0244e101c10f40d08504540c10350707401d202010860b04061011802041d154482c0d031780c840c015002c58498958a0754195442000210050101c00c04040002d05220485090b4a0310b21078070703400000c03600c110381c8886060460211100300001000110070740d028000704400803a0f040f411025110301c40c915074031642050040c480c0c4211404000c0756148141d60f9030f60aa50042d900304905044c40e107440381680700c0c8072201d1100303070344110490300074107841c0380e911840c0030721035149030b282da0340c0d10840c0f511007240541d40c907081c10007188010031940c4000e020002400c1e1000e03210f21505040d038103444010307a0a107923154002c80200840015040d0110740c044070b0583d005407100130405032035103681c003061880420b0080085820342c2420140b1240f42e1b8550b12042103503000d00199100d9054004030035080d295489050001907000d50275100d0754000a00b0081d04080c030081030b812070249005001d50821508 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 835888866 1250 835887616 835887629
    0xc0d0f060504120306060e03032a030a0f0228060b03011107030801090e0d050d0509010f060e090d0e0312031f120c091b0804050f0f0a02011e090302120c0a 68
    0xa44141c0f5102c1074142c001c403070290455046c11889901030303101107556070142900e0042000740a000500035280700c50b1f8602080341c0800c060b2562200c1c441009400782c08030008000061040d52031011030b164030740e8150200b00390200402c00711012951182e20181080f603441075495581c4200740441020504002d2000034841e407100b21140d8500324030301007100c1080903520f480c0d401c482d200b0902541e014085440005c0c0501000850742c039105003150041100d10051200c0c1481c024011030032013030f03100c506072080003d403045408000000320121442d0100302442c13a01b43d400400010032103240d5034081d55000700018502d510704030001c03042c0045494540e01800b01c002003071003414140020500c448014205010b401d1101041d40810f91b14001c248000b54820000b8100209040100038080a028143d44804607240004e041485d1350301c075510000c0032408142d0407001d00304849040c03880c1000e20041620360301a40382c650307000d011001041c00c118042c0da00030908500100e9440c01c03040300141c401c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 835890116 1250 835888866 835888883
    0x15090e0a0e100902032805060f1602010605130c0203070602030f011503091a0603030d14061207050307051009081603060e0604020a052202030a0f0c110c0d0f060504 72
    0x2480e03880a414194036203020401c10b400c040086000d07850000d50a907800302c100a0880b40d1141e9900400a460546c02004055000318000c1c0b028189003010171900503011440c0f955901101d1b80c100380d01f00c5031188a0141c00c032502c8144030104544550000300001f01070300581c1d1038000c041d9501c800320382c8119052050300c100c0e04018401e1608c004220341c008040fa0804100811854940c8590f12280e07658a590044186000a03c41d0300c081c4103494110b50040801d01031102e03490010b2035107000403500140100310000c125021202c1c0080d07080c04480c005005048124140414458003c804010035010b12500340d0001036075480c200050b4000044004100c14814207510700f4400791880c038400103040368400c0c4284005607407005210701c2141c00071107a41c6a42404a0222541e5038401111003180703500c040708003c1048660b4002d41821181c0d4401080742409200741a02c40059088203a03a499020820000c454181880904115401610700a102c072141d43e484405881c01140e040f500340700b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 835891366 1250 835890116 835890131
    0x3020112200c071a070b04080408011a041104030b0c0d0204150203090f010c0809120f0a0c03050f070305030a0c020616060f050c0306100309020d0b01082b0915090e0a 73
    0x3e010035000381c2501811080500000c00201115000e464005407034505040e0100c2c01300404201110010408074009101942d08440106c3c28052888011802a4203090004e0b0224035074004440590360301c80d990040507242c2c00400c00c25500090403402c00c81d0740c200b0001ca01503040440c03c1e1a8005198000e5540d40d0301d038002d04c081c607982c98442c03d040c0100e203151140010765140590741d050302d055519050100301c0d10442d03864014412020259401050116000d1212200304401904d0240c4201c0303101154120380207949910f240b1000e031058009014501c0c09910541c0c0142d1121300060055040c5441c00c10070720f400e2040e040c011901c4595a098055403c01d0500a403684069246002e9003545050800301d9200c5a0818802c0c00b01940c0305144811950346801c0030341102c3e0000726001c202c5da128272006507207141080c80395000848005100702400c0c40703600407003180009030340c40c101e440e4500f01c00c0340c5920000d08204414054000000f00301d050004900f41d00c9048480d40c0400c405 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 835892616 1250 835891366 835891387
    0x705010c08010302062d1c0b03030a05030f040c0803040f0e1509013f050f0303011d2502030307090b130303050912010204060215150a0302011220 64
    0x12080c240a100500021000400160380c0b08000e841c0414481c0a0360242c0c010043c0c00100f82d09640d034070b9112188404039001c681c05e800038078900c43c0076801d0031041110088600030982e4a0203075000410020781d041000542d43e00000ca507498010b8030a0481ca40000d4454800714110f40040d0403500c01d0001c2407004020b8481c00f80a4180c10000b08961000d403080303002d0114002200c1402070b00021000042c218408007003810032216490f041400d11104010080083c4000d200b2481e0140d07141d04c0b0304020a0b000d0323607010046904803100480c822103468428244010410350060885500800c0e6410032020510040001a9161481c2d409540c2e680b4242c0d0001c2d0020b10650007805081e1024050409410084002c0509407901400e01b141c40303440d510009400303d0103051f40d46005e035001040014009800003032880c0485084007114005a88078001d6402008000b035143e41d10082500f07040001d0350180c075881001202c0c0781d0010a05040b0503110050455010981d0452540e0028500008 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 835893866 1250 835892616 835892621
    0x2105030a14040b040803131502070c0501090e0609040312140108190809060f07050a111c030210050711250b040e07030b0a05040609021305060a05300903070501 70
    0x41840c4100750020906081d1a0015403000060004164003000004103031000340c50040c200107241d0103241459403442d62080200070350400341044511450511002c51558050764041c0151240369208021654442f020848884000b80041d0b080c4a0000d46900c0210440d00403c0301c88260414680c0f015407600041c0c0b858082f0500740c25114921840c00b6a0003c2c07800c008581c0121000c0b40c99540b0342d104240310380c0480c4580c1200400c00e1056000c0b0004108483e464074101e0501154164000e40c42c2c107041c2d003800c903840d000040050304461096102c031405c0303510940c0c0200b140e01e0140c034200988407144d8507000b0028080149241e5400318204441403034807246010b070a03980d880c24140b61a100b0846c00e9024082c00d80001d141e10b81514614036200c0100e99401020b0042060001c10f42e11251540254400d0340e4085004034904c01c0400c981c1001c2048515000e00ca43e1801c0c43c01206038080c1803e0b42d0804048035022030038847c1400103e1034000030a0280007124060340c3e45102c0b51401e20308 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 835895116 1250 835893866 835893881
    0x50706020712080a0c09050f030f0a031107080d121a03060a0b0f0a05010903081608040b09010e01110601090b030a171b07030c0b0f270315060f06072105030a 69
    0x2070351360810542518143d400a1064201c1c4e00c10b8030107804040744d140010b414403c48000d080e42512410380c03d9024107610603800406a90f000c0309540c02141c88201e1503072286100800d5001088554080b88421142ca074880305515100d21000e400c60319034030b00081e0034200207951421040d82c4078140d881c4649481d20380c94042610883c0c400a88074a00300010340440c40b04d21024042c01004918a401000504038000350323190701401290b510b0b9158551120250006508940000c040711540407071540036603c401040d01024000313200907817908007480068417441c4820f540502030102e120b00001c69031389041d940d40c2802a1100c0e01c3e03221500200b003880204110310140b03540f00c10700c200301161045d0101003e89a51200e800d0340d507814891404954481c504407500b40c0c151000ba409500c015100c032040302107100310140e43c0b9a4031200030b44100c001b01942c0e440d03400891814840c0c2c01d0729100004002a0384541c0d5010b0b0710411a190303040356000084190800326500104004880d5138600c2001c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 835896366 1250 835895116 835895131
    0x905151902070f0f050f0d080f070201200c030c0a080405191211060412260a020309060d062706091806052214070803031b03040305070602071208 64
    0x40c2000c0c203640354041042c070301010107003502c450002c640040c00028006c811074200b10b002110301c0042c10f001d0051622100b101d035071080c9003d0703102041c00644180580403043c101d0b108800d18000e44400000ca55501c08601d1402070300c010000c0d8030040c40240052403015005001454442d03240a0a109500d43c14101849004100b14414040c0054a0191500c05500410f1424254049030f02151040c400e90300205c910b824105040c02c10052500d1616041300103140702001940040040d81e1241d029861030342000d40c100740005500b030b041460117880350a11900020a50955409201c0405204c0b883c00c08844918000c1e441035a14035800390200905000e0400c10032940d104901c0350a41d80441001006540c0300c40119220101c030b41520304829180003210340d901003261401c0c02815041c545152458002d111002918503404000c0d6489004170481e038040c0c2a00990b844409030340300a01c210203002c014040b820203c1c0391440900031107440b4414091486800b20005011000000c01301c1c03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 835897616 1250 835896366 835896371
    0x8030a18030c0821040b06031e0a02060c0a0804180b10080c07170f0703020106151e1101020304030e0f0f011e091805060a0b0306010c1509051519 64
    0x1040042c1c0d001d5005000b09070030002958554540341010900384003003d0201d414610003000384010310043d000301c3c2d0300a44085086820580c805036511f801105440c15030220b0342c00455100000d414040003c081100039101500c0c0060490ba541400c1c5d80c00581040070400b01c0c80c0d041e86260101d40c031568100601c122104200c071000c205005200c0800140b42640680010a04c0410082e0444039123040c0c0300c0022115880307880c0918494640e400c08a0164019801c24000040d1481107015a025551050ba0b549640c0c1c0c500140c020f540800800a5030200305c84240d41720b00d100401e1000e540200d110340c0e51f010001d554601008444103d100b03907203101d0076544003032014980e0400c42855400b41c18411041c030302c1002e10019610000f140e8012103040e540214101d03d0314025911585c481d150440e03481290b640c0303079810b8401501080324081d02240780824800c001c100c0b01c5000110807003801c40046013480c0960784a40c00d00604074004a00392001400380503e20a141110340f9415401c1c1e5404c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 835898866 1250 835897616 835897661
    0x30909040b04050d1d120c030a03050315180a09051c02030405040e0303250e0d0c051002030f0304030c06270302070801021303060c170906160305070c020f01020705040908030a 77
    0x100f01d00117a0703007002c18410202c594155001e04000d020944080d04c0040c290b0f584d0b0080780c02d001d0501e80c001c031030040045881d290200031610344141d5008a03200000c8131450560794406002000b4122070b03d00341c61610a103030350344e0100c0c0c1d03001350320542d01c00a03640510345403881c0c9018032045c0d07402405641d4032a0010b004100c00861070300101c404c56805a040c44c0c0c04a0b11101059804e06039440803107420004e800818001d0205030843c100c101c0d01c1c00e4a000c03200c1c0307840243c1240c6900a656400d50030202c01c2022602003445504401e8150b030044a0001d12161400c849006802d07404409281c13242407841c0007007d150301403141c1b4004107003060003035160040480341504640260301006200c295910900b6001910900002c1d105000d400e41c440441e06104d0441e0791b60308030132580260802c42c00c0442c1200b091080c045d0501801c001d4464008080c1c80d6070130022039449035100300381148140c210008042c0d8541c011501e02d030b070260308151f54a06001c0c060b07400b55040d150010850740c0d0070441 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 835900116 1250 835898866 835898897
    0x30e030f04140f0d021504150504260d031a04020c060406240512030909010605070b01050415030f0f1b0f0819080309030403061b30020c030909040b04050d 68
    0x710004c059045031245402c200320450408580101d401890144140d40702486200d5003140c002e0003919082100d140c120b001c204003c00c1c1d00340d020b003442d03c5d03143c02c544000b620080c000d400c01e151203441c06003c2000304100c0030104003240c200014104640d4820003d01c0148031b940c1c4070303200018000e40708042458138090341500e8412550300c100c0e0301a030503581600d1140c600520030b9840c606c1009022240650b560080180103800600c41902e40b090f080000144078645445442e84050340d0b0302440ca80d1350701c3c603140c00107040c0c10140107480c880c001000801c0003075410394543d5409070b840d05201d0b0605040581480c5050019004040c450340304139000c029410340e0394034001503c0e5100c090680c0c3c80c0d840b00c0e0441d085018641c0028946800c24080f0044d400780b0941140c000c04081c0d40f1408489244d07240400800301135002442d000741c0316000d0300030b56421034004020040c810340480c1d29054000e4089111035000725070942c0e44030b90900520081000600101c803c607030143c9440502d400c840032 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 835901366 1250 835900116 835900129
    0x30a030905120f0717060705040f0b160c0b030901062102120a080a03021b0c010c08090d0812011a181c0501020304050706020607031a0d0201030e030f04140f 69
    0x1014400c0005005044904008008010201000030305884110381c0d10034030341d5102d0070300245c040210300800000a1226110702d050f6012201c1014440510525054155003640c1c801100c04410401e410041c2c4082041404103000070048800c02c00e13920f2401e400050301b150042e4000e0445444c94000c0840d0160596481684d4190100c0b2410745418030350101924084408a000744000404150310300401e4140d409000007002202080c0f1094140013401512100341000c55808945500580000700e10740f03001418051601801e0503025240f035840342002600801c0c4800c18101d041390050046c01800704043c43c10b104801c80c040e0030306a6400e0a40f481d0342807003031118007030380368442240c5000000711419140242c001c4001c650300d080500b42103861b005180200000f41c407404010408451003032040420b220a510074408110561808210380f4805403039041c1d040503207804024121550500041c001244812001d954070f038a4054a6a00c0461a890f401e124554826400c0059115035 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 835902616 1250 835901366 835901369
    0x1020706021203060f031002071a07020d30020904061d040f060209060d050612120a03021c0e0a0303050615030708190e15090a051507091d0f06030a0309 67
    0x115406483e40d50703a10110701680125041c403a89482410b0b01c1d0007810405a000744182405100310100142040700f01c200c0400c0191170040c01688901c03246078100b4811825110381d4071000800b58030031000c4002c40f40405041da0f020a4505500051041300ba203024801c090080c01e10541084c4a005140091580e203903008101806512405420340104103a80d0b04845202100424054480c00040f0038000244000c85219004491044004113810310000703511000313020f4211030610b001c4001070100d01070740006400c903000c2c04e105607408004003c0ca0094407850702e50b0340010701000849040080654002030682402988401d503018001844030085a03401a203030701346245d540c0c5404180d0807005080160040c0820f20703180d10079001071340200d01c0344140c00d21001c006016407a540341454031000070000c010f02c10f501c4541101a0500c50788804c540c0850f15052505e0003071703501c2104451203003107a020101441c85050400850481c00401c10f0b401c9031069000307188805c0c107a035000c4c041850a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 835903866 1250 835902616 835902643
    0x90e1b03070c03020a06021204060b0a05031e01060807150f0c0201020316030e0d0c0510080c070201110703050111091f080c0f070c1401031b0c020108061810050f0102070602 76
    0x40c10340b02c005240c02080070302400d44c1d110314115074801d0543d200341840c3c0d0055030304460042c100302c088902403601241e80e1703080e510003d0141085403000700c42400e4008824200b602107540300c031800a603420b42405140c2c001c01c1405840c0c070444000000040c0403986e00c507a48424018001102401f45c0d80c00802e4a4580e6400229114444494101580d450794603840e0a54461010405c2c0010003d0341608001180c1003076035502c1c840f00108070103541c08202110002001f040510004001d50701c20700e654030a980f281c00581e00c1494032500e41c82c0c2580c0d8400110713801c205000400f0021420320290704900342031511941810784440e03800003014100c0103020b10400c400080382c0c10301d01e0720001c811036402c103a100c00d41f116401e907108410408441c058a2690219150101c10807100d02d4540c0d220100500c40c2e03548084a00d060b60055a02e82805420150469541c000c501d49140060702c81e01e00510307240790451400c5203032208103d0000c0740c001c125070464212400070881550009410140b2105 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 835905116 1250 835903866 835903877
    0xf0b100b04090507140a171302060d0507030219021605100512090705030d021c03020403080313061d160501050406050d05180a080301061103030103151a10090e1b0307 73
    0x1c0d40d031001c0f540d02e03c0701c5c0c08220403501c0010b020000543c000c03034907040d015880700101e00c00b5983c181a284040b640643c1c0a074015130104409800c00005910440e80712645050041c240318603083c0c04d40b40602d00b1400c101c0076a02c85011030042d6402e00180c80000c0c501111040226028400300800a00645103010520070340000032501620082c0a20000361201904a8281110141000707668058454040f03d04002001200c001e0302d1180c001c6a0640e81c02440e401e15544501161075a0605d40681c03c1c1e2b0300c0d0703945220030448100d0707001c02c44100300351020080c0040000242e0034a00f40055901c12418800100000c2004507006810780c6c003410311b2040002519903440762030f110448403030300f0603212078000c1d00121001c0007442800b450595004d0b135240364032910390090480e520301c000c0c040609020060898002030880725045200190816916017040300c080502060fa101c5804000300c0100d1040b92003801048030b080c0380707198413803513046145911610b508180301540c070014001104106 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 835906366 1250 835905116 835905121
    0x304030c0308070e0333010305030a080403051c0506040506030a0c2606010905190b010806040203130204060303020f0f150408090d0c0b09040e0307030e090a06050402070f0b100b040905 81
    0xd000c3c501c0032100740400b509940c0c55580031b0b441b890f181c0700c900303403040d0f0200310324641050120402c4d0344c2c45060725480f000640c50810080341c00d903030110008008804122080281540a4010180c0210078059140002c60942001020002680c500070700482c020f42c40324400c480414040d02041044555000f803640c541004081281b500d4501c1040440312881000c0c00054540820b0b404079100c0d80050303100c0e14402405940400541ea444c4482900103079292010070300901c0c15038000d60704480e007121080f006d500b4a50105090b142c1580c01500136801580101c8100b800c03c0c084900032203108405400380740754400540e1104180980080c005c0d11011481c81a2510f0340e0200c02105900000c1481080e43d5589180fa0b0301da10920950340a1424440441200c2c9400801c0d00e03501a0305441c2c099401e01e804d03051050f0900c0081200c01034503211b110010ba01d880c3d80c80202500f42c003502400034103400c5810200840301000c0c129000e6050030801c1000301400c0b01c0195019603c99980106158 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 835907616 1250 835906366 835906381
    0xe06091801110309030306030118051b010909360503030c0703020307021804050d0327020f1c1b03330507110607080105010c0f02040222090e030304030c0308 69
    0x42c40000000b030000e900c00024410340300e10000c080c0d485014120002d00418024038404001111ba45c0d20052884d8803040290040d55014802180780307180601d09070300c0c215610600740043c0c55003049011089006c0c1c0c9500140300d12100a012000c0e141c036100d50032103030903951700c0303170359a1000801c50f092105010038100c3c105403090040700c6103107400034560b44030a03070745042c100008a4255000c452511031a12601e0015009000f41d40c0380b17850b0810307018404002800c17030341c2154011000490b481100c4588083d8a6904d06c0f1400f207500480c0c612100202c6942d14081101754905038007000c081d0740754441080060b030700c40c12100c0d01c460701e40003d403200908206000c01890415030202c0845041034100711845900ca080990030940702c20480f241512000010b4840d03110a01481c0c1c0010103ca9003400441d9513160003144061010b840185020b82402143c4d06c19140d4409641e83c10304509010802e02c111406040408804040518a5400c0a540c06424965119402020f018041e00040c130359 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 835908866 1250 835907616 835907621
    0x1d04020405120d030c02160311130f2906041512020703080a18170714121b0102040e04240501090c110601030803040b2a040f0e06091801 60
    0x104070262400000c01100c0741d03a03540f201007000d44000020700c0c0c4205030401602c0014030313a4410064000c070710066825502c030020f4602102000310781040503085811410f010354800c800e05044442d5002034500c40c055460700780c1c105000c400b000d00e130324540384644c690781c0c0d00c00c2120215004040c45c80c5080401c1c5c8400d0311035004581600c504148086414000e0640105125114000c2080304119646040c02441c0e000f0045950150460001590751080b400c461002000250f0060391580d0029181c0800e151509034035402105200b5030114500d02c048070001090300c02c11840c0c0d00207504090610007054000e0100a0000d8000800944080034103601040389940c2c488840c1d509000c06d6840703e90600c0500600100500040c1c603654038035441c1c07513000c154607050f40e60101e100c0c0c0c615101d0361109001510043e1000741c003030703000c0f10301070aa12140080e051482013443d801291200c2c5880c1500102a0303540d840080c0e04454201000311654481481d10344c000006000300f485004403802c80c500 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 835910116 1250 835908866 835908869
    0x6050a020f0307060b0f010c0c03030305070309081603110f0c04050402012604020a0803040303082409070c050709021602100212041710020c0a0b040f0b0106120b060a1d040204 77
    0x510b02000640c0c01c10b12025800c0202500001e50792030394000e48100c0119803100c034094000c1c00b0111121b00520009101c0d400c15a0449880e241c00b06200700281c070740f02003a62003445a600d0300700401400808054109101c401074410f0700010b0214401590421603c92040301c21081c4541d9441000404580c0142012a01d0890003e15040c01e20010107081d40c1d140b4041c0e805a04c68000044000b500120010441d0b041c1e981c960740322006030312410001d64503900030f201c104403c04d00c01d00498009031108000980702d4052031b070740d00702e2458031814031078109038803a04600d036583d00400150001c50a80c110314684075505581020b20015180c500300d0504141d1006450a2800041d0000b070548241440580345010740f02a40d042001c2000800c0c100e100382d00d203540701c0341c02440702ca10108007615902c1c1e40c0b00c1d01888400454110603610504840c400741c015002150010301c408a48031140c1c032401c00749135005c0c4c403920300c3c00d4007403140900000440c017440840b24403a01000306243d16290151030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 835911366 1250 835910116 835910143
    0x1050910050c16030f120c0210050a0608010e330c0a0903060509010b1807080403140405040606110f0d050d09050f0d0c0515040c1203020a050f030904061d0106050a02 73
    0x8283c25514600100f031851382c01c80300000070b02d80840c50082203003244628500802181c004101c220070b4024610301420b0020046050641da03440c0001e04003000780580c000c0ea1180700302801d404454143c98255181039803803034074102d085101000202c1880c1d800144d42290f000941380c0d45032070042c141103810324a83c0e0001843c5a0401c02444a40744054201c86c5024208407010011034100024a840400040300e0200000c3c200d5800300c1e011900500e40c131040014140c080034035040c2c8640101d4141c0d0a83e501c0340c00054220702c0314101131001400280f0141c0c5240025000703110f03080e20010414000c1c006d0780d418043c0e451500b030003002001c10010541c0c030600010b40c1c18401801101414030903801e8420b43e0710340200c004000c1c0c2c05581e91400f0340300b1540030303400300509410441c04040c20184800101d00358421a44c501c804144100080b000c51244c640045030f581c0c01c41014030007074480030f03840031305105403280d200540300b00c004048905540d4117107001900c2c3d085903042207180c2010f000820 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 835912616 1250 835911366 835911397
    0x30b0d021f020c240310090e100e0a170307200d170f130807020303070605060a090207020306151c0309231e0103060504060e09010e01050910050c 64
    0x80d403140e00300d8122282505070203980d1008800c2c01482000c4c2c104240700c00030420a0b5425074000e100703000c00b9603000b92040c030740140041d48442802007181c1e110f01520f0199070000301400c00207101402a88a503007800009840359800a644420251250a84407544c080010000034951403007650303400c040341c0c1058050b81e00040c0c4824929210f00303403503541c1e00c0010724200c00c9480303011903d0340b0240105c074107800d900700c0c80d078801402c5600744070b200340f0807501400c0030000080503031f43c00c002511105000f11000540350405800b003000741071490348540e0300c1a0052010002503a40490f50315071103400d184e92911701c0ea40c501d0004141c901c5c103441da03480075200e0822500a05920a189030f0660303242074003542d80d80343c41546403100c0713160055686500080f040c5030032050022041d50400441010304002c2074290321040060265581d82e04941d07020b203a031804000c00c145090003070703000115065000300158107200d40b65541f80c2c0c00c91100e030300c403141c1c6500110303c02c001820100c4c0c20440301d44625 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 835913866 1250 835912616 835912639
    0x212040201121116020906040b1c032f0106061e0507080c0d080a0c03060f031b08030a0e040b09070c02061b0105180f0705090a1509090303020702011202030c03010501030b0d02 77
    0x41301a501c08110a90049400c9030001d0350b0b5040a01c030f0341812030f5004203003540d6008640d50542494140040440c10000e044024502801008002c26502e41303075041e00e440700100404500d421104103a000b4000c104500b951808103481d421921001d80e8203070b1511a41d19151030408010a2207000780c075a0a900c80c1440c02d0340c980307910003000e6000d000c0c507040c24000ea512800003113058441e14041e000500d0382982c8204002210394400000c1e4014080450313408550b546001402c60b0130030541e850105000301d80b10011868203116407a200202203403007074200c5c2448140200120300c580070080c002d100c005103864042623448a645840c890b008002d00a03850606401e141c0c202422160030300c00e00c99064a0040d650020030b803401a070350050f00101169440d506400094006a0403e460030f04246001095120080c0982082c1d980662000f59a440c543e01c00104220b18040c4100c10b0740e032060092004404460f01220b046074024079001c10b54040c010002048008a00720003940501181780 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 835915116 1250 835913866 835913887
    0x3070306090b1005060d09060b040c1806020106181d0d051206041e020313020d0501020406080f090a0f030323040c06030b0306010306150803070b0f070302120402011211 74
    0x40d11481921010150f40303400c003c5009003030081c01007641c030810501040708103080c01d03805031003050f004850200c0c611341c4110204044440800070000018011062854551500b0150340000c210a20003002180d103005000d41e1503582581c6c0c01c03010940c90b071035950000c2c4d0700c00b18880c44a10718001600c1480c0e0310350f41e000e48164401551042c42440310000242c1c50b180c00d200d501081c000e80141d21041c95002c04903c402036000034110000314440700c480f00302507113a40100c4500c0341d115100050755181494005040c08200420030356481049000300481d62002046520140e60b0040c0702c0d40740c500c02850f081c2e02034240305424440c51441003c0074540703913001f030000310301a81c0590a180341060712914100c003030384c0301818407a805d640b1243c010000902e0b540e100791525461108001c4500b511081124156482101c05454812040c414004086d04841c03000c0d40064080c14211310f40380c0c4100e0f00340c5009a0040010381406040e40b01c01654490070740001a01400c9504841d0342c4552030358 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 835916366 1250 835915116 835915121
    0x90105071b03020406060c0510050414010c080f0604150b0717190f1b110d0b040b040b0f13150e030c01061a07050c2e0e0111010903140703020c03070306 67
    0x2c8140d01c168104100001d02c18026048005810b4200c0040c001200c2c00511250151101a000b01d401c1c000350304a81800b0310081c810801020081c0d5603010007402c1c42c01d440385902c00050982d40c802e600d0075144205c1c118965454170212a124588a9100c406504020b481200c5010b054980003100159030020f100d01050302d20040149901e80440c400380c064000c0740c40c91202401544483c0c04003090f8004640000c0500c03544200007030895500402c550340e030210000c03080d41c3c02c480d0740c0210028041000007081089034400c00e000b901852a25100b40c5070203003406000b4016083d0402040c07110616881500100c0b0001154400c44c0e03075558443c0c1850b0700a21561140990b411060708403110400800404c46100e15081070041c4580c1c0f40a4041200780180e03410301e00ac0075007403000410740e103034261451001f150216803200c1c85598a11000503203041040d80e81c010060745815021000690002106031007242d0345140ea40e101c5046180c00d81c07520030204004d030b5051085810010070041030341c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 835917616 1250 835916366 835916369
    0x430080105010809160b130909260a0c062415231b0304090504060938091615030608070e0a1a040e0d080c09090c090105071b 55
    0x81e6543c04075070b9200440a0b03154969545c040e02d09601408081008003045009040440f45c0010301940c03480d5030702c10410884143c01d03411200380044d458501c444500d01d402c854050003044840c1464000c041c140100080000b9800a2603242c0e145600260030340b14000580465841660b01403c854590181c908a8078031608401e0003d8240084012440c1340c3c40c508400c07802601c0a0381e4104044011000000b001d4528140441c0c07100f80400680d002c868041c290080340138a0001650324218100a01010f01c0f0203406500005612000d0207280c41080801102020034100792001d03444111103030f418a90003000c040f24001c0c40100c0455003010741c016442044116880400030140c3d2020030503110090f42c422051240304c0036002400c01903543e04003140100819030301c00e565004100006d000c982c900c407416001503020301c50094103690070122854122800604040c01c06070308500085152000400c4400041c002150490301c42c1d01031401d446c000e6501420510b141c4130a404005900c82d000e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 835918866 1250 835917616 835917619
    0x207120614150907020118260a0507050d0c03320a1e1e2a0b04020109090203091e1203010e070801240c03200109140111030430080105 59
    0x2240100300d6040c01403040b0070107803001d4690281d5103045519040044a01842a100200c8e922407403400010350341d000509205481e525416200c03c26802d0052401402e004400240074111000502098010085c002c608055440e4907081c01020b4665035450450324810140350500810044c00c0c0c107400110000d041162444520b18140030000c088514006054a50312213003043c40b46014254440d545001c942ca4144a515020400c1c03d040c202c280151400300ba2003510f001c7d0140000c540e40844820300801904a0039411810100005030715000981c2c1804a0740211000c3c1d000d0038941030148011408a40c4e100c40d8503581d607030b04400310301481158403000003040320001107100e03440c1c0f25620a042c08a00184038144452039070985140b8901c0d0026010b200600b5998044000103c02c45800c88a0304c5002260005141c0f91030480660a0a10504281d04103690200032503403048c00e80b5071143e0800a0000700213401d00410503a04080400b541032030b0034110351000c840340c04c6070700c1d035040f52070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 835920116 1250 835918866 835918879
    0xc060c030f050f0114010f1412070f0306210c0504051501260414031303110a0b07050303060402090a03080d1b03330906121e03020712061415 62
    0x11a81007142c040c01c000d00451720b1a40d810101c1c10310b03d500c03035240950448803505040801d80f644460180d213503084107145408255504003000581a0311209000408102d81414400c45042150036100d610ba040c0740302009102c0c0404840c01d20104a5280c8000d1401034400c012509041d0850500d981c1441c070300354045400714031a114000f0f69140d1195061407202012842926240e0311320100c1b650007844407031503100c01c0c450510801181038626000b03610680c80c03203e038089a8000d000800b04154000605070100b841110007281d004070450b60310203011103005944040000000d800d1010f103030400703091148086002d0780d00140c958002e410540900c5490301550461800c12400e07540010001a5000708140520800c02c00d100840c000904402c80039061003911165940100c0f02d15910410a00c02d10305c1108080c40400300c6041c0c01d05084c125a09103810154501030368403801d43c0f080c0d03010752040e482080e090020366031041c01c00799000302400200303041c43d60350340103801d4988100c10700c90350 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 835921366 1250 835920116 835920121
    0x1403100306060e07090504050a110a0f020c0109120b0601020f0a060e070b16120e1903110303120106050307030b060f0a14030709060503060406090903020601170c011b030c060c030f05 80
    0x43d00d40b030300d6100754407a64481064604010a01c80941005810810303495101d50007184409850405001c601080d9558040c0c080c2c0c040344020325251030b00e01080d0600204403802d01c032892556494501507034008828a10f030f40c545200403132400c010031001000601039a022241040f5080e001615030310b0b01c000894298036185c100454003849000006480503891800f6500002ca01c0700003108509031500704492031500d048081804036401d08158012152014400d00c10002001900400785000703800460400c851241300c002405018058402442004400103038594030a8002e0944504060401a01e404010000c20308039000801c0040c0070a8a00c0c0b5070134124056101924401d00701562803404040c074007c0191034a5101030724094100b0385a00020818400501a00744100d00c01d03802410340350714259110780590201c114000355500008803c4900760382c002000c5000044410308c0906a1019240966040080c01c100a240e00d0800382084022074040e4042c25801480780000d20442d0b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 835922616 1250 835921366 835921379
    0x10f03110f0109030f06090b100504050a0207050601270c05030609092e1506020a02011b02030d050c1509070807292506050a0b011b0201050a140310030606 68
    0x1d0380281c200d00e0000d10400c1c801c102258640c4d4010045500984000604161545551400c104111082c0710196a9940100030b00d0516104090307111002541c118141a4540e1f03945840342c01c103102d4406100c112120292262410060000202c0040d0b038040010003050384000e0681d800460ba0f49101c1d004810008004190102c1c5138580d10808401d11031131140c20480d03019040c0315007210011030300c1d92850142c540f00f01c102c41500107080d5640007800090424030004080d41c3c2c0d07800d0840e010800da02d4130380e001602c0000310b01c101010b03541440d54482866002c503920740005000407001100007001800b0103020b0200b540c1c41075800d24015a80ca440d243c03038180c109104400c280104440d08140c914520440c400040d00081070030000511802203840009441c0c0f40401c2d0003680c2c030903618030900081031107070300c9480d41d0300c1c8007070800d6011510100713080148044101c2019040c0100018422031945c451000a070700803010ba02d0494680c00c00e84580c0300c0c410424002142c06910348071000c0f030803 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 835923866 1250 835922616 835922629
    0x4150c0210080f01031212060305010b040b06040e0106120f02160b061e190f0b0301090f050603030a111603081c11031815041b0f0501171b03010f0311 66
    0x20b4420709921243c503483c40da80e0454100e54001c034001040048208400ca017402800b41200844c000c400103c0e085804404220456240881c540c0c030404040000f01b00b00c0103911001411100c1a041c40400c2242c0d10101070007910303414091945061001404107205145018290200b07030080d42001d0550b507402c030a021403221103842d20034001c941214518410300e802070848503040024035800c00142c3d03883e4108510410260060010644040018844c5140c40e1091303101000300c10100b84101e00385080880d07140d20811142070100b20084d0030b5400145e100700083c01c81c1300c11030413010301c400b0b549017000c511036009498510000029500c00700211074140c01040c1c0f1145002c40c11614544940c20b04041c42c055650f600c10550103030080e15841c450025020f80d200d2809604075098104540340707034803280c44480d00700074000030007000305100c107076407268014450266903007030305141e500c0300500a0030b40380071807c1094490100000128000029284690440f44a0b0030482c180e95443d6080082 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 835925116 1250 835923866 835923871
    0x70f031101050c040317130602030a0f0509100e0103110318101a01110a052e050c1c02190f09080c031f0b031b01020d0504031106070804150c021008 65
    0x83d42018001800407920070100c0920410082003030318a030002944202e48180c1d020b60250b00560070204d0030346441500302000a003428114a4003a01c0d083c5103400040318000522000c1c020020100a0400c03241d01135030050403a2a460100c0c29124a406000c001659031800880b81c440c0c05103000034549034145010700514082c041d9034880100307000100440c1c080050064410040c13180580440102e5400c0c8818010207819041240d240100300302da2500da03480003541d85000528000030807216501075810b0b01d0b102c0104004203481008540080b80c0079004414016505020031b90000300c5281d084601400d80034034586640c007130981d58008954071154419142501500701044170416844241c99030340e40002c40e81c80000d0484440c1e0042450b000d445858190700494560f229200c035a0104581401460b141c50150310f01030a69031041851450564114010100810500708204a01050f20094000c00901e40f04403901c000000f4802c47c207040c0241d0286040c1c000c00c0715441e1188ea406031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 835926366 1250 835925116 835925131
    0x90f030b0403111005010306141e0f13020a090203010518090c0d0f05060906190608030f07020f10030902132c0111130807050103230c0d02070f03110105 67
    0x102281d8454800b42c48071546a50550164003601c0400d081000c04d82c0b0900d030182d070294000103005485050071104c101c002030203e950700c5d54051045015880391184c62070b4080001240442543c1300d00c1c4241401600b0807000940c07050180c0000f080705241d640c043c6048403802c81c1c1c4035420b14151312098810a03c02d0750800000e1f001307003050401e2420800200c2000d07500c644461086010720303403500d03070800c40240c514041c160403141c103011102030714076854450720000e05420842946001e201540e80e102d44402d1140c0000085268002e644d00e070340c95020b924401801c42c0c000c255045800400a000b4074008911800e481200c84030b800106100d050014003030601c100e800d0310740c102e04081103500c60121050300c0f592103440c505440d02c208000380c03001c191b1503200c41d1a2242001201800c080350b5811242c109489d04500094190000550000c1e070721907030010403040d80340c1270701500b29881461501a010b9000140810070841d94400405045000740c3d1102041003507400c2103800da070b80603507000c3d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 835927616 1250 835926366 835926383
    0x40506060c0a080930011a030d0c080c060921030f0403200708030a0306050316050607111c0311010c050d02090303040302100201020306030d020a150f021b030a090f03 73
    0x22800a000744004044d0720000a01203c40083c40c211071011721114210800d098108904110201c11424001c4074852074a0030000d03607001d8000004a5a41c01c00340c02180c04101d1884050380a1041010869240313621000a503966031428200e002c2d0344141d0424802501d0040409410b598200b03081903c1c05090800c2d10745c0d100b07403125103040f545250010faa41d00d81003000c003986028180100070741d000505541001d1a11031a030700401030308596265000b80e01980210814034845400007080d8415503c00321035298035031030340723091403800300501145841e004004a040c060b03c1307094900200c3c8407a40b00ba5035640c00d025091103014281c818144001003c43c070240040c001d200110740140c000064050116400c0650300c2d000201148807001d405030150b5270000601c691410240200c000454180c0001c03e5550350300e41e540f020200c07440a0580c11030340d903541d0340c07145004682c044030801100b078914074080344841c421385610780d400926190b003c06c0c00c8140004514000c071441c6c0b0102d85d000b4048 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 835928866 1250 835927616 835927633
    0x30507080f0715030b0f04050f1e0c07290916090b01020a03110312040b0a140103050303061e1207090608210702190e0103020109061416020a09020414040506060c 71
    0xa03805400c517004010743c0084603110032403698072a48141c030310900500c1c00e20052810811100c0c01b03c0480c41948040b50310b8084c080002e40d44046c000c40316420b501000715a1071071503000200600d00c0c000c0102c248401406000d020303800c80d000070101116050a00d122400710740e41d002d160111016403180f240903070000014800843d0086400c00f00c036a030000705617031400c060489201303002501110103ca0480401b401d0142d0006c03944a5950240b40c001ca404006d54110749a0955a000050185105200000050070040c110080340f8011724005401e501050303450740921610b95260740580409545402e00008512000180c0c614802c40c0c0d07903100085428003584408469800003005980208a00400725401094105a40003c01c51099210700300c0d41944001042c06040707a00ca8070402c41791840395568200b403d0116540c10940726400d61082400d480414030203651a800b07604603c2c4003150005100f520210700581b0400111000c1220f0b07502c40c4c0070800b060280c43d04003030440d48801030303 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 835930116 1250 835928866 835928909
    0x40608071101060803040806090d0804050a080706060504180203060f130206030408040b0703021606030203070e0603060f0301020a02010207050106080a080f0f0c0a060e1516030f0e030301030507080f07 88
    0x581c0a0030744000004948030b9110009503140d507000768440031072036000320108440c81005014807008891180307410b80c85030400313440c5c180d40d0354000f44d400790426000140840400000c0c3c2e004800800d0080c0c0103103c1e00b0405d401103051030710580d8045c2d01a0040328000760344100038980c030900c40d201d080d228245203401d640038804d554200038011520ba603010030002c50404400c0d400380011511035401020100040c003000d101000342c0d584039409043c010310900c000c298008041404c2e05074141c07140d03600c0740d581d04001200132044505054155100083c04901a641900140545030007240240100340d03840c0041541c1340d11a8030060100c0006000c00f407c170240070310003080201d007405c4449060204083e101420100152002c503203940e070700c1c1c4c3c1c40d500140703041c031680c0c100a40780c01e1142000c0c50045c8041c0c9801c6a5008440109a654500c65042058550000ca118588a01201d44a41e12440c1a03079460150f40076515507031098000450007000700045400a070341e007035075245a28841100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 835931366 1250 835930116 835930127
    0xc03150e121308011b270923010308183016120314130e09070b0d0e0c120c15070b15090618060d0218070f1404060807 52
    0x1807400011042d0038006541032003400f0b259036900c80c44000000410090070042c110300e00c4541c00100c10410680007014980003e14074104071542602d01140e9280740024844583d001c81c201c00e540d94000800110a1101400c040c19640d010030b4550402040d4280c00c00c00c1c1289004030b06c2c1c01090070019082d1128690100c1030b81c1040c489000c0707884003207140c420841091020f03001503401445a907001ca092503032103c071b01d807035035242103d54510308148554200382c0342c0340a0107081801107000000c941a07500800c50400104080d81125031103540c03c0310060050205a1552201072007001828812460020182c10b401d01310080181002d000321001e20030100fa102401c54040c030018400040401d0962400501c5041c51781d801c0b80034080340b1400c010103000003402180c0100c00c800d01e81110100c20346441a0060340c00c07503052814800a20010300e0401c0c40400f80303d103403034280e41445962500080c2c03401e90260503072100301d12224401c0007070145000e02c1c40345100054403800442c02e200d0098 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 835932616 1250 835931366 835931377
    0x203160f11030f0d2d0c03050106020307030807050c1f06050301022701031b0807022803031107020409140105070509100c38011e1a160c03150e12 64
    0x20180402d40d102d0344240500340000608500084015400f082c125012940c81b4208416130503007810029035050000080d603e009103d002424081200d01140006000ba802c2c1c40c2c0c0d0100603c00c075008044240c640311201052403525403000d900701840410340345818025100321100342c070b41c4c810361081042411000c1031294050039042c99079801070250b05510340c40203601d0700400c1d605c4049450910200007886c00c110064241c0c00120460400d41042e0050162640ca0641602e8007288000c1d8109040f00c551084100084d405440d051402040040300003040d415001c08000812003545d0f80b010030303102d41c800d0060603940004031000c0c512400340640601d248031070094000203d880b440e505a011307418020001c250b030050500040340c19403110107070143c0c090000081c2d2220310309240c1c04403032441281e034000e51302c034041825600341410000206031401c814444d0f00daa40c498645080501907507070103000944404001d5581d01d101c5c103d19006208003110480010803d0344510038010445800c030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 835933866 1250 835932616 835932637
    0x71112030f0408160614010321021f140108060103031707020712030e0904111e0f010807020a050d0e09130309050105090f0d05030307030b0d0c270203160f11030f 71
    0x4130031101010543c02d109603800980010250100365045040640300c100c0d540c17810314003000c40200d100600c0b642c049803252016040382100c0411281e01150309002d06501044d206031904c146e0000a61f8140004269040b02d009403102100c50f140c5400310300300058120740020259101d03078010040d08403243c142484c014080d1620307950492012002400c020000c0d039050b103038000b14410a08032490b02c5002e4207400c046101e201e01c503518200000c03502000712084030f82d060205880c00140110300a100d1050700d640d201c010b9485004040801901c03400751511070b1401080c2280c0003038030f00b0118070444604550143c0ba1090f0f81c03441d000044a5540c81030810395005240550022229114010301c03c5000f48103038051074480c50400001001c0b113101c06010b0b4407236008481314a0101d00024540c009070744c0d0b02404d40d5800c0c091102281005c2d2605450040800c0c070000c00c1010003149906203c5501c01e0f550b0f903a03140c0c049440400c84460103148e001c1031803070304108440f004d01c5095000070721b116586c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 835935116 1250 835933866 835933897
    0xa141c0c060b0d0f2001080f0915070f0906050720060c0730020a031122150e160318020a0e0103150203040b04080a0e09071112030f0408 60
    0x12040003080740d0b5240d150045960144c0c403049581009518202c0e484404204000251005150300c0020300640703014003212031000c0014081030290708180800100c8e460303030f850100b01d581004d0100622000c3c10031201c0e030024405050202d109032244084401d1a0f8010f501c070940c2501080c00140d00100940c0040c0e441601004001409841407240320000d10f403d90b0301046080340701c1c020100301c906000d00a10b03540c2900030000c00582d500d440f280c094982180f06940d50344000702c00704201d80345040c030000c1c0117420180c0a0600070b07865005202c118080800313804410380d071785015954001d41600c811160f0b4885040c0311448500c82d0340180d280442c0003010042c480700a8010804207640758100802042d00d900c01030041c0030811030305811032140311008511307503e40380e190100000d2015200500251001070300102c803034890705107400c0880009000d05450706200d04c02a000c80c034005001100350042004441c4080303041c0b01501c0c81400340d000741c040b242d595903a034200f6952005555400745030303 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 835936366 1250 835935116 835935131
    0x601170a060806180708010228050403081902010b030a050d0c0203070f141c020901030f1b06051c1a0f21070311090603071e080307050a141c0c06 64
    0x38001c1000f60300580941c0394070350000c001c680d0030b41c2c00d00c4e4864002180c0741e8010040000001900c082c5142d02140b141021903040001250448a0303100b81c0d1300c00ba0218201140c1500071400c01a00e401d0600e40c2c540081054003400801c1c1901e980d1a11406400794001411510b50700380590414001e0b02d200038240d407031554807514101c1d1002a180c0104010502d44280c511a03402d1003410507401d81c08030b000190b110111617000800c0c14205002c000c003550f510041000400540c100340f00e20b003030302c0915908015a2245001002c680024485509103000d103d8a2800b401d00c500c01c20b00075a13040480741e602001c0400038800101d0b43c0c001031a811203980709500d00200440080740841011910280454034034504007500745e107840901c603510420790f071300070720006950008840d0120740d50f10180301040d000302c0454032030828030342d44190218000024072908000c00402c03841e05540c402c0c0c080494030b0688132405640ca0307032201006600c2c00d40d92882005482d004880410149118050208210 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 835937616 1250 835936366 835936379
    0xf0e1504060b01021518160f0303051e280306050a050603130b0a050402030c10020309040b060c010905060a14062d040603050c13050c07020d1e030815010302030601170a06 75
    0x450215042c00315410340302649030000390144030f4802d07c0b078601c41150801301c0c201800c904c0c40f1449488000d060120014400700d415180f002a2843d01c0080300f480f40d15100e5000c019003220690303041244211160552003580075011b407040b04203a0310090801c00d00035080c602480200c0d4009049049a24503208a020004003c04142885201e502002180d5030405105145c60000b0100c4034503c00c88000115410040d800401d680c20102c0403940480e0700c04109010a80d01c0c810a0000d50495080c5540d007810310800158890103499014000c0084039481000355010007c10b0b14010707841510288840105440744010140c91150158030080c0f00204200040458105038000c8949400000c200300703045c985074802400c018210350301407010f80380c0f200c0c2d511030340d01c95a28000e00c5509c5080b5503809000301c200301400e00ba038030300c1410722502129040c082c1242d07608544d00702030110210f030501a95480782c001c0c0c0c1e00a0506071107420394203900c220342c206001d000a041907400ca640d10700002c0c45 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 835938866 1250 835937616 835937653
    0x60f0e132a060503192003070f1101020a08011e0b0a0f121505121606020a021905090c030c1e180409150e030d020d0f0e1504060b0102 59
    0x80008020158410340d46404421000600e901410030f011040c81001200c0e400d18007213011401c800d1600203a005407400a070104a28810f02000070b0000101c2084202c2c0d4010780008401d40c1c2c16101d00e41d000d150046e00900343d21407401e651000940c103500400001d2400c00044052880c2a0803100307010751501d004803120303040050b4240c0010103010404000940181c400c1020f000144414003d2040c51454035444080c0340c4901ca02a03805590802d009040074045040710f415084205050140d540300002d40d500d02001043e441274040c1102e04d24021001c5c44124110f5201910b400304075a01c130646400756410081102c070320742c0010003603455107c039003030704401541e011180900e440d00e8141d014108040c040415081c0102c1c0381c05814408600f5944540c0d14007010180c01045010036911341a040d1f00a41e0340720b0391510700200380d5031407801040c0c111807180f642c00314081101e0780c01c01039500d80e588611008194a034400354003180100b50a40c100f40d1440c2d9060045a88076500c61488000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 835940116 1250 835938866 835938893
    0x1407030302030601140304260d05010e1605040806011e030501140103061b0e060c01020903240c09060a122705010c050705030a08070c02120609010e01060f0e13 70
    0x80c1e0300004014056821500d16020300701e004400d03600b1440d02c0d07902c03c0015404a9000f030b4690f443c02e0383c032164010500c012901c088044410070301195a444d00d0412070914181c42c002034000c0204102c0e503507148504255001c8420840c000c1c4426481d0034103500c0e034184010b070445004c000e03108002c40412002d0040c42120141c42041c1c0049601d10300300881260030006001081c0c2c9048662002400e500c40c604c07445030142110310030303510205104903034020301c541c20006406005241200c1c0034040184680d02611802c120505030380e0b941c0304200c100c3d6124800000740d000b8000e020344c5a10612408640104510f02c1e00300007803001c0740c0c003840d91002440040c42200640103c2080341006800e01941c1c5084000341041400c0040742ea0b60191240210203c130350030800041c0006070141e201e9a0350a2549030094010b646220a100340c03540c8850007103a04052941c20305042002d12407052280c036044402589407203482908080300422110030103003482c07940314400880080400c0000c1035030407 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 835941366 1250 835940116 835940123
    0x80709051203120702072d09090302100b030106030308070c020d150c0e06071a09192a05030303010504020d0b030f01140c1309021c09050c1203130b09011407 69
    0x140c0b5850068082683e0303002c003c05035011500040c40c20042c042c90103c6080c840c4402c0426010800311031001ca020b804090b03809030241d82d0426803c2c406058003c11200501d85240c80240300303404084042c107090340e00610008002403071010019100701e104130300396a02680700400c0c0c40f5030b1100781c0c1c442200e61088201078050a80d40c803101800c82c00d412841030f03d0703811000c0d580b0504000c059165100302d0a101c00007000320038500000900c0e906400c0c858502581010324031034460100d40d0a103661642002d1402c1d862201031031180c01011601d10f105030040300c01c028021461a070030318003840065001140c00380412a1165210b100710f42e07050020500030910300c400015500f003110300d4240032000c05042c0039081c280812086400144500d0390500b81e0f030100300050380d5045a04d1b65101400942211003d2013441d0103c44020041c012a80528215089400918007c3c029030095220311400306030b8100300180a0041252001460181c00c240005040c4540c3c500c40d5070002c0c2c151503214880c1207 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 835942616 1250 835941366 835941373
    0x21030e09040c1403060c0f0313050a0c06031a100e04090c030f022d210a15060801020913050711030a0207030c0f061b06180b04050606041b0807090512 66
    0xa000f012044181583c01c1c14044000348518241403810040620440300245d081c18800000610040ca840105440e1a503101d0120765202504d81007c01d0600c05d54000d07000002c1c00e000c60035044d051000030b00980840010f11a8686200c2c00c1c80680302d00d0100352400d0b42140e2038180f90404213183e00c050000071409000b02401444413441045402d490684d0220107401c02482c2051929010a440c14820a8140e40001d05005240201d03000624504014101361160403081010810303403501369000b143c1041d0042c0600740d25104c00c27509038011400d44681104403d0444c0ca400a0681c01ca0b070740203003090900c20f018070340700e218450455011035400c901580c8101c4080040010b20020070008190742e131000c1ca030040c28007400801c181031509014121040031000c0713000b0700487e50b1200c81000e030011f00d5500d0034038491a0444607078004450548050043c800024074600b0a030041b09010001c2c002d1b100b4100b00202010744080101410000030002807600114245d195045644900c80090005 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 835943866 1250 835942616 835942619
    0x70819020403060b100f1403041b0902130e01061409060405060f0c0c0301140a05040c0801020a0903050111030c070f06020915120709050a0b0c0309030706051c0621030e09040c 77
    0x1844041d0300b0b00850342041101148001b070815034060251502c031400d5103080b070350300d884908200700090041003512040f415004030004558441d50300400504c2c01000107039104940c0c0d12031180302c2c64400d115100c00320308482040c416280b08c0b2002000b030358400074000350926880708081402c68218000c800350800380095072402c03008081004040c001000c8000384105010000c88802c0c14034042d113144485900d40c0040b4040111207408075000d4800c00000315101e05d00c04d02c0080c401e900750700c8190b81c25440c0c0501e0713581020482c030480384501d00c00130b00b9500d001010340e40c040702043d07165826110980e0a200740b54080d80c8a003045020102e4440345c0a45494103000f6540e20144041d040b60184110114204129118442d608003102ca41649260710350304411015800c40c4620445142e05029034403021800c1900b0101810300300540ca03814030280000c8041307090440b140381c0170306501d0001d134542500c4620407070503c03000018400d10348443e00340751901c003242149074280c0b41280c1640c64401d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 835945116 1250 835943866 835943869
    0x30702060105130603150b031e030a1812080901050c060406051608060f041503080d0507020c060c1b210705030d2f0705030312090c0d0209070819020403060b 69
    0x20707070f40f21141c418082084118610f6980707a0139100d48900d0b4080303417512583d05c0c07912580c0c10b10000501d00d10210090711a01c4401800a46a5224081d203e0210788a03180b50904074103802000b10585054418030000001c00741c50f4066260000100c1504000c030801c40022140710a01030036004501c030780404141c905141010441c00340003021040e003007001c601c2c1040901c1d80d1b603175a5440c1303030b410698001681078061070802c01802402d400240c01040300056501407402141e11071446100d080e402d031122030752403d08000803440b80303050b4110b0f145d0001126a02c0400460045c6644400081c0584528041c0d4902065000c0f0182c030284c0c4980c000d00420804e5050130b0018504254591511815140c0390001d0410800c06418544a242d050305002e080424020000070028100003003c903521880c0d81404842c00c1d100803078071080c242c0500800c60038941414000d01d40300582c0100340b04881c0d038403400100d40280008000d000c200306204801082e600503440108003440c016000450207600303540 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 835946366 1250 835945116 835945129
    0x80c0f010603030f0c0201080403080613331a0f1603051308030f0421230c0319060e0a021c052a0907172d01080d2003030702060105 58
    0x20644d0050240c0118400010b03a0701080d07065019501d03050445490703c481012501309c44a141039242070500c0c00d058000990b114040c100703c00303451440b04122030700100c0d000700c01210491141c101c1e0103884504200c0701658a402410b1b03480b1108200c04e003400600c60b0005c036a036003007020903804a00000b442c9405900300440c440c0142440000452502d01900f040d401a0700c1144111000120340001c4213000704442d02100c865190803a00207003145110940ca078681004854040c0300d9881030010010440c14046650012820140b0700e100c203000860312810003600490f040c402d2940124498080141c1c0d40b00990b036424101d1001300740400f17403140f4040f0300d080c00d505081c0720151814803540310351820701d18210f5841401980c00b0703965500e400d1000c5e04e911070221307180c180007481c3d03400304400d10300329440300400d001210511104944d510b11052901c903000380126415900541c000f05401030084500001c1e2121420301d401c0e040103401103031411034000351200030050700994010400c038640070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 835947616 1250 835946366 835946387
    0x3070f0b0123010f03020a02010204090501030606170f0a030503150d12030c140702040c09030c0920090f010807110105180d1707030906061d0103030f03090201020613080c0f01060303 80
    0x900503440e0b50180900068002c0c00c44080400c1015000a0306042540c03003034040c1c80082c0540c1e4401d11495031a8a00100503280c1c0d8000c05140880c2d009030101c00c4500002c48118a80201024040c20700c0700e03880440341c2d540000c04164111400f030100941940350385204180300d1b40212000144013042c448000c0542c2c908240c00c408109025490001a040180403540034a9044400054940d40040b044c0c45207070440e400981a09004040091090300c1d6401c481c43e501a0306501241109940f0090500c9000b80f02e41d29030850800009100154019464503400c1311203400e00340c609500000c56982034542c1100c0800003103800003030316141040d041141d2031240c0003900302650b0b41405901003500600340102454101078403841c060703007804820380c0170342c0c0a411802c04022992030182042c0c120070320b003884110000341d1415612203819110f84102810598141c1c05040f06450300c070b440030140418680c09481d404001c0001d00000001040440c51103440c140000c60071915500f009000c80607034 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 835948866 1250 835947616 835947659
    0x2010e06061233010b04030c090c080a09020a1e03050601050607120f260f15060405040b030c04020a211406060c010f0606051210060903120203070f0b01 67
    0x100301404441007008540c140da43c0320724041200d1000b158620003c82c440b0454101c40301404040300210b100e034800340040064a000302c2c0d10046040d43c0b10050012500ca1400c2d80000415090209003500080e0300312203450790000341284286030702c6070701039141d85a200806010349442c03400100104242482007900602080ba50181004e042351504440545208030100030400c0350f212004240d0300a9190000740312688250840805083d03c02846101c0c003615240001c696a8002507a03903200380e090828000c0c0d01900702c0307041c9840c3c03e060001404000001c20f90500600000141a8030780c8d00c0a00340c82d4172255102d9401c02642d02030b02040b00c403d46082220b081c24205240a441580e0301c207a40c000f076064419658405154050600600c0060424200181130a03000100d039507000700034100802e4114212002500e900c1d009442a505900c940d601003041107104201141c5a21044c480000300c07401500d140041c50340d142131380060300308000c440c11205040140700441440e450714104600 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 835950116 1250 835948866 835948879
    0xf060f1a030c0a12140a09060f090503041a1b010c1b050a02011d0915130213120f0b0f040b06040c02121608030a06050312030c0d0f0204080d02010e0606 67
    0x18038403030000d0b051042e045800140101c0303103140701e24041994408210240e1124584c0300d14102111340c2405130040740d109403603da0901100108601152284510a59000000703601d0245820007019150b0118040031140d10000d10608500ea001c12801c0000d0881035800005d66440030b080151060043d0002540c003040840c51510004000003003403016140c0909008680c40000c4810034030426124501c2900b00e07510009000c0d08240d141d02c0b1402c80c1c00115881c0c0c040c0340c014800364049014880c1c42c0b110b01c0040020800000013040111983c0324028980e4481c0c50b8441d071103402440405a0f076180d88141c00204000a00c012400e030550040c01c1101c00780f100d41c11400009580b407291840760000c0c0e070400100d6011000c0416190a601e507405281f072038617458000c0b0310000074000c41c41142d0082c0101c00c00b402091a001c0101d17031060403130030300c12410000d84240c00002011002804550583e0030030001c40e45507001c21040840b21150380c00072400441d900b1b5500e00309600a44050300914 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 835951366 1250 835950116 835950121
    0x11b121503063e0708040314070f1406071709180109110f030609070e0d0f050c0108010b0d0504020d0b0a150b0306030c0904060207020901080d0f02070b1b010f060f1a03 74
    0xb40000c8580f118510703100c4186454900307a0070001640d1040340c1c401809070741c07050710320081c0a801003000710403150031920132640c3c2580e40154000c0c1c0e524506020f43d11000410804000406042010a140c20000080c9003040b044c14040351010160024550f01c03120f2407401044490824003480e000291007003142420108240c2e0344012600010304a940300e1500b01c000500000d01c038120031491000b000b824805444003c2c1090849000c480700140d609014089912400e0f5000c1c070701481c1207036480200c56141100d080e03030a0b002004050700032030307000380419440b002042800340103178020703928998000741441c00c000c420211400a940b04002d00c1c0414020040340da90040b546440c03402040d04e05498640c0c0c0d628000e0700a200303a040081d8040e01303100010560101c0003a01313110041551b16182c01e00c011807003041e640c03010140304441c000081040726201d103840103110520030031011400800d2000c0c088208a041e21042e801104400100c030604004443c05401d920b514070400d03407503c91850 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 835952616 1250 835951366 835951451
    0xe01050901030b03010b041104060206242403040c1e050a140a0510030204182a0203120106030e121204030324090c030b03011b12150306 60
    0x14040c9225050526030f656490300c215842c29040880350700300091003085601c4c0008101c031150340040c05000c00620441001520541301d41e4001c15417440342c1a0410b50207056a401c0040c0c0d4603009811100204c950038140d2800e52030180038600a522404401c904541407003c9184003440c0d41c5034039045c0d040c22072000c11440e1200103070b85041c0c03502009081d0100c0030b0703030010a00e00034460307021507004050003059009a580c1a4050410f0303544c0c058400d0030304e0303c510184034281d0b1036003240403940820252415003e18001d0030403030f9021481e030042e207041006440300f03101008000d900117800700361110300030000da000501842c40440c002d51714150404090b1500001540340052000b0180b40d503840b02840e20107511110700c00302810800d841501192100c814030701070800007544030042420074940095504e818064000003400f41d0266040304140800100ca810300f500080c0e428240e591140f8503001e0440522000141d4003440340441e0038450360008641124022a030100c14143c900d14104a0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 835953866 1250 835952616 835952627
    0xb01050313060e0f070b0d051e0c09040f0c02061009063f050a0b0105040501180f0605030f0a02030f0610030807030e1816020d0203121005061201080d0e01 68
    0x240d410200c0019425030f0401e00324604450703401400c42030311030a080002c0d40c1400100824860b6680d000c10301181e100e0070a18040104102e10928112074494001100006074201411b281d480041000c60240000c0601030304881604400f44016000700040110700104081004003d215442c0700700180c07464040f80308100380d00301c200000b00800cc0701480441d140001c4210791007070004c4039008454107031464419a07610000c4030443c4c1500d100c6000055a1a00f132040f14102d68502260f8040c3c500311030408070041c0b20001c3c9a2840700d640340b1021440351001c001641001c00004024082d00005004062400761400c0000d04242d11090401c03900b1500c8135001411030f81d0080301c0948505841c60190341c001c1d04000b015405c95110310545040c1d0700316108450141d209240601d101da07503013000490700d030008000e00c0401f40c0d004005c0d020040c02c110714415485200a46100c02c1151540005001c582c0308038452900950301400501c050310060002000201c201d081a220724580340001a00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 835955116 1250 835953866 835953901
    0x606040e0c2b0501150f08010902060a0c0204060f06020309090f060a03080705150708160e0a140d0b07020a0209010e04030e10120608030d0b0d11060c0f06190b010503 73
    0x420107480c05403952044103108950301202c0c0d02c10f00a001807403055643c03040e0400e0701c1c46200300c1d41d542c01000217014101171041203a140d4014110074a050450001a5800d580c9298101e800954501000031000502c5245001420b04e43e800f8554aa200034200040b0800c0602400c49100d1031a090051542da084100811a40d110f8542c030f889110505260341030051101c0c1e607100d00c0d41c0358410031400507070026200b88112118054940c00c11800402101e160300300d009055006001c082050001c0c0c400d81203598206180200038845450542c6e4490152200030741f07402c0050380c0803000c46030840c82c0c503140007405081004a840c1c030ae460710351401000000060400c601500709480c0340e8020b544204407421107411400810321105640e466a240e481d80702d0340e00f0544880c58461903894600e840d8001108141d0070903600c614510300c000410445d80d1010301c1140c082e00c5155261440030300c01303112051003010590038294210b000d07150796005481460f5611410071030200300700315124495455554 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 835956366 1250 835955116 835955149
    0x24010602250603090312020703090f0e04030207230406090f0501170601061d0d1a221707120905030c1507121b0b090f060603030d27050606040e0c 64
    0x89902e0b2130309080e103c02010705c11174101c21f4000180700040c036030000144000c4405107402a024503548036070080040fa810796000700160059007041018080302c00c3c0208654051003204008001110700080442d200b46c1e2003130708440d46a07130500f014030495225850040c20101203003141620300500f4141c81d840140150000d0045605d052181d0031315980b08240f507400048d00d07041c041e2085041080c2220071946442c0e000400410002d6500c01601003060307002c072001c4101105000301e0b680d40b400c003101c005d401056034000a02015010030301030007020258182d662104040103060805060401c482c51104500414104500e00032001700107040758601c9030000d00140b0440d091890450b00a5101c03c001030205021040c00b205025110612a000f0754901c000c50b061141c51202c0991503000c100d81260b81504144901c401440e0140c01c0303005c442c20403260094100c440007002000800954a00341d8a5a200f00b04001c422705252144410307952000005114451940c40081d003000000e14528 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 835957616 1250 835956366 835956371
    0x40b0a050102120f04090c0c05011b0c020105071a0c0301090e0303060a09020913020a1d090105030a0b04060621050c0307050913050f0328090b04150224010602250603 73
    0x4212140e5144d041d103020389030f111001e101c0c3c0c0c415001c1c010581003032001c0a0316170b03500c0d01d400d400403640702a08003d079808154642c401c51344850b40055805410070801a58800011b41a1488581030400030611507104114501c2d1079504042409007107404800c0409055481042400aa9500d0303c00d071038216001800c1c0580c0d2401180c010036000f10b5280e5801e400b29001140c203801d1a03130801c03942c80369001c100e00c035425041021801c0002d444070a00c0707070f00d030150405410403012034546690683d006005820104a440e91000703109403401040005500100c40e207082001000424800d48205100440060650314203040008228400142088601e842c001440078208a8103000c0b88401e40b418005694a4a24800005441070300d02e202013480d04901900707809507103010750144820307150040b8101c4e041c02c4c104180502e000181c4403003501944110b0000c40721078401c0302c80e07510b4003203482c2040f00c107654542100030b031030034901034880020083e40200d00c50340e4600060400080312101e2401 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 835958866 1250 835957616 835957627
    0x2040f0b0d02120f070e0613090b270402270105060c0a0206030406090b0106170601080402040e06091c110a0b041106160c06030506062b020a0e040b0a05010212 70
    0x11000f441846840010240400104049519003514541c42001e0302e8554000c0b508201003040658850a031200070640034008003403180c01c010790310507010160090021b40440c11b84042d806401c418046100d00410f06041c00c12045051141c001503031803961256140b000110030745e01e0041c3c404140200fa008910101c0c4951100d4030403ca20b000403500a4400790f43c0741040e041c0100078294443d41a1401c80d030010001034514843c0302d050040008541040150783c54400c0111000303140038001342d9000d40c0754400070300405424403500780100e0303018008100d8160007101031642d400700c6041c404148000401d0f803811203d008107100c11455441403075203289682e80d190889881d01039030ba2580d0030280104420207806841c1e080d20458034040c810000070341395550b901b01e041d141d003190741c5500f01c20f0070700c00e081a824000b00000810b071004d0000f9030380d90492040c0c050480c1c10140748640040c1c00c4101003580342c141440b48103148102900c10781c590034185000030759580b007519444250803000244 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 835960116 1250 835958866 835958887
    0xc02060f0907171014040302191b15030f06080a170f0a0903110a051309061413021c0309150c05011802131407030207111915020102040f0b 61
    0x20010241c0108100d50a0118075000f0b62a0356010341c0c0c42442d803039880d00500c0d92070090a03e14861051b64580c0c020822114005202416040091011200c0e9244a82d07801030b007521101013407014016905248210b02071403100102540c01ca414158003461810b2010b000c41c8801040a0403155007001141205a07102100d506603842942840103154001060401520340d002a00c13404030b0b0300442515000c0700a0204200b078001a134460a90f01960b07806c00d03462940c603581c0043d00b50b140142400102005203100c4515820401c60b070701010341c68440c01202c11850001c13005108002c0041340c03605c0c4c0b00150f95000d4481d14440c000c0f60142519a4841401c2d2441400f1039410140d10000900081c80140c0d6000c01c41c40080744101c1c8594150144107440c117080c2c0c840c800070416a00340d4219541c4420606031b000794800b07507080e83c1103403071003034506d84648541401204c0d00c4546411203030b000b0301c1c0c002c0e1a141d100d1402410300442e40100020810701d6450320402040d83d61030034101d9500c050041 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 835961366 1250 835960116 835960123
    0x132d110a08252309100e030d21180209040c1701140c0c1204120308090303060a090b0d0c0b0a171e1003020405040501060501030c03090c03151119020d030c02060f09 72
    0x140081d900000c4a882d12a005d40e0099100c81d51000513811140b1540940d8815107840303002d80c00400000d001391811000c0c1113081c3d00455509002e42002500c242e4664001c41e50120b012034054548001084040002018011704040f030029208000c1140f40621340d009000c910b0060940548813101007803c2040e90300a1201c00601d000100003d42e071560740d0349112035034000001003613000c101a40009048020701000701e910401d8010000640c0a040012400051065514480d0083c011000701c00024250a00d003c019112506501c0d4454800d1580201040420304091003001c540c5030038000b0b680740141c0944415110b100889807542d075030700100d0b100050303075600c00b81d401403c010622041c07000c10351150060741e100b1f1341c060201d2000aa810f81c2a111800002805143d220004101007aa16402c14840c01031510000c41c3c10f81d05440e08a402d5002005948100900382c6540d115a03501000400f40307000b503e0500303001d06450208080c0d02c2d80070040448507000100000510303410020f0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 835962616 1250 835961366 835961377
    0x30206090f0901090b1806060a0804080904061701051e0a0506241b120a0809030708040807080c01030b0901030f020d080d0b132d110a082523 62
    0x600100c0ba03035a5500070440c00b4007482c81c0d4442c0290034007031800704850054444580700301d1000d40982e00d454404007045030300003c000c1c01131302d0381d030414800c010490307549018000c020000074036000401c10000007102c1c01c40d03e01802c4904034403985c41d02d07084200c0084105560166030400f00080980da41000304911f542d41600e0041514034041c1400b03a1207143c0b03000f0b02076402e440e1100441441c494103c081c0d03078102c01041110140004c0c032941e1411072140010a5001451030182c900307002d446e550b8600355801a80007100103410000081c0000c620402c120b1107030b81c009107001d00880c001c40001c10302c661018003001e4000c40b031170f14441c030564881003000d10407103070302101c100d45d104d9410000c035000f031600700303509445401440d28501c0d9048481c0106240e81050908230031a54078520503c400d01c140c82804001c0081c0c50b000201852b01a200c0900220751842d02e6401c00707441c00c4c64540c1130034820400880c60001c814105c0c0d107409944103c00c54204500308100d00741080700ca0306002858002c8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 835963866 1250 835962616 835962619
    0x40e1c0c03030209030d030911090c03150102070302090f0906161211160605011a0f04060e0118080601090513030e101709010c0e030304030b06010c03050c19020a0504110301030206090f 81
    0x303c003504400a0762541c04023440c0760141101c003640d080d04000f00b00d0702c0101031754101a281010320101d20b0241c02e028103292a0801401141c01c01592036020554018044451848001c40c26003080440b0005000c1194070454590700b0010020801c0c03006030010902a8404841503602c120041d0800710100481e6003e1480d10300c0d1a040700071900c0c200d005070200740954404076080500c250a0b021951082d2042130700014460707801d090a1400c112000003010204504101c000f00c044050400070010003000340072644060301c125030600007030070291000070309480c04000a4005180c080b0ba403181d403034038000310200d940411300f4078040d03400c50b020b104211920b60380003186001d10401c01e20560160070480340541360381e800032500c1001c1607224029448003529004444c1c0020b15158840c943c002c0105210341402c5045c18144c2030030030b00e4040410321159403003800c02c2d444000c1d45402d45400c030007044210790500903071403103099400075400180301c000d003e200080b032160465520510341c1c0e69400b20 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 835965116 1250 835963866 835963873
    0x7080c04031b081b10090302010804080a032d0c0519030e012910080903030f0a18060b01081f1e030b07020303101a09120a05011a040e1c0c0303020903 66
    0x45100100e040c0031210a0310711712580011840c0b034545402418140d0072280c05869168081d82c4640392204a5801a04003504255507030380c0b40c03551031202c21484405081032420844240c442ca5850170201d45c481002c1009000c400c0c480309220f4030f007204460301502503924003c2000c0d5200a003142c0581040420300d0030195072050030343d030200b4003100c1d114401681165812510064001c095810040c1034450061907001040000c112001c104e0150b60041090140041c5048032450003208552240c0400c440c65511038807a001c1d5582c5c80910300d41c101003082d115041c3d2640c44120030011690a100e990441564a0b54081080102003c14401103412420a500314900a80000d44070781c03049618902c100d0a481010420840b540b0ba07031020100c0100509141023075850402c001d8401102c540b508a01c507502c0d10000040c028040c80880707076001486109601940c40030003055a0600c24004015030240c614107092201d01c01c15491820000d05001100502c4c504084000e0700c81c0701c00342d913011310 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 835966366 1250 835965116 835965133
    0x60c01150815010905130f08120c0702130e060a150312032f04031e14010e100911060f04150503010306060501030e07300b0f07080c04031b08 62
    0x907012800035422803544540300c0c5180c0c0c80704021800c030358041d1645a225a0583e02c1440010b03180d42070500218000d0201030b0509030500700c0c01200403422030740070f100400081540811420841400d0340f89201d070b41000c0c06000c502541d4181d581d0310090004441c1c0c0e072180c01506111050309001006990032420ba050310303214403c4043d018144004624145070a11180e00c15908207610f65007594002c0011000e180a156807220700c030700c000f0402c0f10604040400302da1400585c0d50f81010035622810800070400000e4038480038101041d0f2565010a01e00300038500e00055095070890003170f96030807201079464052609170351807903018641010032000c009806407040d80da04440614101d03840f940040c06943c0e1500011000d490710b189801460b0784c45042d0510414452908800e0300b0000081c02041c00c0042c50401582030401200030ba42c01c02120381030100b460701e102c50b455032003503603401d01c10010300708514080c2c2c1c0c5100385d2002401d10044c06d200e280d014080305001f10003c0008204861031034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 835967616 1250 835966366 835966379
    0x109021c3207021204081209040b100f080c0f0d05041a010608190903020c010806150706050f01090204060f141e0a031b230d050403170105040506060306060c0115 71
    0x300300b80e0b00d0101610a024120344190004012201910710b808080c20f400a00b0a108860079005800302c0d03a0700c503890f40703070740c44140d01d8403c0e0810f0803141c2c42e503680044250800d170141050a0140150030704100030030184030300343c05100c103c4140d03200c1840009403640c0c0c0e5042c500f00c14260b100d120044114044000550180d0011500d80940d081044444081951600030400c4407149400240907802c01d02111326258003402c00540d0010000d46409150f8800c0070740030a2a51124001f1680c540c1d6880a10040318030310a119405840c4114046141c00e040c440b000e04902c03c84004c00c0100111501000c0703007521f804040c0c2d070f51304103081050004030200890500141d00200155400a454590a03440e40c480034041c084411141d5110807101c50390102009942209448c08041c081908001956542c1040c0c480e030380c401c0d80a640c1d1284100c3e0144d8a01d1000ca078180c0c0000d101d541085d051042c030b0713540e0908030707600580c080b80c0c4550740740180d8051314090900e030001c035094002d5490002426 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 835968866 1250 835967616 835967711
    0x60302040e060106170609040b060f04050c0a1211030105100309080703080402040b100905100903081204050f010902010e041d0f030a0e0d0b0406092d0b0109021c 71
    0x1a20266200c01d04804c1c8104840010480c1c111a026805807c032404180421500c1c4035460300304002a0010100724564004501075074000d44250720842c10010b194000182e120301444501f0708004d1050240a0174880c0c01c51242c04180541e42c40740b0300c0100d0403081d05010381e1106541541c401d100544903045400d000d02502c00486083c0d00484c00c0c56102940b03403401041455807155207480c1ca5000f6803c280a0111400c08001e1a0050019804000c404600601c0207898000049003a140882c0380034640702e802c0010900f0003c81d1a81131034061740c010b03a00140e03242100401030710006481c01c0c1c1040c03c50360b1000b558500c40001c0c000e02d150a080740002000070318034080b140d210103003403c0c100010b11100c005c00c80f01c0036148103481c402280009001d40c0052000c14000c02d440f1302003500d440c8820b41c0c0401c440a0401c0022030005e08101000010f02c80c050060104010071814200c4021402075218400c103421031000d036458034051500c1344d0001e00c094109041506c0b0a08401e00c28001040 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 835970116 1250 835968866 835968869
    0xe010906050609042301110705010c0908060115030513150501170c01140f070b070e0901090c020615060d0f0e160b0f0c1c031a100203120a060302040e0601 68
    0x1401820480041c20600f8800d161501032940005105419034190000d9203d04445c0d4030031141d41e548581c00490701c2480140a4400b09000d240002186081d45001520300e81050344207088541245004016001c040c40d0380401e0100613080104403507691500c01344401c881014014461008012500d40c40c441590042d41600c40d0702000d00d8a01046002485d90313035420505150004007070303ca00c985845000c02c05003030811200c80802d030510100d07642d0300441d42801c890242c00540703059112034082c642648210300514082504000c0e109502400079100c02e00106070000d02400d0001c100e01c3d9031240c070101c9081c26044181007080500035001031025021102c0014080d01c1841780f0950415000d491010480303900040302d038607002010031010599000055901400e025546095154001c500408440c0740c1d003e03a000212511a0f8000c1180e031190420b001c0e0003480301806110a4a4000040343e0080300b04442d1000c841d61124480c83c041d03c1a5000290014284440c404003002c00290720ba0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 835971223 1107 835970116 835970123
    0x10b180f12060915070813141e0102090310020a1709070503070e04050f06040b06042703032a120b1f09090b0102030309060708090f010e0109 62
    0x5003030070b00444a412240c3c02050a90040b02c000c000c5603640304882c2c2c10402110b081942e103004c5078203413120004107442000c1088040954080040b07240c89010758281b404e19449102d181d50207504015042c1e4028460405540d01803032460096584800303c503a00c6061001d05000c01c1056078038040c1a10010707010300040480d06480c280f0107280a86510180b003855400c00e840d009107080080b40e41d0b051070350840c0f02440006032680c035603913401850840380460349182c10a401c8a0307152421b92541171a140c0010400101178268001c0d64a4034611564000c09048802d850300c4a044000c0c0100001118034032001c0f507154403a40030102507800035007122040c2c40394070401542d4045032907410300810b189103402c001c0c07164203001d9412540d800380301940c01c1d03081941d0741c26502d042c0a001d280a010070700c0300060301d131501004524048440c1c0781c024001e000440c0000c0740200840c040c1034 = true := by decide +kernel

theorem cover : BRFrame.Cov 835791366 835971223 := by
  have h0 := BRFrame.cov_init 835791366
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835791366 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 835791366 ≤ n) (h2 : n < 835971223) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
