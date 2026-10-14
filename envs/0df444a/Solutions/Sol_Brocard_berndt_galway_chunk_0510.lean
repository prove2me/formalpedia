-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0510
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:10:48.954594+00:00
-- url     : https://prove2.me/submissions/7a25b377-3953-46e4-8369-1c613bf655ba

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 91546763 ≤ n < 91726619 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 91548013 1250 91546763 91546783
    0x90b0a090923120f0307080f070e010f09050d050a050d170103120201021314031b060d02070302150405060f010608070e0f0301021c05090f0f0d3509 65
    0x8001c40e41898650a04003202040550040b54465140c082e542a0910010403c6000020740c0b680320b59840050000d15041110000d00041c1c80d4400030b10400e4204203407034018082c50302e86000500d0302e076004460300549039411606001011000046a0701d401c030046e4002802800904a0b020340780c60b0150070008460446010084002081c1c2d8404031760480250440c0c0d446403101c500461344001c180e01a00440511030a60307841c1c2503000641c030110300ba46080d08441101030b41c002c000d843c2c40030789600c0c03140c55550b0b0b0840401e1112041d8000d00e60f00410302c650003401210540300d45c504000a070198100c0342110203400800511030300600740d56180307001d401d003400d02d64214030f41100000d00c0b411454041d00e2080110081541f031603102035046038401320202c4900920451404444030241605881c042c415114400c888402090007145064883c00840c020f841c89017003494049800384114440307402d000500d81c0090f484820300d058220b0510040d00221209480d02c54180d500341405c102c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 91549263 1250 91548013 91548029
    0xf060a120c170f2e020d050103020a050d0c050f0a030b0c0d0f0903020a02090a0f020403051510031502030c0405090906040302151603050901060b040605040e060402190e0f0307090b0a 80
    0x5098000b02030707000319a168030100000c44002c660760a0001e0813034203184038200031810b213100190400c04044140c02c6503050340e000b541c2d80510035564806025915060349005803082c170308140240842d2601e41025a20250000c2400304803d442c2e44401c607031803a00395007210400340000380070226480c0d507019004415003c084208480401270701c02944030112180000d10504903200042c12241e50780d48000900b0844030403c540300c07030326483c01d590359040401091090803108400600e0710507031182014240c0f0340c01180d01602d00e1003000c4400103074001522403440d0f460184004619070300d036480c01070304ca0103412000388114206030070080e0902011815124081c50358204002020032035000c0c18074100c4c480d01e4005203c0c0e54444d42103004150903089440e450600040000b01158402d001c0e0056404807901801c580d00c6c1c4800b048228800c04201d010f414100001d0920703414082d56180e0083c1e4005000000082030750380009082941c01d03000000c16542d42e4800e46c140303081510300800504645 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 91550513 1250 91549263 91549273
    0xd18110d08090f12070f09110c0a12120908040306050609041101050c0106170a1202070305100506010c1a0a0b03010207150b1c121103070b0f060a120c17 67
    0xa8031403900c544180c00e811030003591007100e0491035031100c18001492141c0c2c001995101506c0c0d03500c0008524151044c803a140313007004800c1e01010071030801c5403451200030b0000d1500c0302c46651000c1400e000401200306000c941c480110f0f500590780502d0131001d00c01e10b0200c0e915825407600c902269000b410b03032409814101d08003c0040d4a8071301c0c00b8090740c0f00342003080e10349102d40038113409041a03030044d82011805002240d11500005052844244512101d1105880b6104126500c00c01448064031546c4408104d403030901040d8440d41d0026010300d841701144809444000305204003e80c103507a8a0b46035810090380c58160310032111100c008400039407070174200d92159070400d02540c541c00c80403607031082c4200c8203640c1d00250703600c1c078407421860031010052400c0201c5010081d03510300d004140f02001494541030048200d07520281d2010424007213441d161883c41c4010700045c04160000c100d210701040200c0080d824842c040d00c01d440c01844181440741c400080020080500e03030076400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 91551763 1250 91550513 91550539
    0x3070311060f07110304051804300507080405040c020718060308071b0312030902010e06030c18040b04020721030209060d02090102031c1a01140409020306060d1811 72
    0x102c03101c0310f0741140c081e1402c2e0841c0c8140320200c60452080d0b61000e903210605010a92000c18000801c62059002c0c8000720400340000300c6010450303484284036205c0d03044c481071940f60640200b01502070309028804907400d00c1d031180040750895000701400005607019107010405042c11140c4041c403e00441c031b081c0801ca2450f51040c0da6401140002810303081c00705144160b080c80491014025504044054120070380c01c4c0c809001810010000c0e80001d035240041501c0c0c1c01c1c200202c900034540041224038052000c20390342c0c0e001425604d2254040d0b01d811002183d9036450010300005401080101104481849646a00b0401d1180c0c02d080c135005002c4440540e07100c605650542c4103e89c2c0140e587d44c2a080100d04500c20f0035030000c8010412a002d0612401c41d03448101d441c04400740c0c402c0b441d22041d00540358000358110b05520341d0030800c001d00c1840c2141e0040c1da002200a0081828840115030950030f0340c4000381c0981451000c02c0c42030f014401c405508901084c1e096030010081c9174 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 91553013 1250 91551763 91551781
    0x702011a010302090d06060b120901060509040602090409020a080114161b050709140a0e060c04050f0d08031816080304091d0f011d030910080702030c0607020307031106 74
    0x9425030003107041c0340d404640010f00d40c0710400f4030584aa03000d28200103041c0c03503256141da01d0708941c044000c10f208140029001c108148154015200020a20141d036a0b80c0c0d500e480281d40094446500591109220350040c2c0b41c59078801c001c1c0546000200d07010404d08820b01074020002c118080321010712001002150f0820041e5144148000b100f0203207140e10300705186030218a43c0181e00c0545041c0c0c0d80d2061131504400039003d0482804240000302d040d542d082c1c1e803550259401c0040f80300400081019140a490b900000c0c44040c140740441c4185488100c1c058104840040c040e12070b4220300c0160100500c072101103800c1101e1176080540c10180700d9a5213010700d02600d040030341d071507502c0b0402440908080c0102d1f05020200d6001409201116018001c06c10300201044042252010010004030a482050f030001d8038020702122044011190900083c1c0102c0650100b00488102c0c100301f8489544150526001166292000e10b00100031400d8950340c841d064100c0424084415 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 91554263 1250 91553013 91553051
    0x10f05060607020103090c08031908010510090504020306040608011406090c27060d15060806040614090619091506030204080316050c100804020f0904030903060207060f0c05070209070201 82
    0x50f4082c0380000d51071041d4a402400d01d40c154020301c0080c03102003090021130120064561807004140c1d5103a40b039981c1e500902c0710608000102002140320741130140b000741000c0d405554080c500500100d04a55030751a10380c00c41c1c1c82d030801816595400c3d0200050350071305c054825048107030082072501e040710108040801200d03405004022494100303a0103c50740d2a43c040c0c4034001c40d0040200000d5000105009101005202d01c40c00714101e0700024802e854184981030072108442c01d000c03c0304004008009990000400c0d8650280c06800b600d40c0b0205c0310280c100c09448440000904620004042c0c100100c09900c0202018010401440b9a150100580e000045001c80c088600c2139545030050800148140752a04030705408280307510180c0c8400e0031400b9500a603a41c0c10550b041d9414080000320848018004c180120410400a40d4590090070214041c01000560303000c5c007081c1d0011707110f08501ca8000074802007103540c25440c0c80002e45030070880380c0c002002002030380b2807086281 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 91555513 1250 91554263 91554277
    0xf040512060108030d0f06030b010b0a0801080609190c09020715060909120e0f03030a180902040b040510030b03030d051501020705030c060d1d07081506030303190b031b0102010f050606 81
    0x11684484040c0d40720300040c7c010350b001c0c0da88a040605250b0716034032107100d42d4201421010000d0100c1c07000203800070002c40c000c4d0084841d04090130070401411456075280c0a400d200700c85845204034002118a65880600903141c800d0070400b0141310503100070340035100706070413662106141184440006424000e500c29660403420300b195444a07100c00252100350001259805010015a500d1420780c080e81d80341008914070311000700c0584403103100702240038500504803039500803c000d001038903102042014019191801281c0400044007103411074110140f4400d106882d0803d009100200d070007080e100e4142031004200d25071810001a079110200b004481c041d0f0380014480005040c5a0041c0c00048240c2f0030800720494008802503494a1910848a143c003601c01e841c8100c82003a4111070080100030015415070312004010002c0d440d4032a0007a4030b8507a2040514495101400503801e0b0440c58480c510b05c120400c400a825282c15540c00c005045c644001c000c1c059899031b092b2442 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 91556763 1250 91555513 91555537
    0xc03070905040908070f080c21040b160606030503030601080f13030f12140103050c0a03030f12060e0403020c09011208041401020a0b09100609020c0a0f06020f0f04051206010803 78
    0x1844500d04082d041440f8050313024103c0c41d5840501b03030510407100c00901300030b40e041c2d00f1101100e507403c0350300740310f5200043d20340b004440810042000380e90b81e002800e24081040440c0f11100e001c0d40e00e4a084032810742c0200c0c0c090b000401008882c0d0307002403034250b03c6a00321520031003d15006018003e0102c07020002020f00c100e0348604401c1c80d01c84e14050048580c10401084a00400e00848030005c009210484030740c41622001c0449040c0582018126681502c5840c4596141c0340140e50581c4040300720500300380d60300b00c0044e203a14180c003c503000702c1c000e4024081c04400081481400681600404c0061107a41240800070351410704a404907110907002034105185080100e0030300011000243c11072503140c1c1444500d540220320414000510a4104002c0365160003c0c0d00303074041ea809001c11794008038401c90100d00d000c07440c0120b0911a000042c0f82c400d21400d840f140c0d801843c24071000d1030001c40c0038400d80c2040503402401000a200400f00e40d031401c6071040d60391040c070390301c400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 91558013 1250 91556763 91556771
    0xa08030a030903360602030a020712020d0f03030e010605010201020903070524030c120f100b0307020f030d0902040b04050f01050d050106080106030303050a0b01110723091602060c0307090504 84
    0x5140c4600d01c013a03103641208615001e85140e4601c5288140d0341d005285640307030742c56100040d0382e038000000c582c4246916009803080b145003100c0010410183c410507a004640002100006011001c0500c00c20303110780c0300061240b1904500c1400c541c6940c02881c19680b04000b07000540d42d00250034022540c0440e440c4201e000005031400032201070b00000c040b68840442480300c0d10f100d100151100b82550350300c022142d42c0eaa41940000350041c0e0f490403404058803014001003e011005550003a0340780110f07042140c2d44601103146600a40c4d40014040e40e4081c40300840c5483d0184404883c02120181b10303509126080d6010100f040c071070948036a0710f46260604001080d00b2100c010207020b0004c000c085d58a040281c094101114035814440c54080c2c0130307160358000c5880c107a101010800910b02c640c02d1581a50a00041c0039005400685d02c00000010b562001c2d503d911604025840341c0045480c040040e240c050042c3c0043c2941c1070a0042001c42c81d03000680104a40c0c089401003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 91559263 1250 91558013 91558031
    0x6030c090f10020c130501030b070c03110f0f0c032a011202040f090f09030c11010201020d1d07150507020d020109050409030309020a1a03040b0a140901060806060a08030a03 76
    0x565452045080d107810100140c2c02c0840240c02203407a003101d0406032040d4400601c40040c150807030340240001815203851002248215200e4098503240e9442400e20444548070798091501d40545150074a02a900c42414400c8405003072020301d144007815070081928400c41403078610300b0702901909807150344000241c0b1010380e1140b003580c110100d80020840d51036840b071504600c0c540882c06088201414070321080e0500010f8800c0407042501907413100710140080d0b50705025003546015450446d9001d201c01c01c0000c026200c1d42091410991000d5900c2c48280c2078a424081c0581c456a00c543e00890b02c0390080b070b0010101c07000503604441000100d841440103a80540a0343c00035504103107404200e00030503130190301c195000e5000300c941e103035840d50f2039954845c058183c41c24089802d2050000c00c0c0010348181d5500c0d008140036202086072544c00d004010394040460b00c07844a41c0d150b0348208100341c0d00f40100c4e030b0052020369440c2c16460500c0c03c81c036038030b11070310701d44e00e08050b907596040c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 91560513 1250 91559263 91559269
    0x709141b040e04080c010b100806040b061b030405091003121101090804080a0c090501080304030308060f090c03160905010c0f0c05030d03061e03021809010b0310020c06060f06030c09 80
    0xc40107080003050100d041d007810304100405401440c0e005e00c031907290550f0355400d89091809510424000e1b50303640d82940d5000288005482c140701031507000340e0140a50203010b24403400c800e1403000c43c00010740d2940d180400300224030f50054800714562081c02c40c00d00128215030f03080b0b0039009203401c0201200340c10715401c50040c440c07401c000c2c080b05d00200d00440c48203000704514171000d014100745400300d5100d100c01800c50f038080c4101081603004000820010b40684160340e40004014184907850740741c1d40200c1d4003000201c030310307800c080e0300042001f020350110742c00142041c1d0740d45003980a403401d005c0060706000010002803c0c50b180102040708201400303440c0070103070070080c054a600001c00f0790701034050b03e058022011040d161010043c41d40d00d0301c002c40001c6030740040c60021620b0160101d40740913640945a00515500c5401c150034644080108140720351429400607900c41c4200c10700782c00c000c00030300401c2c42002030300e186182903510141543d07000911041d9640d5541b10403000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 91561763 1250 91560513 91560517
    0x303041e020a06030c0f090810090203010212040303140c030f0103030c050c15091206090a03030207150501290304050a080d1808030702010e06100303050306060405210709141b 77
    0x2940300d8031100003c40e034140d258200c814440ca0544800c154080d1105054840010500032101298019040880c1020f207030741180e102980003600040c903000c000941130f16014021035090f400301e9162912724080750025071650385d0100201e8402415030420760b0324103a41000c107210150400c5441030b003203024450107011010100100605001c1c3e4580c401e0320f1481c4640003001d50501c1405143e40400c07100c2c00c01704010707100d05102c0002d0720b00603405560580007034005840664801151007102448001c941c41500d019203202241515000f030b411044803051440300008400001c1c05000b4440040d00008580050990180311140ca9030618212a0018002c803000303410003034200f54100041c407000400440c0213041507402404154a0320030200e03920b04003035403032104c0c8480c80001000070a00c190040c1da0016401004107203441c0d95140065000b074503101c00880011804040c400c0101006c00030700c00284110740d014070220790b0450403441d118100a28980484910100040f103803090901 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 91563013 1250 91561763 91561823
    0x431e1e0e09040308180a02030a080310182703360e0f0603060705030a0e150108031b011514040e120a08150d14012703080a020c030304 59
    0x340e08110328243c2001002000c060790400302049410300100302c0c4200109802c041c880d0050010240400180c0d603101003a400141011002c005401c40401d070764140d05100d074000e908407200403175194600e5010400c0e0100d00c00d2414445e0718541860780000b900954491080401c80d107003011000703001001280000d05402c4810700e824030300039000c511b18100c0c0e10040c1c0201c680b002c054055035920310500d5035480096074000046042030000907802500383d0094512100302c2001d42e00c050760401c90100004400b80c0003800b46801c08076003142c40c5c0c080d00c00101c40d600c0d4400c00a02020041030b080b6194001c1078015000f500c0da80e410200c2d8261920b030171000c82540c841040381d415030421801e000187d0050708038500000e8070000402c2d030103250407454040f6040020300c0303409a5a01a61030f000c00c4c5d8950312944cc015501c64030707001c1100351041d051102d4490030641482040746d440c6401001c13205c0081a44c2481d0f071052018030610003000003038aa10070352240340d00c4404810581e50400da1900e0740 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 91564263 1250 91563013 91563019
    0x204030c0905180d17090102130b1809042f100c060222030209070903050d111c0f0f081003030503130b0c120703090209431e1e0e 57
    0x4480b010b03001794000f00b03a00000300b010411000301d8507840c41131420303803107a0032031381c07140d150440414010400b080c001084d0f06060b004c0641209518407000c1007000500300c9003640c006002d004440c00015441c03550f0b0070340c0240c240c4e804001c1142c080015040208007250482040b902c00c2c06941000381c40d0341282c2d40d079207030700d403003a200045080034088100920740022402107804002044042c1d0260600e8400e0700c1d44031002d0000303100d81c044122031500c0c02891443c802d05c200144c854a0704621511500b01c4003031030341c5018042000d0500580002408036038030042120000400100c460402400d905480e410300d4255074940300c01d1281d5001590141d00902108074403400d204400c02c949004000c0703c01c0e000d03098112555525020b508803400c4600117900080301e100014a143d00894845034450340100c03408160311502c05d501f8154030380b04140661a200445201ca5010f500164002d0b501c131082d62584062116207440205005101c5c48420488940103001e040e403e030150020300c1d2954006 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 91565513 1250 91564263 91564273
    0x3060721020d1a03060c0a0503060609060a021005090706050313031404080a020102100507050306040504140102130f0b13140102030405120109020f0a050a21060507020d0908010204030c090518 84
    0x450103610081003500b61088041440c10f0f8406100c0c140840c0c02441110840901d84c02c101040d10150303860360004000c50751019082110040c1692200060300b915138083c0d0042600388445617180701211000303403980310160b0055108210307103680842125400608007001076100300e500c0c6420b880544c080c40070040004804a404900c81c1000903101e58414000d078200c034140050504200c0840318142c42c20720000d4001c000183d00d5081030b41019400c50f1145038840c02603110740060a0032600f0000050703039200ca9031041000030303800400a2401400340d103e4000d20700710702150040544005441070090b01854100f440d41142c1c02801035800a04000d000c621820b003000741060700070043c400c1c040748141c18030806010641800b490090603202e010b0442903c107824214003000c800d01c1e0b41a00f80606030340c2c151200000347c007801582e001741e070503400420f8980112080076050644540141c2e40c2d50380b0500040001c51000100c4500320358900c500000c0d02c1d107488188079007030001d05400580302d100e8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 91566763 1250 91565513 91565527
    0x4110d150504140901050c0a080c0a020708070b0c07142b05070e04051b0f1c020d0f020102100203270f070806060f0d0807111210020316030504020306072102 69
    0x4640c0009118208004c020042a41e640341c0103a100e000b800d920300f0000e84107a0024001c000103100401000c4003c0c011110301a641d16025881c0141c030b50440490f02e8404126060262001c10003c00a02142c80c071420b10f011070748010440504001800186510100900c5019030f668034101c405240c1e080410382d6070050b15400312760b0400030251422105842000002c0707026104030f264100790b180c0c005040c080401091000c01500711001504101c20014070701d400310041c0e82c0c0c40b400044943c030406a03240d40e0709030f80c0000b9080c0a5800d100610752401002000380d01c64088014882105d000101442000c8459060502d044200c3c070007051148036040c0003180352480040c61a21551003260f844200d8904074003403107010a11080c008140031000c4c001403000825a80c6440d40f0341001070320b40394610a1000c00c552900c9a40013981c1182c540c0003044c4801d14001c4044010369019a04041c8001c1c00c150340840c0c1c1d1140c3c001c1200003040f031304912030b01503209a07124112150b07031002c0e010354841c55 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 91568013 1250 91566763 91566791
    0x50f0d020613031b080105040210030f021308010606030e060c0d0504330b030c03031b010b060f0406030606090e06010f050f0a0905030c09011a030a0b0406030305030f0604110d150504 80
    0x48081d0b01301c0700740f0352038850004503c0c0c2d05000d0703e445103a01400c0d0407a9000403002c15005488c0d851000d40a49400780500911002c015003030030000c104c1000080f03503651814901904483e8080400203060300680100405100706c2d20440342000d03001000051680e44e80e04000002c03041e0845e50050f108419880e400c0300c100040444640f241a030013080140380d0a16040580e211060700d059609504244010550800f0b04000c00000a00c81000440c40c0b80e1514000740c01c7e0b0703025001c440c00c0444089000d1006540c94407410018200a081c114140741c200b006c10f01d51b04100400060411110036080031242d441001130f07074034600394141031946a200c4500044c0022040d406000d0181c0b207406200b01440c80c00320055412a0318240c0b00300810100d0840001e01c036400108039070280f07903c60001628035102d5100720340044d40241c0d0b950f0b4590402181c0509000d402070030440c0f089003003440002141c4010011102c404440420010303098000a0700c0342030b801d5066200c01d904c076141c4040001111 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 91569263 1250 91568013 91568033
    0x90308070201050d0c120e03160609020f10120c02030f070204050403090e01090209120309011704050321090d0e06030c0901030605030703080a080709060c0b0c12010803180a050f0d02061303 83
    0x41410101481102e41c44c444a44d603900800d0030090040101d0740c560320105158be800905441d00107014940d20344448004076500382201031907800015040c1d82150484813952080e01c0d0761108901c040c504c0c00100c4c40b0b41c079040c2d0080c140041d22540d5a54045400c142c012030402c0300601400891301c481c1c1d0394401100c0000d402c8101075501403910303031041509240c00442113507000ea0050b154040040d284e484110701403540104101c403144000c002461800728078045410295100501000c03151403c81d03402070a18580d0014141844403c941192540e95105c0507203512079106100300b41c440501e600100c02610a65100a8040c09100c0e000b00501000d0401000e908001d0780390800c181d00c2c0c0d60f0b07080310040a079116030310004074841500000078a40c0c40c030880e0072504032a17502d0b00b4001c074440c669061000a92140c0d01951000a0980c00c0402e81d000854040c00b003212914405860280401c407041890020717036214544001c0a0800c540e1207400f40c1d4001381e000c070301c402080e6483c1c0c50141150 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 91570513 1250 91569263 91569287
    0x50403290a0e070e040f06020c030d15240c030518130207020f010503040f080702040e0f0f0708031e070302190510060e0603100906291302030601090308070201050d0c 73
    0x600a4210200e4800702c1450030601032544206d00320149000307a11030300c00940119001410901080090305040c3c1c1c85406481803140400b05032103084d52610b0801142801c0d800d6048144502e046e0801440e00c3d00452a13075911505414032954802c4c11010048031a0303418814141d03c5501c0f0303141840180c0041c1e000d041103034400c0c0c5100e180c40000300e005660300c2c0011034000780700e000f0030580b000c0041c007440c01a0140a00c00b400104280352010109410b2606405040483d64072114008000500400c0780000030b082d4074020b13614056a51064000e683d010303c3c805800104006004030405100700301c41d440c0c10011007125514284103203000c90306c0e20305200d10000400c0c02d0100100d50184a0140c0a001c1c41c4001d000f42248400d049410000d4108420b040c0c400fa9921085182c40020100d5400501e50902401e140504003030001c01901810b00e00b5011030341481402080000d98111040e2001c0d01d400542245d152030040c0700484080c03080030195244141420b00046045410480307640b40 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 91571763 1250 91570513 91570541
    0x131121060109050702060103020d03230d02031506090609120a1a0f0610050a03051314030a021204030b0403050c0115090204080d0c050304050423070c03021501030201050403290a 78
    0x3d40c1c548807001c903030781c183c2230001941c0700f01216900d40002c0e010391241d000301002110404d00d0841c082c0500184c030380001c0100b00d1780640000400140d5100401ca40c410440704071003443c107050804009c1902409001740c4030780a81c000b2100170480c1e51080081c400c046500c01029030041b01040341c04500400151030752916041e13004c02045036840c1c00d11584508407820341d905800d0161280c0100c002d46409042c0400061080c2011350129507800f05c0d8083e1408c81c10003c6503120f00c40702000b0f1030512006070b2139941b0041400240005000000c109801c15018541305e6100c84003002e056004240b00070b040c41d2904030001c070005524020381c02420443c1d030190b0130785422400038001600d03900710075000145071780c00c01c200034002458198003148404280c02d640300004091180711544480040d41c204e004510386d51700e4107040550401c04c001c844007035004c44070095491940060903502640c00014200d0381c0d20780401c088088000710381801c0c03010f00000744015042034008076004002050010038 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 91573013 1250 91571763 91571771
    0x50405090c0712050306241c050915060306070309030203160f030e06120708090102040f090212060a06051608071a0105011e09260a08190305131121060109 68
    0x14a103001d13105a82c81603402404030b00749080c1440142c10344840d060b108158444041c404840584885400080444100d031000038a80c01c2010340301f03140604e00041e034510091010204040380d02c2c00304031541c004134241400319041c40305190a0781503018903540d0354041c00c400711018062180b258080b05850f8085e8840c2c20034122801c0610200744100110300c2c81d05104c0c0c0c0003040015204654096204515400050405840d07100360b001d0801207034414403100741c0101d2101c0c040d400c9035000701e400c000100e554198203498614064150701030203114005401c80154400d0500442ea82200c00c034175030050b82d400240c40003024690300120280141030028018607000856071348200388080d401d906545070310110502c0c194600348030280e0540c4501410030036019250040c10200b11038012181700c0c01c0c1701d41c0c0340c0c01000c940034203004040b0003c408060400303003404413070881101c107605990742000d8411180d5038400301284e0706c4402143c55032a12600d85180c000381142c0030441c0e5069030040a0140 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 91574263 1250 91573013 91573043
    0x109150504022706090601091e2402060a02160606080321010515070203070b0a02030a020114070801030f1403041e050f0a0e07020c030316050c0d0809060a050405090c07 74
    0x210750342c4940c10300d004203103540ea00440ea139490030091040d4820b03014500303042c049444002c280d491102e00d6000900c07001003c5410300c0811911520000100700c541c0001c0702032015804020b50742e10000c0c00c14000203a000440c5c0d4044407007130018115441c0c011300c042c0101941d0702e19556603039210319409181003610142c414008c08070740310001d0480300700411040c8220901402c01d2000d0b03004207000c0b64140b1a0710710005006a001015009074107060f0091030f121404004082e003521241188141e4155007841080040c41d002030000c1d040d03a4101d100d4842c01041440e0004981d281000899420b11007c140044c0c59a240030070001d0800e044500c41003280d07035550902c041075031a038820b958040c503003140c24498000d4044403c2d038807400a00c1150f0720500080c000ca420b41d803002080040414440740c1340c10510404000000b1108001d50344904210000c0c0c07200441070090503940e62003a00000744140c40e0302e00c02c0c070544014140080460708203080c00e2101c858a40e0200d4800c54074020740031148 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 91575513 1250 91574263 91574299
    0x90102010c080c0d0b01020f0706020a0309120302120306040209040629040308030103141c18081902100c1a0f0907080c01030513080304060f05060607020a05040b03010915050402 78
    0x658050304204018606000e44c103000d14000c0c1c00d00880b00d0381140f02d08199025526800c00082005001980140c0784825660400500380c41c4550482c0c40c81044400d004030000b5400502040b80c1c50381c008485e40c507a00d0302c07030005010744101c8840c1e03030340701d0f00b41a4017140c0000c9588000c0d0321403081440b0720b18071256442c5036143d24041c500c030107801c4181c144010008540140003503103242419000782e4240c1c56190040c480d429503d07640301400200c034020031005141d0a1201103014100440080170f00301c7c003400da44e51144040705002400b0307001c20700a819134240540840d40c4400e50182c2841105658000045a0420101c48078000c044043c0081040381401103100810b50708620050320002141c80300550103898098000c080c6c50714071040200105800c94080c60089100d503001140c04504e23400000142e500c048d00740c80c41141c04001c0b9500680c0da82058000720703002910040303012000900064014a4000d402514400c801c110b28802600940d1103184903d1084032901014090303002c80b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 91576763 1250 91575513 91575527
    0x91203021c0f0512100f0311011805030616030f0c11010c0c0f0b06030705090a020703020705040b030c090a0f020307020703030f0306060503043002070914060603010e0c07080f090102010c 82
    0x240201203942000003d03140800c6898450744070000441c4c117813203582e80790b0074181c0c20350303442e801613461545190380b0102c0c0c0d43c0c0c8902580c007101001070f014103050f810900025182c00c1c2c00f4003204044000c0340d42568405001e0b03000a01706245012082002070348000c406842030200b054146180d529201c0c400c0c0000c0d006225802c461508144520b02744030003555441c00301c400103000030341d0601c58008002011380d03c080600340710344480310340583c452010b450040d01e44200e90304014412420b00061414944000541d002e100204440640c01038030340301210401080c2c40c14442820360300020410025540005021040381d119696280c000052920114100c1d0700354015180020b9041020031f021402e8038007150301c046540c103401da66403010f241e24104030003070034008400540c00c035900410042e11648036151561029500b800c255142050001d80c05202c14014001240000004516602180000c0d90390b801e500070101c990b1528018070380c00d2250030a0000d02d00542c20034044926583c81030171 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 91578013 1250 91576763 91576787
    0x711070b0a0f11032203030e0a0608060415051002063403020c0312010f0f060309050a030c0311190b060301150311040209040207110f01051305040c091203021c 70
    0x81e4a61002d541d01c0800c440380ba00d00d00b5900340510050007a4941c4440c481e00800c000321004d0320742c03001c5034a946000703000000711802d0a44524002c40080207500e030001c03440d56201004840002c0d5061a0304140451000c10b900301c160840c0c00071080d20f268a0f000665a8043c2c4440076000a0280908581003204401010124009a00c4e102410004c500030380142c60301c80882d5050b6410032451001c00101c1690917406000c42e400c2c141c00401524540a04450142009190902c40311515484041c0e452080590013801c01280100310018544135600c2e2282030042d40050310340d0b405031180580780c0344500d15801d9031410b503204045080c91605100700310030000c55500383c10100740b43d5200c10503000c00400035a41c11540811100740c807565036200a00321750b8410020500e10611800c20320505c600c1d107444503814044100402500d02c00210803860840304110342c0401e54183c610320848013280c0c03a6120580c03030743d00515a081007680100708441032040004010501000340b010455241209903 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 91579263 1250 91578013 91578017
    0x915081c082d040201032301031e050307020609030106080d050c0105071b15020f161401020702061209010b04020c0105070e030613080313212601050d0204140711070b0a 74
    0x2c2d001a61825540c0480d881801410002011941900340343d0300c40700c14882d403181295410006108011aa19814094461019613880c400c4c84503941c59a4901c26880068070600010404240741e03a000d4004074003500603401038401c1050030481c0a045508406028040c030750070500040c22281c441c4030800d401c60001d40c11410707060302c1c07911000b43c04043d182020010903001c000c2c00d080c0403510002440c0b8851522405034401d6900c2c244042291882c100a00569004020720700242e90f580003a1403c116200642120325140c2510050050100b1044a9000b50011501141d12b0301c2c10351261b44100e40584640ba401c0740390300304042d06c4103c101c0ba5128003203032a40306480031903c0d0350b0155a0101c80d1031403005e00c24480d80c407191403001904102c01115401c51128208007940800c4095544030001108110500260030b468500e1105000d628043ea403003481703080c19596a43c000c842402c400c00031407045401d261100510540769600040910304c2030010015400008000f1a03c48460355 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 91580513 1250 91579263 91579321
    0x150b0f0a050409030c1403120108010c0f0f030e06010905011410021905010b0a09020a02070b0a02030405040f0b0411030a060e0405070918050610090605010512010915081c08 76
    0x101080000804481c80180d08000c101441d400000e01c1140f600b10703681c01c1ea0f000460b1100c80b10084081602c8e03050300300c1c40c060790500000da52a56080b04c1990040da000d410201c10025134030104500a0100d200c894001d413041b680000392140f5a0743c0700c1811389800c203610444000c440d1046c84061500d080703244c801030303010307041e8000008100d00702041000c0c811000070880c00070341030000c0e50400b15a0400c46800e81c0c00290880c1d0700e070f010803500c030081c090070400c1c604084038203001944a00551190500490321a21200000b216a40c040300d181540104100190b814444201c00b481e0000c68001005520f0010007203914161480f1017803003941d1100c0107041c0142800303800009480b8582207010714440d04500200001c40521595108510505054034a00d2801d2440015103000d944400e05110742000100d80d080d030107840c540d054440065000c904004071020000002e400e070f510011481c01200c0740b8155030007505560a030405440e03580c04240e921040460840b107500030545640702424 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 91581763 1250 91580513 91580519
    0x504020309010216080307020f070f27020307112103010306020f16030305060a050f0d062007060f05011e030f0201030f02040815070315050405060402070807150b0f0a 73
    0x54005503444460307140050f00b4400d400b104010403118000c000c541c019408070801580ca40c5c100403410140c0c40520061100500d007400f1700084500b140601b00340c8412402002942803003c4945800d42400554210f65906d40100001e290788007000030920a409204111070000f903041d0b042c0101080040300461569295035180c0d00254009044402c2040c028070440c038580d4456a680903009000b500c01040c9868000204007101034540c005a01c10800350008015030b40b1a02005092a0351040740081c900c8a5107400c918403070030074511025003503400142c01007000802d03081607802044030b000038000c0e039032141d0281c0281958950f2039402c070007040504102003800004150203050041c14005200004010551b041c0d03401a000142180c0c4101c5191051044204260381d010351a40340030409901d103250580358104040c840c8034807407511000424001c2e600c0d64100c8254507031154100e0340d00d100070715002c4144100d449401c004285032244488990030108a03030648c41c0001440c507148070341 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 91583013 1250 91581763 91581769
    0xc1f080a05070f20070608011401020a150513050d0c170a0c030804150207080a02061302011b14010504111203120402010302070f0210110d030204032102030d060b18041505 75
    0x8020080c142d0803d16030341440b080540144545e07800303403440781d882d03003041d41c102075640b445c600d01050100d04540c0007141000100c1d031300c0041039110039060030740802c450305c44186600017a9100031002d002802401000e4a4280d008540034908c0d5204e0026154960300b00802c000685c000da088400105030148290000a0710403e003013a4043d1040002c4601c15401401102c102d0b00017000c02c5400c0d00f40019031040030340e0108590741e4081940c607040785030212070785c0c0006e003118203000c2400c40d010b46408182c800c12904004070201001c00800130881e6181c1400d207000e10540200c603090058854511520400101008850718070900081e2070302e40d900e81e680114000d5100400035070b00c00c251a41d03d01c005946105100c680e1803482c8c0d8a01d022013030b501c1d040504140c01301d031049042c0740c4104010000280a240304603400c00b000100f20203881c158101c26415441140514202d5520300800443c080c24100f000d402c5440c61000c03a242c0100c02401803004541007106000109003060700300700828070b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 91584263 1250 91583013 91583027
    0xd0e0a0509070909020301030302030702012c040f0f020c0c0f090708070e0d0f1a01061706040905120d0501030b0a05010315050604021b060105040e1906020c0c1f080a05070f 76
    0x80c240d1501843e8280c0c3d6203202da04036082a0000c07401038000144020540d070340b1031801d0b07014110310315840d489400104103c075003001503202c50354011a2107090140241010f80c0c8402c00f00c2900e00402c3d907440341e900000c135803100e003203052180c455240e44e030b0028a2400e02401c074901c112440d0b10f840f00c0301d44411b1026200048442120341e40700c8000140350001505180307803405894030640c0d0410140c080b0ba1300c00301c0401d2058000204011951a41c02c04002e202000e5681001b0192000030300341c000d44c00c0140c24007482103000f29030b41000203008160110103521640c106c07030083c0445192038644085c1d400c203840c1e00307100c042c0009203080c13000001015240c1c00160000401007006190000b904404000d021442c82110055000100104058109406a00c1d6042d5040003d00600c807014404001d00c1103c4240140c50380350301052200e6070503800c104501c280507004000f402d0700c0c44201e45041401e01c400c045480051040c801003451900700d0b00580b8007a040f1500c61070b03405450b01000301c03441 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 91585513 1250 91584263 91584271
    0x3021204030305100302150307170705070602030c1210080705060a05071209151106061008040f030507020306010306060503160f12030203040e100f0602120901050304020d0203060c09030d0e0a0509 86
    0x4c000d00e001c0020041c0c2d143d06103008501c00040b4041e84a14040c1c034041c08104403c8441c1412292030810001c03190380c4901150141c0c0e43c400030050301c9844920b05880035004000c5604004a000c03002e000d04c50208010700c004981c810404c030f80000741c03035605010040c0640c80049010423814044400001d008694880300007144e45001406c855540304801680c060480c0030802180d04556801c1158000b401075590010f030559030480700b0280200c00400802e070003000904030260703004401003010702c0740d401c548003e5001800c45c4d070780d56184d00b840da0050006124052282c46807128418806d200c5029040c110b442d03811041030700d6458610403111180320444103d046000030403004c02e1221241c3c400501410002602d01003143c24900b200d020006203802c03400c103660103480c0710a044c019078030803100400e00a280941d200c0c5c50f83e10103d1582034800200075494015a420000211117400c05001403540403412260a4241d0050507100324000c0c000c0180c00520740d103410302607414621000c82e00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 91586763 1250 91585513 91585531
    0x230901020102070f03031a030c150903030c1f06060e090a020a1b0609111e061c0e15060607051207050307050a080307170c1b0c0a0e011503021204030305 67
    0xa42005683c1c3c0161307100d58010100c001c41e5807000c21038540c006650420301c4108065004204080440000a1128003c1d0003006c01030320300007581580d2601c0a00c2542c0b018124041103904546c000390012004081ca15880503a0516040b00080c1242c81fa030442e0303248000c094549003d81e03e0356042c881c06548441c3e003941c06d01030005903580301b101d61480c03000b401030b025500000d0100d01601d40004020001c0d2101445540c4000c1c46088402e03410886240c6030000300c40265541d09001108640d00800c500c40001c094030300701c4414681d00b07005c100200c50703030060000301400340d03500c01c100442070150000203015a4031002d0310800204014009011060054080301e041100e503544062801c2140741040307407091070110510202e00d400803180c0c50004078049000c11645840b4070790f0301e001e01803a900703510742c1c003100040310065803001e10592842c0f604c0a4642803500c1d840c0e6440301c00b070150038461202c2c1d24424400000c981807080c400d81f0004400211b0302a010349481e10110081e00000e0001c01e5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 91588013 1250 91586763 91586767
    0x50405061210050a0308131406030f0415091214040803040b0f0405030f0a05060901022119020c01021b010506010f05130b0a0807030c1103041203091206090b07230901020102 76
    0x945540d805131020003036100d00d0410b5a074600c00502610107141960098103509028181c0da2095514802030769441f1500203110780f030641e41c0781002c0c4002d828000701610031501c2c1c1210f441c28800c0e420190040203401c0d0301d85d03e10322500e480f0130f4070003842984900d01c540d40091005001e0003541c40024140e03a1501c41d0101d060546840c00a03040442c198182c1141c1d1b40f00324807003c2080030900030380c0e40c491240c000840c241801c018015490502d40b03080a6082e0b0a4a80080c421074031542e0306030f0395034844030011519050150b80c928001d5201035198001c1c030f000f4201c0032911400500440d80304040603540c80c0c8200b0b16410003958550400303031810035040419000402c1005024019080141c0c5a50307405842d410300403800b078119600442000104100c240d844110160b0010403203085509030148400103090f1420219495100740c3c121070080d84810701000148040c9400200c2124000c5210304c0168481c00e9042c0c48501c3c0700707694202844070111252004d10f800c0401b402030450103000241c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 91589263 1250 91588013 91588019
    0x7030c1a070507080a02090c030c0301050d03110109121112090405190203070201021201170d05030c070605040507080609070f05012a06050406060603060501120507020111130e07050405061210 84
    0x90f040c0249a0003040075a401150f884d0f00b545070010500307420040c6130480c0c61840c2070007421b142042c0310500030a40980c0301b0707401c2801003520501c2c400194040f284000c1020790040e15044054103000401900010b4240c40011284c60300443e44d00224102c031002c95142118910500028010007000c0e007000c2c0542c50005d110324640ca0005501c00d010680c00141e480d02c2e1400d04154000060304a0205140b65401c0c11041110004200d0308082043c2000b64507070703456994000140c81100747c0104114141000c0c4020050005000c405840d2510161401030742c500d0012942c0c1c0c0200e1084e154a5010000100560350055040102040031800c018040064410310300c4001580d00904540700b0341e80340208002d114662080b05d014151074941400751515260000b04151142c80d024503105644a010407480c50003584048481a10509402c0d103501d10903064401d01545803080401a1a0f17802c0001c048910038000c541c1039800081550b03003041c0d40940500c246080040c0b0010b100035043c40d000c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 91590513 1250 91589263 91589273
    0x4090905031c02032a0901030b0a050301060303020c18060d080d06150804032a0204020c071203081503070f12060f0f061d040c030f03052b050907030c1a07 68
    0x21481100400151340d90038042007590301210001d8507403503c0030030f840c4886003a544243c21a03040c01c009280200c0c2e0380110000044402105501c259030640c6094800010950080740f1503224841c01c45403289014510b29224020300390841e1500d0380000301520101c00508604c01a01008568440000d840e035181c211303000c040200218408003207801803040000b05030b0300c00741c955040b4a01c0021941d0b40d42049408040358450384c00004c1c0f0881d008100c0b14206003042102c41d008000502e85100b0002e8681001740c0505400c3d1101c02d554113402c02950320074200000c1400448012402c0c1c40c0000b4079002c6440c00b0390041c11811500561a605070212032422800350a84001302003100051080c40c010940b080a00c00503288a5520120070130040071900d00b18194040381d42004030300f0103e500d14681180d040c81242c1c011449401044440e51130034003000f034a40c0409404440801050f00d80d8910307903603108424440101241c10700d0341c0900a150480d5100f1601d45080010941840c06e81c3e130710 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 91591763 1250 91590513 91590547
    0x714030d0c03050609160906050a020a0c03080304021302040308031605070209100f06093008030c03160c051c020106031406040c050109180b0d080c07080609030a050409090503 77
    0x10000000c3d2201c00b80b2070545001030000f0741103030408040c0c80d5503410724200a0801a114070803030781805004943c00f84c0f064024882c034075415a0082044014546074600a48650400c1e5001c3c0c0c00749a0340c290f00b640800c401d04c201c900b030340d4120200904690319041403100055488440f0f0040013024041d800058075103140c800c0c01481108079a06800f070038007803c041d61060279803090742006850b100800005d1003000c0c02d2158030407030074000c4034250308110303400c0c66903c04084000c040d170780000704008142d010000a140105480440a0241d95406100321040707051100b01401680100c03103800c81000090150020540361800007081150f543c3d01d50142c40303400e9003000307482c80e0040400c00c0204110882d010000d0202402c00c400e01a040042c0c1d9940c4500d491204030100c0e50f00c0c541c0c42d01554504903035400302507100035074035500c810101d1841d8a501e0a407150300b190b0302c5a1008141203040100503181c00c6403695461904003442c21030804090209908203940fa40410403503500c0649004030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 91593013 1250 91591763 91591781
    0x2130e01020a170a0c09050d0201090b13030303111c051515071509051908090d060f05060102031c020906070b07050307180509010e090c03070602010e060a050405030714030d 76
    0x303e40700c1d4000c111407101d48000c0b00070540c0700e000e407401c0c201e48402508032402400381c40080d140c0c045401094401603d1fa00d00e50b40010300c15000c0400d0088140341940d0303140b02030f03901c04d9074103000602d900f4a9403111030203440380c090480d20101001c11072110250380202d41c032505c008602060706140d88042401d402040b920351644050008a500c20701c9068010844141c0080c0c00400c4030f108039445482d00c0d0301d00144100c0712050340c03000352400d025000301900c8202c00700030901076502a051074004020180a60801d10050429000070741039800032084d07449a103074101460700059003001010740298032601903560310000038000c80020030045041540714101ba501d403241d0b607043c041005894884d5800b403c6a00c0c000c03205052004e503d0b002103450440b6201075840580d91210410241041f0066408580520410400040f19a815044a01e00c1e10400c4144e5580d600e45861001c2907820440c0d0240c8150b00030000b07803000079140c0040304000f41c09001520f09011a82a548003074841c404 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 91594263 1250 91593013 91593017
    0x901020705092a03010f150c020405130201030c080c0306010302160c030c05030f030301060c0b060102010e2b0309020d03050c150406090201030b0d02011e050906120106090b040608010302130e01020a 87
    0x2441c80c4a61070006125040001c03031003c050540d803405803075100328105409038140360f501081402e02498011240d110100c1c0d070040c424001442c003c80521500f000401c005e0b0300003800c2c800202240c4d4010a50513000380035143e0709514554580e4015006907105c0c5800d030a04400c0c10003080702203070046081d81c0145100c2c00075109200e142c14101441d000061070002c4080c0c10800c0104005c9401070501005d2a0784040e00041990b50b0b040141d00405070680b11500714011401040034200456800c0e81d0130100804820078200305141003241111041c680094001c5072001841c40407902030300181103820301b944111150b40103030020040704084266000c4a41d00d4840300080c007150b8050044034058002541c099582c08174a40008101000c82c150030700c20710414000041c4039612550480720540d2026011a0361800740c01e01180c4402c80911500c000110404000300b00184000c007203a0448100e566402c900782d0850b02084210000564a40f100c15950003040707112190a0001e450110360035 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 91595513 1250 91594263 91594291
    0x1608130305070501091202010c02130c0e0306010602010c02030f22171c1d0109080d0203070203011404020a09022203050d020c04060b0711060c0f0604031106010e010902090102070509 80
    0x1501d03025207002c1854004505209001c9028426618202c88420b9090340903e810004030400c0c4c000318101e0b400091131b664141e414024000c115a4014a0503a0306290580850340c1036a0307910300403400c80e082c0c45462801600304200c0c0c691310b0702c0004068101081a10b1206030528181112256495110392000201c08548005251812024088640c0d4048501e407a50181401290002c01c1d201c035004140c0e249501e1a2483d0546074824000c0f680900000030496280307442c0400c0180d40c075004418121710a42c280220b004541845180b0140103e40c054004a051410310341410060340001220401c01c1480c3c001414846501d182144010350060026040302058424001d04003c8a804078038080c60502000b000702c110141c0403180c0362604103810462500c0c1d414005115885000a80c280610481030040040d06021a03030501441c86904c0e00f00c0341200c0680c43d191039100034272442d00030f26100d00c0100008203107070b0000c0c030300e518051060340d40903600c1d8000540c541c902601c87c10211188 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 91596763 1250 91595513 91595519
    0x20405041a0709080d1b060c020a2307080102040506030c0705011e02030712110a0309081b0f100e07060c11040507030608010605010e0d031b05010e1c0c0b010605160813 74
    0x106000641c600009480c0118100101910214011506e260001e01142d580c00400500c83d05c280010038019a00810f00c100884441481c06000054001020000d0280a00c0000e20350014400c45d021104082e0040d41140c0c1d0380e032400d03401900b0600c2c05448075500c429241c0385000940c0040c90f20b403000c4840060f2070b0706203114018003d002c9110302441030b514100e0b0a40c0f00002010a035403e500d018a804a103848261030540403034000c12401038a40d21038604c080880042c040365840c0e078459210201c80000500810060584000c001d0800a0750007405040c441c007485512550840c030700584d40846080e120501203012248220354020009907110414025040c0a0103840c0040800746407618844000c8400a034103242c0740640102409103560342c102008030441000703145281c2040003080300080140f201a00c40da5600042821001000711104866020f4040380315059003020100506a003081420707582903008909080341120900384c0c1000096404000b030646141c18079160000e146 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 91598013 1250 91596763 91596779
    0x7080417030c071a100b13080102190305070801270902120705030714031209010c051c091a0a081512070503120a02031602010314040318080d0c020405041a0709 70
    0x1014002e400d254036201c05105a01c4005c0701c0040944c0c81002550b5503032174004000392502c044940c0003160950000c10740c001d07984141e0006039045e2206032020b002c1d40d62080c004607840002405101440d07541a07441800302d003488205646d00403008d440004080485400280140c802001d8010b440d42c800c0c501441541400d02038000104250442c0b580f140c154140000e032140f0060f0602d4034030072404100c0f400d107603214250803c600d41d001000d45a000300051001c81d0242208a1001c020800711400014401150381e5460411a0848602401c196418804a40d40d5a001e0701c0100010b5010813003100542c0c1e514800028100c110b0000c046080c0f42c2002e040c01c0030054142000e079060240003c5030b0aa03004070031110301d528840c07150764905a80b4401030f801400c1a0900103502c0540d1401c01c0201a0401000c0c020700404040c50042c8558a4507015500c0c410803030a400004c0c510031128006042079000650000d121781e103030f100c40c5460031140c420220307000c45a0500140004d501007060320 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 91599263 1250 91598013 91598033
    0x40306020d0207110f06090d1e0804030b0705040b070807060f020f0903010e06060102070302101b0b0901051003050304090911060f0304170c06070809010905060f06010f02011407080417030c07 84
    0x542a5840404040e01780002000c3d809080c50850083d110000100c00300314000782c6c800600214250304124507501410b004d4035542207404115002511034000c50001380c040e100b960220340343c0c1c8401e146018901e5030394140d141c04c000011074005440c0c0c0c04000c4214030314000b5100420346020540d0710703003810038101401c0d81c1b5401c040300c515030003490134840d0a0b6130201d8810140c0390107460f00200368040c10400c40b49001d0310000301e00d9040c0303007404070020010300c60403040c040c000f508024062600c840d4822103041e04a48801400c076070041008203c00d1640b500300c60b010341d0140802891494401e40403c18540c00784ac5160a9468004100300030000b4680304401aa84c55491641c200548007625990301c001c05404c2005010f04180040c000103000d4000725100780c0d021301640e082d8200902c0c00d1070105010342c0d074540441c40c49030500500601c14400c044000503626818011901e5011003510601000b40c001c0c3c8203544214500115040d45100660181c0c4401c005542d035400c10b070406101c0c030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 91600513 1250 91599263 91599293
    0x172b0311090609060702010504120b040317060a030b06010c0c0306050f0c03010b070b04080c03131502030c06011203021507170a06060e1302090a03030503090d020c06041a040306020d0207 82
    0x311050100102648964058038218a01a10596039171a132500060340d0034040d40c0c0c064156020201048002c1002c140354030b40c09284240c9414547e40303565240c100003104110740054200001c0041000410308080b08641c00441c1030415400c040321a40314201c548215420a8a24988480a1154941c2c001c1100c95110140712022410b5505011000c81c4d0351140d01c00c041e1040c001440880d0a00c14414112001c041d0480200d036134a07a000c041c000d1819049101d150110109800291100f034008811548004003000c06440c46a081c0180081d054542d44400d400b184281d0a581600c0803400d041c0c5030180d00140c581c0303030740388034004010032051000030003030107445062410070407865400800b80000c044084400c04100b800344440f04000f4010981c5295000e86550b10000030300d82c0200056001d441e42d1700c2a05e400604440e03060b0b945603001040342e6000582000100203170104000700c89401030104019a142030344c0d070744802c3c0c140d8009a061194180d07002034814200b0410514440b81c07 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 91601763 1250 91600513 91600541
    0x1504050c04020403051203040c1d0a0f02031003021210060f08060c0a0f0e0f090a020d0b04050108210415030209030f0f03030a0b0a0506040603050708011e172b03 71
    0x3c0c0c1419603441a071142000e05581e0070001d4080007243c10000781c44014400360100d03200082c01842d188000035000e007010360b03403800000c1c84d00c0006c1402c1076090003203034802c80e01071060b0100c0924507820702a1150000002d502140031300d090701d40001c941070107600002c100e0350003200401c50030410541e00b030400141004407520406c1103042401a04600080f107d10141c0c2018a0300c0030382003002c2005800800c1f941c55206060740b0402404c192540d026052135081500c042190000400a11045900c00c1c00b030138074658801c00b1114000c1400410803502c04180200142c1400d6507226181c055104510f10704000c01e4000c00c001d225410108001821540391400400b40b08560350036154407072101074103840c1d81940f9404a0505600d800d013855008213800740c070b2641d07103659520300280241000d0303801000142210000103034030300d030344020070000c0390220340000489440e058481000d0b94440b900c011a60252090703212040300300000314007486c0c1400884117220402140018101c480003908012 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 91603013 1250 91601763 91601767
    0x40608010f030b0f270303090c010c0f02042003040f0209160806060d060509010306020a0305130305030105060d09061a0102070602150109091716060b090103020102030307030c111504050c0402 84
    0x101003203180c12001c0e0010300080072544d650301c4800e011400d0150900c0c04140000d04495020306400d000130003140728841d0740050300c0d48441c4120045032081600c0e1000380038080800010005450b06500c08910402c1c4030303280141482c840e05440d440b603013007100e058039200031075000b40c4250704143c94003070703403140d080340c13012000403200007000d0304024019002a00038880400d000090a140d6030008001c2c0070700030500c019540e900d180a00107517120040b00300000e0b06140105030f040d0300320300c42c02c0703102c43d410f80710b080c01c50b8209000c0c03150542080b00840c08043d00c850b0340c0d40c0840c46038880d0340c0038001d40381200210185000000382c9840ba141e40030300c2c11903000102e010981c03070300302400030305540c0e0f010b8000c00c14280508000349120212401b05040b0900062030100d0525001c145121003071080100f88039890715102004145c5009100c0030b405a0000c00010f2401c520070b40c00a20096603d04003440304a203c086500e2411fa50003c103d000031048805000a102c001c2011112211080754254 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 91604263 1250 91603013 91603019
    0x201030c17071107050409060509070506070201050d0218040606020c03060c03060102071802070803090615060301060504030201050c01060f08010e070e04080702090709180207020f1005090f1302070602040608010f 93
    0x2030704044020007082c100800142c061000c0b0310140311840080000502c00d100301000360a00e0340040030103561019051060000003e81424810140d40f0402d405848031070402c031070b40e4200c102175800380000d440000c1d45003000d04074581c0c1760320548026100c03590003048404032030401c1c9468102c02070503d051080c0e0501c100031300c40ea0700103041000d85404510f40c075444e00c20120304001a005d420b05c0104101004010060500d01c002245446080c400c1c03c40005000c181c410f00100d44021b009100018000f04010b202550050f8020010b000c030744000080c2e00c5076182c200c00942c5c5c2c03a540041c0d1090351181410100710b04100718a2010b01281c1e03041c0b0700d080c109030751010004e1144a200a005008840c0041c401d2806001e14100070300ca640c4080c4d04e112040410000250700a1804a02c2080400c0e4841c050f4100001000020b8010340c944c1441c2c50000e13010885c1c400c02d07035a00c41d40d1220300c1100031115200240080c0550f44e10542d00940c850303052001c044e2071020140c00507418015108410 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 91605513 1250 91604263 91604297
    0x2031509041e0302030d02030f041a09120306010507050a0b100503010b09010504090206190c061407020a15110f04260607030506040e03070c03201503270a0201030c 72
    0x10301d42c48861142c540e040409034541a4194014001c81c002c1c507038030200030440900c182040041c80b451040600b5103810041c112110b80e9040103a40005007030b80710110f0072002ea81d64000854100038141003081c10f01c415580e0701d5123801d080c85421070746000d0103014025050310007180d003c050001100203004200310310000c42c9000c101445003900c40c0c0d8580a0020a40d20391800315a00031507222610360071034400704c0028004c3c1c1c20b140c0b01203404510300a4800e5101d0001e44100340500302c16809854501ca070b03030704c07074031804010308200c0042180e42e24540002111440f0061a040c0f1910a05644581c94000001c08001d84400182d04500d048892242900c2c000315042e5880142414006480d4131a200440c00400b40c014800c035852100103110b4090162100c0542e089038440e04510b074903002070f80a41d0300c1440c0030320041500b00100b400c5074004201c00d03a01440d40208400808401c0f8032540c01010050341206800d0496a04010007070310640d40d05001e44910900c0c5c909103074200c40c0040320701c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 91606763 1250 91605513 91605533
    0x110a03271a091c030e0f040b01020a15020c0313140117010e09010605090703020c0709060f030209041104020f041505040f0509040303090506070e010306080c0105030c0f0904020406030203150904 85
    0x140704801040010040741d9550780010b500c0c3d454041d09410000c40d009850084d0501c4080308641d40315450300c41c01140700b80303402e000d04c0c180c1c440107902500c51329030243d9402c2c101c02e0100a85001c425028404907040b44001c001070140340385281891410546014a10286000c000f003055040102d0180242c04c980046505681111a1441401c0d0241d4980000c05d0051500b42c00881d800b800b00f400380104194150060200781c1d08010a44098035520ba915a003140c085108400115529070f0040015203800480141c2c4240200c82482424440c640018220b80c4140d903145407102c0042810721100081d4403480203803604500781580382c0f40c20018502c0b10060030740f103030511800c5000001004c0610a07040322401590103c229941c41c03d012001414546511102d140080d261007400075a4080000d000a500d02d010307100c0ca413450321100b108110560041036201c8410100300415101c40d00e440c4010001061a50341c0144c03203003003540701481c3e03501007030789624071031541501031101158410700 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 91608013 1250 91606763 91606799
    0x30a0203220503072709031b02040902040c0f090603020301050d02121c051e031506070218010e010e010e04021e0d020d110405010509091c110a0327 65
    0x6420000c000d0107091101412a05030080c5030140100c03000000ca4100102c1540b41c03110610200c0c088044c8070300a1801200c0c003410780074002030031102080141c1b210b480c2546400500107000419584100d4011406440c2a1080f2070001903060f0040041d003640010100701405403440c082d460340d45030500103044a50a450084d100e244074074026448882d04020341d4829902403e10142065030400780500540c103c600c62010b40308142c4a0b0f8004040c0c5482201e1003503d00c1e040c030310b40c412103407070034016540c01c88001240c001c440c1600c8042164030502d5200d00130404000a44155070400035030001c41d00c2d041e4003482c00c0c1040c240500c401a82c464102040d55051081c2060402c7d064070000b034501d82e10010003a40020b007114020781840480c103201da00704442540d05220b1a641d510a0101a410498a078001c2d504180408614065002401169500c1d43e2030200b46080380030045c141002054201180415400480010300e000c1d01820321988010b4a1610000a860076850403049844c80e4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 91609263 1250 91608013 91608037
    0x1050f0103050a32061b04030c1a0f030405030c10090b0f04030302040b0403110405090303040f1403040504021b1c02030a110a0515100906050a030f02040f0507020d080603030a0203 79
    0x26407580c0d22400520803110104c13003c0c0c0d43c503e10680444e0f000b0b80301d0a0503102c4171105200700070030390b140c2803911003107a04580e0301000340825649464036408511152a6842841d50710030032a0001c0010104061030060b80100c001c0c6a4034170644202d645800d40504030562801c0c02d003070841020520750380043c0d0b400707481c11150a4081c0c0c4d403442c04800a2140f40c00c5000f4a000208010091103443d07a419600520140e40402594481106850340c0780070444000741010340395851000010182c14050720314190190440382440d44a0300042c0582c0c103d40440c2c0381214004200d0480030504200300c542035092003040c2c00e0064810031009459101d420322040034404030981440708001c08103d4000d609801805855200c0070301c94800d200c41d102074854440408046d4000b00c0d0a0040384030741011108001d00c00d012881c03559031000c010b050201e00c140c5e0b00c03503070301d0305100e000f505a8011248200b4555014005008400101030b2107680c01034421030080d402480841030541d0004200d0713803984810 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 91610513 1250 91609263 91609283
    0x603181203151a0c0115151202040302100806031b130c09030803040803010806160f0c020d230106090911040e07090e0303010608070201020703090509150405040b070201050f0103050a 80
    0x1102c04421420000c1d400441c15498450501101c96221005080800d4200d4028011480602142d4007103401502586c52241d400c00b2503144920300031081c003500340d4013200740582000d60300d800049091031040d240801003002c03842041658030301440310316140b64103242040107520714040410300341707146076511000382656040e02420941c094191180150382c030000c034603540c1c5017910b8600345d00c0e00203114041c4103110740d4010860fa240c5e81c1c008032443c4000e07980d641e486041d612030200ca0303071841d00c90166004a2080d50640104034580344203000c080e2510900301070042d40044403421181c01e0743c40a4911450304c07401500142d1002041c81c10078a007249d0120b2101200744069003400c1d52035002014442c90082111003003034000c0b01550403541183c0b40d03101103035a014416403c0c1d10400307000500080900c5000e10407032034482c0c0e00c513402021114440c014240c040780810b08445c400c0d1030954248907400300b00a6425070900450758484201000001d0b20352442d599140e582c0c070180c000408400b50 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 91611763 1250 91610513 91610531
    0x13051e04050c0705010f0903080601020d2304050306070e0a080c09010e0a020f031003020306010f060210050705041d012d061409090103061a1905040b04061205070603181203 76
    0x2c1c02c01d0b2040f06070002d00030881201c010420500070507007504100d0228100308001421580082000040030749036403200000390311581a01030319000f0510409102040520011400340c03030030004c8610920741c588410241071001c60800c00405e8140c0e100030100da014002183d40b40d00e500500a04681121100d00015100ea44245011380909070000c94000008001c0040d0380b2032101407082201d000f5030540300d95036210180300c507411040d80a1000940d20402d80d10607600b0321030f801198402002d01d4608d09058440005154038081c400c02c940f81e0710f6142005100c1081910000c1c04c1e0800841e82d0220303140c0a86490341c03030480303007072041d1028441000202b071101c4040404580380c140006001205560b1a46031a00061101460b108698400c00b520126142020410256180030241c03200042c0703481c000c204400703402c90300c03281504203031100000907202d5041a0489800e91040d40070344500ba042c0b07d8010102c9503020140320507040c411148001180b4100e02000305440a441c01184001c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 91613013 1250 91611763 91611781
    0x51005010c15110304080d050f0705070803070309050f0703030306090204141302040e01030b091b24070b010306050f0702031e07030314010602010c020f0604020315040c0305030f13051e0405 83
    0x19110f0f400c02c95040000400007001041001440360801c58002000b40e07498001d40ca01181104641e01c101048007008418041401038001d150300001c24503000c0f580d0205665001d04100c4c0c4e41d110111903a01c0440203204154040c0510805071503440021420305180c0b0080740311100c1035010950081c1c04502d18011015429012503000c3c001d031000800d400d503900e2a040c60030f0101210402602d002d84400720080644016205c1042c0000601503080960100350543c98854403100442801c80d003040810005001107544500a6000b2440001c10b0700e401c01c0d000000308001041c040840d002040200006c100725600c81c5803c041702c885154a45003903140c264000c00001d001e0400160589000080780f1754150086010303940c882d425200361444150482d0b55940c02918004d52640040601e07000403a15050140d604c503000390180341e000c035641e4035402c1c1503a00c413481001c0a0040080c5580c00348240800f100b00510083d585a2904112600505c00190b0410036a5100d00d8403200418a981 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 91614263 1250 91613013 91613021
    0x30c0e1507080705340e100b03090f0105090303010e180714040f021c0c17011a16030f020705010c1101080c0c011e0b1005040303030b0105070b150301051005010c15 72
    0x21961701c10881c42825812030100444082e600480e40c1d0f0203510b035010901041031406d0358000e48000010309401400c01025a12039000100b80c1982703403086040610420600340a090b0060800002a60356941001d0252540d058018101d00c600341c082c0c00450110130300000d140c021640340e41d01c020a10418400014050a5017a842091031800811404a1244061241126030441d00e50810024420610a0b20b018030801c6070040c820709900c00400c80d58407910320340008a5030b05d020140c80d10300000c401e01c071100302c80ca000707030300207500502000c0c001c58041202c400545000d0a044800c02d40c5559402e01d01d00440150038100b12007140810b149044200c140e60825515100074000302c0003146c9103c03190754282c8159010310b03040c6080c001d401d040c80100460102c03126981d00345031600f0354030183d01401d2010304a904114080001d1804180c0300d640c0a4083d05200100d512001e20080c100740c29110041c0c103800b110440c1c014100b16036038002550113607481d8840c0e10443c8020301207500f10020 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 91615513 1250 91614263 91614283
    0x807020703020d03050c0f19020f03072c0a050f1503070e07030c09050411030402060f0d020f0702031c0e0f1201020c0601080f06060a05040f0b0a06030c0e1507080705 73
    0x319010308148410580c03c0400f1b030164810b45021291403540f030311000c0b41d40c1c00c0d542226060f01c090000c9940c001d800d141c00f48010105001e400c5440842c1c0c2c80c030246400102d40408411110b1204001d99481008603c02d01c1d048502400c0520042c1012541144d0211001d060100032410b1601c5010a0381c0303050005500824400c1601401481c01d500058040c0c0701100000001928854000c01c01d40f90038881d1402c0c544854040c941141d40e180d0a020340c55003c0f030595444030b80f003881084850646400240140591110741540784c1c015132050525129114592160052104003a20b81c126481003c611013004100d0303d4070605040d403001315911043d0030301808a29400092001d4030303c4400540c0074101c034641d43c11a40f030241010945c0e5112071081c1c826650240200600b040b2074601500b1480041540f0200050301c8aa144009031183c81e0980c010004603480d17034084051142c0000e0580e214000c251181c034031100e060100400c01c0d21480000514035400410f4481c14010708000c030b0003003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 91616763 1250 91615513 91615519
    0x21e0901141804030522030804060806030a0c1d0c07050c06090d060e060403090605071502070804080316020f040c02060402040905030c06010b090a09020406050904091104060b04030b0711030703080702070302 91
    0x454181030500811a43c85012203111b134580304104207451484420412040300e81190481c2d04060925600300d800b5440945496814403c2480309000f040d100c4413160010901d02ea00c4503d44000d6080c001001c2c08002e0440340c0c1d005052080402041d80071032004500310007225544e40c4e54000100040c96003050405c0a41418a040002603403900c001602030b01550281c0c5800710741c10394480c0202c0301c40c820405d00401c84c005460b03140d00d0400c0b46402825219101d03455a5043c20785600030b691658119941045858510b14100d40c00d43c1440050750211101c1900c0c14841035070716001c00703595030b0005040240143d136130b01114000d0060038010741e42500d002070180c03452940c1d9804084400e41004440b584180c520329000100d07007102d80700b25011901143c0300c80b0b0900d0403040400c4004c1841030b0059a08102400311600c1c251b581d8030a90010307200300c024880e125805c3d400e1041803204001e140c0c8040c41000080c10041400000544480346d6051600171001e43d9880003c0781002c5840e440290 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 91618013 1250 91616763 91616809
    0x30a0b2205061902090d0308071e020c090a0204120813080115060f0f0801050909120a0309030e040b0622030f0b060f090c1611030a03020307021e090114 67
    0x41000c08640c41e40108500f54180401042c2400a5000c92086103445940140850b4258000034003419800b81d00281a0400d204504c02d03080e1300a03401c0d0135002c1880d0040c0c1012881901d1450514503643d040740d1028821814a424200790308486280000b0150440502069404169a01c0b070000ca000e052000000c1c4038400718100b001920494030b001e00380104140c014003810440c803552208082240326a00d0710556440c0c9018410110005481e10186000703620342c41072102d042000400c3d4207000c41d50002080d440c58100141030200da5426148114104810120941c0e03c01090321011403504503694030070800c0142c07415202600360300c0204005d0000f2126418004c3d01151984140c0064428000710406102004401e40b0100c84004c01510140000034007806c4a4802e40d1009219640c0760b0640041540004d1904145500480060f80005000c804504004903105ca08034010413000c04241e50035000540604014000c2001d00d0346541c08001c40c0d965030710b0000d01a0010708191217 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 91619263 1250 91618013 91618081
    0x503040b0a091212110c0d0506060a0603090803070813050f011e151404021b0601090e03130501050703030b130f060b04080c04020705010b120609070b0306030a0b 71
    0x8251a00700d11621000308040d00e9002921800d103910754100075034041400c086141d1412001e44944109030307040040e51150018500132034a80411108890303025200903c03080c80c0800402c04110301c1d0382c10080406082958000001c2c14010580360412082c4c105241d09903121800200f0b822900312028051f8420f10221000010065010449000c510300e14005802012002c00b000c1d6248c0202019104003007140c00c00c0707841c0701c0048601c80820003c102501d0320702c1504050300d003201d450014103c46c0d000303540104424007051107006c078083c1c428070295007004024600100c400c54688540760601c540041c9400405219910941194400a1000180c4000300b81003000501ea08499003170f000740f4002021503541c05400c251002c0301d120000a240c50520b070414400650000002190780b90f4860200c0700056403040c0e00c40c04005803040c014440b600d0480d1020346004826804a201e20402300240141034601042d00d105140e000615200d481d1988040f0b060000c0c04c002c400c00d007507503803202d0396 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 91620513 1250 91619263 91619279
    0x5031801050903151009230709182301031e0501060b0301060309260702040908132403060e0703051504230609070503040209090102040302030a060605040507090e07050d09050304 78
    0x1325006159003003030404a01c0d00d402c90101180c05802840ca00f40182a00c908400c83e5200349150b8000410314040c80244d0b81e4081d140c40e00c003a03407042080c19030384540c0d000c0c0c00010204204800c24000210005aa51458a444d215400c000c6030300000021b0581c0c00345c003070000c00d410010040a88582c201d9403588e5500700200200740028003254014540902d86400300c940c0c1240da041d001d0a407441324030b005119802c0000130009268100c51041003489108528500030140d20010045103940c00710080151940d40c00d140381e812000c0e018140703490801d00200920551950b407055003801d00207400d48401c606031021000b0440071582c440c1c240914400c80c02009030041c1da400ca000040c0c03003865110343d800c002440b542203d2250000c1c405200080c0546000c80a0a801a0400000610b0141c890300401e080c1307a5401016502141c44aa0810550a03d03201c0c0d1030b07010b0f60a01e8030790103540c00c264441e007a00030007901e40010000081003212185499a100c261001c1e8842e0403680d80355581c0c614 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 91621763 1250 91620513 91620553
    0xb09010219090e0601021615020a020310021e04030f1e0c030c05030d030509030a0f0c1208060f06030402100e0a1e0e090a03050a080c0d0e1606020a05031801050903 72
    0x1036110051510001c03903100c0d400011900407d01d040c0110401107403d05400052540d9400401411442901c4940b0302588040c08901e107402828400541e82d561f07100c1104922126910b4418a00e8200308000c002092041c101d40040c01ea00c2400c020610900d803c907568070000b0050041c02c21003074400004204070180010f40116082a81943c010785200f0000b502120412540800941c00820040050512803030080a190144d403e140590888075116501c40c003181d50304504c085104101030005501d42404d43c0d02d01e002d011207046145142580c0400c150100c0014641c007404082912040c041e40d545034550b015000c203842000e1035065041c448941d025a5208403081c4a800c0030203d007480c4408500880001d0301070700c072145000040c8070204c45041c40186503249400081c040004541118007501e01c080844100411780c840c4101440340c01d24000e603100c41c05541c82040e0f0540000e0340442a11640d019050340440b80203860401a211031113601d4040340d050040340504e8180b014150303c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 91623013 1250 91621763 91621769
    0xf0501030209130b1501110609010623060a0e0301020c030a0c0b0a09080316050f0301030f0b01080d091403010207050f0601090605011b08030604060305120903010f02160b0901021909 80
    0x440c2c112540b03030360104112034003480102078105924040080c81d01c3e01241c105500144040c5003407981c440040d038000b03080181c2600c0f15040345c3d456080c2003001d400f1911400040110f110600101c2c5040040000c031070748140780318201400070881c0b41504990302075050304c8085000100b40c0c0d54070b120b9403c005000240203c4201c0c8c0e0500fa403804030700041c1079445030184d440e9101d009c5d1841c54036480484e82d0801146400703602040010004000c420303031050007540c002d6200d280d4220700701c541c030325000f0b9080205800001c051341c00700a228901d66400031055040300c1c01c60000034000c01d00c007004207000e84190200074169105100d40040d403000001011b504850000d40c0c10008180c85800469020300d40007413000b2408003802d0390b140402d044000650300844001e0000640a580b941e5042c2008181081c07040307820008184100581800e00411001d40c50508003146000d81103039408640130b501a2003e80f80812580000b407043c4002d604540803d906a11011104c40843c200107040b07003c240 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 91624263 1250 91623013 91623019
    0x1e0e03131202180907150c0510111608040503010507090503070602060603060f060d02090103150b03060606220308030c09041d0c10180b0307030b1c06050402010e040f05010302 77
    0x500040e0000c0d036100564500368024500c50880042e500444900b02026005001601402800042800d503498140702506c0040e2100c107050b00341d904005041c040c4801000c040c060130304a02c05882c5151004480041020201030a240c0040707060400d0f0300c0c00380b504056015841d0500303200145402c48a0b0394101c2c0d508a0888135940c1c1c030703000100d8440c94103807506a011b034080b001040904025005a65100c40054100c00e1404200d0b00000c000f5a0280d209a480610402254034102d506000301c00035402c06a0007045a400c1640118495110715080628194a600b1030400aa107100b0644d500543c0c0100003181c407800d040d0804240f0358400d080551140f0729043c05105608080303040c10403400c804c0d9020309092181401400308400040c004a0200916440e103000ca901d6201d072030f500900a0400b0003034491810000143c01c030b88007070420910882150300d5100c031030042d814421030400d40c04100400d1680351440140c4120290503007445d48542012001030498940d540000d040b03074004c03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 91625513 1250 91624263 91624297
    0x1203060406060203130b1e0d050402030601050a0503061308090a081501051806040e010e0307080c0c120604061a040608010903120209100804080904090f03111507031e0e03 75
    0x1004260782e6407017000305108541800c1e0400300600c51907903002d041d1044802e41406540403413040f0340c403c02c1d408011401c0700710355124180b0056050800c1444d000d810142c564030364943c02d06000a075a05401400514038900007072448040181da070007034540c0d204002c2d1040f02000d03120800d00351251501c8000300480711100b030002a6134500038108034031000c1d07440b44a00d12502c0343d030184030241a95440317084056403107190034405250100000c049082c0280f03296525458035903441400d003035074403140c244036020031a58815180030100f0200d40055204400080c85a0814034103921035100c54580c690003454594001400103040d001030300c00610954411400c80380038405801207003d000f94050300024564140410540940b0034240c00c40d025810143c1480200800501640e171132031f80c1103030380340d80c04102481010307089825210070003111005040c0890782d040042640c55001040d24080507110b0443d01d007447d000410440440d41c1b40001400030345c3d0115107aa03034a6104003000351540c0c000e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 91626763 1250 91625513 91625519
    0x4060507030501060509120a0c090f0e0a080f1303050d050703020105090a030e010c03030b04020304050102041503140a1d100b10030b030a2603010609030303110901020c130e1203060406 81
    0x468842c55043c1c804540b00c503070600c5040014805400720078044481d60744100107151003c1031000b040c407c01404440c0c8040780b904110f666a0040e1102c05003d00300c5540710b03203071410005800070241c1e42c0c400381d540350303003525040b8005c0030019601c200e500140c000d00a954081d9060f0354440010300342c0d00d003e40c0084c8400c0e1038078017096640c1c00c80e282c0f02900150003800690680c1d0b11521510f5500b50107482c0c0825045000382c0013800700d074000d03503044a050713500140400c0803a14401400c0301201542c102004541a40c2d01c0d00003040c80020420540c2ca5942c900904004080b8150108820070300c2e011208203a01800c3c0e43c0005260108450f84500b055024158086104e8090035445040c041d01030800b040460362034900721200c410391041c1140c0c3c58098020180b0400300510700a10310351752210219032a43c103010702200c010f007000c0c80220300308003c80180c0e071741c0019550411442c01d0300e03d58003c0301d120018500404100030391a03080e0080031415224200391202540c00f03004101c0c2c04110041d5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 91628013 1250 91626763 91626767
    0x1406150f0f3001030b1e0c070c08191101050c0105091b120307060f06050d030503070306060504030807140c030706020a020f010201050712020a03060504050a0507120204061407060b0a060804060507 86
    0xb20802c003150704000c0050041c400a140d40007680c0d004510f03540b0f1030190040000c83c13080c0d4120700b01d440096418021401d203003400400003a92008020300e1018001080c142c40c80080c410004450140c003811140d40b029a19902c10401c4600c049124002002207080400035a84c480e1644041a0f031110f4a1511b460414035100d0445600803441c200210b190560542d2110068404000186281c6070758410000721911108404040c0303501c03a1344d4a6560b07240500000e8200c42c80b50304803208101c401d0000784006014441150000380e044a1007550903088542ca039442d044282e2615900340c02045000108160005020005175100300c030305d51800c0070710360012402c0356802c580c03000006048400710f889221060303004050f10800341ca004924191508080707416584241c507107007840c0e84d44208004000358003c0d54005411a0b40c00298a0a40b038110010007619050781c0c40856000002109410810160700c450443c202c05016408850b0b65034101500da00300481d81a01c0050074000005c6c0c00c0340c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 91629263 1250 91628013 91628077
    0xe010c0206090a060e0c030303040812090a02010903030c0c052d030a05190f0602070305090301150b0405060a0507060e010b1f1b05030d06090c030e011406150f0f 71
    0x42d40a030000d1000f002c0e140c449102505048000e10120301544c0d0345500c01c0d84051005600c618001e28099a50722100c0901ca0403100780100240c0842d00140800c0005030303407200004040306d42502e0b080c0c040c85241c0c10f08042e050139030b9000740c1d4400e592040c00c161042d000c0c00c6910140301f0032180a0802106502415240e20415074010441e8010001d403000305070340318951109c0c0900a614010000307048d582c031001282d00404c4150049640400d0384801454240500c95417600070340300e2103042510b0700b240040d26004e42d00404c2d1240c980030502c650828402c90582d003003ea00900140000c508142030079000305542215a40075160540f881000c0048411b11851582656075403030851485140c0c1050142104100481e210702040001c84e0b402c405500074000500b0001100140c01c4a9503500a01240c0d13844d0150f01036a4100844100950000d6102e20743c4480706451030b80103c4042e00413002c01b0700c038944020502a1011031141c50340c403840000f80444100700c0030042d070120403007901d000340b81c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 91630513 1250 91629263 91629271
    0xc1009050901050913060c021006080a150e030702040207060506041521030c050d110d030e0309040506010212030f0a05010504020f0d0c09091a130501060816090e0a0e010c0206 77
    0x200728144010080c604000030314030b900500d500300b400390408440d80c481040d00c04925107100181d10003210107c0c40e40700c920504005210b1413000b1302150035682e4602c24810054149207a5481d5103040c00c1000e01414021509010341c0100110b41d9002107203401001003c05aa009008900d02402c90000700c14221007034040d9011006951001e8281103003540c0342e429081d404404105420130400e0004104112000c2040d889840300307481844413511080c0340c600142442c40415091000d403c08142010044074043c0c517003510081820b5a400700140d2418450f6541d9010080002003001406013403018414026034a00b04140720590780d400c10001030340907940f80e01031100c0d808c020120b21703005a0b0344101d002059504150080c0341e5a5100f00c030441320082e440c83c01c007240380540d01c0703550b1505040407600103104400801c0a94103242d0014003140c001008501800190180481442d00601201c40180b41c61003081815240c0000c1c42d00207415002c0710b1141c90743c00e25118089050000c6105071007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 91631763 1250 91630513 91630519
    0x301050702100e10050a0f0506030c13051b0310060207080a0206040605071511041805010e0402090901020d0f0209041d12091206070e03060907060903080a05090a080c100905 76
    0x1900880340750b104010f203802000150301c0e2044014400d910051401443e111301d003901d00001d02d403400031100c401036034801401d19102c1e42000708050802d550b00c9100089441851000042da41d9840a00b4a00f002000e00c0c1200a0b107008010050248101c1804105582155003940c0030a6641c0040645d036000b41900298002e40a00c81404100d115030040c0c842d00b0b0050102c1d000400404074030f0400c0b02d420074005100d0181c0028184401041380441c0b990088200318100401e42c0b4041c503d070b0700e40c00c02410003841444000c0c007003504c0010940584040d02d0440000300900c50003642403030001d6115020301406a4140b0301c00e40740c0603800361602403240034518045c002c00790b600d50514013075900c0201c00a50020010415400c0c181c0c0030403504c1d05c5140c05440d0744074000000000c044c41c2001c014128102079105080c244101c03a031101d02ca00459511400703c0341c40750600c40c010380d440d009a100454000006140005180d2170005960a5620301a209c1094800300d503802158010707520301030150 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 91633013 1250 91631763 91631773
    0x3070807050a0216030b01050411070213021c020d050601080901090c05060a09080a0b040c0f0303020d12090f1a09030406140f041d0405070510020613110d0c140301050702 75
    0x580c4502450040003005528419101070390b4040c2c224520f03000442c0c0003034034900481e100510960504c0c1c411100141175204055003080101c0d03000900b0901017400f5001126004101841d01080c0314648901581100b4420b40d10b401c0906d2420000341000c4490354001020103010504259041c440e02c80410740144120903201c1c100781c140031550344054281410000150303c0041c40070400c2c01410b401600c00c02041015040c9420316420241541d0054400036480702c6040000a030006035417a514440c40c18041d0940d1036110b94600241018000507050716000b2150104114208140c48490415100001803a45503003001694038000c90007800080303905071007040b8106007680003800d4510942091203181c16160140050b00544406451903400c41480500007003110620945000d80b1003951885058495000000d58403000030b000c0c0c10318100c420040e0000e0024a1401c07840c0420080c140030303114080c51234080301340f05451190400c800314402182e40301e46018011f6900079400303540202 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 91634263 1250 91633013 91633021
    0xb070c0506180d0c0f06020f0d0f05030f040c03021f120c0c0209091e03190203030c0f090f120d02011404030207150e031c0f090e0a0c0210020c01090215030708 70
    0xf50b044503400f00b80c071601e038810000541c01424241c940007500142d07010701180c00c54034510030314100c40c80356480240211011484030003a4803000352a408095103c03541d080743c50700d080c44a0303048074640000c0d4002c0840c1081c01400d40400300750700001d4032940d45200069011642c0b1000301d4489031041000140818030b6480176103031400340e194200a0100c19501c4071452604a0001d04841a040003025040811468900300c0456a001e040d80502e00165180d071920030354803101c074424200034000200300450310800382d44580034803649959014000e0325440045c40710990b5919a0070071850300560a04c6c0c4004a025a0101d00501aa41c15002002c0403420425940d400d4582c02e4050350401c071400c03809044a07901004107040c0301d4104402c002034003400a20041221185102c0d46003440b40750344e804c208c1804c01c0d1514940c806280d000008061008043c101e0429509401844400c1e00200d41122409019880888040c0c4222007400c0c0100d800c2c124031480780402c03120500840c6c4400002 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 91635513 1250 91634263 91634269
    0x60612150501050c031308070512010509030f030408070b01180f0b0d0809031c08160201050f01050f04020706051f0e070f1b0203030a020d12090503071b030b010b070c050618 76
    0x50998041104c0640e4242005d0000b402c103104d1469001103015402100204614104985a400c44c60080b2009000500d8222841039883c400d0404000c0350000c00400602800545d10030381d201168403007006481c43d65680c4030015048080d040e2070036401d2600c0c5298190901c1c0d4442d08000741c10180a841120020b52242c00c0b454101e440c549806010b6112103500c5a104880403c5c00417045803115402e80c1091038030540d24000d0240b40c00c0641e8500410301c03001052110b062811200121196a60034040d100030901038000c4040007440c003410b0605120601041c0b280c0c01c0340642008403910f40c5540e4030105040c08540c10b4400344042071907140c00d40c03942485100110307907134020340c3c2007142c4072029a070110b4034650020b180c4000680251442084003030788140311000e0f000503e4418403d00000c0e4440544078400e110000707046200080048000341c40f0404aa8019500700d08140880d607900c2080301c459520600c0c04445052412401140e1803421900341c400c4110612600702c4440c418070b083c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 91636763 1250 91635513 91635517
    0xc03070b0906090901081f0b09041203022703010b01210906021213060506220f0617070e010e011409040f080a180b070b2a0a0306061215050105 63
    0x406802020030000500240c4950a84ea0700802d2002c006080441034100191031042c2c00d8a44c241019007046070201079030755012490f642254028132a035600c000000400e8000b440b5203c0c42519840020001d0300c40321507005047c60b070510056009000c5c07040e40300300440d0480d40112004506103030740c0108044e001c00580c000c1803014481c4200515000948010b0101c62004640500d4042d8108135401d00300031060040c150018420342e00c2014800891802e904100d0030454095000c0d5070310b81c1c01c50119640d90704681c000301030740708030320f103522076414042504c1c1d000d00d0050048031880c40d0000920300c1c2c00c04006034103c80320142c41e1200800b4020811102400140040e02c6a840b40640c903030100f40b004005106601030f64850f5040706c3e0017201c0849100d00f1581c407443d00322505100150100d0201c0ca902c50b841444071104c403e4030710f032075900d403294042d1520a080950401103007100c8460b826a10400c2076030b00c540c940b16a0700c0032002210f800e80f80725568101a10b1041c1b0400c000e01c1d4040c0c00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 91638013 1250 91636763 91636777
    0x806070f020c0d060b1c020906280b0c0f0706020c100c0210110c0303072a1a04061d0d060b010c020603090304031a04032f0d0807020c030c03070b 64
    0x8107440301854010009400d0750340380c00d07043d00c489680d01150346040c42c00004624441d11b000040030001001900050219140184601d010f06c030140500081904005401400340080f2514040c1710b0340c4038041003c042e0080b80c05401c2da881003200010b0b900302d00050a80480d0001e034004c2102d0000d2509119560516404501c10f200c505149440180d6801c2112505440d080c0d5070b103103600c0140b2400f1780c0360000b564660b500a402c100000301c0031a08200f00000743d00310ba2040c000b00d00182c2c0070301180e9030a4952018000300340282c456081214094010011515144d8905480150b107000481c410503154101d2a4450000c088070000036030329030840210100d0504104405900075008103440e0b5000b100c030f4111b15080000e09004001101420405541c100075402c444c0e4a400d541c042c20050a0401141030100e03000900c2b03c071440c1491000309140d6141c0d0035a06e0300850800041c000355001d9030300c0300160085120115030b500300050070405c001d00060042001c945000ca00c0e00c3d507540554 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 91639263 1250 91638013 91638017
    0xb041406101a0d1a1f020a081809090a061508061305010605060403080702100203090a030b10090c0806091605070308130f0f0c061d04050a0b0306010f08070905010806070f 75
    0x102c03100003480f01c0c510410902a5503400f1101c2d407055640c082100c082d4295000299a1401140780e0100960024600c01e140390700006180e518401e210000c07000c00328903e60300e43e0012404e420000320010110b040079042d841042c05121140310b120260202180501414011b5806000001c9444072001541c224003806803000050316a01d400c0862125889900256450300e80041c0301c1c011801d00f032030304a4242003a0701c05107047c4115003002403141c4d00789200140400c2c40d135401181240510031445001000d0048041084260840018016207000c8030003d110b00001800140404001010f140d5060303c10b9617064a4825669400c0d107000c2ca02a01c0302c140e180108038031400240d0a6042042c2c1d1900900c14090a2685483c5c04201e075003094010404205800c01c010030041c0b030107600f403000301c40119004140e13547d9010b10540101000740c22258144600d000006040d05801c6074181614404001c0d14522901d4000c0c20342664428400d1035455407000300000d000521030006941c4050141c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 91640513 1250 91639263 91639267
    0x40902010917030a111b01050a030f29090105090a0e0106030804030506040506130201020a020616150b040605120a061d01060303181e0306050a02090d0b041406101a 72
    0x7036103040e004001140c2d840815510006840032003c4c1c20031490000030301c981c0000e251100403080d9141030072512040d014144800030444c8808140640c004694042001000700f11410144010644120084d17200c44a40703800c00c450200607060040026040e102c0c0940443c0c55616600b4170130004180000009102e07540c2c131040400090403030340c0104010f6002e40001c01d800d08141c00e1150400901410441d01608468034000050341c01040c14030342c6030740403604c964992924034105100d4440c10000281440c00030340c0701d0498980f0710351005402c00b80075a0100b201603101c030b041c40300d9401c0904070f01c5941c0c0d1040746800c0018840b5080210000b0001c000c3c090490382c1c02c0001c0c3e00b500e070b20382c00813404203da040d0b5414926044800e240001e0000c1d04580c045420710001035529a0850301010308603613117031000508a02c040d0340482c1d90b25040507102c030308003003a1410050300e200c02c20342d800c6400b91010360999071078860000740d40d800358072070718800c400e01403524000401124500c11501c40079001 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 91641763 1250 91640513 91640519
    0xf06030a050a0b160f0e061e190305150d02040203041a0406020a02010b010804081b030417030d1d030d09051002280203030c04050607080705030a020304031e020105090409020109 78
    0x424807007148202e126000f00c83c4941041880d18680c51030000011042007030f01d980551800340d100b0f92241c05560280c490743c2da0f65240140405076990381303111658008000064080c0a4058a2100d0201402c03581d001c0045464181076000d0b403507019001598444810780011001d4a05903000f941c101d40305504410b189401354240400c0c0410840c1c040d00c8281d0701146010417290207000b070399541d03242481c1ca03a640b0316141d581c411681c0074800c040400f4412820100218101c1001201c014201e91420f000c546041d040c095952503100213940000719041c01e0001004005000c1c800d078401c0d06440103142085101090b46006004034141078500c0d2181134034401c0d4240040c4000e100c08a000460710b4541f10f0002c00000e4610b03620040e42c0110b40c810010804c400800500341c0f070139110112030300707507030b941c0c1c50b0070714409600860300050b01c28080044c10703a520580000003401220301c54800389034118102c4088608000314514082d0104504010140d298500381e8425014181705040000340a52 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 91643013 1250 91641763 91641773
    0xd0212010b09040f05010506040c1407020a17010f0b0303040305030f0a02070504090f03081b03070e0a0b0307050c0d05090306010311040207060507050406020c120706050304150f050604061d0f06030a 87
    0x10190f4041d1040204450f4800501c44280141c90744080305803001d20160070481e000074108211030701c62908a0342c011071181c0131941d5158001d8004c190000c0324400714a0549647c50080502c4c1c8201d83e5080e250081300003140c18040141c904881d04800a1810005885c1400b00546d211800c100218001da030741c04103150f0f49a10901807030501600c0b00911400051502602200000d807403112025000c0c06907417840070351403040300c0c0c0c06030840c0b400ca4000c110020200b800003410b50481c02140c6804002c01522907840750140c070458601204444400c2190703601660300d0311501031040d4040c0c101e1001030002c6400c880c80024280c078007600c01850b003c055200e91007202d03410f0700c540b400560300040820150f6410171642661050803a96103001c005a41c200725603034140c42c800e2200f404004030005040c4445240141014108000244150030350b020104004240c00c4803440d10031464130070007140e801c840000070f260980c0310704503410341750f210520b4204e510803000b4107156042c070074402c02d54000f034 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 91644263 1250 91643013 91643029
    0x606130905130b090610090e0f01090f05060c0301031703190f0c021e07030609030e09040c1d0c0307030e12040303081503060c0a0509031c0c060c020c0d0212010b 71
    0xd100414000b400415150140d8020030191121480303a00410521194190555200341201d2140790002100180141c80c01c0c282811002d5440c8a54600300d03001052200316101c40580c0e603c0703001501e4a07a03035040400603070f9020030300000d04003004c0754441605240700c1500071904101d11201c0344c100307101c080071000c0076903115961403040d454890101a48541d010801d0b0307a4030807840155149103141d03264042e5690710480c0710203480241c41d441840203041c080d142068038028041e0254060b07192606081c0307074100c00d500c6200c2c1c0040080654a40b41801d0300c1d8240d02690310191041e01d07645811004074043c1c049010324880c2e40c002d410f4900000da03807040042004600c05d03103604074149088514100041c0400b0700150003074010400304001c840041c0d0444090801c14145180c8500c91600480e243c0350600705890748161160b0b80206c00b10780c00c101400d070b010b803181005011900c0270b14022a00d54000c825116001480480141e0051419030a44081c2e005004000103803d2000c0c03001920030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 91645513 1250 91644263 91644271
    0x4050a0f20061602040203060402070c030c080601060c0201090e07140c100501080a0309121103030a080412030e0601120303090501022208030702030604170c010f050a0e0f060606130905 81
    0x54504040001e5444000040c40400041c04440050410120b440007010740403445000a115a50010014105a5643d411381c3c0401d50042d1540c01021740744d1400030b154034045d001d819510700c41c00000064003407040190b40c0d40c040e41a92044a00e92030a08a1545044054140c0382446401c121001c05550040c019100c26103041c0020903c0c01134072000c10088400c1a00704071280d0300b21800280c0420b1308040c003401124840202c45248505074103103000080e9400c40788540c54000081c10102c11503104104600584c025100500101040502a0219010041001e80715005000100010301e0180c029000f00b50007820301140007011541d8a03400ca81c80040031112904541980080350360810780400d01404690005500c1d0104980001c0d680d9403000300700500708841411032812500c0310b00151000390200200a001030720b644060603005e400200e0307400c00c1540c036041e404a0f2007013000610f2545003a0030005040181c4850007441640d0f4031401a148510b10362500015007a4201e01c629482 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 91646763 1250 91645513 91645523
    0xc0405070207050411192f06040201030f02181507051504030801062c0616060501140a0b0301030b060301061505030601020115060203091011030f0301180903051204050a0f 75
    0x40d9061804010890742c0c410318180320048180704039500301d04078540860b60441141404044520490401c819170380b542247e06201d030100200f1110f00b030342c0025005004d907100b40c030240211201c0041c0c940807030091501407424018149070080c098101060000c0301e103120036404900e001c146880303442c030f0710000900508844c40c0355000c2100740f6034020a200e002d41840c3c6021041080c10340d030500c01c04044429401e0b06000c0c050404800c0703556100440300b042d8008600700511100b1410481c00501c03007449131325082070131a120028a0326100352803406442488650f64103607425501e8809502074020702c0c4682541d40d4000100c0c808141101d5841c100440307984440c0da03464920002801e507a81e186102d50b20003440001800101d070040240d071075069050b0b480143e4284000c00890356148034101d03800a9010000312400311148200066040c0e07072080d10109000002c003400364048032503203800a400903105008501c440320041c0f0b400b40d00a40644104e84008125441f103455100b114002210 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 91648013 1250 91646763 91646773
    0x60613120c0605070201050417030d1d0c0103020903030a030906020d090506240f0112060e011701140f040b0406021306120b040c0f1202040902040306090209010b04060504050d050c04050702 83
    0x10070007500d602240c01804103850080c2c00c10300240d001804a01484c000d004048681d9000d880069000708180e501c1403181031002d210480740c50058100340f20500100702a2805201204a400e50203402210540380b0302030300540c41d0641190781140140f940c11401c5131345036020410810720b10410300460a206010f04042c0c600f50800180d0000180b0040c140541c07446009115150b40780d4801c607003030700280420f007005400a0b4100004e040149810b802900b03030040800c1c00400c1c4422a5000ba805042c072182c020000f49401c210021003c4800f26134410010850304009000901c05540d25604144141c5026052440b440b02002d0b20b01090703002080003c4030b4500e210580606401500e001400954040004031118000207090222920000e42400074444c0c55041e002280d50455006100401007191600e45902e02700000d0504010264030560041e000800d0110070101243d045401c10b813182842c2034504800d201041e0104482a6520700600c0790001407602ca5024880c42001c05c3e5001d44 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 91649263 1250 91648013 91648049
    0xc01060b13051311030a0c0e09090601050f040501030c0506070201170901050709090e0c010513080109050f010518030306041509020706050901060603020c0309060c01200d05010e06010e0108060613 86
    0x101400000754a0303580c41a00745944d4071660082102140c0d002400300301d0101c0c0e02525802c042d607a100805620039084032003102002503001e40403038807605a540c120b40079425203501c2e00400c41550800c0c040500341d203080304410046860300800501c0c4e0144181840e00b0140000005510001c000300c50140e038594442e010010b1060703201c595032015011400d800c00c03200c00c0800c400e580c0d503140f86007094180b21000444540030a51f07020104005c0504400a0001c2d040d58a415070b15036001c2d512080440d820800407410b884c40814031b03a50030080000c01941107941d840100400f80034500004000d030389500401181c1c2c2c0030356000520441d4001c0038041528108208000d085404a60004080500c141702d4403507051004402c642c0410310071a003880d1922401a1000d0040080c1e00007186229649210401040a500302412103088820002c1100d6a0b03229084901d003041100e42c10b0000f4019480320441358002c0c0328040d04484042c008d0303400c01e40f00c3e6644040802450f0000e40507100026942 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 91650513 1250 91649263 91649269
    0x60a05030d1101050a060303120903030b03030d020c0105060108070f0e131a190f050108090c0d031707030c0f0c1b0f0512010204060507080304050a0819030b010207050102120c01060b1305 82
    0x1396004450340b4020022039140d034a000744180d8540b48000503884d2503841020900d4840c1d00a047e501000405480c0c0d1303400e21484e440020342c0264690710982d42060000340c3d8943c0180304c600d1040303280b40c984501d9944005c100300e0b6030303503016040180e00c4503102082c540c41500302d01c124415158900b10204040c5c0c107076410404c041c1c21074899000d0b0000410b4013030104200720645842114020700b00300105484426a290038003840501c80c03a0460400320b550818107901c400030800900310561200380b41e4682460450a40304007148a401160b201060088900d201d402081c84e56030042114042d112801065800841307041e0340038807405200d0f040d052025203000000181c460400c20021894241782030b802501500070082c01615001c03001c000281401000d0150348005030340040750031340c6e45010f03111200d07440b640c82c490751002034640000400c15500006080040e110141c000301940803203c40641044e1740002c0c0305c82001c0d52240000102e00b2a001c01034854141d00390140344169080400f4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 91651763 1250 91650513 91650521
    0x30c0a0c030218090d030903050c06100f08070b030105011b02091015050405031903050c010c03060e0a0b030a02040b010207050d0c03141218012007211a060a05030d1101 74
    0x180401c200301c1024000013900016407a2501c084504001c02e00f000c440c2005c0d6540c0c01509160b031081d015007020042a220407140800640f86800d00d02c224240e1507005482c1c3ea962140200101d0b6001080148040e40c0211b64602c00b40310012203002c0000e12603408949085000d4640800419155038103110740f007014800e50301128400e1602505091130200080d594000400714141014134154107502410f21501c01c81d040c49e00c045009020304030355440c0081c01020300e881100151819207002c60060705060282500280004004140d5040350342c0800004020381c0816034194402c2240004e40c64803441e1608030b0480c010710606264070318605080801c3c0d80c180610003000c0c2c0004000c1e010903210103054803894995601c032070058584200060319505110b004c428490403000b2080150b10100003150015206c9210180310710f9240005003d2140000790401805002556215425062b064402c150300840c02030000206a81d0307100881e0a101ea017100d10000035158056071f2006039003d001d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 91653013 1250 91651763 91651789
    0x1709100c03080a02070302070b1b06100609090b060307120b12060910090c090203040507171f0209011d0a1203020d0201050106020c0603042307080f07050d120809030c0a0c0302 77
    0x20154601005d9a800175201c011600401e8855140805c003108030240840c1407400070004c84003124900c2c01c0001c0c0330b038424000e030712030350b030016554020200300c41481b070280b18810708018014a0841c1c880c11001c0d0340d03610210019414565032801d6260b081c2d0f80d82010340d140000c0540250049084c08403560b41003540c054149a103075400d02c040f54001840b8030500201700d0382c54903001612a03c4030314009081c1180707948418003c071840d501010320104c000c0390713254407401c081d25410101c50f08100e0304026030041c1d00300c9602086d181c0c200900d28941d2645400c110106c002c0a01415541b180804000b001d8050b00c02e4005074413066212042a030240704003800340c110b900003400205600000500c903480010001041d02c101c0340b16071801d41e802580c02c058003c0c1c0c10010380c0c40c045e03114840c3c243c1e600b060b80035600c107034403608800194609101404a40c50768101002240c07800803024151440301300034080710903500c02000a144130050501040f0240d901c074004e03604c2154074500401c88412007081d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 91654263 1250 91653013 91653031
    0x605060304050a08070807020a03030806030f010614040e1f06050a0e010e04030f030e060c030702120f16020a03080c06060f0108070903060513020306010902040905130f1709100c0308 80
    0x10521020400000d085903006501030402a585e5503180f500510031f0280e01402504070303070b50410200030981c110714849d200f18000d40895140340d09044c00c450a0320001d101d440126000c9118203155818203402c1500c0c01c52994088070000c0800540c0e10890600c086000e210b4103a44140a00107031610749000001410910807a40c01035041c01d010300a071b194081c10080501c000c102140c078001d402a0014828141c00c141601c1a81c5851040340c22140c4c0112403000050040702410900b03a96031406a078404c003540d400250902c3d02500d1b0381d564014001d2003d903030002101d8400000a606c160061240d002d400010b00050704025042c03142403041c090079941800268000c200c01c0310361040079001140c0c0c1203c00840e59440d01d1003002e80c6804802d0f00690107004841c000300e9030710b640e80c00900899018200402c40c5070b88808680c0c100b03100c1c05030024298500d0141c1080403456200da116403441a42c2c41007441c0c440c2e038400040c606a43d07054bc0c00701180e6500440f806041e000090306078404580 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 91655513 1250 91654263 91654267
    0x10f05030405060a0216020607030e0102010f0603080702060705070512010603060b092203030b060c070f080303011203080a180b09070501050903031c0902060a0c0b060301021c09020d0503031009060506 88
    0xc0d6561a280c3d100107000e01482c036404103500310781c003989094515000c1e03000b40071203039502e2140c10001c180c034050004081c0950b0800b040c450040029204040860b508003007018101143c40d420401250700080003030700c0910803404080303840c1e40c58a0401d0072030328102000040b180e1442c54200c040d100c29060303003440f4031580f20804c0840b5400d442c1c55050503c83d01d8506115440e980350940041c007030720b05810703080070000c01c14500464000a080c070a0301c801e0100104003e6513148400ea9030310003406031345540090443c600002070b00a001c1039070803400c0940c022030150a004003106684690941c1034030a40400307414410f8101003408280081c01082c40c2c000e142c94819401f103592807141400d000703103000700180c40e85800340c480c0d030010010320f81c01018556900f088440041641e60004c0c801c6e00d078640007401003041440c051003151001084500c68410031881040b40d540105032015003641c120034a5074140f40001c00030300040d44500c1503d2010000c5a091150000c1110038a4014500810b01 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 91656763 1250 91655513 91655521
    0x1b120403060c210f1b0c050f0318060a0207081203150a060f0c030509091f060c030806010c0f050609010219050c121608040305010c08150d11040908040b09010f0503 72
    0x600701440020300100720f01040d4103000548007401000c01c0114074110b0402594060308643d40540206003290050048903903482035158041c1c0c5034803030381819290ba662418035102c0507090a40c0901030400f164019604a1517a403000e260034590759641c4d00d000742400108010051100d00201c9840c3c2e081514503040050a01001910000c11200b1510038000f00c00039120400d84078000705c0c0d03048031000e0510105030070a58622540e00d400c0b60441002c00d4409100410182e1048000304d850036056070b142c2c521911521700540c0c0f40d50308000c0c140d03403000c24601420b020507400c10244d4050301440000503910315100e04a00790103580d04518208208040002140c80c042c001614000090341200b690b42d0f8020301c07800310000b01c564460040408201160010601c0010b5019058a81080d15080300301d41c0c0c0c62001800c2901c81e5032855900c45441a501c50218407e646482c140400141002030340da41d036511040031940203640890b61004001600c03079015688115001100310050400600b5814 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 91658013 1250 91656763 91656797
    0x151d0604080c0118051501230405040206070b040b011703040f09050603071d100b032202280503070506040e010b03190920090c0a03021b120403060c 65
    0x101800c05004001c02141d600c404036002c0d0f1081800088401080d030310032405142103a210070315a02c24612034140f0000010b48180c0c10040000202908007a5021505a40d02004010203001d042688c10140c103000100c0020031412815000f03d010f01d5646026625002400c1c600d110920401800b03500244002c22868201150000546001803c00720740c2d0b0360707080302181c0f400d0801c0d88642c3c074007150910480030100f0b0800c8624000c07000044030104464503110030030544d1005072201c0110309064038070207006030703005e41c0ca0302d01d0380d48000d00388100040400c1e044000d0b00180d420100e01c69801315420091890304102140040c030341503035a14185031408003400b180700014415405020800400100c2e24500b901d4401e24403a90058204000782c04c904190300c291100d14400e040e01421910009034034606410658810785840f6080ca00d00001d051084000e90404080800c09a12200030a14405000c0c0545480d007a0080d8040e0b4440380b5508200e000c0c0c80aa690400611505040c00d403076800d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 91659263 1250 91658013 91658023
    0x40b011b060f09020a0e0403020d020616030509071a0a0e031c1d0604030809040b0a0302030706030c09030b09150a0203041a09030721030b010203030f0a15030609151d 73
    0x140c02510000700081808029005030003ca00029400f41010340086814001d042c40d00c2c0c0203c1c0240d088401d0004d00c1901079a0300c50090310318805e140c80c000c81214005100c1c2d00155030002518054915043da11104104503070915801c1c00340340d21000c81c06103e000d80c00b02002a540000b10000c20308450030403140300895141d41341d003008201003403480d5000a506000c007000700e26000742c07070159203940d1b03070170000d426402240d0000c0c491030500c0c0d140d00191400a01c000160703a0014054695035180c9181a4000d00d072001c03420041c8445680004007040d00e0309038051180201e08050100c15500b901860b164580060216941d64818014040814002e2107444d1030041802070018140d02d41c03109442c69030003a1a801480d48496401c1420310441054030841c40716003c2e02c061180400c17800040ea100e0000f165001d4494035140b00003000e248840d085414241c8052081060040c0c4030f458035019610500c0341551020346202c00403642800c03038401c0c2d4100e00c200400c20700308018907102e00c517158 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 91660513 1250 91659263 91659317
    0xf03010504052706010e070c0308011e0504090f050d1403010e07050f0d0c02102f0f040906030b060604122d23061018091a06040b01 58
    0x19552140051966110003015000414022501c2d4507200c3d900322110f42d07108424000c900d80908894045800e941c007641130700b00569410b80b103d0344a0703804c045d07504019000c03110450540755030b03507040040d06032168402c1641050080d070b420b00d4001220305055140c001c0032420f8034104404221000068000d04080e40c0c1900c600110b4200e40c0e4807005821100f500503100340401c400700000700c0380658101c40c0d00c407601e0007015400b618012601c25000c4c00488118595914088410807900c034039000c0005139190081c1020a002414803d00c8001505150002c0c0c012440c3c01da550402441441a4000025031005084898a241c142403180c4c490812483c03800080c044d5240c1d02e0394285c0c03136002d1025152000c555440c3c41c0000841402c10203414100b154030920343d503c048407a00964200405c9943c400c00010b1800c0d4a624a0420340d1240500c0b42c0e840711041d02d03a2003a040c1c0014015415181102c48614080d030050f040c000200004c45646001c3e90341407140481d046c01c0000c0c40b010b132000c48 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 91661763 1250 91660513 91660519
    0x10e04120309020103060b18040b010e0102031b190b07030e031e1303060216170702010f3002070201030b0d0c05010c0809030d02010c09090b150307110a260f030105 72
    0x440d0b0002e00c0142e02501d10754202c0c0e9800f540205500340306050a0702030114950049800388040c41001b0010364540c0c411101180c0103810030081030400088002d00a4801095041240c2c500103128590b404848642503080704d6000c41c500c01d2040f4654940241420005040c004d035180c005190b600c2c03011409001402c00240002289909040f941d14841d44021500800c2c255074402d001040449000c3c04075000312072039000c088050512520341e074182c0c4c074002e034181c444039000d4140035001c1d50803035a6002211507000e91400d00b00000048250041000d04480f8805038450002c1d20015082d42d0304482d001e0700032006841c036640402c1403c0e2001c1c046410a090100e0301a407a818101c2c00b500c186001c3c0d5401d032052310400a81306505600140f1060003d940b00f00c0e0507600c8546600c250340340c89500550280b2000700310100c043e441d00081d0380006960410304504400c92803c3e6081980811040ea00507105040c0c103500c5c24040e811380e1160b1a00580030b2b6242c6589901035140d40e00060140d240 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 91663013 1250 91661763 91661771
    0x1d06010e34020c03011413020607140a05010b0a090519020c010e011506140a050d020904090506091501080705090a0c0203130f03050c01050307051206010e0d050303040b010e041203 79
    0x1d81581200c804005284448441008030412102940d1500381c8005540039600e4100180fa000302843c2c40d0078010640b002c41031448102c150200552a040b1202c00d440390511110364006494040000002003446100086074179501d81040000340a007944c0400e161a080c441040f40d503010300c00000200e003140820058849451034030450060074100c038903880f03942c0703002c8411144007000752040085a505540b60a5908080e580c2e400250155000c2c0f140400e10a00030f148030507106401614502402400000e061241c40d15503528184003070341d8031000e90b04921980c042003800070490f0341c003600c21a030080c444a450300c000310b0107035400104080c03c895507512264460070b00c280b0898403e0032843c0e918900c416192445001c481c7c4107407108881d588942181940d065020350203036446581da07912801d08190610302d08854229008002c64100a82944491400e96410040310401c5009100030f5880b440d1a00e400c0c3c131060010380003a040c00b86040100030004101d04001901403a01d032170042 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 91664263 1250 91663013 91663051
    0x7090c05031f120501021806070b07030903050712030506030c0913150f0509031c09020607020120010203010b0a09080f07150201060f06030209030606010c020901090209010c151d06010e 81
    0x850b4001190410000400c95900e01c405100054010301100e040558a40088040240c20800301c0d2180000c0200602080d400080c080380c0203901c0300c544a13002c1e0400d0f5241c80c11959a032221150660980740c0401da94405000c09403c08100d00a8200c5c1c3c1542c881c060350608010001404445080003040002202200d40102e103081c0c005650901034068140b010381801c1e0242520fa0700000d011220030134107440104e900024500403507080d583c01800d182d2401680742c00442c0e503448685410118440030809200400500b417004500800f041a103003601c41c490400002c10ba56890303808085070f83e010443c40000c051000c10703a070f400c4900b07500310401e4240600e2002d03800f4020f654031200e54465480c200069054154005141500084080e1a010b59aa80040d141c070f1019a074080e4028038014018408c03079540b517004252215050400314802c02455403200c2082c0640740011007480d07240c0c40907240800b2043c0c0e1140c5004402400341c81c0e5581409004060110020100d100c400e070000460 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 91665513 1250 91664263 91664311
    0x305090c0d02040920190315020f090a0603060f0902131502070e010e010f08030a091707050603010b120112050d05090109120b0106091217030702030f03041407090c0503 74
    0x3e0010302c5d5005500c09014030480264400700030781d400210340a0340756202ea108101c00c1000111040d02c2e07005940c40d10703030561100000002e4000250074544502c0030021303540c4540c5c0b0000c1782d10042c0702c00d507008981d85080850522030381032641d1141c0314460051000f030500c00700b00d03a03011081d0b45100100d240c29502c070702412482d00130aa40701c0860740c0d021500108424103685034940c182c661069001c200b4070780c0d464200340d1345e21660284000041c0300d1a8203010f411104054000d100c1007080c2100c0c003850b100d400007291f030f41c42a40055510100082e09010100094044500410681d414503100000a480315521501021902e20401070000380300c03420381e809100310b40c1c054800050402926800e61408403c024030078003507103000c01d04080c800038100340480c0c0c161410301c1e8020404044504000ca1844031078002034948070550106002101940e0b0809000e103110324001c01e44880d90401c0d6044043c02c2130300d5500240f40243c14443d102c41e506400c00102d98110000c460411814000e2240c5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 91666763 1250 91665513 91665521
    0xb04150f141801061e110d0f1e030e010e010e070b0306060f0d020318060105181e090a060e010605061b01090204020f0a0e0904030f140408070e0405010b010305090c0d0204 75
    0x2d60200761040045080790380494841e60b4400c450b01c01c1c1c61010f50001060700d001302d0001e0981a258046d251088405105d5028038500c4205800c158924401304042a40350003102c0703c0b0711000950710001c6424138402400f84c0017855520b00002c0103003100344207109407103035124002c039103144000002044a44d200c1204503964411800c05898a0b4089107006d00c010f548155031034140380c036548020000191001c03580078100c0e840113000070040722a00406002e4030700014000710310380c0f400e1180c01400304441d0906621494607000600b40e04040c3d0300d1311008039001c1e1203402c50503038508141488552200e03801c0303036031802620b860b44a0074910000603502510b401080290001e0020401e41e05c54110b050140030111030548450b02c00768030480c00d0094160b030844001d00043c00100d21032000d03070b006e82101c076050854024000d1402d0340380c62100e841c2407120b51145c41002107000410040c00070a210b40c22500a09190510460401d03010244d984d0500c6c0048a100f007903011010f40c1103580b0790388 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 91668013 1250 91666763 91666789
    0xc05060703050d06060801031b0e01060e06090a03140607170103200d0b011802031326070c060311070f0201050f07140303010314060903030f04080403060509010b04150f14 75
    0x1034284413040c0ca03290001c0c0240d500303100407504030700d84500c0c0b10b03c9a041252100e003a118011103000f4203a11b003d800b15107005050100c02c2d0007400030824a24951198144900610300901c01e2074509560052124030300500145603a0400011031000708114140844480c112500320100c060099a1002102030b20142e054015901c8602404001c1c1080000080e05040b140c101c689601801038216a2000f64802115205000008401940000303030440503a4425840102840070044c1d0440e254030b9020381c401030054548540a0394100716440c0e050240e00303000c1c204d00818900304842c594a42d41180c1d01c229001f4140035020500092010f49074050b5450907401c04001070b0350002e01041c2541701d034001c0c0002d580303041c14189469400c04c4001020303801192040003c6245696162061180f001e0180040701d0000e030030000040410124001c0a0040140700300008143e02401d080000b100c00d1000c40344028900d460301001840b01a43d00c0004170b407402540c00d10148201c40c001039800d24950 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 91669263 1250 91668013 91668037
    0x21090a03181503060602010b0609090426070305092b02010f02100c03090204050108031c0207060209060c060702060106020f0318040b03010204030f051002190c051c020a0506130c0506070305 83
    0x50305510741c141d0542200d82198021b8000b04a0300c0c0c50704080c04a24880c14000765040f05184003c50300140b60200c0c0d0035030340c80060004008401c005040c01002d40e103c2c00d07084d00003410200e20284517290864031403490031042d807558403007900a0706c488840d002003240e020f03050040f4504204400c90080c0710040206a500b10104144141444041c000700080d0500b40c1c021480c00e40045a110000412a21410200c1240c150040c41403c900700c0690311143d0300b00c9030590280f1002005407240800741503242c0c0000050036031454007242c000c0c40d040e4140c0c0041c0440d805541daa2500c0e40001c000c031940c245c034a2204210890828004c5005040c441401a805602c005800414064211450a000c520075402c4d110ec0981c11030710b0b602a1700846440ca07285104950004a58600404001c12004d104500340d442400f00301010500111507030b500c01001da0082003101d4104103062042ca544405002da015400da806612104208103aa0141c0c1e406003030f00103412000e0502400c00e942c0c202c400b074 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 91670513 1250 91669263 91669289
    0x50105010f0e15030a021203040305010c0504150c080a050703140706090309060e03030d0911180907050114040905090a0b040c050a0602031204080a090807090221090a0318 75
    0x155544859240080c03082409811125011845004892042d849060f60044c000c10884d4816020010300b50040c910180e002e10007040008006070082c06811031160350b035210952100e191405162401c050b8a1801040005c0e48509000164069044d21380e42a25454825203400c041d203001c3d01e40a043c0d4003906007214010860300104001500310082040c42940c0305064985d44076000d503030100d4445ea1855040e04203210601c401c121a902003240c803170080d00d91100c004038a802040d07190601c01154050801986c0801003648000c0021400408003841c2c8964846072400602c240f50269003e8880c4094589000c90a0200c0400012840e150010780c0c040740d504080c901b40003c2e50052150600410800308000ba07680e0010003980d00391440001038040c0c564031344c4e40b00c15076603101d80111428030030051030101d4405030800c0110090000c0c0309005a880a100c000c249a480008080701a0205103200700104813201066001c1040c0e0b040c00c007002c070221040f030008400005a0882d0038030a0407 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 91671763 1250 91670513 91670519
    0x5030a050c03010c0c0b040f1e05010b0108090c010503060405090c100801030c0f030b18030d15091820040902041b0917071404020708040b03100504150306020a0c05010501 75
    0x419039680d0711400b02d000300b08010003030005440b102e1900c48050244810342c4001804a40d074031900f159403a00c904402e5482c1d0181c0b14100403a100600c400380c0d01ca0b035441d0b01d1581d8550708040c1482c2c102e8040402400814498800240548401081c00e8010398580010400d403910401030000101001000c00b6041021500c0c001c1805000b48000c0d5000f00c0d01400005c0c03a146e0f4002c07100c00340c80d0000b14218465440c52403001000b40c4a48640007648401c02c2440009082071081c0100b4400400c81101d410b031620004905a03a0b10701c1c0a0101d0b180711004c0b202c0050041046012380510000340340b03a030195010006030007010f40ba02c0c041e403c2800c3c034008005030310341c03c105001d080c551500c90410090303d4031a518440d06d4001804003050b4018401880038050001000400d610010310251400785281c0e58290290891b0303010700b80124012003030140035515110721001034902503900b0411044050701c0000f4500d428400581030650001d000c2a520b8854074030100c034a90468003c0c811965 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 91673013 1250 91671763 91671773
    0xa03030e07210c0b0f0d200d021e0c150a02090409060605010807031401090b030705030715120b090a050705070506091c0503060a1a04180207030e0102010b03100509030405030a 77
    0xc1d90000448007004100004130f2003e46070019103c056114075101414a103503039199038010b100c911408543c0d0032461880e803840f41e40b54001868250940c1ca0003503115440c94100107040c400d8603040005c039100034000c2d20f00c41a00005e403107042c1c400c0001c04542540343e404000780240710740825140c01c6420f0020140030b0240d150003900c222a4207a0b83e442c100c2d48d071080f0440403242541c0c09460761813101d000400c4140c0143c1c00c00055a007004040c1c40030039a9a00010386410301e0356001c41140c040361803210070403d800c801c24035420904000184450283e100000f2402c2d01c0060892032240c0d914004a0203542c8100255040d05500408882a41c00d104403026501d04031940e454038001d46002e0440307803151003003007503d02034800584914046030420b40320615000103a40e80607100c1605003c005070440d00841e49540c244907036640180c0d078040600b07006100700d445030700c2641903a0400c0c400c90b40989000440c0503085a03001c2c00003c031902d8001102c1c2c203500c11a880581c0c1441446500f400b441 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 91674263 1250 91673013 91673069
    0x615090f06030b060910051e0301020d06030c05060307020706030f0902060703020c0301050c07021509010309051b0118080309090403050f0a03051f0e0f04080403060c05030610020309030a03030e07 86
    0x41e01820000b03510351340b880200110500c0c2110465120084401e0801450400e8044804844440403040c60501d110002003802c80e04400380443c0140d4699030200107100d422040305000e0711040d10303020714616102c00c001e07550f00d80e0b6119103004c1550300d28820301043e250b907208002d44e40d40181180e90392181170030300a40d100c3d49640c400c2c0c0b09500e0309020412205e0850111410568050402855600802d41480880e0044150b1700d0505881d00301c9d4a0010700180f01c0745907510640860000c00401110004125003229085074100035851007007804805000000c2d1032054000b11540e417420703540d41c501181e02d80540c1400000c8010302180300d8800c5501500b0040c86078922814a5003201c00f04451003110031118441e100b2269a40c002190b0410350401880c1c0e48940540210741c0703052f640380c1e15001290116080740000510100c10300c03480d450580c840c201d0905140c8000c60070004d02d400003e80380e00340c1d240002c0034107030350750241000750b101440008002c021000e203074403e140748081007603004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 91675513 1250 91674263 91674269
    0x180403050d0509030c0a06050a150b13050303030609150117090309030f07050603070f0c12050405040b030a111c050d050301081c05070201080a021204230114040615090f06 75
    0x85070402e00040d2140380004141c2c2c011840100081c66030781d100d510b420380140703800b40503181d4245d00c4850051104c01d9802d000320040000c20b02060b034420198008048001054000a10039003042051064a43c2d03440d005075040307402c0d0350800720740c2c91a100050724180d02c52605048041c000314208120074002001a2218400540c1503408280e50b01100c2c5440c0c284c540071b480e034005018404610924860501004c25410508150200c0e040035101d035800c41002841b100002a00064140140e091034080c460740880c3c15802003500804641e0360f110b503c0d0062415038091814803421034641c0b8100c641a100c925000003d40d070113103005150007411980240640c402c00c0c401d0b4002c4485011442d00d5011a8041c196070f8941090005d40c01110040c1000d049c020b01c954003840005c110b0302c403a42c80b590003180325515103070500d417024001480c8501d03400910f5a03964035000d05d070304551143d542100c0c0e0041d400392000800b0b103071941018060380c00607040112058a004c105200310046603103c4819 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 91676763 1250 91675513 91675537
    0xf10020319090602010605010e06070803070c0602040e160507020310020c010f0612030e01020d020d0c060e150f0603010605090103060e030415271203030905010209031603021201020a1d18040305 85
    0x1031540b24401541c3c06108030741c2765900840708000072400b1030f8424020395008540d80c505000303011043d45505050380c01a81044c038408000000b445595411089400050100350501c00c3c01d0402d25000251220102813407980c1898002501c0c5030010400e6001c1150144021720421003181c581584984451003814220085003140c4a80c12031907000003130302040b84005034004e103403095000400722200707203100c90100d0704aa07d500d19040a801d06110303104610440c0302c00180c0501d0030f80407070120700740c2c00340489000380d14114007800705071207015809040d2030b0041400b05030b001480181501d184501e80c4201408500f9050742da85080d40030b41c22041d000507440312030b06060130310101d01c18000500d100300200661341c2ea03190300002e402904002c88407405a0001401c10403601c02180c100b00c4500d84201d20f0711140c1c10180110328000d882600c0c00400312000b1418051065000b07005403070a0104070341440138007120341c130445d520807201d40070803c1066580c0c02a414207240182654200000e840a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 91678013 1250 91676763 91676771
    0x40503010c0e060703030e120d0222050f06070c08060c04031203060509010e0a090501020a03020a090e0601020d080a180602030403030b030c060f0a0e06040b04060212090f1002031909060201 83
    0x24010b88102d00351501030200a21091500700e89036015001046481d0100c50503000e10142c004c1c0020300359001c0d02100c900710f40f002da619000320486140c03d1840c011510408155010f0901c526141c07180111040034094450395510f2183d802c209607040c040f030348013003054400c0b181041145414400a00110b07407250507203204812004105a040e540e981c00342c66002403040004002004061a2403500982101d00000e000d070019181c16099078003c200e4080407980024504e200150b0113040c0700d004050b001003404480c05d04100003501e4222080c6403404108484000c10a021400d50010748032110074071040301d68944a19061010350012101503021030f1408034911103d00300802c481d1140e0700002c0056181880701c1203085c000d600564842c408002000c841680305848132002440600000d20f09161140d2130064024a880071030324003641005030a000d003100d55100c010300019142c104645285c451580341c6800c034a54090070403102030081c1c1c100103920010350085814000e0300e40d1680240 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 91679263 1250 91678013 91678031
    0x180b0a240305090604030305070c02030d03060503070609031e080f0c010b0f0d0b010303081305150a05010b130918020415030203210711032401090b091306050a02160804050301 77
    0x542203502c2202c40d0401d0b07411000014000a201e5402180d1104440c10008801401a004203180000d00426140841e03900d1409014600e81046060010f003254681800d1342c5082d1750702c00c0d0080d5008020841c110720b0000300742c400c0045001c103a40d440c400d1403050580781c00c0d20002c0c140c00b8241d1683c400380107106000d6000124201a1341403000943c0014940f0070a92865804540d070100040c5555008104440d400d0001001130010308405030b80f403d8030307a40e2420294244002c440040e0b20200380e00074200b144c07142d10b40c001c094034000c4502909001501c00b10900740c0840054103154000d520501e041100d196406c01595a81e095900a0b8229541c0500f102c50300740003140f8400703401388200010f2002000040714010800700e41d20014054074500b904254040d00f20014000400308800d450303900602090704180710300c9602c240e007120141600d083c5849078886003418568058415a11080010744840840d01162107440e0388120207110f0410a0070204200c2e0410b0083ca4401e5081070a00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 91680513 1250 91679263 91679267
    0x20d140d030204050a0f2103200309040c020a0203061b04030b09060a0b060f0f0c03120c180306040209071d1207030c0b030105090105090702010f090c05040507020610180b0a24 77
    0x194007950340500c40501c168030b284151403400300f032002e0100c0270003002d503041c520300c03040c600b983c0e401d510600d81c01540c88100780c00401003540ea50700e41e00001c540c401030a44d000369400040c0950040b56882464a41d10700000c1c10031000c0c456034001800e4140d5a5042c40201d5400150b0785c1e20030443c020003000340d02424010043c89200d80b5403005a000020300c00c140342103485c40d00034000150002c00b12860b10007108080e10055204880d5003500d124041b070820307aa100d1121584400002c120040c10f190715140d40010320101c409403c0900b000403801c2d502d06401142d001404134048010b140250140d0880701d03c9544449502044403807030303104080000e1a60302d80c1e003a80d050b201c0040c00302c0001da00700818009a201c000309400b04664890082c00100c009a02c55140500d0003070309a807900500700428002510006040f003000c5511030740030400320540c10910581034400031031450464004110b6007002400389a07480c603510942d0780000103008803080e90315500c080202034200b040300b05241c000b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 91681763 1250 91680513 91680539
    0x302060f040305030601032f030105011202070b0a05070c0c0b0307090608090703020609010210090f0605010605030f070e03071e0f080a050309060d1e05091002070807020d140d030204050a 82
    0x10080100c2d00070f0005c40d00039070098000308103008100d540c03850510141d040e1000d05500200410240d880c001005015a50703000c440b40039650341140382540b070203001d655441800303540100841e0000d5541c10114580fa8030540c030072803200341c001821310b03a115202c007900c102d564000d862110214002d42070000e803090081c3e124074492043c81000d4910380d4610f40070301ca2313290f01484909045004400b50481c8010003445440842c82c01500544182269860048121401a0090814008107008104088409220443d17000617103103840513103200074502081c2740140541040c28003941a840f000010150956200215207400d40304424640c1c0d40c4810540700d04030000c0103803468000304a070540381e05010004052604000c6000134840e56489008620354441e68400c580080e00c03203040c800558000c200c07140f46034442610841c0340082c1a55074860520035000001e00031103801d503141045c000307008440300c968415081030f5101d4540390310008009500a026641c0f0400112001003450b2400e1a0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 91683013 1250 91681763 91681771
    0xb01020f0a08090d0b09061b0712120b040609020d050703060303050a111005130204050601020c2103070203030a09090e0a03080708090a0c0f030203070504050c0a05180316030302060f 80
    0x3014144400480d00c88940c0307030b030000110310303007241c4c40d6004400021080c40d00e461182c43d8000c0646503070b0901c00000050440d01c01113960340740b04180315a0021420881c100305801c1e40e00e040a032180f11035900200081e1010405041d440b40c600b400c00604184150002c00c031030040548100704a5039207607001d500302c0b0018000940014414400060002d01605486004204200488289400720140c400c180c400842e140704400d004407500008608180c002d00f82c103c1024005001009129004100d59010300514048051408020035040ba034050040340c2d412034000e02a03035528485058058680c00c00c42c0b0501048610b08404143c44040208480104035450759891400d40c407041c0c0c08540d84240a0f08a085c00c0c040c080c00200041c0e007840445009004c20181414082e24600400d420250246d2200e0301079401c01c010040044206411a0040f81d12404c14680b035030140264542c40c4d00384020754a4040c4103840120b08520742403605501103e02c240c0c2121500e50764240c00c0e9110180a80b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 91684263 1250 91683013 91683043
    0x11030915061905061803010908091002010b0114070303140709030b0109090201050306011d031006060e010206150d05151918050d08151302030603010b1c0204020906070605090c03010b0102 82
    0x407003440245810002845c041c8100c20042c0005106000040c4c01c6906640f02103d108400007114401424084e000c891040c1690008000d105590707800079251503040700042c110305c80c00080e000c01b018080e07406056841d50310a6044610320b45020082d055032203500098800b00f0540c0000030701c1c644103015084900d9030680d901d60640c0c48080054560b00503611200c0840058015036960685007009024035a41102d0404911207280500c0617002c6240620fa940c1150401d900b004030701c1a0040b5081110442034824110074a2203061050904450010523001500000240b105023002c2201c40c081d412070900040284001c0c84c2041c07140342d0000d080081003500010200c4d443c4a01071941d01303503c058a4480c0f5801882d82c0300014021441d00d000340201c3c554080244101424244141d8000080c280d98801481c9441d24410341c41c541601c000038815078000800c078800c0c2d120001a13032452544640113000b5414201e84403911501c06482c818007035840d100390440d10390310004080484040035 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 91685513 1250 91684263 91684309
    0x70305070e041b061d0d0f20010c050604080c070506280c21050d090f050c0307050102120a090b04060203030604050a02090a0603020f0c0304030b0702060106031505060d1103091506 79
    0x6210102031045c160032a40d5001c41030b0003140c0c1c045000d003540d10031800d126100e5100300010507580c1403020f0050324142410000346040c600c000690015802d42c0164202d113849488074080444280303410415049035421040210b28040c1303841100030445030b22f00a0441000030b20711200c0f003c403101c1c0d12024000c0d01ca45003c10340403070b040e410b43c101c01180980d286019440d2044000314407056840340c08c0d0868214080355012418008144a994612403040700038210481c50000002d40ea01c461015810701c2c1c000000c1d2a03044640074000610040107079468058603036569050207034681e001200c0d0301d4025801c200c00900e07158501e100716404440001d22405550b0300f05a400c800940000301113030714a0f501000154031000b010000f03840258030681d8500094a00702d6002820004180c1c8a03005240c1014090b16044420f00301807070540d0410740310070340c41e140e801e44000d01400c0c40c0e40112161329000024401480000b013480c0303100000800340b07942c00d9194901882200d0781c96038241a640240 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 91686763 1250 91685513 91685537
    0x120304061106240f0907120f050610050c010e0a0f06050f040213090201050403020a0b03091c050a080c0904050f1b190503180d02010507270512070305070e041b06 71
    0xf81d580d4010300600c002e04180c8441c00f44001140e039000081d950303034001c40c3c8988013182182401d0b020b42200448030440900050400b01c0214000d119100103100506c41d0108501442d00425031121810001e075104880c001c220b07900b0502d40f0b401706580c0c291807107030030803001422074007400e0003080c050369000c0d00c1d501d9581e803009084130041c136400707004a040220800001000d0b0707a80420b00d030003510f20360015507600d007848031159203428807500401c1300c400503912140252641010035034090f40041d09240b00541e403072804032805840384041e003da0003458001400825048500313001e1189441c00d14002440d2440020030703406000b0303e04039802491814141c020b003107108070099900320340211039504401600344505410041c0c26141080180c1d501d40401c000745038010203050808441203501800001c006c501880c1402140c000d86008040444640b5000441081118019a0084152181c00c0d0f00e5043d0000026000d850036124068185000850900300a044104940003910303003204140c2c0f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 91688013 1250 91686763 91686811
    0x9160c03050d0e0601150807020a03050d0b0a0803071b0605040b03011701110f070308010603091e110607110a0b030c0a120605060a0305181906050a02040302120304061106 75
    0x701100640e01c2881d12a0507040f000d500800c5198007a01d10300d200c00e400120a00b1004212280050426046502000080e0b011070303042012540b280008200100c0c080d070148001c01d0200702c02e9801010706210015070360052080004403071415a00c485500740030903680342c2e4111894000c0f4041c492040000704010007401140c10005800d44500000219035200354141392001d03904000007905102200151100030103500000700c40c003415150808200d24546070300e690690507694851000385183c141c0c0b1030b40911002000d00b80450310000d207425541d4603585001c64408006404803400741441800205400d0800c20030790340f0480c084028a420110702070b104403401c004031b81d100203003255550008100c0e925604000e010003400764402050706d0030043c00440c032188284203011a0390704000b0034039814083e200c24180e405170304480c000c00d40e601d40848040080c440c5500c02540052100c03200c002c0d441000c8041d0085420f551214195407a8969805454036401c0315581c840c246034800000c8150 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 91689263 1250 91688013 91688017
    0x102091e030106080a0b10080105160c050c040501080f0c040b030604030c0c150504060e030a05061f0801050106090806180a030f020114010b040503070f080c090915070e09160c0305 79
    0x940001c0010444956a074100340c10b20384180e2007590100707044020400e801030500e203208010f205039002044549030040040701e1030003614540b4000c0124400c0c000040c09400c00c442c2d070701c01070001d000304400e503500e04009a0302c24004901e4001750244140912040c03800348101c42c084503024001d81415900c03985c040307030390208030813085038041d15003100810116203003550080001e207503440c0c2694503420a040034100f0403424904600c250301c180c42100005401003800c0750407041044a0003c4503203171a43c000d610900b00c0c0c00a0150750700e001c000040d9143d106003040122440c82c030940d10113480c0c0c110496000e031018801d031644c030f900100f21000000c0c07081d030b09504005061f00c00000d103902c9040da200d405100a0703000320212000480c0500041c60144011340082104540c56140d45290079005500d800410340c941e841980b0075400035201d21b8003884032084136103005c901c42c0030b9031910100191400c1c984007455170049040381d0002b40c0c9682e980482c4000d0801d1078644030400c9030155001c079101d03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 91690513 1250 91689263 91689319
    0x50d02120304080a05060411060913051003080c070303030507110703120c0803040b0402030706170604050901090f1203060504050103020f1516142514030c180a0509010209 75
    0x1807100300b10004000d00705220141c0210b00c244040c00141c24107003030545801440c0540e480c810f08081108850039a500007411503007404a09004c40c044e60380446545c00108540d00140910000082c0340c05444004100c040980e442500c0030001d0303403100351007200c49007012203001560364000a0180301056800e9008402c103a4140b0f4a005100204e5451150f1030700305071801c45000d01e0030000d0004500e418004840908180e15007030412011145001d0721500001c0c0200b802a540c8034040b0b91060320a410101031035802c5008500c002149250034491928040075180001c1e141002c0803034a80b620b4081c0504890b002000c0341c5290b0b412204100d2020a0340301114420f400c1007041c12105a11160300540380f501070300300700c0c0b0700240c0300c2c2c24281400203001e42d0000d000040b2044180540000000708140c0e00c0000c4000c1c00e01c40c184000c6842c1940400441d80d20a0a0b101280100c820100c10f00348181c180880500850315030f62240c5090f40100d50225610220132201c211600350804040707d68 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 91691763 1250 91690513 91690549
    0x20903070902041502010c0e0315060d0c06080f071805061308160810050402030d0c060906020f0901030b030c0108060105070206040f08030310060c0506060d08130b04090e07050d02 79
    0xc50794803000c400882c0d0241e480030407565024408880340070340a00c21781d00f14003900d00786803005c00501c1c0000385e200c2240a4181902083d080081120364944d140124080c0b94004140d0004540316800505003070000c590f4544400540740000309441d200d08048214103402c140d13000e8066041c201081840e400901510b03164008150000910000401407000071107031084032141800e0a00090074102201041c2c1099400e04000c2888010f860000e1840484040c40c40c22410840e268500302001d4000a000986003d00100703841204480d484010310351a4401d03241000711110407000c0c55166006140303004d020855810020340030354010b00c000c10710703075100400051506480780489030340041c06802030000340d48081704012801c1000001580640b0319800d0000042045598241d43c40c1002015030380a4040040310500304105502074402c0010342c680c0b00c00055441e40b0000995801034072410301014108007101400f880049542000d0301c43c09001c81110b1101e640901c050001d40c0343d92040 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 91693013 1250 91691763 91691773
    0x22d070b0114060705070b041a090609101803110901050103090b01060806012c0103050906010b16080909090d180e15060c060106080f0a060617040201140c010203010f090b030a0303020903 82
    0x800584203000d0040070b001f041c0c125a446030b0511941d400c00320301c0760360030b03c4c601c00301000b20401c10b907078203030907107000c4001101c5e0303010000038480b8115071a10324080900d015401c004d4001c0204034018480c551129019119585941e9890004509850445c180071f0403003095200103001c0d661245442e194890018140554240502c00810220101c8a0489800c2a036202080304070740d0b9050084e15044107400e002040d05504140c0d10070102e110b041182e80075440c28480850030040d005d400e480080600910b8103030303240741c20145a43c4074010320412900155044402200e600700c450003820588442d95102c282c245e0b100c1500c2c2c0218202c1e0b09400d50312240910050740f0b400410071016000c0e050b2540c90003440d05291100303400001c5d0192242c00f0b0319045c00010310060354044059400705a90032010016071b1181d000590307095103822030070004500c000441c028000703015001141201c00c8001c80482859440c0840340807180c884440a84c580c21030000e1001280c441d401a1901640040641e030f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 91694263 1250 91693013 91693027
    0x11b0c080f07080610050105030a151d070f110d080604060b03160207090203010605030403050310210201021b03070506070606080a030f1b1113020904022d070b011406 73
    0x518007007014090600940c04600705009901d0140600c90b0081010038030042c840f07003403400107010703404010803008120303075514808000c010280703040721f00400321f13100015411904080c202007040b00c110f8225000c100100c0e405407105200b50740000d1000c82200240c41c0f0005001c5013221000009044150722a48481011445454040085004150100c0305a01035040800080d0510410380e1040580700c0c81400108412900003003200c3c0d0103603041c5402176690340c0300440416064890307040021303a9031100d01c54240e01c4072200c0c01004010b000341c0031204840741d0116580038420b4004403980c3c06400500040000c2c0c00c003040a0810740e8440c40c004210140c90f002520b1502d003184000f540003815482c448003200350030105203580d010448031215249103072512001d500c4d050751440075014640404402010611580c1901d00e40c00000f0402d66403030000007a00c0002065141f03e0100f0510a03c002d400466880d408661500c1c1c1e000c140344005a1070240e1001c04444a00d40310740e0844800c0220f0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 91695513 1250 91694263 91694279
    0x702030102030a140703090302070603021b0708060601090f08120a020709051e0f070e060d11070b011406070b1f050d0c150306051503100b1303030806010509011b0c 72
    0x910f204103005440001e06000714003e40c02c40c2c4401801600c141850100c00101003980418a0b50940c0e48a00b0050382d9107949204038042509811600b12850141c20408a50014041450380c000e0030261307282c0c9507454441c4020714803950f284c0710300362059100c1740e4100c080310b000d50040d0901c4049030050340d6010b0341c0d4000c0d4505580080301d90124012428110700e81604446851075000184c0c094210914a04a180030b00141e9480a0301440395201041c4d0700207540e4980c0202000760408015035407668401d28045010100a002d01202c0d9118000c0c22042820f214094801c5181c01240329040303500c03041603082500c4002c12105001c000d6852022650b602c4010041400c0b13031050400d002894549000c3c12459004403a0034003c250419104211641da80b20024050300c0769130700c6c030b147e40c4e4984c051f2017221006142d000e0703500004003203442c140c0c17803008030000c008403402a07d682da1103545c3e0000440d000d00c42e043c3e100d40481c0d9000488a080c04020700b110000f184107240e002a11600c407020 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 91696763 1250 91695513 91695517
    0x30c0f0109080d08041a040b06091b0406080405070b0a0503010603020903070504090f110102010e0d141b030a030b010329030c090c07020114070c061125140901030209060d0203030702030102 83
    0x184000f2400c0b1400307102c00c000c0d1003241002d011390701e506c0d081c43c2e50901e550780d4224002c000d46018410040e003004190001d02071141d040d540380c4c00009070307a0b846585000c0a07005403001c03681588e50740681680080d4200b0f224048803035a02165175480d207140c1c04e044003a4025045540b00070381500c1075901c0450991210b1090100703180c040c1c0d046054070880d03031602094104114440c10b045905025861a0b026000075280c88486100d00b4898648141c2d01501d06050242c3c0708a03c2c10086118002c031000351010004205c18042e541d800e01078802c10500640075200307103007540460214004281501d0009111000511240090030b071031415901d00005104014240d5650b040745400041c0c210840d0b8101059440e4141511f460b10700340b00107506c60ba00c030105980300300400c0c000e0305400020280818080c6094200f1341250401d149180214202d4014025014100029a401461400d41e10701a01d200341281e90040ac01c09a0b5079540c02071010800607100f0890300340c4010300c10b1000503503080c00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 91698013 1250 91696763 91696783
    0x902030a0602070204150506270405100608070e0d0f0303090f1506060206040203060408070311071503141b0c0304050d0b0402030606120709050606120a0b120c030c0f010908 76
    0xc1c0140c1c88880301d00410044074141d910440805400c2041002552181000d8421503210340000104421406001803c0c608605102d240d01900c1c10303042201a002020904059a41c40d548158203946e440320103441c0303510f4021040d580080781101c6500010702d1000001c500034400d25012030229020b1741c0e00c1810003290401101c6c04603071600f04241401c40c038411503004000f50300c010500c908064000c251240c2003d40003070508180045c0c14421705002c0c0106101d41190300007140c403140c1c3c0e2101003841c032285280c126000242025811802460307030528150141e802d025240200c9000c82c6205c8000b540080d00003a10360100344400140303642d4200742903100a0080c44410302a241910401d800c160f40101030902c40c4c480c812079000483c00000e50601511403020b000141600c8000002d0414003aa004100d84000140304103c2d1003003280e00b000c00c0c11a000d644409074020031581040d145c5400b80f1f02143c0640c0502c00c041e11900c1e29a14943e0642c2060409989083d15190720508020703000c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 91699263 1250 91698013 91698023
    0x7091e0312032f0c030406050d0c09030201050d09030e04230702070614031012030302090405010b0a12020904020d1503110603010f180b10180b040b03070804060902030a 74
    0x1900400074011006940482114503240c00c000c60b0f40c100240c00c000c2d40c0054000c1c00d03c0e00302044038203910803c02c4111a590409034045a031126035801c80200301e94002d44190382c3d01410301344805401c600030401300742903960585882c1c0c1410949105140104110f10003502040000000c44d0403644892003200c0403403010030f000701c080e0011000000402a00500140115440b4240400c505503010340b03212915400c140081c0e0750307074480391001200850b454100e100e5101c200c0d0ba808013096003680c02000703901c0c4140d41c2800241e80c6d50f54888182d01806460001240c1400c00c0d0303004400c0d40780d00910306031500a000500f032940c1440004111810303500403e00a0200300e800780140003010f8545c20000c00c003140c0307592640d030500400709158005445640101020300c00107444900c400c0d008054407103000781c054184503010300d400a140941c5020002c240c2c002080000c200c54006100300d40c00d82d4401d2843ca032442c0c8a0080071208078200a10aa4010b41c0e03c858040040e076040c448105860300031 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 91700513 1250 91699263 91699319
    0x5040c0905130b010e011401180803030114091e0c0c1617060112020a0e15040f0b011101050c090108180a0303020a030e0f060403030b0d0813090c050711090709 70
    0x500d44400383e003a040c0c000c1c0d40040d041d4001001a40c5904840c0724441d802880d02102c0400d5400324005460000e400ca004280000b10010500241a00300f543c8098402c03030f000441922101d040c8003006005408440201c03840710001210710a5100041241900d40c40c1100e540c000305106040c041c003016005504071000c12078001615006c100701243c05003084060a08020025030b000410068140c0300e14060040c05200080290791500e070020500b0501400034403107030844c2065107004180c003124280c003246810305000c40543d4140700321071042941440081c078040c4000019104070768000c03c0002d810f00400754140d1602014401400b5440c4a91409600c5503000030300034041c0d91201e0b10400003648600c40155081a001581a80003505801d0001b103090741840420000300f10220090311140c00010171035a20343c0c01d03035200c02c210746095100f0000d00012000442e040d00ca180005070528000d10506061403800104503030b0055458105940c0690b911603040c4450243d00c2110b810349100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 91701763 1250 91700513 91700551
    0xc06030f0601170c09090a0f05040f06061a0405120106050303210105090702060420060f03040c05120a0809031e011d010c0207170c0d0c0906080606011205040c0905 72
    0x1201c40004825800003c80c03056151590307500c500350042009691282e400e20002c50b10440040e40140c2c5200001a800d0001e4602030418030100070803007030202c641c00d103490000240300c0542400004440f01141c48186454644010801e007104203110059545d5a0717010005401d0b40d00b000109082c1022940f01120f803000460030912010050780030b03600070342214040044983d4007003000d56110781e11084003d000002400101c0c00912105074968100400160f02c021850720003010350720403441203260708040b540f1201804020041c024050704031354846054900001d6070312014081442d8050b00b00c13500c61040d16200c03030000490301902020750755a40e81c8410380c01803202051002121407030080c0043c0036400c00080d610702e9a481468070944401900c00316502c81400600d4411100600006100b405401e0002c5200068825032040d44d15150b0300103001c5a02050701c610844c0140c44030215045070407a203c01502000b0422540203c1d80c007800f00c2c0104c410b11955008102e40b188a40b0308040e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 91703013 1250 91701763 91701767
    0x3050601050a120615030b0c070b16052b0603060509060a0b0105040603110c030301090c0f031104030b060d0204060b031501080103200105040f0b030403090905090709020c0c06030f0601 81
    0x401070708064003414280106003c4424510484041d1961100e00044d610000200e80013a214168100501c1000c0020a10550301840005400114041c0e01d9a10003a240d070f18046d0301c40c21039481d800000c10001e10802a10340b000c0c2140300d0f00d2034440521450016084032044084076625001158505c1d9200309206050204120140d0700c441441001c001902c594000608540251b20a501c1050749450740410321211680c103407510010004226500c0e543c59403104805000b82400c00e8000a00703030640940f415109018556042030034010951a0074159120344c00b01035001001c10f80c00070700350001440140c9503441001300500d15102110b8481c1410b956400c801d80d0401d8049041003000c60040c0089105004507110107030a20030880c03c1d441d8076000607202d50060b644002c492400640c0d000450714a0b6038000c5100b184690303680030080d9142e44048c8100d400c10360304040306d603010203824822542c0ca903000b0101c1c000074400f203400076500340000441079881161814807020822080c411256 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 91704263 1250 91703013 91703023
    0x203040813092702090f0901021213050d080c0d050714070c030201090f0807140f06030108160f0e0601080a020f0c03091201020304081204081917090115060302090a05040203100305 79
    0x110618902c3c20b580303021500085c648103006040501054803210124100500960445aa29190208500b01442c0034070091040f40e040d0702e000d590314060301c0d5410030342500c41d601e40fa21691003100540d0620041e120800e0081038010102d600380440070040c041202c15140107000e00342d118840e100c08690552000600c103000715071152a2081004805120904000c200002903401e4041040002d04400c1c0002c0c1e595600c006407140c00840001c0040303081b100100305841c081c5140e104602c2203c3da126a107944c03070421880742c480b070301c401100415010761160f00c140b60850b04860000d0b0418041c42120aa69802070b41e0048260b4000038944405044c03902501c01c004424030021803c40c501a181d90041e84646603101d4041201700c2300190402c51804103a4070f0004082055080d0310b002d4a60241000c101c00c41c03004c02c0e40840da800180c10240500880c032110f0700c03c50b40540010324101003600a0f402c003048140d03115525940204247c0c1303032840030314402e4007099800e42d6460700d9414510f00380 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 91705513 1250 91704263 91704311
    0x5130b01150e0907021906020d0e0304090b01170a0506030c092a07030c0807031103030c040e091b010f020f0607020601060f1d010c0609060c051c060503070603020304081309 76
    0x1241c0b44400c01c00b13595004141c0c09020011584c40e02490001071809000038428401c410001c0f62a200d1000c003541c0e4000058405d0314180101040f2008500c1d0040d075407400700d0b0604800c60000341c000036026201d9900515084a0007404662404254200194100f1030803030f0410040003005c4440c850000c0003021420743c0c0036100c00e0140c03501c0d80d152402010105450000b800c5014002800d0f402c2500c1500301d4404464541c00352900d9082911182045034864490b91084a030100c010070f80c40c480101d68810090214410910644000c1005441806121501c401507000d03005000c01d000b081031002c01c3c03250600d80d015011a43c10010041c010103c020b83c9030080041c10326030300710301c2d9080480303143c0022070908004400d00800e10f099000b0b08003028006040a040510010404d5084000380c5201100444410404c203030461f0711108903642482415455441080c1c00c00241d4000d5008642081c000c4107440c0c03402c1c07984e284001c48100190300005905580703e00d44800300c00c100b150608a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 91706763 1250 91705513 91705519
    0x40c110d050708030403080606070f0b060906061612120230040c09020708040305011e06210f06021b0c030d0302030708190b0d0f0215030103020108040605130b01150e 73
    0x41240d252a03c11040c000203000405115030080030540310b90721501601c100b81d5101e0b4450440c26824036110440c0c200594420f0b020b04440070103d060f618100d0141d40c00400300032a1940101955180d028000a1b118485c50511001e41b02c00c44000d040c40c001000d11017400c00413007002207004a001a80e403a40c550010202401000910000503416075600f8100c5c1c05c1d000e009a200d0409042c0400148a80c0d403000300300d507281c00c0c0a0800c407690300e100b2805030002c00c0010410756a0303c0881102c500c48088802c1030100c4c1c2d1156410014419140c5034030300c0ca0240c5401818002c52200d004110342c0d501c100010790354403225103046036140422105203000e0a134030701507086080980002e40341460113003030b09000c013804d020b80c620342d00926800b100c2e035a0001021500315030014180b00001c4c032292070090b80208611503a00b1b07400c1c0c03200070459040740d03070607540d1149540d03480e16174070010700020b440245156840100440800d281c040702e140030303207184503011001b0b4080f0000605018044451140 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 91708013 1250 91706763 91706767
    0x120105031204060c110603040b0f01150e040908090a0f210c12060e03160c080604030804080717030403050a180308030a0f0e07060906110604230c040c110d05 69
    0x202a8403800b658111074040c18040454003261425030388004a0304030542e049400402004180003048144c03900503042c6084034012a43c0314908544000e9410410902241401030640c829041680c851309245000d903110508207042000080c60801195001054070340e4030413020700c803102c0302181d071441036000c080b0030111210039030b5200b0302090070302e100b0301d410055200001c0301800099000389203884003141c1a255203442c00c4c02002241d60800400b03895201880d600861104000070789280102e4054036050050b94456581c0c0350140d000d1241203814001d00e030740b00f201710710a00010b94000c43c800d44581da110403903020300401c968004a65254000f2540c20f040001c9035040e02101d03007029803040d0220b01803040d100c624000d000022005402031050020010311140c0c4808010f003500c1555071034119040c001c503101a0f0700c28098030080c110303484680c02c4404e04d00c0001a003010881e400d800380c9080a0b02503002608489001a43c8030114140d2461244880e6080c08903034070552160400038 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 91709263 1250 91708013 91708033
    0x60702060c0913020f0d0606030c12021c020f04080106060507140316060b010908060103080310060203120a0902010e03010c081f03051515030604060e010605010c12120b0a090212010503 81
    0x60038962039940810140f41e8005126508211400c00f00c56003044503010600941e0ba036001c009008160711030300c800020360f501915240e015054000c84102c111590031501203468039400d1000254000802d01ca20030703c0070000010112401c1c0100b800030b107816140c50b51199000d00b40a0700904034171030800c0864204014680001c41c50100d1504119080000018070840410040c2c402e80b18a0300401414803031030000004026142d4000d62050701040a40350320b540e950304d001c0c3e03602c0c0603402080000c1e540510004100c0000c6600c1144094014075180c00048600c1c0d010900b1582070043c80f2002503904010051141100c0c02c42c0307819508481c403014112032854488039101c0d1640502d8001000145000c03840c1e4143c0600e052044000060a42c0c04505052904800800040017458407035401c110001400d980188500c1071142c1c2c002200c020816007155003100c80d21042481d030359185a482d150035150761100984900680008100142e803000754200c074a10b0b40d1016400b0310721a90004404e0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 91710513 1250 91709263 91709269
    0x7090506120a1112150a0e0613030e03030403080a0305090f030a05040614040b040806041506140d23100506060304080f03040804030812060405130201052505070602060702060c09 78
    0x19014841d00842045100650000080d00c42803818284c284c961203800c1031074004054850089026004804041104103030ba00b1440d07881d43c00844040000c8400c5406100c0800d00034000300d010100c000b425a4500317034032a603a188003508009058000290350342d081001e03201040001e100032448200c0210f003001003007400100705100b03031300130389007000304421034104885250010b44003d080300f420619122611084041c0c0e440000322010fa41004039800b80490090003442007070300303940c40d1040030100345505d01c080c840c1100d1894401c80300d001e10021200c4461021180c03603260110b00368090846100e801c00210b082d14006082070303100d404200240030001e12031104950083c1003030345505840f03030b41e24100080b4900a550016080c0c000000d58810140301e203180580c401d41d02204c080040340c45038804400c4490324204002d011600801c01080209802451442d86030004492983c49030900e0340c403142821103651100340583e00c180203000001d5014007005c1d07407042e002480303d41400401400 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 91711763 1250 91710513 91710523
    0x80603061e0105010516050604050c19080a0605090c0a0602071a120a090c030506011805010b1e18030f030c06061f0309032f010b030a030c1b0302030a050709050612 72
    0x20f0a4144107000803822007002c0303417009040419411800f0b4a015203090f091158407071000b00c080c0742c442d08001e0003803161882c01d601408181e41c0243c000b482039030a5591034500821001e40a5901d5105850101c812681d0b40080d0101030440c5501a10b0386503c0c240c6c0c02e0b081c1e900c80125407007002e801803090340440601c070900795034001101400404d480e0064244a291003649070009030043c0221800412075811910944002c1d05110b9401c000340d03a6214402c1016002c1d4800340c401100c0a04017503958a140700001c0d040400d41a250321090f40d0740100006c1c50640e05041c0c20f0b0740d941022900000d90303003060009540c001c00548903069183c03d01101b07000014042c0041c8018195a0306040d024503203d200c00d20213003201085171030703204129524480c0f800c0c00004a41c00882d0309002c0c20100b1424049140004241c0c1a1105601c211265550741185051040118104004000b0000141c0e604104100d03000b40500c0c05000d0003400e103400c00d015100300502560140042c0654a2484200011 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 91713013 1250 91711763 91711769
    0xc030603170318071215020a051602040e010e01050a0c171603060b030c070203060a18080d0b09041208150604060e01021608010f15030c030b090307020d03080603061e01 74
    0x5180e5641c2d1000c078801e0000110100310b030001d20480c0c4c0c01040340290820644910303401220413000360741485524070141d03c00c0c43e00c2400090300c14071901c80126203604034000e240e440100082109480107458034216031702d0544084c05a03440342c041c0a070b8514907106009002065103450075061424074101e6800050180814000c01c0140306000d03180741c46540402d0203441580710480d60b1741005a049081500607034802e9100b03004003408900b40401c1d91048405204400c1d80c0b50004950075110b044e00c2d900500340c90340250340c0b83d103201c880c560380b0584024131962050b241d02e101c07002c4c40071000380540d500800000c00720300748a28007903255440400395000c40e601894090b001c49080c000403410710280c01d11912044d580c140c40816841019044140d1030060088100085c0e40e00103d10b1508500c1840060035a54910800340046002d4a000365070040d0100100d0340340440541c049041540300d548281c0025030781030107102c101e140512040340c100750b41d100001d0000d800000c40000e001810302c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 91714263 1250 91713013 91713053
    0x108010303050a03241d0708010605070203070305010513050d030b09060d02031507020d02010b061801030b011412040201080f091510030215090301061d01050603180d030c030c030603 80
    0x11030319481e02e82c86504242c0c0c0100b0428170340103046014811004921001c1e0256030001e409407495101d00d8a00e524400740328000d29580c41d9401d0b46000350a0300c43e13a2181000760b0300350240a00c044003241007405190301a103c450f5848076000141d060260810100901620405041504a0b1060303175403403400e150880c0046800c031408400b03620000f0710704030300c50b181100d800102c02d0421200031703004500d4001c03940c1c01d50000d0091110881c02c1004074410b00c0001030022803414104802c0354820b0307020480012040c145110080c1e200500300700c1542240c1202040b00c9040010803045590000001c0d40010ba940e0703e2541c1c900b05684442e48a001d2042810f00503e45080020095a0010510304c0155000303842280c08502039610608684d000c0c1c0c0e0034600945c00c003180000c0300201d184203081c03120441100000941d09250400c0b00581c00074101c2103204411500342a142e2100f801260300c0071707016403000100303007c40c2c0d10050b0940307400c0340f0910245442c1c44010000304040d5400c4034000c43c0d5803 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 91715513 1250 91714263 91714267
    0x40e01050f060c0607020c0a0503010b03070902070302010e0303090a05120f030f04020f130603020307060e060d0b0103060b0d090203072301080402040e01050403022b0e0105030601031b030b01030509010605010801030305 96
    0x5075002c5201c40c01408045422840340300c06120030b858011940c1d580151064880e80313125929042407500740c4641c00b0300c0076055401107030708012120701c1e9809482828440e00c004106110902d03090f030b18540040e500d0705c0c000e800059070b4001f08041000141c240303c0c00d00403401c0c10448150200c3c105030000401480620710240006000c65984030100382c0c45100007482210010165074580c40240b0032400200d0003482600b002040c824016018065604002040d0a151102c9040703540b018211360200c041c117054039500080b6003076110030b015058030540341d80f0000f201e040500400d8a80317480d9070712829203801521948110055040c04001d0401001c0c288011680c890303201080080060b825038041d103500c2c0c0000e000c101540480c1c480d40b0201f100380c02d103000d600007030080500c0084103041000800c05d401d81020341c950050f0041c1d94070000505000960300c298008420300710100785584400250b440c2c4030355040f980c0610486400043c17000003040b0303141c00c080000c1d040c9501804041d09000c80 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 91716763 1250 91715513 91715539
    0x103020103090c0b04140405090a2a0510030f14010302010207050f01090b070501020703091a04090c05120103110102070609050d031812050a02010f02010506030705150d05090a0302010c0203040e0105 87
    0x40001144010304070703404c0b101d94a503621070300d0911200000c1100d610a50800d80855183c6400061407011320340c0000c0030500c803252252a009024110050f0040100200303407000585946488402d020120140c6011900b0701c0d002c03080b03408460003111421a2070310b003e0010f002507680000e480301070340e0701a14505500c00403407005880010540c0d0244001140009102e42004019005048014401e0322060702c060340f6940c040d445034050f00c2d08080b52800c1880108401c60141d0410046034401d418090701c1c108880d6005031046000341c0046c1d40c10085001c0c1111107507410402031009042501d0104062400c0c44002941c5544021010341004209820144400080c1001030300400c40030741c0c0a0312881d0607103420380e11658540f900386c0c00300d26590840c0340742d0303401801038900c1084011302520f1200d007030400300043c1e1001110300701050380c000c2c000b80060007501d10680c1d00980d0580c0040140c68481d1071b000b400c0d5070f1807050501c02c540082c4003c2004000860104d03054800840b030007240c400c4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 91718013 1250 91716763 91716773
    0x1509030624090218090106051c0b04020a0309170c060114010203130314060604050108060f04080f040906180c0212030c0f031f0801110a08090f060106050c160509010302010309 77
    0x48840301c0011805404000060710b88050b80101107403440155122502002d030000c20550610074030070640420010030018280541100a80c1d00d0810011800205140100d0104040741c00c045118000320f6618850a010320030030381c042103003002c109100310b49841034403030b4010b49882040c4150180f4101c0154000072a80c0244240d0b00c40502c030541d51560643e4a0a140c80380070703022013a061290080f1004107105052034043c11b4180e510300c10003058107494040b800150802c0c0200103a0380d070300041c410b5410a069404c010001007288100200320241080c1040c140c0000c1c096004401604c1d24101404242d00419540c40e480f800465007034490361010012012485544440351500d5000020400d0346203c40c042e00782e20400078440e0221203a00c9400341e038200d9001d000312040d120700910584070308501c40e0340340c213510040300000e03910035454140400e440c1a50a801080c0418808508508160001c001c464542c0352940360700c41216140131301041010806000c0a81090384800091741844 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 91719263 1250 91718013 91718051
    0x11209060e0d1206060c08041806031b030b010909050a0b0705040302060f0d0b0102011103160302090603040501060e07030c0906050c032712030f120603070e0c0a0915090306 76
    0x11440c00140c4403030520030314004265103c02003040600500c0c0030800f144040c451030000500a0384101c040d4a0141800705481d1301040b600142070780301e034481001000248001d10446c103601c01030381c01c4011440c154613184007000d4050b00300140492811418801180c40000d086104039002070680b0100d40314140700700d07a01d215603040039402002c0094020000b404040040640e80c680c140d041142d100850012400c0c0d5500c0f0032000c0c00b010041c40450362080c00c2e5000c2144101041c1801407410b6001d8021418603081141c1c00e03a0103035034601c01002030880255806601a050785010048112211000b808517007140c004c420401c440800c90b01c2c060380c002c100701c039101c080c41104562210b09103085020110b103080825401020000d048200008001083d19000605280410305040445034901c805401c020511640b500c44c04800054000c28140b05501a40c520340c2911b96406103c6000ba00c5442541d03c400310340480c03442a032003082c1d0b211800c43c0640b60b0100c1c0100d021101210101021 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 91720513 1250 91719263 91719281
    0x62203051203010905010e060a091a0316051908030f0702120109060b030c1012051003080712200316051006120203070f120f0201032012010e0601120906 67
    0x61160512400c1c803079240c81d000d94129034210100b407103940e882c0c00350a001d600043e28059048442c04400384001d010030b800200690b000945c01850201c03c4500003071800031101c0d01048421400d980602541c240311800e01c1c030ba003041a08207080c00b813400c01203503a00e03c940c00d005100d848010403480c003190b546564441142403520002c1c080b5110a051400c024410401c00901c0b07885100b1100d5014106000800c0131840310361610712104081903169405000000c1407240e00c0400f8078008000651240f01410a8500503042d0382c1d051a644000942500d414140c1c402e010039201c07982d42c0c1002c3c400000c07114100f6504e0000d26500d0183e107402890304000b0078030b1303000c15418000d02103041d0b0a07480403907296074001c07022215159030700d8100b00c000c10342ca03026030101c0b03002d01d401d00d001080c0380002003d06144107250000f0b0540c2c1200c03800f070615100b000107600c40ca000203000000c11984060042c0505111010354170f95051150019052040c0c540005202c0e83d1900003103424002e1503030111200c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 91721763 1250 91720513 91720523
    0x40902131413020a0909020711030114070e04051306060b03191103040818060a030e120301060206041205040f0608071707080a0e070e0106020c0901091407141603020f1b062203 77
    0x2508e6407403805504404460f400705000c0d40c64540444405013035107903070740d000b036009071601c5581e071419009000141500904040b4500016158040001c0c541d101c0c3c800200080310149803a0b00700803200c07540704d92030240c46190313840c04d1800b07804400c1d10a000300c030f8029510010f61503940d901501c00f80941011250966800b2502048040b130b10f94058119020903088002500c1c02c1911502e5003441c903001c01e01501c00103a001500140009040b1080020072002a0070901d0411743d841019004402c61078014400003401103061084013500240355222410b103003429500b280c900b01500a00d21a00204000c1040c1e0315400307103a8182205100080207044102e9082030700323603103a50010395140c044107000c0c2d0007500c00368000103201c041403140d503254801411209030300da150001c088030880e20342c410420443c082003103a020520a420502c0080c5841b0b50050961018102c58050421642052211040e4658030b20b410b8181e4031001101e40403540d1115a079005161045200c10490392038000401c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 91723013 1250 91721763 91721767
    0x2030415050c010e1204060306050a030803072601080706121b120603021e09010b0301030507030206031005090702070510050406020709020a0507020303030406051510020d0e01020111040902131413020a090902 91
    0x175a220540020010384580c4d44003807002c1580e600c1404141031941c4000307130400c90240041040d01384100e1040c0c528000700d40d10010300c516101812101e401c0d081c2d02440d5a94440307101008000d401042c0c00303900d090022800c000d41446440c11800c039140701d030070f00c2e0704010b4822035071051f08070310f58046006542c000c1e144502001840f0040c1e941e00c415580041d02c2503d01c1300000070750340b100c0011241620b5100000d020007516540c280465a040a88a5124024095404690f54664480700351059142d50b0060210f58a00400c0c0045139081c541381d0010010b08200500c61540c0005841d001c40f40c0c90a0016519002803804a410340500709009615000c00000d10041c00015003016009a409034460721000340740c0c10030008400d8900f5205070258000c240360a1f401c2d0300034805054a1a410300002ca1001c0c230103804110f4aa0042d04a4404107501107100e5035100220b6814401270301c0360756800e200d800380700d9000a40170790a0540320010550005840000c0707500ca501c5400082c050584195 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 91724263 1250 91723013 91723033
    0x3030b010513140a050d020105120c09130b100e0a0b030603011418070e0402010c02270a021c0507090e040314030106050714010b0f0418051207021002030415050c010e 73
    0x24543c004402940c46460040c01c049007603d050349003240d215505841c1c15161469134a02d00740408801408180031040510054229403903006c60004280094040058101c04040802c5000070303056060f0000c00945074070780c0890303454100c2c0040581e80c0c01e01c07525880e680d9880c00680904444a41e5480c04084803040c440b403030310100107507280c4201c031409990030f0544440385c0c020042c80c2101c010b8001401c0c81c0000e0007600b880030002d11144003540142e00074041c1410900100407086d502d400003d6400541c07600c29060513041540d245011820902c00c0b41440c1600401c0c0c20b80c14020341000680130f00c0401c04142c01220190b040a084500c1503031a507035114030181658011900554040c4094100740d118000306100d916040301c4020f08490517815042c042c08000c00003054845202562140ba400200c1c004101014004443c0070200e55541814410f001010f500030b140d0f1815076006110900900800403415654200c4070b02c0d100b0380364004001a54050103002c3c0034401c547c02134281c45 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 91725513 1250 91724263 91724279
    0x1006110111120105090703050702030904050a0b0a0602030414030a150506010c0501052a0306010c110105090406030f14070605070210210c0206070203070201050904050a0603020a0f030303061203020a03030b010513 93
    0xb05040355400c40b100e20066481d1201a415101c0031240040140c2040011121900c1e1560204e90450081100010301006090225041c01c40310707001440581d00118080200c0700456400d141c04035016409450fa509803555100c2e10352810442141035140c83c0d0340001c0941e4072482c4461100b40e0804000c1c002c6040012541c3d4440030108070403031080c504440105206514201100c0c007440040e500d0082846464407030f40c218a99144103a810400200401c001603a141c0c007443e40518000c03241038081842d6890a031104001c440c1c0c02e00907a030000f403410421150084103462074940c050303661489c048011030007206d0042c107100c1d04101c1240e0341c61000b0740008040e4491040b008e025001c60b481919400d105903030301d0107010002400980c3c100902c2903142051342140b600002a04008252680c80e0303400600c414a082c1c0040c046121403036002c006060741401441c000f00802c00c400750b80080203407002521985c2e0301c50042c0502d9119000c042143e40300e14100c031841c01c4a07043c41941180c0354408 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 91726619 1106 91725513 91725547
    0x6010f0801141522090b03062806050a09051e010521011404080d05010506070b0c0c0703080d0213050f0a061101060302060d0905151006110111 63
    0x80e900b810030100c06141c10040100303008054060078000c030b4800303d907411b086042c803a82c4a00103010503003074621103c0d0041110003180810402142c14400090402640629084031001500088890310343c0d010368080c5007042e084919074600c0310445180744034217000c0d041e80070300c01c2d400c440200c200490351120001400d0001255420240c135444206d164101c4095540307500029118811840c907100d000e0144c0340c00c69213a410541e55407140a00540001c0c070182e4048070004d01178210700400c02800000b9507102c0243c0303039904543d407000760294125048441c030790b104030b00000c40e25140c245030f0544074079406401607076000c0c070b030800803500c46142038051485035507583d4000c800341c0c0340c410003484d1502420f0800306181e60341c0e24200d8074100e10490009117110010050042100e100d003210800c41d40c161411610122400c074140d13004080a51509400f20301c00502400c88002c0c0c0d020b = true := by decide +kernel

theorem cover : BRFrame.Cov 91546763 91726619 := by
  have h0 := BRFrame.cov_init 91546763
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91546763 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 91546763 ≤ n) (h2 : n < 91726619) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
