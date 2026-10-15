-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4337
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:17:43.699507+00:00
-- url     : https://prove2.me/submissions/6bf2067e-a2e7-484e-a8b8-4bc94774107a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 779856115 ≤ n < 780035971 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 779857365 1250 779856115 779856137
    0x80c25021c060606031a0d020910150503010801111303030e03030f0f0d0e010506010e1c02030703120315060e090601090302090a0b040b0612220f0b220c06 68
    0x96640030140307803510055104078904940381040c8015203004d20414001c607140100900165459042003018001e02502e030038200d00c2681e0911030001d00060403c45161a0b180740810301109900c0c0c0b600c0592000d95a05442c3d50400708400d007144c3c1c01d030703010301212801081940303401c0525020980403290541047c54641d070324807012031305600c26480311950380c1a00142015030480b03002e015115064100008100c800e00041820f400c132030080d1102c40c00b0610b0414107039110700e84281c01080001804518280664080c0e000c40e207820020741003114541005011000e01503414842c0035802004860480d100d545840c80c003601c041c03003400b5154050300ca04400280745902072074281008540c041c044841615203035035210001c106000d0035620403400d00c8090074a07403910601341e0380c00700c0ca50040044503445409140a44400b000c0e034044003c00c030098801c0c040b503612001d45031818095040081c00e1316241400c1d81e000c0550041704002c4500c605031788404109400e002c00140c0e19039080100d2150 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 779858615 1250 779857365 779857369
    0x30f100b0907020705060f190801150201290a0e0915071706040e16060302040611162c040609020901121a061516030f090b120703090f0b010303080c2502 67
    0x22040d0441641507950715141041d00b5980f09c0c1940d81207402d509888820040c00c20012401c1e10310522034003108450074100104580441c0008401c10a40203100c600c0e1284c3c0c4d07010002042c401210720280700e400000d07007491192407505009a10600034940015100903c00e50340035525800703050070340610b580b00610f060250f000c1242d20300060800303915510607652628018040c5d81b041c090440050f201c884801194171000606082038514661965030300e038108184590030407001d034100129200c512100001c900d4541840701c0c09640100d9010444000071300500c0103401042c2d01030038035040c0107144480481c2d140d041451540c440b83d100390032107455200014240c0100400151480c0000182003200400e44140c01050941710740c6506400c0c040c1c800064900c090704c0d108154080038201b01030388403408032041c0380c1e03444641401e0010718624181c5900000729880001101c60314200300c01030040c56000208268040c5060f01005e28020755101401c8800103940302002c0d0440103054180119 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 779859865 1250 779858615 779858617
    0x30b090d0c080f1b0c0a0b0a02060417160b0f240409020a080d0c0c090c050403030c0507030606080102090111010c09050909210a080105060a0516030e030f100b0907020705060f 77
    0x1401307696007070145406403810f85484000c110042c03846402c910780c3c0000c4c080044d90940340252003540103090315954603250312600c1c582070448400b443c00100304c4200c00010f0303c007501144901a01e1410014981016030810451024010341d40c2c8103118200100000346007900702405020958020840304081c0c4040b94851400750490b01c0e440c020307a001c014203607600030f56441c0310320b00880c400c03010301e0343e00c50b1060203c1e40340d140c210f000218100801c0c00800d00801280034440d11500c04c4840859480e103a08040755216001000c450750000340c102c04039a40121145402000301d4020810062513203000303000709003944299400340c00c0903130020300d40d0441071082d1910641c44400300c1c8080150503071032081c6c82c1d10013254000410200000802d443c01c120003034610000403a08ca017444c1610060070004011442d0f08124200a500e02c54003240d80c8085c0f002c1440b02c400c0c54000e0580004084901064881541d055800380c106102045109540050404100c402c240e80103039803100d401c00b5200e05 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 779861115 1250 779859865 779859877
    0x241b081e0d0b04230610021615030b0f06090d03050d0c081605120f130606180605090f010308070f14060712023112060501030b090d0c080f 61
    0x18549011440c0700d1031001d50340007450424800c407410012482c011061802d1850200e10115030007164800158090400b03128454400003079004a4507100101c804003441c800854101507809100081654011509405038820803041260030010a10b58000031074000e010300b1042911501c0400501c40605010b0380444041071a0303040c06001000c0f8000b4050010101503c00d104105a01040440064400d90a5544400300c4c8180802c141c2c0f40c0d22072403203880c3c401a007194000990320300501c001507400d1141c0c0e0000c0489208044061007013103101c03001c035500781d400240076101c400100041410740c2e021182c1500e91000c10035440342c42e5410008808407003080c0040101c24019112a40420b0000d0307a144a240e159981d10346000d6442d8884080e4020031020080d500320039003154980d81030301c45112041c80552072405d11301d20764541258412003a02e480c180d95a540d5580144188060b4260084c0d0158005005108107030b061b840050000000c19000352010323102086581c0b901c865070b0100c0721 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 779862365 1250 779861115 779861167
    0x50c1e1f030f050a06031b18020703091508090105160215090c180a0c0f0e040e0c03101406030d020a0f020109090e03190921050f030301241b08 63
    0x129518040c01c8440c0200302d17034002652a1204a02101d500d1640c1c00200c1e815115012000c1c0c0864540e07414200280d000764400705c003032040c040b80120700796212141204151082d6902c0100301d050220710142182c40c0a808951945403030950480c1c104c0c0c000881c2d9404140f103402c20513003952100d800c54202060301c00b01642c03001c0c0205040c00350000300d0180c64041c40700c1c0c440c1007240d901c0d103d0080d102c040300158610046a5071076181310301441c040c2d021815010202c402c0e20340d15806840000d0424640055000a0720b80c1c0f21081c1b8010ba1103802c40315071022041d801855546401c6201030742d200e030740c04001008003440c0010602107911550a46008280255042c041e40d81c81491464590704404154488503802010102c1c00d113109248900031504115200405015586582070402c102d81e84182ca40e4402c15803201c5121500304011402480e4000070034105c90030040200a4226031101c0d49001c2100c40071140c400b05190b0600c810702c0d81d5010260560b11100302040041c9081d003034007504 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 779863615 1250 779862365 779862371
    0x6011508180106081c050406140304150507051b0321090106090617060f010e010512030f0406111006061707210c090906080631050c1e1f030f 62
    0x10300e0002c000b542d00d40440310814a50030890440c17008460500491081c80001010001a0503040716030000a41e0024040c0c0f4003840181480b651716029180c0689403540003a4001850300440c851807500c440d2558170002c091031078000c00e4041c030f028441281c610400b8180c5002d0120321060001d503ca0401000101018040750360f5440c0d03042c6404d86200041445402020001102c0140c6181c2d1541610061500b680e882e03400c0400740075603200c680300031184602c82004090188895103000c0c100801903580c1d0001c2c000030414480d41403807580c81000100508042d000c0c8070454118107805101c0c8030200c001c0306141da8100d01240e402c10340042c1e18416080b6010111600380d0380341c202501c190599141c071003d15941c0c000f1003081343e121740700d0316a064020501182c1b008105854501400041c00701e003807540d420845030310800d0602c0400841d60394dc48181c00302c00c01c1c02d000c180c011000351009030b0701c000003514101007840920701ca450903080750004181600303128001d9200d0203828039010820 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 779864865 1250 779863615 779863619
    0x903020f04240b0d0501090c09090b0607020d120e030a20011e030e06071b11060c060a200405010c0f02040e030c07050a0905060a0303030b0a05120a0b010806011508180106 75
    0x36611070351140c000d240f499400d100010603c081d10703001d0f860704540c8d55074030207030403526100e00480184944185250301210030002c100150f03540002c00c19906000324901c42c680c007100720001d4801c000342242c0c0d034083c0e0420b240d842f0108160558218140740c003404070341420011000100c070040700010446001c1429802015201c1d6850352241010400c1e00049542c00d80f9030f801c05840b10010304c0200b04154407a41e0800002511005030304005200150001e42007160301901c95040a10444090a2aa68603403440405a544110b10a000380741e440c0c8040c5814100400285405c85000b03000e4203a0320300c407103030200315141c651103406145e19140940e40c41e03010410990380c40c4e00003032080c2480707011070b1000842c4a0000b4420540507600060441d00000e1960b0341c1900500032440c00154059480040041e15440c0c141184480d0460074016001c20129484c00b41c001d044103030007008081d801080180620b169400c45410500950305001404c1c0e40d80c8400700040030312110921200303500300350300 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 779866115 1250 779864865 779864879
    0x6090510052812050d0e090c041a09060403050a0c050603040206090918010501271116030e0405270c0609011209061104030302250303120e120d0c0903020f0424 70
    0x41700301d141195130b482d01d503400321a00070400d80c100c0964181194400400c0100508840b0055a40002c207140703100b072b030424801c14001800c9030815441543e0640103012044204100103403034002501e4101e51340c1b4210700303168010400c00d0044030842c2d03002e490400c01268206140850f110b0349070350158000d002641e180d1380322070443c0c07800d1280030b624041d0050119200b191113004182003007009034440c0c0d00386500b5820041c1da00194070001c1d420301a202c000021280c8850203003500c2120b0008c01d4036000c2c0c6404803840254030848001d00002e4200001c2403c1a64480f011121544030929100780c0030601403000500801d00200010300117894042c0c40f41480000101400480e03000342c003902c03280d101074241040c802095403800c1c0011143da1105000103400394005801d4200c0007500000d1400d00884e11500c3e1200600c402596020040381600300c281c3e56018801c80141d0390f00e40801c032186150b0105a191101c400c40d80d215607100d61001a0004000000c600b480c441c0a0012000300e030385680e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 779867365 1250 779866115 779866123
    0x12304061d1605010503160309020d060f050711010209091f0e0a0b0102010b0a0f050126130c1409040b04050a0f030302070606050915040f0b030d030609051005281205 73
    0x180c100d5100c64902c0040c0350343c060000d8900c10040d11000402e842d800035001c80081000c41d204a9000b90350000800119049d4071030761700002c0e010800000c45042c808005000c00702a101d10640a030b004114920003510b171807508607000403c060401c5402c01e81607011900040d80d54112400b0354003a04104410030f1a580c120151014081e0002c200c0b003124070307040c0000c00205009903502c15400c00d004000e55441501412000c245e01041800c80980603a8029082c450966824800e0245850307100c060056406900380100b42084900460303051442c080384038480028805026007058038002018440c00744890602141d01040c1d446000e401c41c6070290003034000040a071580c6160020104071030078014070031030041c150a911090840416000c1102902d20464005100d5440d4166648103071002c1004c44442c42098030082595403c0003c10300440c1c2c2e00803d60140311000040811071074840800000c3c0903100d01c240b400c501010400031040f100358980c0704e10210301024207448248203000c2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 779868615 1250 779867365 779867383
    0x1140609060105131503270c05030105160e0a050a08060f0a0b06070602090a05040c090315022b02160b090105070e011d0d0212010203070809012304061d 67
    0x211501110744424004458602035820207044856504906001c621190460b2640590f03040c0b40c00f0034980021014050480e10265070000c10480203c03800c001c0010924684000c1c7c1810343c02040585840005400e42c031403050400e009000214404100c5a1504c46442c00540006032981c15000d50f0340030b40700da440030211696540000041c0c0490f40307000450045048116005228500b0000a0380f81d5000a40c0042125603010058000001d01c03a01c640c0940304d8202d10302c0d25111000781c55811311643c000c0c4040c826094541c8104029090780a1040100d004c207405003103401e0200002000c1000240700d1602030218003007a02c98802d0400082e120100d01c0791500301d00a000d1a04c40d03030416a044552501d5090225148494200c079010402160960b8041d00520030410400650042501240c80c2d901c800c84a9400100300803031345400c0740030150441d040400030026104400640c032008104405034448903900c41c80410144000d50708040e60100320100d2038080c440c500c185481d0f8030301c0c040c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 779869865 1250 779868615 779868619
    0x30f07030e12030403030f05031801090605061201142d010b03011a1c0e0c06030405030729040303050703060b13090b01091a0d020705030a0c030215012d08011406 71
    0x200c02d4004002c007020041d00d040341d07407603158203928241aa5041d07415800050841405410081d0700703004160090081a60041c000c5070000345a003060350520586840304051000c190381003c80342c2c41c114600f2980700f0340c00388080d09403100c508902c0c13003190321103d011300c0c0900c070348020300d030010400104e600000c40c1250310040c00c1203929983c09842c94114008c0200d030044842010f01c66440e8111203402c500103001c0207405a42e105040940000c0f000d8005441c190381c1a03101007010001c0055030480c401d003a10308001003207021103022180c000c0c1d4000007400181003644031000f01d00340a001e030b0020009448642a441d48504016100c040041d0a9218010b001c5080104582d09540600ea42000341c442121351050510103505401100c0da011038413901c902a030801400700491003c1c0302a03e4814a81d95070304403d49000d0400a24050402822840200383d01c001044150b5504a940802a07020980021001c141d24181c03150910598050700255003000001c0c0c0002c40b1440e101442a401 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 779871115 1250 779869865 779869879
    0x1c03030e0313140d03050d200d022212030e010210050f04061506051b03041a040905070e09161e02161505090607080405040603060501050405070c0b0711030f07030e 72
    0x215901300801020407040240c04614100495000c0c40c4980d0880c8001e608501d0702d003030300504101c551001e0341e8082c6400c203003002c3d408100c0007511035010000400301d12542454201c0c0f241000040c45812051410040500c58605080c040ba48d0091004510710318400004101c10314042f10f4003669030000711030440d01ea40c039050600041c1c1041c49051800d80705103584007070608002a10f031f0914244410035103d01c0c0e120600000404140c241404059002c50050407600c541c5894a44815210054030744070500c031744521104220713118070010725402402c02e5038003a003d4481d40d0080d540f841c01c2d04803144600034400442072015400041081c01d001e80035680060b185e81e038800c0c0b54030005000502c203000541c108082d00d620b2820402034044d003400b8800302440c059480000400700d0318103500440d441c584901c01040356241034846d00c5c2d0f012205040510104025075a541d10100d8000d000382d00340b050380c004c0028a5503080043c0d9803604040b08005070344a03420300380505032202c000d641c1e80c41061 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 779872365 1250 779871115 779871149
    0x1d06030c0c0d110727020a030b0111010612030507230c0a09050603030a0c240b130504020f09091f020c07080f0319030b101119021c03030e0313 63
    0x12207850076461980b00781c4080d01401e4144160717014907031403c038000c4032441e51a082d0400841c8030ba02c01018182500d031400a1140c400d0b0700007602c080b80200d1900816454560204070802108400c0030556a00d40303450ba948401391316001c809120241842c082910140c10184607100380040c070240e4421007210045070050f610b80686050306e40803140c1b55096082481842200c6006101c0806160f200c1e0b40700c1c21b200c1c2d40e820600d00c480c9507010100d600c0039840e2070030f420301030402c01c01c194001a480802401240303015000314508011488a1a00848581000907400681403082d401c2c0c0f145c05440314003108c2c030300031500000394100c241d40c0281401601000264503000081079118504680c0c080c50800c0312100d2440442c030320030120003082c0368985400f180382c5c0e903036100078850416481c0c80340c601c4400c24030340d01498400c0104420034262008084a0090395620880490030034029030729100b41c0746240781c00c4019145845401c89188000704001c003082d00001d0b01c2e801554201042540307170303030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 779873615 1250 779872365 779872367
    0x1806040b0c10151a03070912260301050d021e1513060201020405130207210503090d05030108071707031e1202010504030509121e03180604151d06030c0c0d 68
    0xd0314902c2201c45400038101344841844004000d550301206604180c403c803540c8030003107264403170904801c48100c3c0581035510040d007044400910300d00d01081185045604100108040000200d800b80c8250612005490f5002300f01040407500640030f07251114815078100080050307004070000c0d000c2c42c079100c1d0010505034414800e403411208000c0081c010b080c0603880d420002c1d0b210800544001c0e001c0303c5246003881100760100b82061f420780c1c076982e41c2e00d040450310303003400e45583c500810080c08200410030710100040c2a410340d419440b0400490901880301d45c9072641907403000385400c0068a054407020101c0485410b41c0d030107040402403811080504a00700d95044a0080208009210002d604c1c180440d114207008812001ca0780745802c1340c0068500c000c2c62030141c0d01e01c0e070300c00203020f802007444030f000ba0503078182590b22504160400c01c166a420040480c607101b04040c01004000352030078030711421000700d8060170003a41c82c1000d101c1011030750f100c120505a03500c11028104a59 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 779874865 1250 779873615 779873651
    0x1906020a03032a110a0605150f03060118020a110d03060303080901020313060209061c0501140901030213181406010620060103030f0309050102030f100510051806040b0c10 75
    0x14100300300c3e10030403e0480f20810386100808114003203561242c2015403002807141c1c802c113400b41602000f183c00101001040005629054070380314081d801c80d00c0108800540c0280031100c01030721400260b158286c071039045400f00f00070545280e0f24814240c0358880035425900100581c1c0c000da0324810182c0d240b5800a0907071100340d50124031421104078000110b40c0507809030881074001002e0a1912181000d002041041c54900c5400d0559410042050700c0b543c0082d18210403054940b01940d614540008180b11003c0015107055611640a141103080c050f00803502258413001300c0c20540d149106071940c401003400b9510114540c1c5005202d111801815003036038298500052407141c1c0ac55400301c40318400f048101d81415101d40088000480a0003d10311403041020020018544142809a040b9542d480780f4042c207000d1760702906055100085a0a201e030540110b45903d0303011011940a04c25075002850000010a602041300f801013180c030480c0101120510680c88107550301494 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 779876115 1250 779874865 779874911
    0x509010e1302010507020a1508090d21050622051f03020303090f030c1518120d030b011b0b0a061e030204090f0218070f05271906020a0303 61
    0x1c10030352080440015031181c0010003081c0c0c405002d0702c1065568190080c2600c01d691240008910f1444c200400b0a2082040c800c43c034a00d850a40150b00440741120b08920349074400c080d00d20380710000556a81c884100100c01c440c1c60f046008034100c07402c5c003030f68002c1c2826942c0c009546505000e0343d00101088031541c040d25001000b4610700808203041009400341966402d400d80140017410040b907960004c000c20a1000c010016070320458910902e113140380ca52a114440c0c2240b11090010010004160081c0c6c0c0c29400e00144c510204001607030ba06c940d80442d5040108505403920400c6204544240a110300c0c00d4148496501c40485581c40c0d00d1140a030710161341c60910800162801d030300140029801000812500d061315000709415102d00310303000c04980100414003142603842401d0880c0402d681c6040e03801c00145481c3c005c1d00c000440424201071072240e1000c0d0741c40d43d80d090b10341c0444100b401800b09031a600c0c030010791142001c020a8010074589101100030b4602e244001103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 779877365 1250 779876115 779876131
    0xa03181401050a0215152b080a02011e29010225030807050a0510050105090a09020f030a030e150705070603150b031509090316081809040803010509010e 67
    0xd85403200380c00450301a00004440c40462055a00e02c114520034a15a2030051400183c0c007210400d441c0706002031984101c600b0160700304180c0130b1000c150115003180c95940d501a80185c1d0303070346c0130b010f0880c05405403900c0380d4200341c075801401c1c0300314803d0341c0b1800c01100903403008a104442011902c032914104071885001d0b82164580354840c50f00c10100300e0031400985004406d55031241c80b0a01c07160080a8100c1710b540c00300d9064014050304000c0c0c45581c00c03d074001480b240d07061038046080c98001514141000d87c81c1c0b2100011540c1d10034000301c0b4928040c0444000b081c807400c0c01011640700802e51406880081500a01ca0355481c00319100c00b0b4000c002044524909075048005081c018031070000304400313034000f090325001d2100840c05484c45101c9075082211007420080f031250085d2003014180c0c010050445144481d210509140d5001002d0b581c444c0b99001985800304000c410556002070900b0170802009500d00285058803400e90314900c150781c80b5500e04550101c00d8600350 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 779878615 1250 779877365 779877389
    0x50601050c0d05030a060e01030501200c0d050706020d0203100501121116020d150204090506060a0c0209060a0503010e1b0103020a09180f020a020a03020f0d0e062a0a0318 75
    0x100c03441e802000110317080400c581000803481d99a0082d01c844110a8104540c5a51282c61a04113119a140451000f0907082c403c9850a00a1021556100360a001d198203100f0081460001d000490307064500e104501503066540f072404d11a80f0f081e411301801003c2c0401c6e03a0240c440c506403c0b42c4107244d844010401104d1410341c18110f00e5807140c580303150481c0d03c0000041c042d800201c80c5948c518400f0244800562100d06012001e000e030b64008107117a0062030240100d99820350711030b84c102e1616405441c2940180c44203004200c00402c143c004980640c03c0804e0f240e0395010000b1042c2c0b03e090800c8001c03000240340c10044060b032040fa04ca0100148591406021550a20050450400303455000003440a05d0350540000d980014140b1030158009010b120141038060200030142d041c030001a10070305115210181c0800b610006546c02a0008101840b42e03c43c0c00424045c3c0003030510020028451400c106540d42c0e001e184124005440c1e00341809030103000300d00c144180d8903d0210b507 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 779879865 1250 779878615 779878633
    0x110306090102160b0a32010602160b0c010f06080a050606040e030a0f0c05010c0305041101140415030608010609020a140307020a0303050c090a1404063002060d02030a0609050601050c 80
    0x500e82120082e2941d031030103581c0d20603221080603800703800402c48000b01d05031002c5922446c6404062805030301c0282950401850303c02d01580d80c144140071b40e080940003e03101c2011004040c014030920320720842083c0352000100704407034002050005180324004580071a5104020f00040e40c240e009095041d500a000c0204401e0160302054a03850f03039071400942805e0a52101801d480302c0401c00c801081c4d450b400c1c0814800e402c8a23488040c8820309008400c90030b6a0170b1100d141c450341c446e409540381c2860140451512030f401070401860660000d000043d16105071310001d600c40c2030708801042d004d0014922002004059a106910a8018013902d01c200d843c1540a080000c107030b01100c0d0020000c1001035230303075014038102602c941803500c08440d40d0381c0c06000c00c6962a402603035010750004c0c9995000c00720400c910003c031008400b000c0c1e118820784003040e43c502030402c09104481c0048200454803a0742d90041c0b04940c03082c8820b001c80e8982c0e40054410340700b111407400c0c903074226030303c1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 779881115 1250 779879865 779879873
    0x2060a0e0304050d11012307030e01030c021e07030501060308090306100b040b0a050405040c08010512070503061f030c06051306080403170c04091a040609151806050a0311030609010216 81
    0xa66aa0040c060401100a050301003000704200082e07d22100c000c0e2010032908103240c2c3c0700800f003a1040e82030078100300046100c80302943d08c0b16582481c480354507031550402d141a40500c40302009562181c020302240380c9a1402c4207964000c403d056000e0300c158400902110302046154007100d005101103460309040030b68400a541c00b41c81c10b0001d101041000154544a611607265844c205903a2500d0550500b000c210f954410014401420b6000000902455601007881a0010780500c010340d8001d0608290343e1803800c0a520180880828803000514990404014901410b00c00042e00700b81d034889406440700c02064801400103600b01d906400c540303604404083e0085415161141070580c0d482082d0250f420b208080d5000d4002c0405c89611810103020301300103000308001c00d004004100c3c41c0310010708500c1c807e0300c50424000c014030031400c40642c0030b8800f0700700160440d260366449040c0815814454504a03000b407117903800150041c101072098a0403840c2443e41400000201d487d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 779882365 1250 779881115 779881133
    0x260f1f170705060409090605180c06030613020310030c0b0a0915020a060e0304030b0c030103022206090c0806120f0601060e01021f0509150c090103052502060a0e0304050d 75
    0x105000c814410960007040560b100c03009000100105d0901203440d443c540b50420683d4030103880321007101440e5100364400b620200310310000035000d03181c054403580c0c2c40c40054529403100d0000c40b0428400818041090400c6003003205a82c021464420a03e50343c500c0f1f03171020312400b101c00340014050a01440640c403012581001c52030244120f50040d145a1107450440e64110060b1000382d000050070030802c40500e00e82d43d4040070101416083d50f15503008640307400f82072280d0300300c2c50314000d0701261010320560042000d450881800c000100055a02420112003070301c03400c0c4a44485590404517100000345c01207400314071030141582d84d281990595021071020b030480d042d4080d1298a0034039000c0c079128080e02070030411010825044c402132103414401030340980891882c011041088200030b4904840fa044000c0c40c000810369102e05482d200c0f51a01c400301303c803503100a0514070202d60700240480c01008a1001008008503140b4034959900c541d00c10a6041440c0c8d02200003c900560 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 779883615 1250 779882365 779882399
    0x3040518040c12050f0115180b0306060103050705210a0506060306010914060d020c0307170f0306090a0e0109050d0207050406141005090d120306050105030c0316260f1f 74
    0x1000300c3c5c0d60075240a52807401d48602c00c0d07084030720300d590042c1080580d481010038201c007010301d081000440300c840082902e03410014501c0f4149070311500400d00c5140b0917030444642c015400107407d0b210244010010810701c060364170b40c1d81e041c02c140c04102c880c07a010b0112406140142c581000300c3e031a06284101d0405226070543c0d01c40c0003805031008017140c900080c240303503108401459540d0803038904100381c132540d04010405241e05020290500c005802202c0c0c208130221501c1070f0541d15042640003412589920700125402c0c004000200315001480c1220041680c01b505da08948940a000c00c035078080c814404c5034820103000c42e40754109107181242502c0207107015132602c49a040800d646204924088a19039a40801c20074201d62511514002c1d010903e00b05245007041d1280151500024048a41d052304801c845e0185a0044d00d503102d0714400c000300084a140c9403181e02c242e08208880c0405071028100c001900c08081900300b800150000380d59440b0982403013030300c0ca9019003003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 779884865 1250 779883615 779883623
    0x905040b063a02162306010e06030a080a0305060f1207090504020607050a0819080f0103030315051302040e01080105010501140705010b0604030b07030c020f0304050f0d0206040803040518040c12 85
    0x9071110080070f40000e2007040e80c80d4900d2801214a17140210000c0031141e042e1071a84081e000000f414400458941d044809500003050540ca03010300107820903002a01c000c00400740010003281c4980c240d040188160300441740314500103003180912110410315504800c40390003082050207902410707442640c000c2d001038107560415500b07944081c5802000d42c400d840d11440403407904002461900c400c06420424940000385041c02c080840c040c10f13040c00000c0078581c0315159281a11080740d2400002e0400030401d418003902500c0c0c280003503200780143c40b03024201d000040388541050061a049503010b03543c07010000c1d01440c1050b403d030810345c4215081d540b24000000319584110141025601407078468089003010140541211910700b50700047d5003001d40c24406038000403065404071401520b0340e0b0482c4c807186000800e8916000d40081d03000b00003140100e0300c0f64002000d402501c0c400d458001d4081e10801090403020401c4400401045046105010082ca021a105126442 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 779886115 1250 779884865 779884957
    0xa0c0c0509010806010e070512060d02031f050105030c010c0203070501140c100b01030c0c05120c010b090c0a0225120f05030703020a06110f0301030b22030905040b06 73
    0x11000000c4601c0e400303900c442c00d00d9000d0030041c02000702d144800b9801020500300607280201c8200c1e41105001c004101910594501d40d0250a545041c02010146540b0f0748400d01c7c0e41c2010b8600c007000348401c0c0a044d0091151a4900700d1550207a0310090003550001c0090800c40d00d000c004550100b1600c02c5a41760080902501e110701038200580e228006481030301080d00c1250000040445034088038450800c01c0c06890b02020503000f00d410005a512520170341c0c1d88409031181203000d8106a4000d941000482c000c2115030501a0003425590360190b007581c400581d8488103004040c24401d092920900c131240410440381c130991f8800049200305004000c40c3c07401e8580c6403d5030450b40065000d608801c45000c00c0242d20300c580c00c05001303183c01950401000844601c214001404018480111400440e00f1403402115040c40b2426101010107407041d2840c0042c14828a03204030303400b47c0d003826140720503803034844203442040c0d0005001150f500c5090092003412a40f81c000c01030303040a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 779887365 1250 779886115 779886119
    0x2060c09061201061d04020702010503060405221b0602060702190204140112020f030f1f150b1c051612140a0b15161b05100906120b0102030a0c0c 64
    0x20340106060300804064403624002895241c1c0051420171000215200c5c0d07204011110040c0c0e00201a01d802c880f09590001d0681d64500e40d400724074604c28107a0007034880d440d4000b4200810458244c900990013040e5401d07095849100340d0f5208801d40d150300242e00076078080e10a20003518512140e480c0010b0000c20003492180381c46030400b10a80040c0c6402c103a0b088a941942803903000f00c80c2d0000c09800034460b003a41c08071010b40346e00440703400342140c42d02d401c06200c202150340c100944c0710308410342106590f035403940503510b581e000001500c00910720341c194103040d07030151207a54804c9070342c85e1400d1594841d01c3e40c1110003101d156661842c441d9030b2100c074951560103102c9244500c403003200002e1000441d2041010b008052030206222810800040000d080100084091194404038a0100d26214000110218582c1d00401c1d0850309100020710142d9100d4007270b608950325511400820301803400b82030140c40007101403e01507030081108003c1c0078810407010300164042c0a2240d9916 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 779888615 1250 779887365 779887387
    0x50c100504092909011a0c0a060f0c0801060c02371401090f03020f10090816090c0804120e13020d0c02060123090a0e100504050708030a02060c0906 65
    0x1040f90300054800c031003000a41959580101a244103108112000311417589058070311034034191203038481d20f1003050100f90a0701c0c1d1a01005504802903101c10b0900c03080c240010518028880c07140010001000c013000018281c0c0076070709464500fa00035040811341e04401d400d03050883d803440a00c801c1d416035081440b401d5240c02082d68007030684448103880b5035080700001403140d00706412041128100340700030401030740d81001b14098800709407a043c0219008500580f000081580415a503014134050318520006800503103082d104940410010701da4081d03811605a10200c2e0010720b0301005000c9540d0381401850702c800b299400038a020082c2d0340245820007640c004910089601e0b454900d07a050961b0180b0850340500080b020003030b00788646202410307810445401d800d0041c2f9a0310301007040b20040740c0084256100001c00c841c0c0340d030310441209005000446090b19a406140c0000c240e0300c1011084550704000780d40140484c0d180d40300c0c0d914080d807190075241c2c1d200d1020403004101e0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 779889865 1250 779888615 779888621
    0x6060f090d020f090702100e0c061b0c030a06060305191505040c0503030a110105011a0f03100509010312030e030a021005090a050604080a0207050f0d08072d110409050c10050409 78
    0x400507540503040800203c1054401c0d41c19440035508927800c000400001ea484d2030080d0b45030580c070441043c130a40380603100d5900f042131a00099425029810f9201c003844801d0b00440102c91207101102c0c4c0e010151041071455110310800100858070b0703042d90f40c02c0d01341d480e000f01c0d40180c0104007605841b40d0700d0000030b1441c0c1c84503003003c01007400e03011420280e41081c8070b40350040c100144e00110310350b150449400b49104200000c00c40c0034020020441580b1740c60b00310b90283c05d0141400005584a06180d41c000c9403113001c010010741010300d050740c210705c048252481000303190001c24000300501190700c003074200108080383c20f10030101d0910225504028982c041c038021001d8680d10780400700c0c001e007820507a4200d01c1c01440c101000c0070198494441c503d00d40c80d000f00303d81e03447c0c2141303162004c81c920344940000200c00f41140b03a0200d1001c2014920360007842125091103055000080c481540d0030054041c1c417a4104d000080c01c80d091815511030b0180c4d83e8075000e807415448030300072021 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 779891115 1250 779889865 779889871
    0x90c0512100f14060d0b0f1b0708180406050a23030a030503061002070b07080a020327010327120212191731021309020906060f090d020f09 61
    0x2a00f80c503442c00362034083d046054a0b800c000309945103900100030392100c4500c004040c121912000340710001443d942d40755001c002280b030340e08100079a24409810030441c95000000751003003042036040003482626040c450081100d8010f000c0c030b54446d19041e1403c41c0300f42c07200307115181450768900680d550f41c0c0501018842500c6503c5154590500c0814007003840e000d00c07103010540d407006030b050007201051415916050792001540fa0748a2503060102d096002d82a0b80d48078400d405030034256400402c03412000c03400300a90b0200075103101c00c2d418003400740804402c05960703080c40c00d05202080404014600c00301c524011a948220489200340780b82d03214104400301500c0030721140c4421580300d40070f040d02c14a2004020003a042c0f40318888000c085000d80503142c201c0050700107000b0321010b21441c03021038009003d19025030150000c003004d800ca8100c01c0784903201c050001082441c2c001c0a41e55405445400030b030030b04000717005000d1201a1820241d901a0707a003030343e8122590318410143d01c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 779892365 1250 779891115 779891141
    0x30409060b03162a060f0c0c0b0406090212060403021b04020f0403020d02030102040b03010801020307091d161b0501140106030c020303011e0e011404050a020c0d05090a1a1b01090c051210 82
    0x601d80103c51b01441102d20703441d82c0408105081d550003001c11400c985080e003054000704005016204c0f031000034a19042d040c80c0c042d107802501c0c10042419000b00b07001d0303884c1081400e210007036540c08c001c01040b445070482c60007403540103110070b0002d410581000100380b803000d07000518040d11346125a02a80099204405581d000010005650750007050303c0d0090401e10341c1000140301041001d02a40d100500405030030390198034801400b4441d203251400f41d05808078031221a08503042450190401c5c0046208440c21076000241c014460300c41c2d40c051558650141d41982d0030200140f055032000e044440300707443d580350046141c02c0032203d168001c00ca03803411211000001001d10041e181c008002610071031041c001245100030200e1589000a401d140917643d910400740001c00f5451140c00c80c1a000400c0801060201401002171030b02d4043c0510301030558001c901c2c91800d032100c000e00201b2604041c0402c001c982050a400300c0001f4114003506c1a100fa40400b5038212101030722461 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 779893615 1250 779892365 779892371
    0x4090504140c0102151303090509180c0f010804080315031e0c0f1c02031c1809090305040902032e0501090b09030703121808030409060b03162a06 64
    0x840c00c00c000c442e10980d401c1c006050780c4450007013400c0c00783c24000c0082d000e442d0916010810140b054080d80050b002c000c0848020b81004100d986860020804650280c450801e0811291600300c10642104205a541c0000c6645594030b500143c1c00160000145101c68200e0207040c5ea41400000b0052030507450004241180c1100e480c41e20b8100c0c0100343c0558070ba01e07001241034a644c050404080103419101d9607510340b51022900d40b4203601304132603218048202c6c40030071640c0420120541c48400300304011894850590008542c000c00b402004500d0422040140c05940e802441d4000760080b0344c0c5450200d8422055a5812038403d00b2003c0340c007014041c882980c000e0800005081c4000700036040c264050042940c41c108c6000107800da11101036803240c42d51042c01c103038002042c0c60f88581199035440600b03c0d9030b6081401014551801c058000c0751a281700024ad910a00c0800700403c0c0049101000b9147c060300900d060058034503003c015110050411900010f0b40c0c807a081c00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 779894865 1250 779893615 779893643
    0x7030c030302030d05010611070509061c0f020a0806070804061508060f060411070b0a051b0c03070501290d02060d111903021303031b0c060c060608062a04090504 71
    0x40c20803113134160020030601c94075400b86a200e400000b1501c1c00cae0b5000382c404440d252203900000c0c000c0b43c03441071200d90031112010448100b01181c0d1109000502c00c0d15800d5102e45c44041d600d40f10002140c490700040c2609000901190f201c0d042440c9a4240075000703000c0a4449260905261044544c0702850940d0000e005d40c509051240554130a40311780403505007091591825108a005024864180d40300c40200d0b100e50844c0d040b41403010058014581da41140701407590701c90300300b580b00341c480707510748805420303000c22120003986c0c00300300200710b10316504c0f4600400070340a200d0441640c1000c420300169011846610505c03500002480c03145880d041f03001c804c86903035203106100750200f40c0103000c119039184120044009030380d07040c20a403650405030b461706014401e154401414413031400c0b9000850a80101d01400d00c68000c120501145441d458070781c1e600c900a94114400b40e018080b90001212040030b20b03c40030000450f600d14056543e0313403410555030141c80985001c1014800 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 779896115 1250 779894865 779894887
    0xd050402030c0a051e0402131502070603051012150e0a0b090102040e06150f04030809040b040e0d05130f03140f0d231201030305040f09060305120c07030c03030203 72
    0xa002089500008443c00c02d00483c0000c4500e60050368148480f171603401965445406541d8011100400c0312240781d030f80c4000710200d411054800c001b60007803030000f1800d00d110780201407040110004000382240741c81c100340020440ca48045da02e04180309141c407404002c3c1c3c00b03001128691580204034108941c106020702c544054000c2c1c8141e807041004010142801c00f61561082003225295801070b016a9101d84500c54070700b22004042c0c00140200c01c010500000d020100d0007075a04101e5070f5016400e010440790305400d5101c40d580200803041043c1d20880040075200d03540e100c4100341070780d2560040c07240b05245c1c104446d01200b84c1a4001c05072001c000e24510b2556890081c868501006009450147c18510945014101008071030614a00078101e0710f100542c0880d0b0000d542e96030900078001d07001350240c0c02104007990301c00601200c035401840e09494228020308074032029a03204500707075480740003154294000d001000002c2035a000d03200000754000c0d0007a596519607812 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 779897365 1250 779896115 779896123
    0xf2110091109030601140303041805010906061107090c031404051b0907090e1003050d08040201021209010504090209040b030a15050a050103120305090c0a12060501060f12110706020d05040203 84
    0x880102030081c00e01102009030340c00542e850441e000c24002c00c0495212034046415445180c014030102c0700520182405664154403a5040321080d0404002a03074407480c040340c00d000c64415000041c2e12008040c0400c1d407565001c0205207803a81000161403400108441c001003040701e0130346854203c51952040c9090f00302000d4201c0b0011110048186084600034002d605140500385401c2e14000020300d4101d1040300304800381d80c0110480307002903020344000348099812a0120f005014074080300f102c5203441c02c107448800750141c442d01e01385801d013800c2da0025049400025840354a550201015450038007005000c3c500401e81d10030150034005210050b40d1014018181c55803400b030040004ca90f0722821542c5001e03c41c0b60208941c1c8074108441d2404c00d01d0b801c0c060384040200c0c000aa4501a04103d0394402d05c100350034402a039a81c0340546503444109005004520b0518150456503074990190306a1300d250070145e4209103450311414102d030001c01501c0e0006e5990700a00055280403c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 779898615 1250 779897365 779897381
    0x20c07060815091b1621170912032502153318010b04050a17031c02040e0f01092904020d060305030c06041b030203030f211009 56
    0x942c0084240c1400f00c0710032000b41a1103080340c084d84021031031141d40c60300070424448854000c01c4020828a0301142c20100003504501c6401151450005202e02c8004030b084a20440010016180905080c4d890280d039510040c1510003101807a010b01908640031040401c0780c5000c1d5004107005c1824110704018424083d000c1540c14200010400c058101651500c0c0007904801040440c0d411a8010403648074a65100c84244104030300045448078014000c0c00403548100c0e0340c000c41c0c907a00c00c5921105a200081d004040e00100140d65045512411301010581c681500525007540c1d56a50b0781c0c0303040b043c3c0f0043c3d099040103004000c100704a0040444030300c15508a0390744103402c1544007e07104000c0841e14012a0041416442c0503c0c541c0100025034104007581d50361001000181d4544030205ca0848441268009024100c00708162500c1943e41c050300071403910824940420741c940200301c4482c4c060030942d0030b091300c51040c081914029200c14608080f40c0d8101509a42921800 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 779899865 1250 779898615 779898619
    0x602190509030624030a0b06180f0c0c0708030c01051510090e13150b030f1209040218040903020d0905060f0702040b150a050703020c090403080f0901020c07060815 72
    0x40c415035900c2d680c0460810340103624214606014103400c0f82184003070700d800e0038503540340c002c0d55000010301030810141c0344124011a1782d8000c00c881c0304501169240c0a4415210a180ca500051100b03407103c0001e06080e100c0200300ca0803581d440141c0c0d8030399440b0005019559449070300f4018800d000000c101da40800031641c0104448402c9401003c80109100742c10307001c448003011036001031210b440c031141203801296000000705801c0701c0d10f001d4108600991302074842e100612800110118900f40d0000a4150b210318220b9500c00b000040e4004110010801c0e5612039801c0c83c90b50b13a84519214a8031075006080300100040c80540100301c03e03840540902403c00541c02031811000c1111811641150001041d0400d4000304544594001109207508000550f82d80019000703405007074818030030740c00c80c1e400341000801d00c501d607141a50b0003404100b00001142c145064240c609502c6840c2c0d030001400c2905450340d032490308583d03a1100010520000505c0b034a02c0e44010200184101 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 779901115 1250 779899865 779899867
    0x3030f0f020d18080d0203180a21050304170c030f010626030702030102041701060605090918010b0604060306060306150903120c170301060210050601020d200a06021905 74
    0x500601075222402c960b598410000c0010b002501c0c001003001d0507014140e641c00320742c041c10103a8000380d0750340c0c03100741891031005a5008541d034600e4041602e9050710303448105940302403801200c00c01d4010484a0440d8980400d000c041454003004200c11b040c0c19072000204000d000031341c18107090041e640f07550340f0340307905040007031140d55500b8080c1c4480b41070b40070f8603462403419090f83c02e040d03000c0c00000035815400000e0008ae03407a01620791590741007045000f004007958403c0d003558288a45640590800c0028000078620481a94136040c40c450301d00c00030448441880014000341c0c0301d6088100400d503148030900041ea4140700c1d92004d410655a00400f1a00551026220002d18800140381c40c5065036500324451040c2d42404e11240e00000c02140e1050304400d50307800f40c009005040051160302a02e0081580b070b406102d005010607000b90101b00c010400031950380c601201413a030120b1415505a401c160308000f5901d4490250f240141ca0300315003062112041c00c507194803420010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 779902365 1250 779901115 779901137
    0x18010e0a03050d05071502040b0306131e05151f030f180f1b0b1b010903140a03060b070b1b030c0d050a09021804030e1816171003030f 59
    0x1c0005040e00f111045400d20a450f0312aa18040183c2c00d080b80e80880b02c580041345c0024021300b450091405802c04690345034400c3e05903c42801159852501200d0400c03c1c0149400c0d8206164401d9070420211860244d10314040c00108650659281078484940900c4407214623143c0c5c1071040e003200c40d01c0c902e01400403041c8074000707030010056000090071001c1900c0401d0208444941140105452140c44011043d80c03040b44100e82d4000c01608007001100341c0410482d58818420400b05650540303d00036005092030207507019030018a107000600d6a00c034804904044075070090a050f0f48500382c00c200d245440c01e03605104130243e000341452840d0510074400341d002050244c480c5c00131280c17400030346030b503a0559607400741c10034400103500f1402130600c00c2c0e050600100141d100310300079207460007038841c10000d0241484105015404151045001c00c1d15040c1d411001c01c5442c030340d8544010f0245092a80702000380050720340703011400000404004064000c0310600805041b03040c04c0c10341030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 779903615 1250 779902365 779902373
    0x90105040b030c09090f09120418111c05040218040201051801021c031d060c09010e130513050f0109030c02011b0c0617091c2318010e0a03 61
    0x4000ca0007007500505020001480c018561001c1d111a04402800003500c2c2c208044900004d10b4180c0f0008030500880456840c1c0941c0c100807507084440012058140340190b1a290005202c194800c1140da072041204003200b80c903008680d4010b0510000020f4181003c4c410420030982001c0c640c00702d030a9403410800503070b8120090b124064500003111312192441c000403801d103800307409203d200b81048040c00b4041a0f165108184900100d1310044030300c004500515a0f07003c04803401081403201300081491075210f089071481d510f0000d40408920001c4420707440c1903807021602e042d080c841d507071800c0d021f104040040310610041c0c00002c01c800d5545031001003800c0c0c90380c035020381402031402202d941500001c10768491250010341a509103510340314000e007050204884c0e40f2200d04c201010448500001c550106007200e039560ba141080300e020401e0b1070018440b1644c01804801c0c000441d002000e68005114a100c1c40c00210410703040b8030000340144106065250250480200500005d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 779904865 1250 779903615 779903617
    0xf15011a0f0409060b090f01170610090b0c010e070608040309090c020a061b0207050604050d030e03120703030902040f0e0a032a05060906071805010305060607060507170c090105 78
    0x1034026031a03610703903a0a20155400e101e10a43d80018039280c0f6250700052494a031002038400180100c605401a16a040045a541c1341d85480060303031010078804200c951418400030142c00c600340c2810000d05503504080446034010307800c5000541d450790740102507034400f400340c507000c0c10040c1440b500d203040c240c0b001018966540540700d20135a44011800c0454000c01c000800d81c0e62000e0188142d40c020142c0005c0480c2011015000d032280c00b0010504e454118156425240054485d840b0440c0d07589045401085104a454050261310720b400a845060b100422885019490205090000d481800100c800b6458110980c0b0301e0120000d10540c3d020841085454042c50602246650b25048007803940e204810f0300601d41c61200c00d80100310780443c0b03141c8035140c0e660549232141d0f01d5080c15134080c580c0c44818086d460001005100d2507000740d10250700520058202400c1681969581c0200c4000751030340c8000c2a0b42185421030400c030748c110684e00c49001485a42042c0c1a0b0002900c1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 779906115 1250 779904865 779904899
    0x3007060c0224070f0b09070b070206070609020a061e0503070509040c14040e010905151c1104020f0d0e0f10091401110c010c0305070f050304060603050d020f1501 71
    0x8108900b005090b21840c001e56224004480080340c1c0d680c408035840d11406055407110115007241c19140003801da00c03004950b00782112a6050401d1505809030300b0004a9400031904550307980c0d80341d16110268545403c554080e050949407228010442100c24030b1304007800c0790174400c100c001c0003002591b40d84041540d140020942d804941c1100509042c1c41042040315480140c54020500040d0341e0340a540c101d0480310031b110304100c1a100c00a40c0419202d10549258105802c0404e8a00d1000c5a000c0380350250301030b005140d00354814600180c180da1041001c020f41c1030020034015801c2d800c902c40c12070001001002000d035a2024000d0303e40700d21010a0000d54155a040a02c06200b038070000d00601e0f00c5140c008210040d5071084100f11340d002840d03000c61662074810b002508138060b03c1aa4028980d0751141022281900070131076455000502c200c8031562a00c0c40000080c0341000784035603c0e00329401400d050406d11b0a1249804209d800e1188403070b0500004000010213240700b11a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 779907365 1250 779906115 779906119
    0x40903050f1c18060b060702150309070503060c0a0e030a0201020601180e010e030a08151e0609120105220c0603020a0513090b010e0f030c040f06053007060c02 70
    0xa02c07207140c5602c080800202d01c04040c46030703051401400e0724260b02480840214807511040202c40c990b441441843d000744070000b5003000380c1812070003408041c00081e56100c0d1040c421203044549500200f414040180e42080c015507011600443c0349401078844000190260010302d507282c01500000d513140e9061060b03102c501e0341c0c1400c0a00d03500454000a07002c8008030300034008010260040750b0307a0750144e0583c0300054441e80c0840e42c10100721b51050405e070b2004080c4001104006c80807210900443c0c5041e92003402040217070b01c13540b16803507881c0c0341c40e15203800052180b5011640c03440c00e8070440d801489245418580e03400049640e0051020b80d409441d0040e00e850003824203448500c140303418001c0c5440021000590700c40d6580103884001d4007179171441c0401850b281031043c00740203ea80c1c0c03641504496500e04660a050740140d210005a00003c110250360b00013281c03040c00007107d91000c010780e00c600b03620b0080740710500100c503240140040c2245464050010560031032400f000f4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 779908615 1250 779907365 779907367
    0x70606061d061803071806060503010303020d050906070b13020114120109090c080f010e121801030c09150305090105060303030f041203090b151005191404030f050a11040903050f 78
    0xc20001040c5040c201d00c2c1c000a0102d03580181c1b10904031859009100303402c0501402c201c404902c5074401c2098074101d03a403603001002d1560300030005a8090b000030707100c10382124040c0003400106c1c2410745002d002d64030320255154004060300006041e85a106d814241c003000c03c101d0980004141046181101e0710b1440000710242240751900c1950000e0740305045900c184261821341c444198040c07030502d0080740481c1c5080082030500303541c030b010740841c17020709a140b545070b14015402a000900000e28918003080c01c1502c4400715601d21084096503000244e0300e5080048440c824440c950300064110025811450014900c41080c0c5009000400c0c070012000110b480c68060f8002c940416030005c00600b2500d4400002610b460343c00010500c60f0000c0425120f003103004030100c03240c0c843d103600c41c0c2c41c4003014402c0c00e58610400c0350401d140c00c0020800080825400300709010144d110b1400341c5980d601e01c0c1403440a4800d981c0d032f1035102e07501d08410080040d030000d085482c0105400802c2e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 779909865 1250 779908615 779908627
    0x31e0c07030e062a15071707020a080708031009060f031505010e1b071a150d1e050a05010c03021b0606010206040b040201030e01051816080c0402130317070606061d06 73
    0x903c0c1056054941608140c10410510106c1da070855030074040900d4941003082580e803130a004907564500c0c040040c111242c00c01001c0040390355400216404848181c41045d95030342c07501804221003a0340c0c0320b028240d110100610822040c0056164103018408041c80254103014000b0383d51000506130440301d200d0002c10f280040301e41d00a030740380b55030041050100c0c2c01d0b142c03154004e10803048884103807007207081402e02550301c1c1582c01c0303492003600040b4200b0201c207070031080d40f046020040280d034580f080c405023500081c001d0250000b1a403090344d0142e103403500510b0844000360309032686003451708500b04115940c0d0340020364035841a04140300400075229030006800034000703c1c03a0512154280310811410818508408074070798526011034001070400903144400b49a603010b04180c03600032100e10b10061405401078042e001c0111000c001d00e60781d0b030359000440310f0321800f92000c043c07000c41c001c0144041c9202d41c0c0014641401c02d001d610404009085105018003241803241501081c4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 779911115 1250 779909865 779909947
    0x80303220c030c120201090503010c0f0e0307050306040614070c05150402041806051803070c121a0f0106020106090204030221011d1b0307080d05031e0c07030e06 71
    0xd07031030041d0340000d143e81083d520780755180110f43ca0180d042e408640e40113000600c5080510608103000b106079590065101010300c121885249108503941c5440345010215440c4e4060084a028030721514002848100c103e450044040000300240103210002204001150021440039640301c04c80b01210103903504c0d80b0002c1d004041c420082d25920445800c6182041410781c0050700a02001d8410480c02105440d01642c2e0300c41d10000070510f14a800c800c02000c0310441241c1d0306140700e813462940c2e8484a81c961031403001e003200c9003108940070b580100681fa07028400e040c09000304000641c40c090454000c00c071010035500ca03203407000112905420700c4010a520050307420f02c00d10140420f5038110207445a892100b421858070712a01c01c120303030010385800581801190a104043c10264a0020040c3c8076500020808052442800030b603d0403802520603482c0321748070034030401d030700c4580c82c0c1001000c681d1190345240c050b00c020403a8004008020141481824900f44030305521802c841c1c5d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 779912365 1250 779911115 779911133
    0x5030309031c1b060c020c04021e0c0a0203012f04031101050a030b0303030c0702090c03070c0f030e030607080702100c0e0f04020915040e0a110306011b0f051608030322 74
    0x500398032903c0500c3c40f00400c0105503000021104800d40c00c541a5807040000c1108902c212100350a840c80007560604001d80144082d2000000c180c060702c140c1c2c0b800d500420b080d50303114031451040d240c0540b01801e03207403801040401001c01e81440f00c1e0400b4207556601c00c070a0040350040c1d040c48408684030050782e210b81c010801100014096075101d08015620032040e8000710001c0784600e180000185218840e1001d136132160007155200701c280001074882030b19030604d04200303900300211500d03810815181040b40314081c60441d9120505c0e4501135900038241030104282c41021801c00820100055100c50102911001201c01004154401303001400a1084640d2583c2020480700180620751032840900100c640d40240d82c00156030390550b8104030f62500000d011081014408031b0720a5208000807840782d18089c0c1035041d0101709895515001d902c4807001c4660354407200c917201540c2540d0035240004c18142000794207505000440303540401c0e1114a903c00315044180000520040c42 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 779913615 1250 779912365 779912387
    0x4050f061c0c030b030a0f03181a030f0903090f19170106050a08060c0d18021305060a1413050405072304060e070512070201060b0c0102030f0105030309031c 69
    0xe01881800d500c0221240107410a2207048000c2880c000646071301c0c0c2000b00e00312061550080c85c800c05021603036000d0354815442d05031005180780d80000840d80d0045003610b040038168001c02144ca03858280020700442c9401040403103a608180450640c1741c4481280307095204040700e072070031007443c460f14180c141e000300c1c1c2c0314012008900d00082c50152065200006480041d07031349281054230f800c03140e035407041d0648022400200030050701041100f1544041560386d00d00e0740302442c070a03031900040c500a0582000b04022a5608140407a620f0101d803c00000c02041c0c00e52103111801c0030000d40301181e06580541c90b551a03200040400c030051181b4009400001501d20044000b503c1381f40e94001254a203501541ca80703680802d01c510b9012481c0e11940c05581c07054503169a65400c1d0000300d4015100200351364940c400482d0b02138002006e0805000d0400005880780380c03240200c0c15440b01a400346002c3e403c04c20102074586c40106950007140c002804440e440381c250a002c0307030a800b00c4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 779914865 1250 779913615 779913637
    0x110f130b120a03030b310f0912170108010e0d111603030801080f030f090402071407090e06010e06091303021f090506161b0221060603060c0f04050f06 66
    0xb90400d00c0c10150035038000c2c440c2100c280c884940300c4400e920f880700c100c40c0006840b000d000000b130366100c0c2042590080b0b1811082d80d030006c5101c48555450100074844e2150b04400728a010007000800100c1d0482c8a004041b264001d200c41c900c900710f00c546881d6a0304080f0100074002c011411040f504100c0441041d05007001034940035904c2c14000d04a1000303015100c1540660440c0a100041c00002d90b622145541203d41c40c00a131001000001d40c080340041301c000c807030f03200f0441558105000e100028441c04001042c501025000f076410450160801484e100511083c4070040d11404c0920b0b07445400d008240190140c1800d059103004601035030300e801540110111003c07100103400c9409400e2040c02103c0490310380030b07100007146651001da00c0014000840070b410000c0c407c1402c03100203001600c0e201da9022944501c03072100030048040e003401e42c0000203028540c1001c100707980c1d2007098551400e0400c9949142141944507074882c140c03203a402076040c1b80302c5940713001c1111580208 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 779916115 1250 779914865 779914873
    0x108160b3007050304020108100302150a120e100e0f0c2404060c031214040201050f0f0d0605240f1b0f010f0507020d05070b07031b020109110f130b12 66
    0x20b07800060065000315006c0740002d420501180d401500321000304150381d8000c200f400d40701c21180c80440903030001c005010070000b4113031580f00100c51a12400c202c0c5030703500014007a080c1d05840d8000c00d81d1941e0200107035a40c0710600d408107601c0080340b046145801141c00d4000b812410400c112115104e8548400034140003e0004000e900030001c91562407083d103443d070005103c40d40d20021220140084605079030740000040c01580700780003e14103c41050084ca04014400c4c0100b1029000a10a50b00c05a680c0c0d070141b01e680b82c480c1604200203603503000e031804100710268042007070089034100c00100e9030106196158110030744907108035070903810440356200496030085028082115101303018514010103d1242e038804100300c0740c00c6a4680720342d454003255581ba60380280c0000c24001c2050359900740700c80c201008a04c140100310460f800070480361868104040380080306090b10740700b03400241030b040c201e403107003550701d0154145501c001070340048400c0070901c0344807205052005406 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 779917365 1250 779916115 779916121
    0x1150801020a17010e060103050403090f0609180203070210020d09120513090605010e010e1f0507030e1c0803090c0402041e090c081803070209040303050108160b30 72
    0x1015405800c18070455030b03c24101100f108041101043c1c04e010740c0a1120103440020800d5000707410054009109150510001d99103120300044c0001a0b00f08070000381c00000300300104201040742d001800c44914085140d403d200d1400707503607610211848902e0b43e401089a82c07501043d54040d101c13181c2c1040c1a02c0c606000c840c00140590b10510188003640f401e044c0105880d07406114501c142c61060b1901640000c8540041d288489030001c40c507030119036111101c0c40384410401d103041801941d12529100c0101d403a01610fa1900d104240b0b0280d203421100044c0c0280062551101e00d400146d016525268818920b05102c010591941c0050000400017004074018410310941d400c1c0c203540400300c03900c5468050641e0314100b18100018040c001042818148242d4030030a040e8100840c0e01c0c181140d404a40038050031034003680401d950f40010841603105005292210411a02d0b017905182070540c1a0344a02071309800685417030710682c8001d40000b038018128070b010540300c00152189 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 779918615 1250 779917365 779917379
    0x2150a1e1b0801030203060a09060905030c010c080a05090303010e04060b100f0e010219140709050408070b13050d0e04150b030402100810050103050c07020d0c1a1206040207050115 79
    0x30220000307010503018a0320129070180e11079503005042e41c0e401400f0303000c2a102c0d40f100c200a442015015654650380d5620305d00056410001000005840130000c03070b8640004201400c420002001045000d0501d01002510b07403000c01104c0c1540d120044c4041d190f100d0741010001003e0038424140c010420006c80c50030140c00140b003000e40b28141d9100304042c3d4005004980350b048041c80052074912120303103400092803008555400e0320a21003102c40703890b42c17030b0003001c11360784156070035071300071000082d100c045c8a510600c0c4c6902607503112803400055030944c0c0c2d0036600e0701000303070b40410400ca05100385042e944541262016900205461035001e403075582281c400d51003918220b00c251440728001d1501409058014494988140302d006c61a2900c4015400b40500910107000c0da0410054500142e940d20907101c100740c0204103046005d420f04400d0981a0580211301c2500031091044402e001d905602842c0d0004003650050384030801c516011313005d048800d2080035241e520b0788001c110a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 779919865 1250 779918615 779918621
    0x21b06100f0902090a030830040b07030608150714072409080a030e1e0a020112050c0a0c380604060501050405220f141602150a1e 57
    0xd541404580c078100c582d901c5801003284907a424143c3c0181a40c02d0410114000320080c0200014842002901a05441d01f2141016040301142401581c207414002448099040180d1204080c1000c220407801c00000c6603030382204040c115070544420340002d42d00f0b407048407018816801c09840c1074444903180ba00031f410030b80e84010030078800807151110b00300755854001c030000507401065030361821400030340444c0504281207440c2420b10988540c02d030314264160307400500404110241101045600c0010706580e0140d012a4034542848284110100e058040322078921081c1490102c8078100d141a41d141d8816800c4164105e400710b00101151101035180c0c003008180d1070f007072506956094200011105a805050300041c0c0070301c0140841e00703118403942d42510345010080315003802c0c9880c2000b0ba424088804181a448480980382081354080b401d8020309810708d032464200e0b007090025076030368a1b0000b1800c201a10004200c00c600c5035804800d0303280b108582180c1c0c0e100d0030f90310f01c03008d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 779921115 1250 779919865 779919869
    0x1704020f0604180f1a01080403030e16142b0201090e0c03040201080906010e01030825030f0201180b0609070c050607030b130516140405060c010921080109021b0610 72
    0x35082a40e025030400c5584502c0505c19020b1407000501401d040c01119102802032044040c07694401b1840ca800c0c008201d1184450705e002102c1420a040910444101c3d18001d001d03402803003040280e03d152403d85140404014010100d02500c02c3d4500048503211800c2d440f001d2000c0c40c00c010b01c42c218414100440c4100e000780c0312148151100c4000541d41c8509110b00c0018401c5400140005510b2400030b0a401c00c4000a1440803280c1004000415481e50303c11070104071080c0070001d40300c2d028011014240e1140f2014002c201d01d50b03e81c080e2a02c0010080762044c10124002440c1c28050002c00300c0c61038201088400600d000c5030084d0090076130344a0240304001d0140c0c1c040400d107890140910a80000c0854415030382c1800c2d05989004020018040148003804082740946540d005010445c40800002c500700c002800e2041007440740752042c0c02d03c000d0b80340070b908100ba0058005811200f1849006070b80d82401604415004440340090000b4001c0c5c109005a01600c185e41c101 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 779922365 1250 779921115 779921159
    0xb03130512040305030904200a1101050601091d330a171504030509060c07140114070803060d120f020c060301270e010e0a031e1704020f0604 62
    0xc440d4001c0c041080c1036004a101c018400c0e4001c0102c0501c0381440c0d00140000484610803c0f50001807840407000c607040b9044040000e20102580d401c4240d00b4002c00341c01030028200100441c0c280002041c030400740240d40d00200c0010030124007d482140039034101141110a401040f840c1c100410981080208200744120880034020a2800c5100061144250050300a00500031542c0e01043c580c1801442501801414040d0100d5512040c0c0100f2000309900e0240c00d1241c1031083c8080c0312a581c400b52810082d408100118102030f18080380c20b01504002d24945030784d920030003e00c0b410502000240070340505114401160381114041d0314038001c0350280c0d429000c04009010041c0024820b01e01d4401c10b0400b001c1c085060851640b01c0941920000b040c0d03070040310002d60944489910480c41c0354800f0200380d043c0340c1d2000c56244c031748200ea004000d0f54400200010301d541c0100d00c02d41110b043d204045000c56507280e0012260700000f410040d1101d07074460007046034017550300a080b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 779923615 1250 779922365 779922373
    0x415061d010b040608010e07032d0e0a032f100902040b040504171602190510050301080d2f0d030e01020301080319110714040f020a0c02060d060b031305 67
    0x401c2c1046040d0683c3c06550b00741d9038445c00d030f07031920304680c2000034090406014143d880c0b200d00584510030070b04048041007114a200004011620007048a10700118010307103400400c2d5000000e54050440880107101141e044003803060711392003030045000c002441946216080402e841c000c099003000a0450007102c04204c1034506c0e500784030a850341114010a0aa1000e118000003078006001e000b02c0000d8080b0501c0f000c50b02d5012501704101007481c8000303518100790420040c40c0400c898490b80505240c401c0c21549048a82503440b0f4a42c4000828021042011a902c2404d148010200c40452540707000007004080c1d0710341c9601c1070541d803800086c181900307003a01c400c05000703da0403030300c032800154034080004104030323a04075001d54601d041144030b810181d0200c1040108001900032880c01040380010700c1c0c104070440c0c200f903001d0225140140482004103030000c00e07020b1869015100030341c2c1c980b14840d07032100070031280c1c005162404010080c421201c0210940e801400c1c45a0112 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 779924865 1250 779923615 779923619
    0xb07022403160311071101050307050d0204080303010306050c070803040f171314010f0804020910031a160903031709120d06050406080a12050903031306021605090603070302090415061d01 82
    0x600301c1882440f10250071b52a004004030160f510a40c001c5038000c00ca840c086051440d1880c801c02030740c2c4180d01494407540044018010311142d8890150011100303440c1d40d141c1040c0d40e403004032502005102410f272400c9000074034103009034800e0300c881d4500030244260f603440c0740c020301c000084528091441c10b25042071069846500502d410307a600750f01e945414800366221350800c1751444008000210f0849401030010008010041001c040c00f21152042031a181c01029246c00041c0216001e040000c4060200003282d080740011414070840480d06617165914444246070200ca480d141c1d00001c8005040101d40c2d5169000f4016a0402c1740e05000603075480c00021f03981c07061400080e145100040c0080c1001e802040100080c410140c140c80c28413000180900312104d41d0b50042002da0407481901c2c04483c40032b401c010152208603018200c504095010a07540d69550000174014201d40010505110074024030140c8151114001d000b0b140e1103500340940300f180d105c49904010110000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 779926115 1250 779924865 779924891
    0x61e0c0e01020a080c030904140712090807030c020f101d03030f040608180313060305061002030d020a05071e0506090c03060403030c0c020306010e100e010b070224031603 75
    0x403060880c0050b4028200c80520381c0359110254440041007003d0303c0108002c1016880354080c518901c241c1401d1403400d4682840050510080e41144648040ca0100c0303901c0040c03240c00948e40480e4040c80c00203500342d01c900c04141921010300e41d90350304c0703000c05200c41c0b0001c1c0d03c60180c65503e803440b03402d8250030702e405007455501c0c0907004e258480d159060006104241c03088017002c3e8029401480c682e0005204040982168420b132078003151204950428480036802d030061541058081c0c4800c2c9644541e542c0c022345074000e080c112440b40360009801e403026441801662281d0340c0140540341040b465040140a070406081e00311824052880052008000401c1c3d6002104014025161650322a03400f20024050700400a00b404544081480940c8003008214041c1881445800d824100200011040e4541382d00c0071484009107070040c41078404100654203005c1d410745001b18882c801c1e03007402032000c41a498a0781180c070044200010340540a400c3d54801d2030780d840410800840c080 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 779927365 1250 779926115 779926127
    0x9060807050f10080405030415080610050a0f180302120d080f04110603062b03030b0a051309060b09070c03182402011b02030d0c030b1309030c061e0c 66
    0x40281c0d0000f840300d00d1000050090703103140d901c5486030f4150303481c250329055512805014020400000f41840040190700e00f80900d9001c003510381c500f000d0303041907292200140b5411604441d442040f590144c100220711208079104090360b4020107588940c1410380f4030f2540c0c1c1c5031580b03095000400c070f04081403201c031503e4042405143c1007000e024441c3d00d0941401032a030720290a95401101c0050f5050003080c0000c1024545844042c1c003403142c080310305004041e240e801890b14405e03000b6400401807030ba0f80070102110f803041c00d1008580d0001e5418001c0c01450140007003a0032230681410001c640d40d00404459241c2d20030380340d0b0039081c42d29400100c8445541e0080031400d280050710038403844a003490111144001d80b0020a071a01d2305945c600a0798440c45011303000d079002190351004090032303000b00c07214505646010000c040203070740007503070814032140090030030303a6030700b002c0303418148184583c01039681c1180082c40380340ca11369541000e15051011070f05c0ca0514185070070000f984509 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 779928615 1250 779927365 779927389
    0x2b0504020616030513062003031005120a0506010f0905090d0906082502030a0206091612140d09290a0e0f0a0e040b130302030f220906080705 62
    0x40e144a050100c5644040c8440001d000280c09200e410f000c3c905111110002c0400500999500c844084c1d205687c84441420005028000e41e0018820811003020b4107507804112175040340c038040800200d48034641441c0c96401c025141d4002c0300e0021507030481401a070742c1143c000790010085655122441c586803011402480f000401540003041074138450341545401404108811084541584c0b0558044e52801a40170141c0c002107803045010f6014800c40341c0c814507034006010055050140c5644a952354020340d840150a0b14581c4180080399090410ba65061800c075410b070400248094030302805481405c0506149000c2011418080ca515400b0038103440702c60b07410054807800a50758104074940d540e0300403d200c090400c0c075990384410200100613107115228103040c9803d0182007804010400c11480412840081c0005d0340041100c80703045000042a840e400c0a042850720781c0014121040c819400e13800c04218900380f03074844012290711004880700c607039440c418800207880c80 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 779929865 1250 779928615 779928619
    0x5090606190b0315121006090e070f03120507150621030903200306190e0f070b07080d020a020106090e0114040821090a1a0408030423032b050402 64
    0x9001254070064054640c9404d8600202003c900b48003425600346042111220490016100c243c1000120501d20070020050701d880040c1424a04100d422010001c031884014011f03400c2642c0b8004543c4210300780d445d403681c00081c10602d240c014a8440240495001d40c00c0810944107400e00031042c0c401c0b5183c540ea0341030b12046a01c502e03585a83d0b00400940c04003411000480c4080a0740f0380c8d003400824468124842400c1081d071800684004641c9001d10014040c0d1100c1c0c2040b0300c0680000d070800c2154141007140b6035640007803608c1c0425015a0032100d000b1400410000c0c003564040d004403098541c110002c000c06005071031020300341c5060aa030100200071070004640403c5c0c0703400040c00c0b0004c030f01c2000c0740c03403000d1070381c50030700462080350a0002508130400325003c1244201d0055001d400c88941c40030b850911740c8940045100c0034000904181002c3d120001e8035141441c030000c0c02c11000180c9031103019900c1808458031122110340c1511481e41000c036894121440b03080d01a40e00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 779931115 1250 779929865 779929867
    0x3030e0108090102040902070501151502070308070203030405090103050a02040c1e0c05210d0f140609100509012d0311060a03090c0f14030f250905090606190b 70
    0x1020054070059000340031411a55001c01011900c2c030307414001440410711420000401c0c44a550103000764141c45d8002c40302900200a0340c00002c2ea0005821003501d0300b010003a0798505807440080c1c55441960700480c0c00409140001041c000040b0b41030800c107009882c14000b80c2d00c000c00c121000b01142c0c10038042041c50400c1d10307891503c25019468007901c14030440e10400217500800b404003e060ba180c0a400c1c00000d829680300015004540600105810500c40d0020007486d06052480042a20740644078a1001411040c103590703a20001f04001340c8101d65650b12410106100c0300140c0a04001c0080e24051200c040320101c5c2d810200c9030021070700141c041d4190104485940606015410152194089804503204104080c000c20b001c0b01c0500016103800340d001c401c140c0740c18006100e504807032040300d01000f012840c01c8021040060f104042c0307548110f0005884030540007403009910788010003102100014049000780c80486100c5219500144055080070317aa014001d02400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 779932365 1250 779931115 779931137
    0x40e010b100f020f1b19051e03030d050c030601320717030705070b01051c02100903170306030105010b0a0f14091201062309060d11090702010e0709060303 68
    0xb1062401d05100381540c41900c14800c8054409442c1c2404422a60514640c1d0303904002d162400c0e0021443c2e25404654081201d8544000100303400c42c03480030b8280070342107600003141d076035002d1086070358040740c004041102d070410071540740903508102c1c0e440d0301080e032180c2030500610600200104500c00c000000f040c000c102d8a840942d0782003910101c5000c56000b000624aa440c6005144100b82581e9850703282c0c0ca0605006010150690021b401503442c0c0007141d6080014807034401c15950191480800e180c0c040038100c0d40680301e87d0000d8108010301c00e42801c1d20f103405000398041c000c100d00038001a40c0390401892184aa824034001140c61103d16100d07031801041c21106400d0018006030401d04e1040104040017815101074150f42d6603480b0a210802c40002e50300d06000031001e032901d0481c400000b2402c0b81c50040c1c6443d220302082d00d061000c10910301c0096038a4070000e016610030f801d0804019010308419a01350029008001000c16110194031800c01120740540d500d418040c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 779933615 1250 779932365 779932367
    0x403020a05041d060117062202120c04060b0304140c061801020109081c0f060b1204170c100b01051908100314031201080c010503010b0a05040807060905040e010b10 72
    0x21181d09039190101c4050f09500c2d1020f014042140200b80218503402142d0b031080c540c90401a005101e0503d41c94150f40b011444030703c00448400d202d0313054403070890b4001541940741c030380304124000c10352007414494045925598900510b0203603100d19440b0515414800b40305484100c80441c15800c4202400314840a40601c140c188a03008107000005500d8055214140140d208040c2450301000c0541060003880c43e0340b0514403100742221007082158149600c004141c17040c007445580d000c88201c0410f0500c40400300000040c2a0742d07c4066441042d0542207454008409110015525004000809501800132600030070040d0b0f02400729000d00002c00d50391b020024203207041c00124494040300240c014440c500d4607121100007036489114003000842c00c600160081c42040c4c000c86815601a40c000082e03030305440300c0348416501c0b0a0452001c8030240200d5101200a210707540000500759003140c001406c0c0ca10a40d414400181c041d014a82a10075000500750040318800300060b4003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 779934865 1250 779933615 779933621
    0x1803060f041506030b1501020607090303081b3a06050f0d0807120302130512060a050c0d020414100323070c060e01140708010305060c03060f090708011a0403020a0504 73
    0x40409102c000070300c9500e9444502c1045c0e400c4410300500e00c012000c0401a41c3c0401c51554170401e00e140240005045d079400400c0c1801c0070300210300142c0020b144040105089050ba6902c403103c1d40310316400c4034140c19540d03442c8a241c010402c8401d042841461001c00e03402143c042c2d40c0c000e480c0300034460400701406541d0108100aa4168405005c01c0d0b0010740340103c2c141c80107500c0c0d0340160319000418130b190011800da130b11151050000349410310809a0100f11103900c8005804000f0711aa20700d01004c0083c424052100d80041c80003402003141100a04c1088450109541101c6e0300043e8240980c00c03a50885500c200e03008006088007405058072807003682c4a0624030b072901702000c082d03480805a804204c0c426800f651036080c580e403034400c032034003041d440105458401510b5140d40c4913140c880f0005001c110f5040400400a40f4648941c080c0d009135403c050a00b400394075011100806019003030042c04a42001000c0d20401c20480200b542c0c15a500100910619841c01e0100001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 779936115 1250 779934865 779934893
    0xb0309032d120609060301090b0621070603090b0726060a050d08040504111303060504080912010e10060f0909150903050c0d030c08070e0a09050c1803060f04 69
    0x12020440350740c0d018110400b0700200942060508102d060807000c128400c24010092402a0f15001c47c5801007005400c04a420440030782e441000300070f200d030307020341013203510f080c482800d12a03c800010180c0c0d040e0b00180b4001e01900c040010b40c1c4a8a00440380200c07038000c6076a00d1035105000d440c2d5a00d03011070b01600180d000345032102007603030346000c10180030380c0b04030680350700d200441c0c10441030404d030141550000c030712a40c180c03038410003e141070000422804040d102c0d6549000040c2000300342d108880a1910007040c1c0c10100c14503841560180841c54449c1d507150144401c0c01d030784102980903200c2070300c860f46845040c2c20f051a28110041a4640342074404040b98181100c6080c03441c810311081900036503c0c3c540c2d503c0c1c4544003920b40410b6120341d00c2058501140c00c5c4056901c2152140c01448924020092602d881c000418245e015013185074028906820320060815900092401540c0810104085840c9a08158540000312040c603086030080c130000d400207040f0038050b40 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 779937365 1250 779936115 779936167
    0x12050616050306191707060e03070f1802070803130311060903180102010b0d0804060f05030f0a020d0905070f1404050103110d020d05150604240e0a09020d0f020a0b030903 75
    0x511103941d00c800d503a4102c14044a40850380003140f0501c440b0340c8c000c0318103030040400d0780200855032030b101d0503a040c80850311446040107058030a03400306041c01c4d01159055134100070040d0322421b00e20311200764801c407503004401044550148440e00180401d50510402069020310308192001e0740c0c0b9081390b11002120740c119580c5920f546c00d00c5d80e0b90002e44180d070740113a600b10f48450404502805207140305503d03030280003040c010098917216105026901180102c4003517100c1c602d41c021a0b0207003184080080c62802021300119642d030306100b1180498542c52881a132200340c60003800111f4800b03000c0a800c210380d884910019060103195400207a1005d0720360300442e0215141d5a007017680c2d41454640e4440034030280a0075180c40d01444a8045d14000781941d01c1ca0302c6001d103540c030703c207901c034a00c404103401001440a851660000c004a41c01501c140360313043e02c0d4981041042c0780e07400202c0c03084110301e0020801481c3e80041da841251021b0081d440c0550842200040307180c0c4440b000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 779938615 1250 779937365 779937409
    0x20060f161110020a031107050705010302070c0e04140d1815090317040e16051c02090409030206040b1e0424141b03071709010f0612050616050306 64
    0x1100500d030401100b007502c4148100183c690b8410310001301507030302e8008140803820050003024041800420304008a4009007001688c2d400c81e494264662035940d48644441251541000f06110084807000c440a00b0102665a1810f400740196503c00b500c00c1e007001751135030303420040c0321001080721a801c1c04221420020070707095685d40c0d0007400301042c1c0249207251001203070030000d4140c1c0c40c01160304080c0941c200d020309091643c008286008188000c0201d4810f4000d4103034a85041c1d044821441015005120034541c81c00c0203951007d080e9001c07207030010404001040107001d45c0562007460381c5013020301c0c01500d65454400380307440350058a100c07009070100568450069440b6401d81c1072655080c40b107003460100d01101c10390040704040d280c0c14a081007000707012644244118040003a880300507501e51202c81207240145009a5488603540c070f05580403074030301c03881c1c0f03c0100d42c00d200d1021549559901c00404501c0d001d50080c000c0814810700c0860b05130b2a01e10a0403840c17a02d0001c5e00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 779939865 1250 779938615 779938637
    0x31326070605281a0918010501062102030a0615030e150c070807030e0303030a050103020f03070f1205030405030d0818190b06010309020d03050a110613060915020a20060f16 76
    0xd540000150380c106c00188040020708868002030040c540140240d040c0b014030b4a8100c0034070f907600044400410340c810b90000010b00ca000e440e80c8110082d0100800c81b98a28020103030103401040050050701c180d1003040002643ca014074050030b40310b049000c17400b6041a030b050341c81080030b401515084091120841d00d50301c03261410001745108000300c05000c1101e51450050149401c4000c001a0081d003001c2c0e414805100c1603c1900308a9a84080c3d44023611103a040680c25030045401040c0d15000c0c3d01403000009a00c04403440c09800305801104030010000e8929590300c0c1620783c0301061141c100d00440200f0056288594050410705001c00d0f07125a50b40001d29400c0c01c041c040700440d102048030417150f68440030100480c1e100c407006264504001150000000003184010070b180e44030012a000c0061543c5541030341c8006141c1551074205945c07014120202001200d605031060215070b0410200004105000740004c04211004c0c1e10380c0c00c00d0f0011518036040c0c0c0e0007880310701000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 779941115 1250 779939865 779939869
    0x230703050714012c01090b0a17060f040f151d010b0a09030813090e0a11060d091401020a1403042006040b0f0c01051803031326070605281a 61
    0x114003001c40c1c0c4c0b150f01c601c41000c410005030000240e500821900e48051013600003a541080160381900022140c0c3e54640d0345e12000507400291100c4402d8106090102011440d0a03d800081907003000c601145240350b103500481960b00d17030600a070300708104c0050040114508c103800a01246080740b4140032600d07160741303991480d54411400310844c4920844204980306192040e441d4201000b0054903406041e9100d0703003014000111418480c00000401d105c1811040c0e00520341698040c29a40d4503440303003c60b03c0e00035000782c00032501240e588440505034244031400c0b070f0720461f480806440744488012034001000c200d48051034020f5010070000c200005007101034500c0c0c40643d42d078550344a100600f40c41c01d4076805405112a030360122082d41100d80080250ba9004041914911020031103080040c0c5115240e5810b940c041d011074522124000110020180136004100030301054660713074001280c2e5980450040d40b121485032001155015940001c00c0c00200c00300e104c01070202142c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 779942365 1250 779941115 779941157
    0x6120609060612040311011524080c09040b0d1a18010501150e030109020a0f1406041203050d090606030f1202060c04060e01030207060507212c0f0a23070305071401 72
    0x100580840046d1840c4421034083c46180c20710b50250712b00030110f4140340d020b01500b4054085c029104075240e441e110401e0720395060300c0702229000b0307003402d02529145121888400055444100d1804007000448400c0d505015150403541d03030b0303e10038480802d041c034222503055000a905615540b00c2c2c2000000d650358003420030182205080d1019400e00e03000305e42a80300309510b030b2140588402d000402c2101c3d482d540a000e030940504006548035050803591009211698000341030900e0680003000780101075098041d002d204456140403442c1034003080c0d81d20f081c00ca42040300014208000e010151140100522051040c1400760510b09565030310020b8620407189000022000c041514400c005902e0302d1a4002c1d4410b800c1095040d260248a003100c0701c115130180c201c50300c4118100c100c20400c10204005120010744441c11014030700240300c00000c0d040c10a84e280f130340144250350b240214080c0116a40980105240d0f840c0c40c0c8107504c1da1030b07401191418008030200f005040f1005075 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 779943615 1250 779942365 779942369
    0xc12051c060603060602011104060f0c06060b07113307141c080403050a0503040206092e111e030405060a1101141302041a061206090606120403110115 66
    0x40010403042d0a00500600701d4526600490441e810030482d500480c019004650a0340d03c240b800b03500303101c8500001d882d80c140e40c08004103d90302e07050000403e01280c1c0090f04490303104c3d03401e00810030088010058800c080c0c00b803030f40c03815014400d0f000d1600d08030003d940304c034456403600c14104500da8071101c00c42d441d1000680584d402c044000c81003142d81010340c030380d401c241e07080584050920b43c400030464080d8001c0b8105011001002c1403d5580d00300070703034040040050122440c2d03030303417169444040d0700f0302211030f03180e841003020310382e40c650059500d441c0f45d070080342c020850500310300d180324103081c0c05032010103041c00304010200341c58803094002e111010301520b90300214a013101180c0e084800f00010500e80e14004014800701030307481038000003010b80466020420503d0701201850700213960406503031101c00050305c4000d0f02104181a40308081c00c50702c00300e8071341c0c3d910b0500109220301c02c20a000304030000300103000203002d0001c04200b14160000060855000c1e08003048507081e039 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 779944865 1250 779943615 779943667
    0x90c09091721090c0414060310060f0e060a0306020403050d030e01050705070206090406031403030117010501050f0d05070b04120203070b25050f060103080726040b090121020c06090d0c1205 83
    0x40c0100407540c20308000741000120507040400ac294070380f8030345140e0503e0500500300c0400c200b2011034000e98442140a025680190301195a10381d68030b807550b40c900400800d00c4c042410f08a848907100c17418890244914542e40b41e0b82d2420700c0300e80c01c01001c0d80c4401a4980e1007940c5010100c00310750022110352540304961f00551392941040d04e100c55121000461190b0f5a06140c0140826240c0d52005608001c0030345038100030a10030720f056400c082c1c894214120420000c034002503040518615180314a009a0a944074940c440b01c0c0303407180b031140d501b9059241541c00824600d8411280c040c603c481d02450568220180312645941030500030381c010386001002103911b00074042c6c03c11030712401c449119002079888640d002104403030b00451040b004481e20203e02801680d01980440d60180c01803507200600748005a0844000e42010a000d141e51003050005a107103200003803264000c3d501038441032201c0000ea40c9000740317514141850000c00a0900140c1d164180038100c600445090b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 779946115 1250 779944865 779944901
    0x90307021f140a021c03060501030b0108040f1b090509060609060f010e06030c09040204030c1401090b22120507060806030c0a0306050901090c09091721090c04 70
    0x54010403064200140144071200a0828000a00c1e504180c106403880c40e070440c5240c0f100c00f00c0c8416401c10030402c041d00e140f060051090040300d030b81a0f2000e01520b0f000d880410018004900441302038008440041000c03012b40d0302d4801240e803140c0c0003564038032880e40c0407440c20344580403081521400c0c0c50300407040d03006070b042c04120301e810309030a5032003002038640c20300c01721034400020b210100c1d040002c2d0007924000042140f0040a204072200306501a01c1595a203589143c0020f080100b4802c10b030a026502c020038407150b1003004840c04603204c0c80010790038007031b04661480e007540c003002e0003211188000000140002d01401120340a034000e60203090818581035011301440c200074000380c800e81083c25094056a1100244401c0c1da0b04070a00182580d1a50501c500401c2c823140c01074051261250005503104c010b802c0104070710300c1400c049800c602221110300b81801140d001c071005060000c200610074407507418207a030103044203044480d591a4000450300700c5001000201500720 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 779947365 1250 779946115 779946127
    0xc070e072003030604050903090d080c1014010b180405010909120311070803090115030f110114040e192405030307030509010c290601080711060604020d0e060903 71
    0x504228035100070002880501d80c44620548555142c0c40010703e058030035503440b800b00d400d40c4420070030354480401c050210380c0c00000c0c07401c0c8008513400c88007014000b889045403e400c00419400f80c0f5a03081c84001080c840c82e42000d0664034190480e5481c14100307900781c0840340da56a2203000b031a0007003114840000303400781c490904c0c9030f200c82c5001c1c9010a040c140b00e800b0f50160003980032510aa500140c0740764594a40218460140403a42e0305001c042c050207030301009103c610094001c2444c40381c007110001100040055403c030400c2160500718200a000401000380c4522503990300011151081301d080c8014502d2000710742c0501e58802c80e1051000c2c1d00c81c69000031008034005041c08800650038507040f554024168412a20400d04105006460b038080045104001e9248500080001000000305200202041080703c1d918001361030540030908180c0550070a4061a00e0440941080e0b542d000a00000e036002c01c014034802640c5190100004900f0305c02180111615070286139100c03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 779948615 1250 779947365 779947367
    0xb1f060c06230604150f0801051807080a0f03031517010b01020102090a12020112050924070f11070f080c0102010b0105180907030b0d0605100807180906020c070e07 72
    0x1c2040c100c40316040484a106440c001c103020340b09a10070011603020880d80420031081d0078004c800d0380203215403212804080794032101034201d9440707501ca034490855000402898590ba52070f19218015003a0803403ca4140450341c100041100700d8003a08021502250009007076000c0b4505501413900c0ca10800002680d4407400c0c040c0d40041002480258201150540041d02010480c0b041001c50030101c40c8440459000b221090540f1805c424200840d1800302e0786039413140d1807800d0700300b103a46c003641408c0409090754001d640540707940c0c0e0710320961001043d4181c1d41030440000d0403032140700b021000903070110290010005001c40201038881104500006400c3d111500543c50610000b807200c500c0090b10400c16008107041100c0f90707d000d03140c01308160000c107050040c043d000094a1308007418081950801d40c000e02e002d18030904d500e81d0f50410561a00c40f507000d207904405c1e01103561482e0011310781000007814000c640051411418070352a40c81c0400710b0340100003011000701044409 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 779949865 1250 779948615 779948621
    0x30c0405090f060a080f061503190b010503010605060f0d050703151716240507060e010914030901020d0809032109280222021b06220b1f060c06 63
    0x30148080144041006c048400e0348a0200816030b05442000300100d0340f0740ea0301000034802e66000c100d01d1065980450802409178542409064025030a02c00300013624108001120044040c0c2401642401040003c002c05088068000400c0607101d0620303082c240e080c00f130080d00401c071100c10002140c088403500303030030035041c0400e100f40f8440070303042045040c6e03084030442e4603280c3c200b0803001a40702480050311503020f550b101601907490035002c023101c1c22056125503021402030464062a040800440f60703648681c450b19030040e0403010b03500b20b03098040c94030a60000341441c15207080c41d008900003920150f80d4814280c200303110707000703201c2d13081c0050100d11a1520b1403038006400001d80b083c20f0401d002c8101d030003802001015a0002140102c184004800f0f035804019035454110082d108075444244c64281c3d0300c0d01a00001c24010a559a84c0d4001c81c820340488003825002e03a00c6010160030000c0c10500301c08400c0c9100c00c0c805140f041c0b02409043c0c140c0305c182600607181040011 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 779951115 1250 779949865 779949869
    0xd0506090a03081311060714060709061706061e090904030c0c08060906070e030c030a120f0e0a0e0408070506090a1226130203060112032a08030c0405090f060a 70
    0xc40138103010401e007504005e850042580c41d01e50300c003c64a850004205282010381082c040c0505001b0441da1215441e000c541d519510540051b80021812040c3c400540d25250301c850100f00981d55001c914501005200003409103c0c106076019010580d00201201e0072000540e110320703100f04000c2c107210000090318a11005015503d0710b111441e03501c03c0050020001e0201c0030070600e6165030f08000b01c4421050103407d80340844801e00e81603401c001f0500e2081d000c120b0403a014100b807481007180c00c4105100030310b8104501e180124200070079201410030b56100d10100403040205204100c02070092282c4c030010308a01180341400d000601a0081903030070440b0349a049644801e84010140a00c400702e694844a174031003060b107444038244010b009405001d960000a6544845000310400300d010703868100b41100601e51002528a840406460181c0c80c0280131001c030711070394003450b801004000d0b818502503d940004030511011503004291943c0b403c00c0000ea810b1940c03d000c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 779952365 1250 779951115 779951131
    0x218030f1c0e0a1e03120e0105070605070c020901032405090c120f0a05060912090105030a050615030a0e010e0105070e01050309160f03030f091406090d0506090a0308 73
    0x2070781c84150014070001031000034600108a0b0403510402c1c81d40e290b118440042c034190103c3c01140d20000715040c0c800c000d6220581d0340b038048124500c64079008290001c654001607443c60324001560b5141401088080e1005040100141d10b140068440300e803031034040c1d800741c541180c2c0c15106051010074468051010001203061005000380c2c1c2000080850500e8021128540c6c07108556004034500340d8508405105031190f59030f0f03902400b0700072500da402a4403030340681c0c1c000706003040d403412a03210382c410241c0060010000038a8100c1c1d1a4032031074201200070301c28843d04450550100ca283c00a0302c00b529000d07507400b613905d441042442042c0142c028070000b440780380f51001c80908103030310101d946814441c0c000002804400c00348050700300195508100700100d138071000c100e202e1941c82c0c0012800b061840040311700ba1400741802000300c0d403005000c81d841c40d44c036400740200380c0c000260250308640c02c040c01c040001c1c42480503d00c0b9080050042403c100c160500815080020b00098 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 779953615 1250 779952365 779952373
    0x6081504020304350f0c0111030703061707050a06080c071205180a260a02031905070806090d0507030e370b03010b03040c21030807030b0a090c0c060218030f 69
    0x42100300410070740354503005920015448051b0005906d01400c8103800036449124000100640240c0682c03200003070703682d0074011610348444115500e68030945030007440e034000142c800401c482d901c10245075601035684149281005641e40c0c0e1071011640208040380030a00c089414081c81e41d81140c00e90909a0481e41d001d601072518030b1036000c0c80e028040c0f141d60b0403a110960b003e030f0b02007040300e454150f501034103c40785c0b0f6180e000c0392000b168007a80d0072141070184950001e441140000d4480c05003d142d009484017030842c00c8241d585034070020703084082c05410085c1d900c5640e181c1c00f03800c0400da12902c1c41104200100701401c0b011a60040b6111042184407003801000f000b201560f055580080c405d03071380ca0302c540c1032000524030342d98403002503010140034601308000c0f00ea021555442c440e4480300310503120b4150540c2581e150303455450f0401c0120b4003c2110800071341101a0413007103400d00320301e080c609480300c81c1642e101d802c40c00604410940750713141c80c6c1400c004200708140048050 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 779954865 1250 779953615 779953703
    0x9060e04090314131a0d0507050c03300910060b040609030b040c050303030c0a0f0302030105030d0c2d021201052e05090103030816030e0706081504020304 68
    0x1070000200d401a04040b5100400c01c40348410004106901500154440704140c2100180d20b2041e40d000046c02c800c49410180429103681c082c0c0252403a103032541001d54101a15142a24145202c504072402200e007040035412200d81c034800e070240aa004400603240c070b000c3c9e403c2e030102500c8a95000605004080200b000344990020910040c0c0ba400b1404040076151400d000700603100640009905000c00401c1c80040c0090500400d00c544075901d42ca6540c43c642d00c410f070f003280400d200e41074041d0010149644884d101c0c00084100358410040307466496508807140403d86089400c1d8841c03400143c5105c8203500d8000096034211200b0790081c0850724182008585d150800c1504421601041d01e0b000c40c081c1c81e030740100d40036101c0940502420341e1359040c01040401c05031004280496000c030300103c22b45c46030048041c001d29071002050420f181c104100d42c3d0070001000b40b0b0300902450481040c0750351b503000941c001ca00038a82c5400a22a5021040e0884d41c0201403000d0b2000203410 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 779956115 1250 779954865 779954867
    0x41a0a11121005100f0e0a0305010216032309040b01030e0601060207032a06140d0504060605013b0a03020406120302070801060f1a0c2a04140f070908030a09060e040903 74
    0xc1500440302454542c1c061906d6001041c440c102980004005500100b9602041c140c0c0c8400790070418002e5a92050008940c04103260255800c860f10b6040d0500300315500352801c2c29003205804080c18940040c0070204000c0c05400e184007a0031010058000345c10400a00140341201c00700d610528420740b16640f904003900303401d21028403c44d000c3c003c001030006842001d44003541c0d488800d00380d080c8490302d018074140d002010180070b01d60106528050170183c0707a41c1c0840407400904030021011081c00c9120042601039030400030320b0743c4030441d03040100050704e03940140030041c5142c88000042c0c00342840c2c06410000d13150403c03683d0340e140003010800c0080d01180f0305d040300d4202c000c108032401c0314001d412142c401e1080d1405c06114280d060005a08084403020b0b142c600040418074050740343d000c02094601016100300d0b0305000310007080d0281c10f100200da81110b21400c0200405584a400341c3c02d51300701e02c0e00940410240c10081041030f07000180d034141e01200f12001c10810b091303690 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 779957365 1250 779956115 779956127
    0xa15051815151804081317070e100503100c0e06130b1c020c06010f0506072a0323061e0a0e0708010608030c010b0603041a0a1112100510 60
    0x12841c41100b000512564041c0c8400700c8058000d165469441d540d481d15003004030142d404541401c1c91a80c0c071540000d01b801981e101c04100382ca8580103400402e00c0c00310215800100500340002c090a115800100c5580800c4a003000020301c07000441c600800c0c0d1006001c140703103003078558007900042050000300300074006940b0548400802540d1501d00c030744000580d00c00c0055500e02d606100060005d015500024040d0499000e80002c406281d107880a00015005549009041c0046600506151080580e4410441c0942e45c101c0f13595542d01e4a078801408a000c40b03a03040c5031440c096054a040d13013408801c0d07001110061300300b0461903004941c00040401440450b02030390340c1c1082d00c00c0440c1845a68020555400203003c034644035946980c07283d201d9a004e041c03d42c07810070342401d0303410040c00ba01d1044e9040400f0306030107880b82e01e18684e6181d00030f001228583d55120200700c0545600082d01c1c59181d01c5c24100d81c0c9103842c008000c800119500020720807481030b00c1c82d05400c0c0d845a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 779958615 1250 779957365 779957371
    0xf1209150305070302090405040506100f06050a083d0801020415030b120105011806081216170a080411040e0d050a140a03230c0406110a15051815 64
    0x3207070028603507039900c804800030301550b5001c80d48581000184020b02c00d00007801e6009102441c0105c1105964000b080ca007450280b03c2c26000c58410310a010303a45000ea04065072045401900c0002d1104c0900400c107a00c80c3c8000840705100855501c4035a0001180c1c508040c0034690021851710b800c0402011080c0c00244400742055129414100746855107008008507604400007030020356101c15402c400781c41000010801d9a25001d000226402d0001d020794001202d440c01034a480040b165540c0b03102007001d4181c85400b80103e0740c034213825240004161081043d503500e206d81c2040c0c80c000386442c4520f0001c510450a10091002500c40801c101c1001003c5050007981c60203100000d5604a1000521102c0c058012400c2d50405170581c014503a403a5422200c84a0700c00c80480711301c04250261840d40740c102c010b200600841d800b0703010030000c070030070f150842d50006400e940c2c0e04044513101311103610036904c46c024000da04018040080034618954054211681c084c04c04045e001801 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 779959865 1250 779958615 779958617
    0x203060a0b0418150e0312010e100e07030204060f110d0e0f0409080903010b0114301503060c0421020a0509040b040302070506040e04061a04090f120915 67
    0xc800c5252a03603220b500c640c1060f506001944400690f030b00744482c41c002041d00144c0024180101d01d082001c0100c1101d000c0400b1768802015642004450202603800500007040c00340201c0002c243e000040212501c61701c250354002d82e9883c18294010242e8100800200030300204080c802200c400219100708404104d04c0c02a030708103411400500c6801280c41165006882c0c0440f040c01c0c400000014980b40000760000c3c0038014410004440ca40c0350001040d50b0170200340311003c110094030825081c40c090021a011015081085400c0c005000b40d51984000704030312054a041d08080c001558840f148150840c2018030707041242000101c80d1420745030b6000b80d0040c140171503690810140143c1400f81100c0100e00d06890321031620101510140c0141c1328150001031140340c05003ca5068907915000055141c50b190341e180050042c042458881403507046145250392140e05c10b4900702d0340120b40c90300e4491550f003020703d041510388801c030007040141034041c0a000c00340b6410459174069 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 779961115 1250 779959865 779959871
    0x2031b010606140a05030f070e130617031204060c020a1a09060f0601050a0c060204081501080c0a1206050402010e060a030c032702060319020f070510050907060e010903140102041a04030203060a 85
    0x502314221030420300e1a14581d40081d89804080a084080e401601034441c020320821801ca4082c480316900c1c010b02c6001e80c443c0f100340e0009000141c6d25003040c8194222801182d00300c00c8035039507504540800a80420b6518100401c01c950030310304002c2540c1145001c0121071180c1003d100080c8980726400011003800801c0030800c0c03c12046504070f4000b00800c0003641c0c00c891441c1c15041e0300c01c800303100329105485203020343d110314a005243ea404454103800c1880c0400c0c080d070b8400000e0680107205074140081c1103080c1540740c407010300912540d143c0c3d80c0c00250058503000050201d8110400942c81c034142e05103c0c500701a003218406202c2d50701260104d480350346e9000000768980b000321035805482e0000c90024075206202c400b4100b03907031044040c0e0b0301c8001c0c207140002c1114411101d000c1d940e48200c2c02008524050a00b05004030710614000581544949405600e42003100000e82c05a41c0018200040100344031091a801104025140f40a01d5500021358408000d050448160f61b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 779962365 1250 779961115 779961121
    0x30b04062d0b040803030403090b03090c093301090f03080d110d0f06170d27050402030f0f07020307031d01351803040308090102031b010606140a05030f 67
    0x60040349040041c42400d41ca541d0f16626048129140d400944e02200854034038000030440540c0c4e503040d01c1c0f01382082c5e80201140070030301c410441081c0c0042c0c000c46110110741c50600c005d1113210310304500d54008551000e100f80180c00010300820160344100b0444c54000414000240138070100c508004c00c1ca040400d182d0070f00c5081c0c51440c130030200c100040d50f00c1c20654903400728040d04924102d448002c12a11a0190100c4c90754403810201480383c0050382d07100300016454403004816402d4645a00c5a074034694490001c20100c0c0d20a030385111807480c110b81000200031400e00c1c480d40c4220717a48055130038540c0d10303035000d0f00c0d2076403032410084480d807000340444031a4401c0390303000e40300d07034004418112040c4820000c0090415010f480720070b502c0000001641c05c5c6e102040092484880002036103014616241d0b03141c40d40207a80ea0750304501040040c1e07100440c542d4045520a0548400001c4c002d24181c40a07003040c01c0074060045503881401000245a00a42a03a034802d035007440381c085c155 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 779963615 1250 779962365 779962439
    0x503011b0e1005270307030510150501023f0d1a090a0216170703020c01030b06040e19090b0f0109180303240b09040e19150b0d03050703030b0406 64
    0x381078913040c0342d0580305421300002480400121031545510700da03020080d1b090a80d0300ca0700850b00713600559025038095030721315414801c92851106c500000500c1440749110400101114014010003074075103407004900f071200e025041c807030500304503444000301600c1a542c0b0003140b1242c0000380681029540404c44112001030446003042407070b030001c041d2444110404000c6581d4002200640041c0f0230ba0150581030b5007e4030400000c290028011410146440011101000002d14540d00c0020559041c3d4100250f800742c1a40103100740c0c2060143d00d0150a28280000d050303100c604494140000c034100c04d6801e000842000d501440c0124044400000b5100c0064440000109404012200080d0015250060501d403041180c0500c000324054140d04e5644101c100681504084004024000750100302001c0c610141c2030808500b40241000245200004550070b03004154001450001c042c1d02d07204227042e03404116400c1102e5820505900c0b10100310540c0800c000c003400c10304603108 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 779964865 1250 779963615 779963677
    0x50f091905041a07080702061341030a080402090601030b0d2924011206030c050405010506120429040c0f050a0e0a0b0a0503011b0e1005 60
    0x28588040d42800107060601c0c1542248442100b0905500ca0500c085808240304208040c062003a6600808c0745446420b8080030100303c048045600001d1406213040390f601c0d10310964044c00c041c00040291204c920350003080001010080b04503a0001c0200f14a825085100144c000d6010b40300c01445030349041c01607005084040585600c0721156034480200100c03d03040803120000d402c440b84250761221428a030b00b0500391001e010350988040941030742c0407600950284554145459041018448001400c0f41c03c00d030000e4451044481c81400582018040c080c0101000e540301c1e440e0038840000c030603411002070070040644e070107580080e042e0200c0d2a0ba01c844248008801312040c01c00b80341a108000710381c03180c18498240030300d000a1074501070b40980f003140c001c0c104034480c6d0b959140e10310004040301000181c1c042c03a201008038250700d003481203440102c1003c0514403100b066000c06044041200b801c0d5108506450368071088079400720641d40c2d2000481c1d02d64890340703145c0100c0b0300e01e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 779966115 1250 779964865 779964901
    0x1080a1101090e1302031b0102060f1b0a020a060b0d051c020102040f1d06030c030a260c0618010b060403020d0c08010c17060a030f020904060609020a030b0a050307050f09 75
    0x3c2c0314405024451080066015050603d100b18101c40000402c4030320b0386070400c07070002c90b40d000d40c00c200c0008905600340746801c3e511020f940007401807101a6601900d0305d401c13120700b10300103070b201e100f05130100001f070b1082d0491b03040300325240b001c0005280e588507501e01c4000f220003180030a07035031840c5002d4000d40558026244500c81800c1c5592603804440c0c1400d20624145107100030f00010480e2400c0110b00f00000d40c0c0f0240c040c01c00340100f600c0b80441d40c98920174500c11404401c08041c1903070101c0000d01003030009200904540d007021135115556104443e03458a0701d0745080c004200655420085404603981070300c1500c00302c0c14501b815143c400341944900341039428000d01c031902c507501c0070808805442c4903844d00b020740c0b80c1000380000c84005000044c90118111442c07409807034600080b6500a1103100041104c40d2100d86070020780e08500100400f07c1e485041d1140c06180c004041c0c005400150010890b01340b0384400181c50340201c2c2c108138064040480800c04140d909074210503 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 779967365 1250 779966115 779966129
    0x6010308070f05010608010e0a06062306250602090306070801260709060308041e050d14031b010b1305040b06040b150a020a0c050613030215070f08040608010e01080a110109 76
    0x206100e2648e08440d141d0701d40080480e40345152001c04224103007040c1032402c4680b000c240800d21075403401c040c4681c560081d090b51020043c0c41300f012500c10345281066445601c03496025072641d9448041c180350000c05401e100134010003100600c6a034800e101007001d00000000704006c4101440100c6013060720b2500b101501908102000c81803000010007001105c900c806c24802c80e80100903000450320050003211b50007a248441c81d00800c0d00c080c100813440c22000305a0b458001c0d051303105008414100007114a0340d4680e041942c3c1d0745400740030b00c50302c103443d0304007809580703081ea56100c11050010044c92086958910011861321800307030740340310700e00e09888981c1d0b43d40762004080d40c0e503121041c0841340c4810428022400d4200314040c0c8400c0a4440040d040a904550030414006a125085402280c1c1803200e040412251480f44100c01d0041a606554500f054002070601e2416004034020180140040103000400900c0144550704182d0040103600d8042c0100ca0750125070748000303 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 779968615 1250 779967365 779967371
    0x30b0d080c07211104020307050405040236240403080a0914040216060c1103070c03060b060702030a11011809020a2a020105030c1e0d060806010308070f0501060801 72
    0x842801c000600c00040e129070b450084240c00a00e102d07102c10306090003004105180d5031002c04020b08098000d0354000005061103810640c503000450201d03000301c2da8a40411013284501c0c0d808110442100c42514004180d000040c0e0400010445068039400002400b4400d40c1800c40480c441c0c10541c0c000e947d00c0340b02d0603500c0c00d0903200100f040c91213000703850285c030303031449403ea0f14070b081e1084812107443d41c0300c40c0e440d1603030312f84440000f0248001094107020300300000f03000701e60050004044480c498280140719900714201a01140d80305010f16002e03101c204014800350303400040081007146c3c00308020049561a400480d506041076840e5059400c040f480402c2c0d501d07aa0b005480100c000303607510a26242d80d1542681c0b60318000b042482c1210741c800502c405544a40011035000c0001007082d45454607484440d6041224980c600f0040d5001003114591100c107402007100814000c00140420350641e101d1010500c52454010a46140200c0d0141042400e400ca10001c00c5544020 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 779969865 1250 779968615 779968627
    0x606030209040302070e09030406140a03381e090a02090a030b2a03060616050d02030301170c060d05150a140a08030c0303041209030602032d1303030b0d08 68
    0x6175071103080e0301840c5050341d400340014000100000a480071030b030312503840100d08600804405102d40c0b00d44c01d0b805c01c260700c6401120b41d020701810821400c08001c1c0303101194007546107410074003040700008248a1041c1d0300d1082d039804450407804c0402c01e02201c4110071502c40441d00c10003441980d42582e040341c010075000052001c15070142c2d2180c17015228a50440c940d0001448445c500048115040842400407400908182c40508081081d800c054000c00b600354075910f02e000390210728070006a00c000014829034030290a118804060b11004060586204000461034094400b10a8404e5a9070340091b04440c030704050300c50900c40c0604003c0030140c50780000b034a5001a0306c501c1e4018600d4a00024013100c000040302c03c40c4415601850460b1207644c0d5840f010320034414010104003000401001040c503620003980210313030b074401504000440001c0310341c070044151b80f0090103c40c1e200c10060a81c00c0304c03401d41e5034a40c0c5460001650200f40000485191984101400c00c00010402e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 779971115 1250 779969865 779969867
    0x3070614040b01050f0d030315030c09020a020c031207110d02090a1a0d050601170102190e10030207030210112106030f060118020c030f0f0d0f050c070f06060302090403 74
    0x501801107014084102d0345a894038144039400486060564000400e01409400f1a02c69403200e09503940203044088080d590780c80780f10802403036400c0b50324100d074001040984540c04010054107070105401400520500d00040c8100c1d0041c070801400c0340600c00349078402c0d50354024001c42d200d07500501c40354041c02c1c150300801c001c1140150400400d03c0090f66a203091512248088501d80d00800906450382043c6a1405040c0c12000000c62036400303004958210a44e42c00c400c0c40c6045550718208640c0f241000c004401e946409074a082c180304001c400c0c0401d50106182548540180c000f0a45080300311600f8001c1c490b0f03100e1003180e10405000ea0341c0352204083c10a029070000c03400c0b00c0721084100d4595407501400c3c03142002c03081549464007141c0b82d403034015280b80314120095a04043d81208200420351103c0d505180384200041c900e076401d00b540c40381312100c1d8060107003000b0314606072118541c02c1c0320f4817401030042840d03107141500704180d0303401240156030f014104c481141080e00d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 779972365 1250 779971115 779971151
    0x130b0f1f020705060301050f010c020d061b080606070b2e060203040e0a06150f11060103030f1d10030f020d0903050403020307060e10080603010e250f080c060c030706 73
    0x10100c0c010300036454001058500b900580c1e050b504000e02d520321106401e001903560a42d60f40080b81c0160610500e400810031500c1094014050103440c61080440c002d0020503904000303100900c190b8050000802045034490306c10f40c4110309484c2c0c9059448102f8040206040c40408841610300c0c2078004200b0310b0740400a4000c5541021035440252a9190040c054400d18007c44100c208601c40451029105a1540b00d03000114108021804020a801070034040d00340c0003500860740310340c040d035142c6a001c601641c00c0b80d20f00c1d2406602140180c001892051400880400c0686070462130b161048254100c5041e4040f0307510803c0414407625010301150400d1005a110b4050708000180e418001c00c140098000008c010000001e04010144d403486130140400b0f8142d981c032003001c1042e10007084403810801180c0c48000d40c002c0249481080a1410340288200402d614030802020100040c0b43c2c40340442155802c0c0c9a56801210030301d580200b1001030181400e260021840c54201e00f = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 779973615 1250 779972365 779972419
    0x27030f010225020d020f0a090e1c0c02030703081e041707050303040305070e0a060509090a060c11030301050d17070804080d14071b0825060c02130b0f 66
    0x1240c85000c018000400c0ca100100c0c052000c0e4215413009035590062810700a12104031000502c201d81241d210000b41007103070b00b4a195201e140e07102554000e00070540e6583c001101d517441c502910188880e5005c00c0c0c4801e500d00c0020b061850204070b01710080b009404031515a010000300546a42e0b943d020309410602e81c040b803483d14010043e0104550038044215815203801030700a040d460700d0032640c003000311030041505041c0c42d6100800324050f942c54002034007480504000b029007d2141c24000300310b9060340c4940c400d202ca800c50f044032480010080c0ca044940440780d07900c00c00700e242420480020044140401c1800000d441000c0215880250040d507d020f021101d59017140c0c001501c3ea00e2a000c0c403415008002c2c04110000794000d0810030b0741c1000201050507544e900e40d551440c100d404540140500c880115000b04003484140c404000c0c210307460125407850180c0c021039202d1140030070081140380c903030055164a84408903030300d944203406024004d0f00580c080341d2440c441011703 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 779974865 1250 779973615 779973637
    0x102070b01030210170c0c01020f041d060a0f03021c02040905150106021b04020a111f050919080c150106050421053c030307020d0206040827030f0102 66
    0x240c542000303070500c0345034800f8900c003105c001701000da2664107a801310380d049040d2031846503400700401e940e149010b0000e44000d100d035a05001c1ca100b11a0726629680e4001803400d4040c0011800401072802c0c04250b02003100d406079104450021400044540501101d001030340140c01c10544200304000002c1540d004222500c3d6500e45907200c000403030722102d0141ca1542c05000d442e0181c1d80915044d1b00815949403a82080c0c1a04520200910705200d452807031261a0716140411195048180c011560b001082d000074000c444031101c1f0300f00c5000400389000d41990404144101001d01c01c004203031560005200842440d0381d04c0400405a03030250050110a42c20310010320720322204640c0d0070f040f060340013000e40905080a504c2c003e411000303080740e071094050320900c000b04002c461400442c03e08005d002d195070b03251100c0f01902c3c2200500e4201d086510510030040800d844405440070701440111400300001000d05404205100400080d0700d80a030802d07100c046807055004000c040c05c8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 779976115 1250 779974865 779974879
    0x207050105160f03050730140a0f0203060a06030b030708060a0f0c110a0204020a030204050a0f0905100605160f15050403030b0d02130c05130603020304020108010b030c0d0c110102070b010302 84
    0x2400c4040c0c5d1410b4503040b000c40d10440016002c01031070580060401e00d090080c000060a0b1821041510348a480180103101c4031803c3c8000d6003413038011441d07012000708055103941400c03004191117a03094412942016600c2d08020310961341481004020407a4504482203810807203040780050a20030205135610b881d1418205544c0c0c012900181036544c00c101134084038004ea02404044e500208031801015030130000401c182e51000300c07000142c0a20380c0ca4030401d0741011940c204031100500740b511603680e24101000065840400c4850984505410740c494620600c1e0110901001c22801042d0752000c00c502942500c03035a2005115500a9900b400704007094820b0155800304544041e402485c1c3e449002c00c0009039411440401c040c914040b440d1001d400600720085c0629081540066000802e010035580c1c00324845000d805002501d51543c02c0201b4202d005105021386072049580b100083c1a44034014041c1c0a041c9800c00000c9d95224404d241004c607594003400200d1007002 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 779977365 1250 779976115 779976137
    0x70b040801050f060f09070c051905060406060b03010e0a3b12030105010e0d230a1527020d211d061209030c07030309060e0f0121020705010516 63
    0x80c10083c000d002c284090706e00c01c0c4648403031104481c03140100000355581d20030181d030743c81200c40031000109641c0c01280500780c10f05040c600241901c0150340b007402010070900c01030010030390080c1c44907080400100c0018440407584200711044501110300001450003d03200c80718030b01c1e690300a415074603005c13058401440c0300301d11442d400d010a014003400a107103292044610b04000600c03400090103021241200c0703040d45450482460703079007450107558000720801002c00001c8501c01e0411038011070140900a500f410710002070003881d03c50090b409101110f88155152120070001c03854121003d801a64041000d84640075021600c0c5000252042c00b40210f0564591114841c400000d05042ca0819a02d041d10440d060161044000e80003c001e00030300031108001c00d9000354442d07120070003014a0454050080b640019185006e04c42c3d4240e0444541c3c0c0c80407100607045540420800d60ba1804203120000340558070008045600c1c1c081408000c80481c110802c041c1403540c2d910911716 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 779978615 1250 779977365 779977369
    0xf08160201021e030a0c140303040f02011e0c1205090307030309171b0d0804150f260a02030c040513060504050c180d06091a100b2a070b040801050f06 66
    0x2990a083d019260014046208581d100e049089030341d50081d2510050b00700420103607810b5074000d54046a50b159030141980455800240b41c082c1030720840398031000c0702080c000141800f40c03524002000c520010003030440b0240120240c400e44200642220392954913480d0141c00400c4078040c1d881403040640c03020711001c40005100d0911358515000c40803000480301401288c01d140c040840d27041c10140004240760004401e64041c040c025564942e000c85d6001014242072410200101030300c06038040b03001c0300c50130340c08400c0c2c004030003240059a999501501c1001d81c0103540180b6800303040c28500c102c0340d014640200050b1502103c040105441d403000d003c4080c4a01d0510364116085840090818607000f00310580e254040c00f40414001141c1d51446a45802d00c00c001c814854070740c0c00e0268039880082824080d02d20143d81c1ca14000801d003075000d52568081441425018090342d0082d451800c0c8802001801d0301d808043d00ca585543d0181e0182804035803e6180301d050000040c40341c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 779979865 1250 779978615 779978653
    0x4080a030c0521070f0203192603040519060605031005010806010923100302040f09060b191707030c0b0a02010b0f0604062006070201140a0213120f0816020102 70
    0x402e0480c0c1020314110b2030b17546841c1000320034541640c0c5400740124041c0300c000c0007071840048511031400d015081c100f1a0b0308203854000c042c0c0b03501681070705100b00800038600003200907010781200c43e40100845145000d201070f05e61900071301d805005201b0748001a509941010f41a03500c50420749035641e88654a040440b69600f50b0f04100035110250b9441c840b14910000d504805c1c90351000c0c078090384980200d000d40d0307103140c08401850f9a8401513400d1003402c0c400c00121050071145c0300b4030302c540f1842c0c441380d68501c1d002d1010340039210038806076100380420a91005540c00700840111503600c00d03810640750030260b1488059420142c6001ea18600040e040d0312030f1304003d103590b0519040010488402c401d0202d221001c44182600c040d00740004c0010601c00c2003168008140210010492050100040c12640605006100500315120f0000c1c0d500283c418031640c1c00c284207154204404051409040a401d0040018000482c030000c403e60040ca64000e0b021140382d50a5a4048818 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 779981115 1250 779979865 779979913
    0xa0c080d21020d06061d0405060a090b0a0302030a081e030c0f0906160b0a0606090b04170a060e1506180c0a0e151b0d08010e0c04080a030c05 62
    0x1600c0030000710140607400896894003081e0030001410b10f995200712800f102c0180d000100070032000d00011110020708100da10405209840600181c1424008588151071038000d4074041500c07498072800546a110641b4000c40d0011300301ea44580f000e040c140500c0e44201c940289410310504219110030002046901509901c03860b5450b1541603104034400307800c24030f80e01e60702c5482007248180704451203d9440e500340c05036213500c00700c0c10f00310700c00c0080300c85560120040c48101c8004111480300c04056504031002800f071f0b071180304c10408941d400c20b80d00c0e0200810251500c103039020101800600100b503040c80e1210070045445940c20800380d4418121403c001406620000d09102c4106020748450240c03070400d42e59448100b030003d001d841858440723403a2150301003000241e82101e40c0f00540c0c00500341e4040d0400c4104080e00400442c014012040d030600c1e15004100c41850482c200c5000b00104000e495505c152450002c00461500700c05458600c40c82d00f420080c542000b03c1261 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 779982365 1250 779981115 779981117
    0xf01170607020606090403090b0304030305010f050f060d02030720030409052203030b13020c010f051b07030c1e0807151b0e0a030b1317030403201c020a0c080d 70
    0x110980c1c130441003003000c1070028411401c0252092002428956900255004d14829180461198107003000c0e000005d0030341e84840d01c1034a000841c0000c54841600b16141081e1000340584d8980d1503070820354010407407904c641e03038003040c0030224080d00c9000310140040d00c58651041c025a1600114240b080d883d007141c0580004901741c1a4002034020b0740481e5096a020701242165540070301500704036084084d83d403801b03035100d01d011070b4025018840c559010001100d0060300c0c0541d03045a0700729024820300142070140c0341c10000c0500080704c002520061101c55581000c0905103010700603900940001c443c01c01050181d400c244203507000c4e03041e540c10404000111802e42000031508400300c0f044403504000d0080c03012002c1070800e03205c0340c0700d180c0060744105501000d15041c04101d00d44820712000383c50a105200001c0d500c02401c00c0803000349003480f06401351240e40755080483d0303102403c03800080c0741c030128102c58001c1082c94085004001398000786658250040c0c40d4017414034010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 779983615 1250 779982365 779982373
    0x3120f1205190f061e0314061504230921040303051c021e040509060a030b07050d1d1f0c05030f06030f0d020607110307080405010309080c0a030c12030c020d030e0f060f0117060702 79
    0x1c2c885050134bc0c0400800407400d28003009103804c01602c1a40c0e40d505032071000c60790300590301c0d01c8408c00c0302d808409003a894048860f46440e01d191001031903400b070606980a0428410070143d035640072070301602c4101c2c0100c801d203080744e0255484101507600c01e1103401c0c05548024001042840c1501c540d0003265000308026180d991107042c1110f89900402c2d040700706076034413801e8a45440e00014203181d01d4003084003c0007500c0d0046002915105410700305000241444034114842d030340002900d42088081c45070b04850703241e02c40080c0c100b60350400d072136a00d48164055050203a80c0000c1c030710700032030383e9403a8428030b1220710318416100e08c220200506030200420007002a5403203940400302d014081c45000f0304020b031505150381010800e1409030005100e40d403800d800e00000003400c551000d07043c00c4c1044841c10080d0b010b5100c000c07001030002072698803030061841c51410b028401820958806580d5286403107040c5054125080c050f94120043d1005001c40c2da80700050101e0003191950024 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 779984865 1250 779983615 779983651
    0x41a10060e0a0b0c0d02011d070509191b120903051204081611030d030b09070c14070b03090115030206040b0c0703120f1205190f061e031406 62
    0xe580d40e0101c0d5203a141c001d02500000074000541502a0100c00c81c02c502406612450700002801d444420300d1803c1d40c0c007070405840003200400a58241111000d440542c041d99514801003000442588802d0a69083c031110711a0248040001d81c18500c1c1c945400315400039142000e01201c0c011382004011800400c280c0c0400c04010f034081c2c1c4e002d489900b1a511b00181d4149889c40c421040c078084031028403030308117110319240c188045540c00800d45020002920400002483c0c040b01a0201041c400c03524072a10520040401840350014000103c91020b55a428144010746c811102c21109500c0d0a21091015034031002d401e0860b50014030707003414a41442541e00c2c0fa94403021110300207200c3c580c00003001540c2800c1c0e41002c050f4580312482d103003004007800b52208881c2801550b00c00c2c9040200000e00e1040766810114074600d078000915403500e800c0c0340c0000c20590b0014249529024010003c0081014a0205803840b13040d603e82c04041e40300c2482e955100640d40300c1c188201c00021 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 779986115 1250 779984865 779984867
    0x9043e041113140f03030a09030c060314060409020333010b030103051e210706050906040321090501091412030f040305160c0905150a121b08060708041a1006 69
    0x2280f40d080303c005140c5003180800c10006031440c3c0c403024070480820b040c0c1c5020410b000c00070040000401c0c0604003401b042c2e166036010101090010000d6200300d80c0c425686003591410089104610941d00700b94000040703002c0c400d1110002d1044402d40324484038004a20100d01c18242c074100d07070744200185081d914900c2000100401119648414410b030ba500e00c0e50020390510802d119907450806ea590b852080c10000284e910041c12647c003a4498010b010009500c07500940c0481c40c40110f0224001401e01060040c0c40452009000c660034411002c1c2032024811982010041c8101111101000c0304031f00c1115020031600c41031482510000203000c2401034004141c0c6071070b4100403a01c0a05d0b640c0c0c0341c24071940503410055826960b1410032500c0b60701950101e0507440110303282403e03540362070070824001c0b40b031083c01841200307001c4641b07001d0f07211070403031601900d038030b0302a98454a44000000d0261000320381c262411002c2684002900600912050080707842d80b0b010b510460410304 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 779987365 1250 779986115 779986139
    0x706210c0c1b150519030f06030c080312060307061e140c0615040204031e02040b0a08031c05132319020405060a0509043e041113 57
    0x40948207004142455600040007107000da1100d80402c1260000c503402c00c080c07441c454450100b12420320008200114805910341c441c41c40309001840d02140800702c05101e03a01801c040c0d44001d0500591009c041204480440030b0541040103409100e402d90315881016543c030164070a0300d01142c403141208200d515100c1400d0688840c9043c01c24010345051001e210a520400050f0b2603500701c40d052068070100d9203901080030f107080302c06504042c2192a205036107c8400001c40e020481c100c080011511140c121042c261001054540c02c3d0b42d50340c042603103030341c0301d09000311a0309088a075400100e042840362501801055100301461030181d6940c2c000116800258800e51103800020021500100800d2610b800004e80307102d00100148148000e50b10701804441c42030103181010302698648542803a800358001040e072280c5d51001000d02021750b07088203828010303500c4407000380c40901150500c461003030069600700081e036040c24815034a809245207584940700d01200c1007004c2d1441e10 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 779988615 1250 779987365 779987381
    0x7050a1203091707021f110c010201020406050d15150f08060402040f09020901180f0302030f2b0e0402030717161209050f1c120b060406121d010e070621 67
    0x2400d4100f2004080a06110b0208551b0b407540000c1c107102c00d66072003191300340212202c0302000c1c0001d505050902d10080c2103401051503d00d42103030341e01c4040f610404614001001400465030940109110410050400c000802980c000c01e0380304010a40a040600c2200e04480340171404400c61814844014040e6015484150400c0700c40e00c0d9100302a081a10408000e0000303a4040300c102c2c0c0746105160601d0440348031340400d0780218082040d07070030410b060105c50501c108920283c0304002c10b400d0340e080b044076000617000380c404803c0180c000e4000350b0f0095008a0380d541182a81d03588909032090a16a44032040001e503002130010409855400c044103661058082c1c03000c1c59043d01e9450300d4106010700024200496100f0100c0654001030340300400400c4c04000e0000c1c000c001c002c291a071280d0310461082164400004854504640c8444242c51040140140360581d00c000e00b03018000d029111682c1b401031620004140b40180000000d003070038825520240380f0b0f103c0310000203010705 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 779989865 1250 779988615 779988619
    0x15050306060915040501110319200316060b04050615341101080c070b0703020c19030e0d0c0302040c02150403050703091505030a0c110307050a120309170702 69
    0x2d004002c6266100203002500d40f442016840d101c80c9000c0c00106100c540c04004030740c41d0010088070418010704210b01e07a4450f0b10f410850240c4100c0c0400e07410311030105419078143d01011543c0060241c80d01092040e480c000c001c184100c3d0410700c00c10045a00503a5405e521000c0300e11800480e50a01020b04681d15181c0540348c1400115406581007c400400908215948042540400c400c28826004020003032030403a2092414889544481c07040640182c480205540000c404038480d80449400c0c0d07218805540541e102d1908a0003401030076a0105c002c0b620715845080c4ca03003482c2d1081d00c002900510103144181c0307503800384002482001401001c50081c100c58003c1c00c0d0071440c0c450300442c8283e4401b5620056400c0c0282005055089403854000301000c0345000c940c040300750303038021851040020f0700008100c0103840c1026088030700b2406000c049040c00c14003001040c1500341038010701d4440b0403068070314000c40840e4421000146203c5801d1034510010700b001014103078041c40 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 779991115 1250 779989865 779989867
    0xc0c05030d0c060e030307050706090602190503091c0207121104060b130b0306060306130b13060f0503070303091e0f0b3a0c02031b03041e1505030606 66
    0x11040860300344410700c400500810201119402003001c14803500c0b0041140034003850440c01c010740b0060039407046c0750b00580429100d00c07450301409030f26030407918200060160910700422080c8060001d0700110b614124501501c40740842840101002e590032031380c0e81e8041c1001609088117000400e0714003505403801089010344810340d8880d442600c0290503522016900c510350300c1c2c80009a40f1658010590340b072000e0090004c44e0f194075059130b410200450315030500c510b002200b84010401090f03900e901400b07441c00c0d4450307c000c2d90321010a64801900b025510b81d03d4800b4140c0e0365580b440020005551840100301c1c203040e107000f060700b80325030f111804103865a030140c1e22130000c1990050f104902001030200d80c107074000d2036010010346440703110342400b50f0b129461403810082400d0050303016446440c41044075200b4403c0f102889910004042c424100a4800e03a032508540111502e0014882a01c103000040d14407090488071454003141c4181050b000850311500080e1509801c180 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 779992365 1250 779991115 779991119
    0x120e012c010204030813050316060c14100504030305070f0212040e090709110901110109020d11030f010f05060909060f0a0b0d02060c0a020307090605060702040e0f2407110606010c0c 80
    0x80340200a00304100b540300c0030106d650614040605018084001750f0201c420044100003064104a0450042c0d40268406049083e003890b1181045082c04a05884c0791420741040b04160b010340c410fa0088050707076a00c090300fa203065820707a903920313088030850804803080c04108910300e810550254460300140598800079511300e11401913403c0d580d04081080d0300421350441c25640700240c8582e058805d00244a41849a00403c0018420440180400b000494444040c0d10f08002510a502180d802041404080c0220f00d00409055820318840c00c45107010a000841c0007444501984005009800c142c0b02d20811000500e400000d154001c100710703e003034005d82e031204040c02d1100d0740907000e81940c915a00c109410940c00f90400c14240e4603144e070030f0240b601c07070806841620740e069500007400790440001030300c2c1024841214034148112401c9102440103070045c1e844681c820100b900142e200c000781a141c4800b05103596055a01000009400c0c0d0f11466519003800c2c0103003c200b05140d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 779993615 1250 779992365 779992373
    0x13020402040e0405100c1d010f030204270c05031603090303060e07080a060510020d03020c03090d0c0602010606032304110907021516300c120e012c01020403 69
    0x2c58100c80540302c030740020142000070311140c051820000b05502e0025007070700c1c82c500419102c2080250060412040d1100141400e0081d0304030750180030894079003804403100c0044250344000128886c1c070802e00b0030b1080c1c4022802102624002c40314038050490007050220200c0050000060650415807141400510700e010011600d0251649583e0704556103031210328113060f190907501083c054042e120f45110510380c0401e0501070000703580340c056507891203980440e141d40502c40d0781a500c00400501d1300c0c02c00451040440480b22641c0003440450794800d030503411110514a00603e02e05840c0c01f241032240d00781030f41ca502074800d5030304004007145003004c02c81b00c0104881210243c1c2c0a490948150708044a009911030318480c0c1c280344010311140000c164000b03c200d2a0540c8602c04810340e890094103200c031485160202080050211141000703209021001c500c0700c00e1840c1c01003440215074103000388501020508004e00003d0313060020b0180c001121040d8201c3e6560a10000c8005 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 779994865 1250 779993615 779993639
    0x130605040606030e1603020a0b180907110601210227041b0b0309210f12060108070318031b02060315012d030902041e0507080903121302040204 63
    0x50a010342e030000b103e141140c04030b445c050380c0c141480001e800b006400c100503942c6180320000e80d2410b0900351f40300c154000f010303010740656210481e407200e046400c01c10815400902d0701d00b0001c1020031116180d90f150142c1c0c580c821480b032010412140d80c010f03100541405032114104100e9500074014100962101101400741178400301c0b01604001c2d40c2c040900d0244502c54044c1c1802c004c0c46185003007070b60801d0366400720307024510308040d03000c3c074075000d1108210180c1d100340204550b056661a010200140a440d040310103602050062020890280c8a8403409042100c9801c044500ca44182c40982e041d030b02c1008400c0100203400062401a1680400f07140a5000c054010f410b24941ca4000b514a5501c00b0000807440e02c64000e88001342951101c001c0c01036118103001032022181c1c0041400ba1200d03410040c50410304200507130540714107520640c41240103a4030319038030b41c88003401d5984030710517030514841181e5040d0100301c04446010321840407a10007400145000d9407100700810b0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 779996115 1250 779994865 779994869
    0x108070603021c0c11100204050612070c0515041b061b020a120c0317070b0112020607120e0301110f0901120216080c0c011e0503040c0f080313150503061306050406 72
    0xe0300d171403c8525250810400100040d107500400e5080c01e09090100303a950140b5010b405601c19103c010907038150140f0b01501020750040c1c03c0e1340703000c000c940000044840c19201100d10148032303011032a641082c11810800d54105980c0d03910141804504400341100101c0160307070203d80343e14001000031f000405c0081c4103109040c0205618a941010284003070000d030011110602088440b0009000c0e5440505640b18244500040ea1540c00480d10314004e540000381003c5c0700041200e2101c0c0c20152034201403200311700034404000c906410700c85a00038076203610590300041c06507210540c020500302544500c1c141c001030503c41c07802c418400c1e44007066025104c006000231109030b8081c050082002500c5d0a00708100c641810795803145920710081d00310b400308030010022904008504000e000182030300360f203224190f034541020540300d501a9980c0507030a0541a000604040301040804015566480765030035551400c0c1802115102c04240700840c070340d03480300460960340e14450100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 779997365 1250 779996115 779996117
    0xd0c030608060a1406151c180f0b06030f0304290a0e15040503030a050c0c100e010f031a010f17041203063c080a08090312030108070603021c0c 63
    0x90089140707041e24450300c40c05880035020320040c2d681c1589000c0380c4030494071f800c880003039018038440303815881c10300034903044058610840c0703290360001c14403c0803e05d81d40040d020703846144035074a030302081590701d601e4481840782c0e94000384010401c06115402036421080f41003032040c4494940001c62079264825070325403010030340030000d4051500f0003801e400c1d0800094000b4a1504c0e0800340041d13543d0280381f148108008000480c034118400a0020740d10381003000d4040034503081c2249000e481c1c000d081c0541c50000d03421215980d5120302c00d004250442c10000000b950000c08540112851b00c002c59403a0203000498406030781481094605e184105d0041d0309402d0042902d940c001c06481d5581d04c1129948124034030b06801e000c49115a080d080005170002c1041030403a0311020905100307a112440c540a59042c0c17400b4800a0130050a100404406550000d0f80b440310000845c0400e008090080c0e000381e10502009020b940284540d0708480200001584100b00401c00e4400303080c0c103c4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 779998615 1250 779997365 779997371
    0x9010e0618011b1e03090213140714120405070b18030601120812060f04060f03060e0d0f0825200d050a1b02030a081c110d0c030608060a 60
    0x1c07007032080d42040f40e440c850a551801010000a00360010707913000504150030114a1141d6500a074814440203902600d03000300d240c40c0961010041c07444920050f01c030800c41002450f1144200c1072400c06109010105081048410005c0640400100b04651034840c00c00c021a44c0e106103009051110080400038848180e01001d0504024060303101c000c50110000d1454000790b40c110965041e01400c00d40b520955032144002081a0500b4000d01e80141c42d200000c11840c482041c030303100740d0740a000c0030301800000b0000d10b07030380c1d010000e6000009111030309841103a511680100390403000034501c500310719100c0018000c040118000d20303000b145034004990b946a042d0041030a0380d40c00c040103480c80e19000170b000f0300b080c81000300880410100460203015080c1d01145140c40c40e40203000c4954410003450720042035445158810700701074600c981ea9207411020b001c0c0c10083c0155518241c00d095454040e07601034085010b203038041c59241c00d40491086801c00456105c8c124045c804 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 779999865 1250 779998615 779998651
    0x2030c040e04050a061a0d083a0b0603040c0605030403050705010c09051011060606070f0b010323030405010e061602040e061605040f0312021204090504140607020c0909010e06 77
    0x500c040f42c48808078003003501e0822804202690b101c5ea01c1d0900c0e0b9400004451b507418280e50b0841464000c027800e0b030f050a400c03807444400e0f45c0303070914801005c02901c00108502244042001018081220024211103117004c05020071446074016640151103402c059080042c1550b80c01c4c00d5070005904440001d41d504020230075441d003030a801d080400d807401e1204c001a13128100c6512400c00810b8140140c070002610301c1040504020b00740003582141708003299585074074002400072080c0c90102c51f43c08460208100040001c400c84044400585444e0341c5034484100f44840307030f0444414400c501080740c0c1c910707000da142c1e4020b0500e1032a020740038000a24210f900350f40403020840380ca40410005102c18080441081100340c2503a40081d460301051481d00c2e000c9181248054600c01d1050300800d0021309015130750003507030040e0b1062204605440c01400c80e1541c1e0301e811140b00006a100c102c542c0010304200080940000c070010002c10300c0f2841d243c10918000080d03a50160140c00f030181 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 780001115 1250 779999865 779999873
    0xd030e0a0f061401150c021e130203070906050f0711010c0602190f1b1407081603210203160204110705151303021002033c1501090902030c040e04050a 66
    0x10481c0501251703c00d88651210310303080100b40140d808002802031034400c5640c1c15955021051080800004082151031403a402c2c1c0040a50400c1c2c85100100d00d041c080407030828080d0081e03407032250880f4003046c24082551501d1100c00c85c44076196050040c4030244c2c0c1d011820300c3c0000c2108446610070180880b00320400280382990744028502003040403d0032070681001c050030045000d030010719036441c01017442c00e980e08040c00c1e54030030000d61240d400141c00c1040c001c50b41400316409a144000041081c0c4901c1c0600d10180c004940181c00030054542c3d808400d0346e034508e829002a10004003144c5103c150880d43c0e005040c00d540315480703502c1d04204c0702c00e14000c13290301620402d04100b248540382d4001e5a0b0b00304407550418455004400101d10f50b1070342c0c91401c2200006c0c54820a0f01c00304031048040d803480444011024880840014030b02e900c0741070142d001c8141030b541c03240c40078508000c01e00290400351140000f202c04000028840040030420b90240d03010300042c026544851078 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 780002365 1250 780001115 780001151
    0x8030402090f090d0c06020c0609070e0606030f01120609050f07051903030c03050705012702090a111603091e05030f0601050f01120e15160801080d030e0a0f06 70
    0x220b45840c281c02201040003010011030314a50f00112401c11100c112600d2800401a0040300c6400740365200369001c20031100b90004480701150b02d0084000c006440394014402039100446520501341100d00041005001c4c0000c50386440f4002c44000278098050390b603c90610781e403c0c2c0f140f4290341c4649400c1c0190300d04403c03148041103000c00e490f10300e6481c5940241040340000c201409202c408191017040c02000c1d0401c0b0b05070303076140e80f5a11461a0015158100740c2c00d10780241d00918011001480d00122031142c6406c0b007041c2055141422680e48014070543e0344454102c0c1040403045001a0800d0441035100b01094074514111000313090a0030300d8980041001e003ca0036030b10038001049180c07a100e135102015070003844c120dd91901600f8800e40178180c4c241c4121020b110340080c40302c2d8541c3c5000128003c510b611040341e404943d00004441a110a028152082e0800401500360740c0c0281c2c0301e1030800c1d148005170f814407025900c40a20030612401c0698030030780c44065600141489074 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 780003615 1250 780002365 780002371
    0x181606030b130905070306090c0f08010203070807020d08040b09100501090f2f07080c0f0d09050d0c09020a021606050a0f0309032c040f0e06010b0405062d070803040209 74
    0x441000011000d41307540b659288a48806421585c0d038102e0001030080894058026102041c108040a81c2e2007180b14002c2d482150520000b840400224140d50f00c0464509998003650b038403005142c9481d02c0301e1401003000743c410701162280c0002a00f000c2d405e4001c5074000c5c40c21500000f0185020f10760001510412002080060940401132000c50721040311900303520a030700c2d0f00c3c2e52190365910f0181c041c0e10500100d400d1a100e40070f424200f61800080d00d01074444140c2e1048a525518014094240c4200c140101150b02118043c094800b8907070141100c901c0700d10481d00f00d40c13441d00383c071008618a900f18400050000644140d1716801060445880d005841d0400c480e12498234020700301c01d0140140a0011411484a42c0d900080c602d110722400d4000c1c020400342c02e05028500040c001000b1721406409003800005c2d20728049c0d820350301250406080907103003414442202c103e040181c4007409224800aa1b01c00280502c1c101070a03501d40708600c40c03580c1c0d0800340100100302e0001 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 780004865 1250 780003615 780003649
    0x31e0603050a12140a080603100515010914060a030207081209030a0305010b0405090619150e03070f0e0601180e0a1d010e1905030f160b0a050906181606030b 69
    0x1850a802c0b81304001000c9850001d850710f002d40705a110540080e0800c1c080c0702c43d84c0c0d03107141030500340948107104444480a142007601d1740345500d603403030728a450b074841e06002c0540d120740d05001078030341c45010b0340040989922814400e8a400c0114162600800c0240c426802c0f40c0d101007980c050b011340510a19002d46a40150141064079110001d0f550640c01002640115900205100040907032210780700942182d44003030002c0444100010100c0e03294810861003445100800174006600242c020103071422505400040d50b03034038006441a080080c40d5480b4508105000a400c8200c00d03103040c051000810007240707080300308070455409042d180d48c80009925107141e26006400002c1d0b188200420f45416403400c140d542452030443c0101d000240c2c0e01580011043c06040408200c004e030070340706003019030312034842d80e812104842e07044511480540c84400440c265025030180007551196540460b40c01206082c83ca40301710b441a80250042a00c40c90140010314000f00c402c0710038801 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 780006115 1250 780004865 780004877
    0x30c09360902090a0b0904320606011803080306091003080a0c2916050c01090804210c03150b1f02010b0105090307031b1e060924031e0603050a12 64
    0x2030030f000038201b4500504010071078001d04c1d00c0340007040703045141981461030440d0400043e0302500010380e125081120307518001101018042d0610901c060000b0680f50131051040c20750381d414041c0280040c010348840d0415421450000000e044000288a01c2050b82e80300c0d406021140703400403030041c5002c1112416020081020080c0e40e1502d40075600012646500d40b5071014034005a0390761040d460101001c0d4240241a801c1c022444000c2c0200c17111103809661000703202c09084000e03d0114402404950281c42c00c00c0458900e0041507040e810032400010a0100000020003145032014400c10440104030b082801580a100759413041c40d007824410702e4100d882e00000d49030304171804010f01d05c03541f40c24800350048050384c1c0d03c4043d203c14850790020022000d50501805041d2040a000507000e03400450a06001c0c240d075184000842c044110312010004280c0107402800d140301c00c1031b0103141c1e001e1268901402032000a50007407000c0c4c910100d503420b014089108507400c020038800 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 780007365 1250 780006115 780006131
    0x2160609022106060f040204050312071209180c02031201030609121e0c1e03082e120f080d060e0901020c06040209090c130219030c09360902090a 64
    0x10010a0f840e501c500f04407a00c420344108040001c00038003d9400054142c45840c2ca040e080d600341c08003c128150045000d104102c0d84070004550000345401100c0304083ca243c49070300340001a07000088103244900549080108201000e4605202644161842c03500c5020036070901c0210b80710804400c120b0318181c81c6440c010030700f000ca0648105c0c40c003410000c4c0d5460600c284200c05074080e83d0400146401c40e252019400e004000e44400d50301410405000700c0400c07220005c85591f090f0461302a200d284640b0b1811541d0001d000b540d01c0255400305441000d403000400040041020308a18000010f11500b06169030300807090080500c440350303104205500605800003800e550140e4115403d031001e44e50b0b40c081d1800d020507040f92540050a1200414641c4080c0e0081c00141401c404003c1c07031404412070031016280305440110100300000d60a000c034900c62400303c2c00010b0b200010400c40b5110648110034a0725608100d409544d680c2c3c40348007145419070180e40c10a80c400001d1000304 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 780008615 1250 780007365 780007429
    0x3060c030b0303031909080304050604201c15092001020a2a0306140a0b06191404030f05070f1703090f040f051e091f020d0216060902 59
    0x440040d000007004000a150175071010900c1e005540b80550092849440b4140707898502d81da0501a1000c4640002c0440303000f480c91440b6084c1d11020500500961003010340ea500d00a000c54188006d48990302c0c80d0700009240c81040c051401038900c41c8841d440c01041c84000b04003c0380b00b0400503030440d0005041c07540407030481503040095000780307180c984006000c0c8290454080059100401541c1007102510b0070785910b03110f043c46849058814001220303e00108410780c41903807400b00c0c840f603071182c0e0480581c2c4a480c00c900c51044104038a0700d030580701d403508203101702d02043c210f1f86580404001d200600c0040354a40c01040581401c030301d14480c0340c440b42d0720b900427420324500038107000c0e4401800381d4803600100440f00c0502c00400241c103200602d005d150040c50341c120342d01d240d40740104405000020302c8004803001c02c01e4208a10200c0c07515080070f0b40c0b144c240101c081c2d40a011800e21f0643d00e4000c4465a41b048100181c0381c1d140d0310510058005509001038882444504c0301004 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 780009865 1250 780008615 780008617
    0x211804141f0501200a1a0a3c1d0601080d0c0302070303030b04060e040506090c0603091506030309060307170709050d0816080406020a020312040515070f05100603060c030b0303 77
    0x50795007031405220b400380346590300303182021410001d4100d03041105114012441e10281b640207100e00c507030a1182c5071442074061014460b0352a50000d44d41845078079480280b480e0400040004220000b14203c6401d0584000041d800d12103580c540e049080100504e0754104140ba402c0805814907100208481c0c4002e07442e0040d030b200140505403103a950400c56070b00e50740080301030804031030415242c0c14541403203a07940d44100c0b003030000c0744229141c4003c0c0b450107200380d92195501c81c006004510301030451480c45440070303045981520003804080141d60340c030b0001d94441d4407503039212a601c544030b8459540d491030150a1006016501c0d000b44401e0702c0c2d4000d00b00615800caa00c0694541540400c1d072614811030b08054840800400e003c00c0003a40825034980707d034006c4084408070204600c03084034521a502c5066880229030b014dd400c241c03030800240130b103180941d1039102ca00b00365031a841d0030305403c1604250440d541c0c800c24004c00200380300d422040c0030240703410081210f084001c241e90b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 780011115 1250 780009865 780009887
    0x2070512030307140c0d030c0e090402130c09050619080114032a100201020c07140d020909030f0c010903171519031703060111211804141f0501 63
    0x2001110501001c00d601800c00705c8031418a420b08607000c44140d41c0f4002c004101c2d81c0540b1000405034001424945481410140156002440004060740051f03448006200100040381403003011b00e4000354a0303a0f16030241c12841585400704800d058016001445030300160803840400c03040b130840806c07603200094152704181c0120813000c02d00e11100c0b400d1391452616154103500403500e002110250f54190090305841030280200c52240d5143c411010702141da5841c4a608901c0c1980e141c3c0144c5000c207c8207030401d60300415245043c640384140d280a41c0000d601d90502e81d16003c801c000c1550000c0700740c20303a240d4801d1405003410b00b6a10a9048903c007a0400e109a500903a002d6002160642c2d250095030b000703000c00c441e602c0c190200070054000311031041c080f64200c0c030004d0464001054913101000902000c10300d039204214215481c1d0040102c400032115001100881902d691003034880a18000c2d8400c2281e1401c40185002c0e130303101810488034500140380400040e40c00c1600303042 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 780012365 1250 780011115 780011117
    0x309040203070c051e0106121e0c0b0403081e09460e090d1b0804090f02030a050a0b030a0f1401050f070207080102030103230106030203030309030a02070512030307 72
    0x80d407a125000b0888114418040203441d60007401c021241d0840020041d207610881000244146603444411032518001d44002510402c000f00c00c0350106c41030304010004071071082e45407202c0e040d181c1c00106850f400542040700c1120000480003003500041c641d008a01800000322458513000d440452031001060049400206110f81902118101e46012100380801c515942c0802403c194141034850307498421a001018020041030500e07201150b4000781d00bc458594030b9503804c00003510303040701e1040d04040e90101004d20011440700d006014816050a1089015850382800448c41c400c07120050120a1000e150026041894a010a51424181d005111482c0510040c20800440d61680b04070b0031495181030100524031451511690054207240e0880380b405840c0c20109080344400e0101900882d050303015140034404040384094088113420010a203580c4e070342d01007855600280c4201085400100e003124050368100080741c010f0a04842c107030940e100d9100300700c0e100d03c0081c2c0300e00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 780013615 1250 780012365 780012367
    0x60602100f361202100b0901030c06110c06070308150103090c0902090114040e010815040309050d050c0301050f060411041a0c0a140c091e18102901020f03090402 71
    0x801c19030400040460043d04950310f100c1d0705008050007500c4400c201030380d40149140a0004100c0e0900b5222581a81d0b0322500441d084d50a0030001c8d07501c2c131426200c410240c412107140b1541c9448140240024900c80e4450044c94201040328040b60059015801d04051a0640d00c102045c0c5c0e06402900300c0303408800c016a0fa80c100401218500c10351542185903d800280014800c9402002c0604031600d01c019280c0b00c411002030380914040644024000400024060005240c4000d003121190f11a008998800c1c100b0000309094bd5000c0700e10055401c1004100001400c0038025000403405c101c107003502c0e29051030342400e00a0380070005003401817004540c600035010100f040341c1000c1d4200c40b940c9000011500c40c590350300c5d00a88114010110b0801040807070301c504898000da441d4505000c0c01940d5080982c01013445083c21080d10b40c801ca080000580d4600c0c440c07000d0150901003860602060780480607800050302a86504650140d46010041c42c00402a100b041c48221805 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 780014865 1250 780013615 780013691
    0xa15140a0b0a06050d020d2c1c030b0a080607230a0c15020903060412140a1e03200706060501080f0406021c020a03091a071b15060602100f 61
    0x108001c0c02801c89030390600b8500200840b450581000f50841015031388152008e400541000070b8543c4403000001925241c2c4540056499000350014009024064000910700d5a50400a8070b4524155034070b1020903444c0340e80401620100d03042d403031100e000c850b10615007020984001d01c002c1c086a00038101218104a40711080c83d950107d41145038024201d8016041c14141882c00a040325a21000310703405219000700b0320610700507185214007030348640240103903000000321900c0500e4400801c256445000650003401c1c01d00c0003041c41081040b96850b40341d40d291420803541181c01140c14021340c681040701204041030301580c000d80c0500c0140e101e61980e008200551080350491010a0021410f4241c41e035050380040c400c01e00483d08055003904001c04a61303099016105040004c00102d010703101b00c11b400d41031600c1d40344280c43e80c0400e42e02807090034080354416080500103820a89443e440c42c6040d010ba11070781c10303146408001c601d20b2159801021854801082c2018600440d4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 780016115 1250 780014865 780014887
    0x11031b0c07150518010806090a0218120d110105040503091314010e071b0302031602011709070314010203010609150c15020c0106082a030a15140a0b0a0605 68
    0x3207400501c415030301c010144980ca040580f00b5000b0b0311015800c103001d4984030355298402c0141c0c90180c17038094403901075919070141034400380d8400400740078086c2d9980104403654a6140c1c40d4203802440c070740900114550350702d00526040e003240280105a0401041c40040381020003180c031288000c0b0b584844102c1140700f20f4029040c516600c0c0201c942100000031040d9105280360300c5402c4960300c0c1c800c104452050b001140f1402680640164800e20200404001001071450b0403801410f010f11071007161900c210024404841080464000c10410000c000e031010400c0000c102c190000e500315070402600030701d0b105241c403510401100d0080c5800a40d4004c0e1142140140c0000307070480032250002d242006135129286031407442d0702e44040012007402c00b25001c810083e00c2c00c00e0740d00d00e14a08251450841080042580c1070084081c01c1300041c1c40a0241d580e1611140800b144102c1c0c00408001c000360010059440c0b05c3c144072a248c900d45d240c0144030b003602c40303074107005464580c180c1d2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 780017365 1250 780016115 780016123
    0x3011a0918010c0e010e10020601030210110f030c011112060112110a090f150203030a051806040b060a0e010518190e0309090105010302160f030e060d0506030111031b0c 74
    0x755026a51800100100303480d840b242c1d4101126017a2180a80d0609034018001000d50034200c940050700700c2c2d8018001850150850102c0c007403035140c420b0000d0703013a00950b800d1504504036141070390704c0042c0030700c5615020300803130083c5820411001c3c2098412040c168610303400810160400403584090321007500c103030340300c1c048512100300103940f14003803240040c0016120f0b02580f000002400c000043d20303104038117461003000490b4095810354494034031385c0c8040c0902801015040d03003030030988180340b07004218003407007580620108409410a0303014006048a5a000424074406110040c041c58a411882e044e1041006140700078130b95500440b4117000512000d442c0499041202d2070035121700000281c401e440c41115024007590340d0303c0040d0200c0c85491030464020752038192000c00b180510008407901400b80c01d100310313511160710000e2007680c0720080400d105a40d0728180401400c00340304081c1152000002d9034610b0815482403443c100d450384c2507036100e01c00003d4100c0507041c140 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 780018615 1250 780017365 780017401
    0x5010f0203090d1715040504051002031906051504030308070c0203160501110c0a05010c0602120703020705060708011406070c05061204031704200f130f0b03011a09 72
    0x10811500d03410b02c60380540e00d803041c40c00103400041d444616000039908008000d801000c007180904482c010309014000503110060080d1500d001324004040305001600056116500d0b446500308003070882d00c42d600480d00503030001c40c01200c1d24224212290031542c00c030b805503a0181490681c40d500c41100300c85000d4400f5009415000e0801c01e00703100c10040540005035442601d5804003180403070384080d80c0d030030100c804550001a00c00308020950161018181c4280100c402610b07011901010700084081503d4110010754000760040910809001d9150804078900e003c60040d4540900c040000340c0e0749012501c43d603c001070140400c000f00d800c140040c00e02a107901d444800c203c244500301c440486055010503140c416141c03501902042480c4202d1f0b00c88005425501500b20740400401c2003401190801c03601e03e0a01603581d109800301070440014840812002c680c41200819100184010b600070b83c1400c1000c0209a80255103510840040d14036166507680e4080300d0210610700c0f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 780019865 1250 780018615 780018641
    0x16030c08010627030308090f0f0703081b0d020c120a020d170403140a0210020d050a0503040602090d050d1b02090f060102070e040b040605070903020d12120f02040e0105040e070608040501 82
    0x162000004041d0064034051140c030021f0180e0b10708024840840b9110040d03c410366505030450041030000031441030181c00043c0e0340e410350214000340c01c201103140c0884100000c0c0980c2c08110034900520f8405820380811103050050410000290f000c250411091000280903024100f0a580d00400340ca05440003941c02c500d4403017020b0440e0b01003540343e1950b0070041c1e000b400e0040450359903500004145064903150350f610b43ca03004c0384450441d031903000a00304449503602040800305642d14262016044c0e40117901609003140341c80e0002e045200802180b40b076000200030440d0160b5101d40b42150301201035150180c0d16030f41e56004030708201c5140c0181e6540c01e00c83d030a1005210904c041d040c4694070901713003000b190300c03a00c406680d0080c161000941c4080075010840c0003903e000310340000200b25007040c0d052110740c98a0001641e42460400008940c0410100003440e10034070b4203070040400f654100310040440a41645074415400392000784100d002c00300d0b017044400d600503003081e605 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 780021115 1250 780019865 780019937
    0x100c120c05070b06030d050301031502091e01090e010b09040b0d02030604031d0a050d06151a0a090b07020612130812011401030c080105041508010603030816030c080106 74
    0x1100041c0c1103400c000307026200d050300702002480c5400c00284007010465946c4500d400c1d40e181d55181c043e404c4c540b030443c1d0401c6400f8003103030903280c940304809402003000f1391000c0090f0700c3c264001841400958009058000010300400410001e44100e81c0c8050090f9400f1441c40302860104541c40e01c0d04a00a4042c45104108010701d0740c0003c0d00c004103c4124000410701c80b0810400550340d0480c043c07568003a00b242101800203506502441e10501e200c110400b01c9541c07100c2c4c119050300c1e0850740343e0358500c0000d0301030303809039000c0e010a01402450f20300c281442c980d60041010f074041e20a099003c0070405002c940e00380700d04080301451952042e006130313581c0c01c1032a011854fc0e20a00c1500381d40c280904084040758000d000f100e103006000d40d600a5581e1a01c010000544040d1001900c0284590f02c08103c4200a010741c1000d9070007510342d99503c0c14400150b0014036a802d00010405182101201c0116404241141140c4017481d00c0c440071000b2044001c1e02c60440000038400c140 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 780022365 1250 780021115 780021131
    0x6010206071e170c03010312090602030307080a1b02060601030605090112031419031b170f0a06030f060c320307030b0d110a051c080318030a03090221100c12 69
    0x80c0c04c0c0700440c180d034416030000c06d10104899080d901408139028217130150300240b001841c0d0910440500354030080c0710b44003040c102e40e080b0340d900062414201910051304803104010319940c050007100c004000660707821a40c2e41c50041003600d41d40c80140300400b0060a00910b594400c40d00085c0c0c0c1c81c0c4004115505440403080d88090010f003a0307040034220306051b1000010b01c16005003110000c401c1c501c10503030010f44d640841d070001001c0040602c4a000d54075400400424010181e52a5440c402c3c00005102c1d030f8014000390801e250007c00282005041500c0c020380507100026080044d103000d4115126200d01005802806111001d03030b40294a0f101540f060100c9104c01241c0400c05651680c801521001800803228008242305809072005e086a00007444841c01140d001221000440903038140f010201d007154004070140c0002612900300700d0652070920300d46d0420318500041c45802030b92030b410171615004984404650180c5d0b40305e1525643e40129101303a5180f90711007080010398 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 780023615 1250 780022365 780022381
    0xd110f0a110406150e100e03060411010318080408060a02030105180901090803040f060515010e060f130b030910140703050702070b0307111b031f06030f1a06010206071e17 75
    0x144286145d0302c1600b407502013104c00c1c0c4c014102000040c8000d8050805035072180c41d45007409100420480c10595550000c0340c03151103292420012901c40c0b800300c3d0b6160300c0d00303185516006000c1c00d4540c0680c8108010480f0395504040e40c5080072200d09940d070507076127100000c0c1c0140514440034120160001c01c00c420018175100d240410340c0b0070001000280c4422454070080480c40c054030b40410401000d4030b4151600d03002a0184014401d001845c101c049400300c60749007607903400700010b00c1c0007000748212000c083c01039174440034440d20300b0800c600d08c02000b00410700000d00080300740b66440f00400c1c50907100340400c2029182c1d172602540e6a01309080c008044074410706040d400e80c000d138040501c100400980454026100400804220313103003898030350b000c405503268250a5a0340340e000000048452031020640c50241c00c1c040480001044404807000d4011300640c1190402800c2009182e00550403807000e1a002041440c1060461019111050701806040c20001d000003000111 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 780024865 1250 780023615 780023627
    0xd0507030903030e0f07090e19060204061202070809060702010203070f050606100212040b031003051b15031311030321070e0105040f06030213170d110f0a11040615 72
    0x1034843da070108100b01d2125a030b1034444622040141c040d41054408008880b0140c000c1000d0200c208181e5012a2080c4900d80d0b020043d1b84086810b1600403504010450b04080e501e50380d5103218906614103141540c917440c6a101e01c482d5907104e107101045035020769108200b42ca008607800700000064200c2c03424820307610703d411144a486031441e50348006038079101080d80d19106400c00c151600301030400405c0750b09900003c1c6a00418a656507002000c60000c10030f4803140100e900b02c15007050a00410300540d080102c1c91032006400400c10701100140e2480d400e0003158010485042c1d2000742e0002900350311409181d0190603ca4003002c25601c56502d1805019400540390107071040342d10360041d0340c1c5004600c20803d0585020104010300742c080d40083c40c07400b42c090040d00c050f988680088007824031083c1001c10a17407001010090701034202c100200000740c4d203001440c0500440742c40e02d664181070030b0010300f10700c140d8088241d5a151500007001800c0070b004006400c0414210003046 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 780026115 1250 780024865 780024881
    0xe0610030e0307150501050f0f0618150315270403051b0102030f1e011e09021c060f0b0d020f09030f0609010c0e01410705010b09090c13020d050703 65
    0x102c00d2a045c000655464840034442201402603c00a40401541c041181d5504010f040070f40e024088414150165a12550701c081c034210040d9503526070401500d0060b001000070750703090013071002d80e80420b043d80065098680c89804100c030010320359682e01d0103da05000303043c59105055100c0200c2510000107401852040e9100180e40701c19a071140f240307007003040d0010004000c0c001c444d401031204040040328400c01c01c2903400c00c0e8001941d2849070f18102c6c0d001c42c82c0380740c02c5c0910b4400c11040c8034150040c040200100788c02e401c01182841030b90b80481c864000f60142c07d40e0b000580780d150b04103407000d49216143c001c003515255501d680d4150748032401101e0f5800340b5460300d0485680700d40a405100400c041c1a076a800540040d01c10700710b84aa050391440d88044400001c80f03068514003101e10b15444200c0300300c551038480c0c600d030482c01d41741000e4100384205501020005020800244044095022100c0026044000594000030b1080d50309040048d4140b03030400801035003507002611 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 780027365 1250 780026115 780026153
    0xe100209031501030812040807050a080c1e073501020c190b04110f040603032021031801020d06050f0301020304031e020f012c070e0610030e0307 64
    0x711020010302c28940c401d400d000007001c4070403d2004081049210030340f142d009124800180c5041b8494507880e18100a03030900320764001c00050780320700f8504144034641100e461604151280c0030a5204951039120a01800905801c60100710f803800d40c10158801c009420444c99401300010300c04520f02039440180701c410b051040c4918203909074480b951600000340c0000b6420700b02d449543e1a50f079a5048900c00703540c0f00070500c100c40c4c010740d1a4070922006600c00d44503100c500b2042030005c4461114511300d100c56401040192920ba0051180c58500040800c0c880e5070341c1c1d03920203410401c1c140906048905610118a0014070940c0c0d80c06001510401c5912007031510846c0101800d074030046030010001045c0409000400700c12071a1396622840500665031030062480c100f80c2100e02080e2012011007240480010b8004031030f51030b2108540d56000752104500306500900ca4078030103455a40a43d04001004280c90301ca44c2c0440c10002e403640680e44c5d0f801c000d003003c070440000954020 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 780028615 1250 780027365 780027373
    0x41e0e151e010b0406140306150c0609011b0801090e030f0406030b09150d0b100b13050f030703050d05090102210711060c07290a1206050d03050301030204050a0e10020903 75
    0x30460340d0351030f01900c04550b05640c4910030500f1080035041d25030405807049800103440c034030b403520f4451714402a20315043d40c1c2002304082e24000000d5829030300503690120125003454a80308066510000e030368150340000070301140d03500d100b00d034152961003541c1c92030701e0001020a0126999078150850410f0010468500e4210b80ba642c1040703020140b5200c00c60792003009100c1071800031366034000c001c1d482550340b40015074655840c04032a01d2640500c00d501c0441c1150a0180001c0c82d00e045015442c02081e0000c1c030206056a9403196100568425507052050202c0c0d10348650784200040c0780302c07800015a107401042d0410703109080e034001a408a5040f40701d0341c481c0001e400c01c4019581c400d001c6c0313402000e94914018030400704041000c590702e40c8038140841c0d00b264680c0b400092049070311555501007060100982501115200c0e00104c0c400c112500001000c40d40c408280da066036011140001d00d0b4803403845c003100030020000c03001c405004090324040640c0c1c595016005014055049d1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 780029865 1250 780028615 780028619
    0xc03070308091507030f06050a0803040504060905090a0807050a1e05100911100306050301020304030c031b05060a020f0705160801060e0105090c093c041e0e151e01 72
    0x40d101c44483c01e0000104100c0400070310118400e410070f0861131501c44000400684034000328012070144d8101489690000038100203509103440b44400820101c80104524200070704403030740f107024407200a0602c000204d69041841828400c48840319481411010010522445e0040b40c0a4205d0280c60174003501a621514200c14040d406800b90f004200008601e4068100505c0d40c0255141c1010199150300100e1140c500744015800346020b9120155030b640f5500d401440114440d494a4071622003141c01c070000380d400154250840c0040c60b0150300c1c0c0022000420843c060f0541c00380c00392280c28020391003009030a2200050b01d860b44c000b40045d41c2c50340d002000aa0f1b00380314854011900000107940300e01e11902500702188000d00105001101d00402c0c02565a400210a0303821003143c105605c0c00c0f4041040c0f00c0c0c0d24815941404000c004a00a8509034549a0b1b4200003d0322141e0742c800604080c40903020403c1c07412482882400c0800105680140c02e5400e141c101c40d0b01000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 780031115 1250 780029865 780029881
    0x501031b0803090108180a06111b070f060c020d060c0e13020405031b030f03040602010605030712030815151c0c080c0403061a0a1410140d1d01020c03070308 69
    0x2103c072020f8040e1601e104035101c1040c030b0f1039100b0005810003c4c81c01060301c50310001c1c096024040d00c82009070f9209441d036040111486541442d007000e505c442d8001082048208414a0307140100c0741e00c1c1c2030651078102c40e80042100951400c1d001044545042446502c0700d42091454240d06400d4413010300120300041d02d081288500c1c064079078183e00160072101e00e8210807980f0790b0100300c042c085c1c50301040c0119040e45150421f03042800507035140c5034107210303a04040140300010b204201c0f01903404000c42d20080e1010f14007410582240d600c2252003038403a100d0190710005e8040000c495650352640010140840351000f00e6050490b0502e02812032841c8191800c0c3e0050401c04000c03850140345035211002030800c146148003100d00701c1031140e416500d0300c01c101d00070074005028124a2440800300645410184200d1b03091010364240307040c1e0400540d050795959810114005044410b5013030343e00703014400b00c844410781e40c0001054140550048080c0c1030ac18440d4940402c0d544510710 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 780032365 1250 780031115 780031117
    0x16150b060306030309060702030a0c03030f0e01020a110f01210603061a0306010b1b120d0e0607050a030e0309030a0812132001180b0a140403080a051c0501031b0803 72
    0x560b0381d403640c4244003610320f078940034004006040c4010304403035041c003060782d402d00315055981c070540100d0100035a6920094004822002074442440508090300c202c1d541c01c4484250300c007400e13018024034551030180340d014820f43c0b0340b0300c501c081c030412885e98000c1c480c502070015808105c6070281400d0315100340782000388020100c454020064044c680c02c01c2c00c41c003411341203e1001c46100c8100440052049002c0c0125002d07800082d4807190fa55981404c00c409550343c0442c841e01c19031010041007000c542c041c0948000c04980c2c0750110307010500640403071860081c0110b05a140c02110401c80070801d5800007002846103044a4484d02e517102d03c000e20b030000032940c001d85490f883c0312400030410580a5081440d10f01410280c20305841180d40200f0242250000303c000c020008000e0651604000d1103000d02da014500c19103843d040d59504100b80c02811980014081c021a600d00358003c0d10700302c502100c2c03040c0405c010960396400d20300007541c540703030325a01c00d010006008a140d80002c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 780033615 1250 780032365 780032371
    0x10f020c06010509190501181109150a1106100302100503040b0103030302091305090a0506090f03071709060a030b13141302041803090e07051303031416150b0603 71
    0x100c041e0489038038090922040890040c466a00140a6210b0001001a510400d40a04001e242240d81041c85c04c10640494103400410201c004d801e0051103407603690203214404283d014881c9076140d211030002600d00d005034590b80501c42c01103008026070255170f0342c020300881303000f11011000c0003000701f81500c0f80d20058034060f00e081c00310300040c008a03009800915044601802d040014800341440c030040710010b91342d07841c9a40003800040c06101e0104100ca0700f1217680f1019103410540c0362200c5590744200c070001851642a43c5042c100240f1841c1940c1d16080007908544c1e88050f9080000c001b40604d000480c4070f44162410781c4002402e5219070f100790a80c2d205c040c0d60313a80710700b44080c51020b450036040340c0c440d858215003502035481e039249403840d61207529281c04040c02c040440c005803a00070034000c20400180040019001804034100440c2d8050802c030700252441580c80c070542c401d0781c0d9030180b14031100b8110743c1080300d50304100143c110b0141c0300700640300701081081590700c026 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 780034865 1250 780033615 780033637
    0x50c0d0c021c1a1f03060b0a14010903020103050c070c080d1805060403060e100204120c05271005150a030e0601240c0605010b070506090a051009030e090108060603010f02 75
    0x901840f103000744075025029040301c1e58410490310041d903111141080300150b0012110503440300103801d82820f04001c40c00c05040b215030140d0f80401c00da00024002342c0b09210203410980ca41c800b10b0540e03500c4208413282103402c6030420110341e4440324125510340504442a000424071a803c60f40555540c403944140c4200926862800d17286072601c80c098080303000448100e000701e9030610341840c06440100014035440f00340700c1c1398855a0401023034200c1c0300d0740040d00611403140c40d440c41588110300300b040b00c8040304415400341ca40140845845e00590421134002fa08041c2c2009400041006040811442c4d03a0600141443c0d02807640c0b544002c0c481c0310b8014454900d05003000c000700502501d41101850000b01030381d0315840b64010780780c0070380c020180a4000144c400170700409102c00c95000d40c0020082482b091165241581e502c80052164503c1c0e83e40c088035800c05120368040c041c1584002d04600c91540c4034400c4944510041d603089210b50f28040159042c501e950082c4d0f20701c0104 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 780035971 1106 780034865 780034883
    0x608070c02180f01051e060a18031212050a150501031e0914070509040c030204021e0d050906010f18020f0403050307050304031502041410050c0d0c021c 67
    0x141c0c102015200125407204440f5101d8500322040100d040c279110140805504140450791000d8000500c1c009aa4442c58035a650000c4c41c560341100e0650200055200c00d030035202111940d502d40d000020358040d0411440d03001e0b51015a008440e0008028416032100300002100d0011400315910b56040005142c0c001e400c2100300003804042e18228568100741d244d0902ca010184070091003a50001200424120502601b1071107168084500e40c54280c000f029602808044440032018400d0f8000020419101e103640021036840404203105000d03000558400303903101d46003814071024100300c00000510100f004101060003400550b403103c0c2503140240714100080000014240140003d000c1014081c050320b200340d1040b10000046a0001800e40d0b01d800f1b40c8044100c1801400b02005c1c40300d40001c15174a4541c802c03910030403c10405103041280041e9840054501c2c03103 = true := by decide +kernel

theorem cover : BRFrame.Cov 779856115 780035971 := by
  have h0 := BRFrame.cov_init 779856115
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779856115 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 779856115 ≤ n) (h2 : n < 780035971) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
