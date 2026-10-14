-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2996
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:21:39.936796+00:00
-- url     : https://prove2.me/submissions/904fb38d-b7f2-460e-8566-4be1eb2612c6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 538669064 ≤ n < 538848920 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 538670314 1250 538669064 538669081
    0x5040b060f0a1403010e06270f0907050a09060e15011b050c09070507021201181104091704030c0b030403050a08071103030702070612051e2a031608 65
    0x101d800800c0d01000e542e6540080b0030003990384049142c00440101400b000001320313240001038040c46840200c9481c1c0060361045094010303000c03540083d942090600001980488800c1a081c0e0031821100456031390760b5980000803c0060913030802e0040c943c80340c0741007010320480e03200e82c1c1c5c10061040d522018100b05100083c02c1140415600340910704403580c180a05c542030040200024018040b0745032807428140c054030070b6000c1c031070807405444042c8041a0010341885620340b40c1501c4800080e4002c41da03112608100d03000c101c1300d43d00c82e5032408004001040000140d455101045410f9110780c036600388120340185030741c070201c1c0206040007040000395002040781c40c159181e0a215206407150003040f03544c501d403c9580403e0703101c000709100101740c001480354111041030b0b8400d011308078044444416503030300340c032009072480f480e0a0101100d503406100e603900001042c0080c01d500303404c0e0300050805108030307802c1065040000620454500d2031050303503100282401c1114090805091 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 538671564 1250 538670314 538670317
    0x417010b010f050f1e090108361006080618070311040f0e0d050309010e0f030904020a020f0613150b0f060903030d02190306050118060819150e0105040b06 68
    0x48881085000202588600c400d6000d46850508917210304095100c0c840c0010303020383c0082122030105407680000381490382c030044174480c030000e824903004294002c02d0101d2646010107600386040d000b9940840f805100600c2200010304155004101c681845d070f00d10b1a030741c280b000c040c40044d04644800d10200d00001d0080301564026240042c0d00b0402c3c1c4d03840d5004119038101d08900c0c0c02644001210258854040d501558494001b00040449503061541d00e4007910394000c880d4105112029142c030307061b4050310b09c480e114015981c4240c0d21901603818030104940e0306000b01111241c031024400d07426107403040414003c000f080780484031400601049041d0300500e21418000a22101d00e031414001e03140380b584c003101c00b03644401c4441075000141180d02e149030002850604002035940c8603440c3d005030140c030142d0040600d800c3c114116008080100505249400d074540034400340e0790f80c070414031100441b603c080c0c0c12600b482d2208010f140c0690000744101e09000c9529010740e034500 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 538672814 1250 538671564 538671587
    0x140901060f0e010c0f05010902090c041202040209010306080f0609100c1b0206090607080306040507051e070302070b030a0c39020d0b090607030c0f1e020a02060409020417010b01 78
    0x10100b007500a1800100d92401e02d0350f4005000c55402c00300c9000b0050305410201c240761084407210129034a50003419203a0049100c0c0c0784044001049010142c1405d50041004201c10701d0040b0354640c591191900d04400c003c2015280e510000c20402d00e06400e002440880b1003052003030ac6040380c0490010003a072010303200425249680765280f0210340c0c519044072a01c141c040c2605481d20781904104910750003c4844502450038600001c0d9110701c030302e003291203100000745100c07440341789a019100580c0000c48110158480c03840049407409543c0080d620078100c0d51000704a10350f0702000100000d42072448500c0d405425810a02a19501a014481660310b001d100d04007103114000a80e9071500c8500141400c0921005d10596820200d0424400c40150710280201d124000003142e00b810416406c0000500c0a0105c200da03c00c0500c6e54840e00020b8030403515200e5044d00040c0d603e170310552000c01c48641c0010100140e01c01040d075442410301c00b60080100d489070000281c122007064 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 538674064 1250 538672814 538672817
    0x50706020105092b200a031d0108010e04080702090c0d0b040c02030d022107021c090605090f121c031503170a1b060f110c1e010e01090c140901060f 65
    0x84e042003850b0741c4035101c0820f04545140a5001e500924080c1030784035000380d10103800240328901590403c5c81d48600d501c05048040c0c2d110103241e031030241d40031110800604115650181041041d008d641d80241703060181094603c0103541d0f04208122800704d81e441148030b4003542c18825403081ca50703000b109444e1503c0d151400940c1e110b500d4030450440c91081e00e40f040e0840c07008400c0c04603d80d80028013210f104901c0381621200d0880100540c1c1340040b5105100c0099003c1000a03640c2c10301041d800d03035517000603102651003001c6400981c10300500b04800007130441400c50303d41c9400c0c1d05010b600d601100941500c04094195200c54081d00d4050050144603140000c039201418030842c074070f030701050b021f10200d01908040c0c43e00102500c0d1050400e00d02c0f81c2002030b48001c01d0407042c211040d100c07808009111020540808240c2c003089240c000103d035503141c0892000180078010126aa0701c642915112103003489060a050801c1020150040503110300502805400001c91f0000480a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 538675314 1250 538674064 538674133
    0xf05030a0b0106110102070f0b060117330d06050a0b0109030f02060a020a2301050a0c0509130b0423070206270a060c051c0b01210f05010305070602010509 68
    0x113201c0903070180c80740300300040180c00c2481e050010700020355002c0e4068103003681e450014114240740d07a40401000c0d076401441c015a44d1182903d408941c00c0815004e076150049800022480001907101da40302c502642c240f81c6031020021243c4e403030300c100d5000c40d070b003406c20003080e81c25038a410381d01c4a10040e0090160f9400030740114030a000704140c081581d84000020145260a841115400001c0420542940c00d040101d4414401c600032401071607100d0740e07940d081c40d1001e81008142452200401e0b0210394a4054460940300ea0141032071000c5d2200c03400c0803207024a4070b4281c42c00401000901190000014004802c4c103025091100158800a0001030044074070ba01d802d0401d940f6000786441c2c506464800354a41040207445d0324051925102801540007504c50b00741d44801c000d0364001400507403003040ca004425041c02c8052400c480010303e100040c6221401c03520300385c105a030903a00604040150030b0b82409491390000450024001c1861030803004002100c140e5913841903640e9 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 538676564 1250 538675314 538675337
    0xf0603090d26010312080a090206030a0c090906080312010801090807080d0e03031003060b010207030506160509030d0206040b011a090409140105040c0515030907121b09060f05030a0b0106 82
    0x300e034602c24501d40348090b5881e50392843c0c005e0071224511012008a80c00500007000a6440c1c85241d40700c5402070822480c1d560366000b13402c010215081035005110303c0a8005c90300c4191071241001800c0751200a5540d291243d40504007410140d000c0017241e0305041c64000050510401d0310507140c0d101070340326140d603400b518071009440c0340c031f03c05070191101108009050303480e107204500b200d008040421003c10041c00498a605103808042e103d5407200d004100020107182e87c90001703038414501b1a00700380030303080040c0c00d101030141c0401c0180d0000041c0024045000400303801410008403895010000b40c00c56a103901848501c03510490b40c0f10745480600100400b920307402d0b4a007000822040c0790030b180c80d0542c0c0585000d59030003900c034480380c400780c0a020002c0b28010780316074000b0201c1520b04046505c804071401c0c8100d0b944032110f03441e403256441041d45040a054804004180c1e2030610108115072080395101078072036440380828801041500d148203065561500d0304880440 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 538677814 1250 538676564 538676597
    0x90a050415090923240603190f03090f0303090303052109071415031b0405030a0506160516200a0905060312070215070c09050c090f0603090d 62
    0x10302980541d0b102824a081c000c200b12240108084411101502a00075001a05515607989280a42a24031038140c803401d55860250803409500c102d008040362401100242030030f50340304c6460360803104d600d00c2c00c1d40302c000c064000700d51602810032545010303865403841d140106031110501c00542401000100700c249206440166450b02180c043c0142c943e041407c0c40c03581d00c490603c0b46800d8441140082c1c0000e241c042c803145c4000392220581415511064290320310408050f1122126580400000072152014802002a14007503009800c5514108903440e41c0c034070341e02d0b40b075000b008020001900c0a0010000a012080d00450001c500340079030300c0225050959207444940c002c0000000243d1026240c0040d842900190b0aa0308035006c99000d1007614050307880003e501c00f07040e80b030501d4201101c10261100c28001d403001c100c261342d100c150408442c0309a4090142400000b040c00351414490000c80b441003050b655280f031841d040110030b0b11080b03d080f5590403c4546000c40c40c3c0322 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 538679064 1250 538677814 538677851
    0x130b0607080c070f12171614030415050c3903100f061e08070b0c1603060e0f1b04020904090c0801050612011103061512010305061803090a0504 63
    0xc169030405030139010f49030b88512440c0319030508101c13810707048002050211690030b002d803864001000c500140c52141581c40701c0481c2c5400311351801c98482403100007034400444031807041c50391003a101c0c559034114942025040021380c803000c595090050507040c8010700d00100d00c1c05902c2081d0003002d0303c1440000041e0411941e4881625228100b80d4031012440740c070342c8403404441c140720400f5001d01c01c118400481c11011b10850005070004c1c1b02c03c01001308144010314040700d01c107041d26031044c200010080c5603036181d00305030345040e940c40100041d040b0400801d9440203c4200614074030b61036140b98503003008804e01d424047c503004140c1031902e0b1030b613411983c420790f0f10100301e40090b61a46109402004120303075592150b40000100807401c5018030680501c8030078443d41e203195031b03a500d05010750041400003100300e0400401c41400388902c4015940c0c040c501c11701c054035083c101112418040d0206d1000381c0c503550820081400c256843d502500304132042170b01c010800140c1e081400d60300 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 538680314 1250 538679064 538679069
    0x70201032310170709020741010902031018020a0b19140313020d06050f01140604060e15041e051005040e06090901020d020703030b130b0607080c07 65
    0x84400e00d28501641d0006030380d00d100d180b18401d00041603584401d5405040b003400d02940998003c0d140078490561190010800c0d1400b03030840c50300304018200001c550701c800c804031b0703000e1042465100030140b1240909428070103088000340700c101d0a64001030703141c40b204100c070347c400b5170340300e00381a0b0046052404611490700142000c0703129070781c4c50903c850b50b4000d040d0200d8803a880907e44140c0c500605220790006030403180e60f404e43d9100d511500032951050300030384e40050300c015245d0000d421030103100c0c451029240406901d5142114041d2030300349007d12039100e079138103101c1400800c0e40303c080c00c843c03450200d680040d032b1075092005885500ca1034110403120146104191003515407a500c440c101e0b00240c41b21000648885000c5450340141d000f980c0c08201410b006c80d00310b01c0c012801e01c1c1c00c9440c40b000140303041c00c2009484100c1e84032a000310003280d105d400c41c194602e0001e12180b4201c0503001c4c2480492030000026050340314100000f428140007099032041c003041000301d04007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 538681564 1250 538680314 538680341
    0x8012115090b01210b0106030b030a060606020a050606060c0a02060d09050d08070f0c0c050d03030f050a0f0609020310030b0705040905010f090e07050108150102010b030307030c0b07030b0d0807020103 88
    0x400c01c2070700b800c69410009008440d40324030740b81142c1028015005860014981049035000c085e401c0074001c030301511050031707840c0d414410402c0c004041f03070b11480703584000e148940042050135454a0100d0034820010909407042c0414007100000d840301080c0c1d0210107a0480d40f02d0b58684d1001004001006c603448003812621071518440c007015005440d040c0a650070b9140c041442000d520b00b01d80d0350300c1c82500240000b055807001c04c2281031441032a0140703442030502181c142c01d007845c108200e030750446182000a0315060300e41172103080c42c801c980260590040540c55440e020489034055a998440101404c8105000404540c030401c1681d01400c0f882500744003650303440c00040d080c0c401d14098101c01d203251600300c035007000001030a5411120103840b181f020f0303550b5884492031810701440c083d0555407036a01e01c0d102513034140014803821b403080d2104040c0504604190461800c020440800d0500c0c3c00c80f625003076550811078800442d8020385140c0d032a031141c401240900138900c017102 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 538682814 1250 538681564 538681571
    0x30c040f09080f0a091502030d05060105160b2e0e070c0605040807021c20060c0708010f0c080114040f0207021809061005060d0c02010617030702030d08012115 70
    0x1a032110143c0014010440c10382d81e1080e985031181404174420000401020250b4010014501c0c0180d01da00015400601414214100f440541e200f001c0503005c00004ca40000c0101e04024009814182c920307917180031406101c2c940402c110000c2c45034942e82c0030721400280c5400005020521480300803d165038442000d1005040c0741c904910b03640c121003000c0384030b000202c01c852048900d64000010a98000e02d9004002c1214500e900e10605c007030341819008a020081c9440350001000b1802c002c205007000010341185101c020070403601c025220324108901c4000421a10b180910b035031266600440e0001001a0309000b94002032051280081d0000c2085a0785503160180808244c495010344042d200e6666401c1c01b52000b1984c140911988100280f00f407141d0910750364040508404240000107802e619004503502084005041407801d6000040680440c2014480c44002e1030813404e18003c41c8d4141000703606403c030f034410104100c80c0e0800451044c81504c0c01e010303001d448070440c02c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 538684064 1250 538682814 538682827
    0x60f0c06010e151810270c2d050c1b0a09110f030c1e03040318080d0509040204030b1003120e010519030906020406050403060506030604021f03091502040305011406030c040f0908 78
    0x1451b581c10780c50403035110b0501c3d086421304942c0c0181074034121344c68070090b5603080640e4041c170481c100307002078250010040240400c0c044100c0400c2003043c031403000f4080303009004011041203238800e81c43d0003407a040c80c20020110302e40301a007811355a1000e4110380d81c80c3c8a40d60600540c81a019000712002e02000b480b40c0c000c0d00b4010003000b140240d000c0d035250894850380381050820782c422441509200d6010500000c40700e4415070103458911070050002d464103940e511070007811403007036944040807400b111003081041810305403144054640e04162850701005d00020705a4050419030a0b140c00030340c108041054480e60001d41c240368482009c648440c2c0340c4000070308035041404201c03000c074900000b1401c40e1400284140c1710b00d60052a0a071007e2400071102400d07083d80320305c0018961114101710001e107003007400085081101c500140c50f05d10314286942034400c18515100c00054020510455440124100d140320405507404106544903a20000042003543c50240120b0300200d1030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 538685314 1250 538684064 538684109
    0x27030804031b170d1503171621080a0501030b01030206031e1f0815040303180501050103030e090609090706050a020708030301090e0601051005030114060f0c06010e151810 75
    0x50a03260441030001c20452a51540b003070114140346c000944010f200e18000203810025100800d8100c1000384001d42020440d0340c0e180b001014140056401000e07081900540343e80a0000c50f4810015913041c002d55242d07486100d4040010700000e8054000040000c00903107030030200c90440c0010070030000546c40c0608441890b0f804054a00c0d14180440d040042c12000c0054001c419912041c2e005249071181c1e602030b402030185144034026000000f4503d80802e2081c030a180c000d40c02a1a404900e0364020104000c2800040030303140703d9401c0100f800054040000c03904c081d01e41e42d09100e90346c0d14100c13005a01c6c051007a885500140700001c000303c0d40d04200d401c0382402e40c1c0c1d4841140c519076258010060107803078141000b000140c042c401001403003406484403001440c0034040320f2500a125150042c564000d00056402d0390100004003c0722503000d41265010f14642078032101c44c007400c0000f5010441c1e1200d40d103a03444d100030100307144412103840880140003071004d00c084d48134100780 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 538686564 1250 538685314 538685317
    0x60108061e0630010902011107031106090a12051b0616060b042d0e0d020607180e27241803220e0112081e0d27030804031b17 55
    0xc101c0c002245000f0151542100061382d0058032f600134041400c802040301800142c0d003103010416400743d1014000036984640340c0b032684481e4010400307815400e10480d146a10400010391407402040100f020107611803055901000d010361268000c1144a000e50004024213040e107a88c1c001c0c01031311149901e4006105d00d400d01606540c0c00140036180b511640c1c01c1d20740f0400c040c51000340e000710000895192050304020100d21000001104030340c0c43d1b13088010701c0326045600e145078040300300790408801c1d000f1941c2c1c1c0c0d4901803040103005019001480c9010401c000600c8002001c441011924070841c0000c0141c1c0034040380d04581e01c1c0c480400c128407540780300100c40031308149164404500d246002c546641aa080d048140880000700d940740401540554000c07140200d41d4258060440c0c2c90000500c6c1d2040702ca17001142d1b12003075a1041680f021080c1c0301c8000d803130303039840300c0c1c00000c2c0c105240a9001e90141440d64550800c811405c00710010120010041c540380881030100801d00c1d070 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 538687814 1250 538686564 538686581
    0x309030e040f0f050919021002010f1a1c020604050d0213020a2106030b06010f03140408041d010e0f09150903030109110723010617060108061e063001 66
    0x80f814030094035980c0c2040d0311603122821045905040051410160800601282c44510360b4030000074105031805a07401201c00b20070f1780c942c400510b902201c8061500d0b0b001c07212910b00b002c200380300c1c4014541c000351140c41a03118550045844030307485003d660704d046100003003820214041d552590f004034020114841e15562084450302844003006458175885814140c2c0e80c8040b07074109a443d90740054800d0713084103550008140d1114401d500c00651010304034012840343c074015803154181025550071905c0880042c61a1a0220040241001c1c02c3c1c0c078203420415070b082080842d150790030060300b842420512070a01f00801c4041c01004030000009504030b0ba9008400c100215203800003540328400c0c5803000c1c003002c60402c6600036030b000c3c64191841640c1614000110a136440d4980302c800e040003d0002c50030713000341d4010400158280102a804640ba06c04810ba400110ba1420003610026150070b00034140c0010031044980b902031110f00310402c540c1d103c49202481d2454902030300c58803 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 538689064 1250 538687814 538687841
    0xf010207062414040b120d0801080601092901110a0305030405061302030d0e1c1506170a1203020f0403080c1b060409150302090f1605190309030e040f 66
    0x50b4404805035000d003180100b901c4403403440703100300008841000013621541851a50100881c01c00c4584014200450a0103220a407078003141c17580b400d101c1608000e816401414050304190301c0e030707045a40c11601c1000c0c415207586119060307112040105c03103100703000011003a00d10680207040c0034160420b0146200303610603011205582c0d03407881c80040100014000035095480300078004016070040480e84c183c802e000d00b05403000b01c090680c194541034141400d031580c0c2403100d8031070b240c04198010703400504102e444612218032544507540d518012001c018040d4004401d04090a07880782c0c0490700140000e410968441c0e40340d04201e80103600498540d4010320035003940003040510310060400c08800201400c1c1001c5ca40000f5501070030524125202401d804c40000c40143d840701d1015010303000d10080c00f983ca02c0c040604524a2034041179800620005100042c030300c2e210001214980c0026140105050025150030b0300c1d002e8803400f680c2d90150511000c031501d071131164046150301422 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 538690314 1250 538689064 538689101
    0x708040c081b041d0d0c0317040c03081b010609020a3902010207030206030a090c08030c0721060f0c020712080f030903160308010e060603270f01020706 67
    0x86090082d5184901d80070045400185010705a20b407906a001049001c00455200444810103492a0406040140d48070101d8448034902042c1580010203000000320300010344d0803820b250300c03a490040b906110081c8201d10001c1c07510b2040300703126558104c4451b0304000b4000703a80c4840f1007102a411000380f100005204820302e2500b0425034640b031032030b126091341050503004c070126540c5064680c40b809906500c00ca140020040c2c40b0300c0e008500c070306210080056941c3d0315142c0146520501d502026056100b400191007441c000309260040b18003503180e14400e91007007107c8a00c440d409040203040c441c940307540600704011a40285170850314070344c00c0e9800940c503031001d42894100c45030050f014410601101c1010300c0210000c680100c0c01604680c284a41001c2001d600c00503a141100010512001041100c00b508031041d0010001c030340307007821807600f9008007d003a080c5035044845000701c000750b100c50090621801005000e0702c0c00075035964056082201c0030b8840313010200102c862 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 538691564 1250 538690314 538690319
    0x1303030206041203050f041b0b0403060b03010c140a0c140d080a110c150a1401030f060612020303030744011401080c0a0e06070f12110c1201140708040c 67
    0x10902c0317490b00c150486468010991260b49600c40060f444c140780c2c08080440d8080418142040406000114070614010600c01c07904d009240c00d48045000c0401409610b41a10180f4500202907039110186854222001c081c241844803000c1c80311007201d00a4047c405402a0165000b91302501c2022540001d12401a011201003154451070b0314240461304a20242c0152459100025030064503018010550500a00b401c4844000070ba1003101c003034210710b40c900108822400349100506050501c0c002d03c20164001c00c0c0c03280b000415100070000e4010000e954502c070740105070501c2103040e03d8203c0d503c000810f0090900740d200c0c088014000b1410000450f444801d0710024000c406075540b90700c41d113941c4061034298000d69402828800c64081e500c00036210300010342079179402000c00a038000c80c2c40c10308901e500c6d00d03d9805020051908180005054002030111007441c054564280c0c0102c4c00010f2401031911803440800141d40005200807682d00c55059401940030b41002c80c2b4055 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 538692814 1250 538691564 538691567
    0x5010608060310200f07060b0609010e04092406030309050d05070308160203100b01030f06030816020301021c05101d1902070b070f11070506090906010513030302060412 74
    0x20400c86290b681a030040598540d41046900040e81c0c3c3c010340441d0400246036480c00b00169040348040b800015008100c10007882880c2c003030580c04075403d48d0301038600b41140300006d040b0310078000e0190150703890352020402c110280e0601d507101d0030060703500e002a04041107200c02902051000350000741c40981c0c082000c0c42c044046018442e40880109016880e5565440582c2c02440c2c08d41a411010509a005a2014850b0b0032911901d00b00005101581c2c40c005000c4454041011044c0e5240038000d100040780001154049c1414080034150140c0b00e00c0000c1c06817141d80d10449104e00302e0340380208295440d40055000c0c0c1e0110310440551a1112005c0ca132041c46030103510801c071414004a880c1d4010031001c6968440b00c00000b51401d00241c56141e0703400c4050b1042c50009403803120f08220b0a40c01000e401ccc10390840c01c06801564504800602e80e4020908a54811761200c0040b4002c0c0c0e0250301207030080d224030700c00715070400d50700c1c1000f0391150301c1110107880e0700b0101441e00c00b805 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 538694064 1250 538692814 538692827
    0x3101e062304020f030402010f021e0601090e0a02030c01121e0b01030b031506010810050d03020f0706030c090b03130f0506071e080f0c041a040f05041b050c0705040606080901050106 80
    0x800c4d2001040c0e003150780d9500112103075a100720300350b0300f58022107c031404515035185115200601400040c0308d25407501e030065003200e1200c540504603030005c100050042c7c4d008241c07032402010918100204601f8017454100400e1031a02c07002c1c18144209848d100c012070707904110005102620200700d0724031400c05158503020181c80c81030001400b503000a01c02d6018010f240d422518905c1101c8140b500c40c80420309404100da0305901607446501410340c21141048403901400c501d107401e001110b0302a401904507a268060a1105600400018141050420402200c07a004613100050460b641811b0b92149400d54007180062014541a041000d88080244081070150340d921000d0341c9210910035000406030030000c4240c81080b0009107400010b610705900002401196507a9250000c1079500c103c03d1352141d8042c50412090801c1101507101155601d1624107100d5569404403140c5400c7c050260001a800340c2f9010700030440940c40a034003403090380c112008105590300c415065460 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 538695314 1250 538694064 538694077
    0x6010c020604151407060b040c1b060e1c08011805040b010e09010f020c150907030b06060d060b04030305071b0b0f070c080607080f0703050603101e06230402 69
    0x300da400c2104025514240002c2d071000402c0f890044110013102c02c450129074414642510005c1d1202074000c402d14051003460204852030619525042401c055519081c1002801030b01490340d5000c2c0380340240c0c0501c00354203041508070300b54460b020300302c2024107400803e014100100405564803080c440311031241c5400b464000c0310050301a0b282186480e54848000d00c4c1d40c0c9595210300500711221031038000b500c0c03980700c040090010b40d42446520300d030342240208000484d90000c2002c0010a080a40f8113412540c2a138049030740d4010075222502808055000840728100090b0000074160b100d40035004092042404404181c0442c0c17503a460b0040c18003c042032100c04010580060a03810010200c451184100c04480e03681c07503203420700b0100c003140c080c00820061000c201d10310001024050340071032281000c018504000f0041703a543d0345059042031440c0d82d10486132000c0b0718828440e840d02a03a1030400e102994a6950780d520380e42c0703004e0643c0412000328082c4413403480c00b0b000f504c04 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 538696564 1250 538695314 538695319
    0x6080a020c0307060e10050903270901030b06061201060203040512030702010915030605060d1b0c0b070c020d0b09010903030b060405010507020d0c03080c0604110a0303050a12020d2306010c02 84
    0x2091980c0d220980100103649400c85c1c035100d28501440420f5082c050170307100e41005405142c844403030780042d160300340c80c50748a0209421002c0181045070f480003222030540341c000d1107480e216a20312010408a1084200800b0050a0100000f507205d1380040100150b410540c2d1035030240003560001a42c034014000b000707002c2980341c4800c1c040112010156460054185408510350b070342c410105d401640409000e080f501d071940c0812068040c080d030101c00941e1140340030b100c0d9a865449070b82d0302c200007420751010428503024036002d540d100e016140c40746401481e0003540341000b2030164001c240d54042100031030b0811101500e00d00c0d2440c1960110703401030315030360b1406076181d0801c20b0080360304900b264003054442010010079112000ba02c5900c90000003001e0608041c144050640e0035080401c2c0300700d00403e400c0c4000380e4040d06443d40d41c0c80c02d0414444500250121402a00400c80980007151800a41c07007a910300725a502c2c6d1006d098110040c1c0c490300c400004503080380700c40c04003a4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 538697814 1250 538696564 538696567
    0x110705030d0b031906060f0e090616031e141f2106050f07081b04033f031b081f080307060b04050a0c0f20060a0606080a020c03 56
    0x3000744070190000b8105800060541c0c50441c00c60280000c003131001d240559a180d80c1701c805000350008280f0b0200a883ca0341c0201483e86050486256252001051412106424503076026614000e03041003581a900341124801454038114800050180903250f4500440920115200d66a21080b807111401c8032218001c07800c3c10410303002d800ca078085c2c28a190f840f009540004c0400d072144a514024401c140c0400700f10300740400300404807032004d002250f25200010000c0c0103007120100b00c4003180e5020004003000d03201c104045441d04440107001200c580188200b0382c07001885171580050003e80d45080000c2135012480108120b072190340075000c00d81c5007002c24444a40d0030001090891828011030a40e6102c006040c1150071100b411202c0175111164001503140600480354000fa09510400619441c08001000343c404602410144140104142d040d26045400480703803e507494112519030a20408440040040b480b5240024502d000801c82501c900c0c001c8032a134000140086 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 538699064 1250 538697814 538697827
    0x6140a0504020f300717011410150c0206070512091306030203061803040f0806060a0902070b0705030618010b1b06010605042c0a0c0201180201120504050322060311070503 75
    0x35811440c0c507104c141c2da8420020009040c2c40c299504900b0b4001040000c1032681c0c10354504040e010b00070f07084d0103c00030512801d0041900e650b09000c610302061514003030b000b41e47e00210b0301520550001030018052040b20b8822508468000e042071801642d060040030106031000c4101d80c503501000b9496041000424070b901443c25900881443d61810340c0d160954542109690000c41e902c01d19240d004502081118940750107030324010241110158604003a50740e40c182418030040070344042c4500400841e15507210029142802c10154030b1100855844e2022401c80ba00041102c400500100e00c0c07144503040041001812903080707031a030a0401e42407c0101641e011700c66090f454203c040d0503c540c03940c0c440c0400300d008503100000001c081071000300c000d080d598070300c01c10350004a00026560050760300400d500000300700c20000044030748035403400750709520504803811030a40d4079440a80c0342040300007210088480b1074908001984480044c650b450040390405441c540080c040c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 538700314 1250 538699064 538699129
    0x16080706141c0e03030f0115140a030f0b0a09020306190510030504031e050702010207090b0105070f1103030a26010312081005030609030d0e06090c0d06140a0504020f 73
    0x4a0780d41c424031103000f080c50818102640d140d504103d90404a1100080041140565296000c010285a85811213040303d0711021801640318400380c1c84100b5665180417600d060b02d607480403d814200030320303811031a603880a000b1301a4000317907010352103500911586480b0790340340d2400c5811244040c3c80e041c080348d440da40c242c00030407000340705a060200030340f261017044213031480b00c40138001640c07078903500c0d8205130000a142440640140b0b004900e40803c0402c0350b070304541691005a4842e80c0040034108a00d005001c2d0300505106035054403020810001c425044219490550352121101c04110703003a1003843c2c0206428031016206910051080c080c0f603100e0030009600881e58680300030610741c1d410119184c4407003191500c0041d000409d48050450383e900415007102c9850001b0089c0b418045c51180c2c444052400d450706c41c0c0e0189554000b000110b80000c2d01003c0713107942c0c10750945024440c40014110440d0308921541c4804140d40482c070700700d600480318420314088a804021748000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 538701564 1250 538700314 538700347
    0x6050f030c0117040611070b07260c09030114010b0301050118050108010b0903010207050d0f0f030902281221020105040f23030d09020312030c0a030b0a05031608070614 74
    0x20545d941500c411052079510b920350014030415200d400480d0091070711100082c41d0304840b0403100d46c084c140740784041d00e031107030031102c540c10188880b10303195122100b000003070041446200c10010405540000501000ba800c09941203505c01e0b01c620004a0400c0c22500010500340540e501140310300c2c005100c94409030028112300a4050001458102c0c1501e0702c1c1c0c90800c81840c1c0300000341d09424040f800b6a4807000c0c48040c130230b0f01d003014484001d00383c1c00038101042c4020089988101030021f41c8151810b03a500720010704101e0100203241e03480c1e0404020002c0034280100540d4039500a15501c1c505c144505031045070000760700c4000e0300c083c1d03580d0540e0000312080751031170070342c02c1c58141c800345414002410442c00d0110300045d4015039205142c20019004a00c4681990030310400050304258001c03259032071601e1a00050340404040021001e4403541c00480d0140314140407445110480000c0600396801d403001c4a880990320401290408c1010f80805a864014410003000492014 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 538702814 1250 538701564 538701571
    0x40b07020a0918030e0a0803070b1f0803092407020f010207050301060603020405030c040209030a03030b1804032c0a0b0313020904150b01080c03061c020406060306050f030c0117 78
    0x20600c0d04a641d0782c690703403000e4034622103003d07410f0355100b010841050b070840c4100151544c26203550404516000081d900c3c0d00404c0c0010b400c0302418400541d2400094130b0380707442d41520001c0343c4111031300c480c001c0e952600041c0d9024001c442003101e08216056016121591900c55000c407440d1a41c150709019040951100d001c0c1503101e100c1c00400c1b10b5400f030055070050b000b25580140c40300c0c9031108161a10350008021400b452042010001a44000c54180005038040c140891441025030104181c000c8444c40c5040040300d002c1030004141d0700c1102c0000d00d10085440d10b01009030801c074044d20f00c0301c071020320754410010003042200c0c4441b800555070080c1c61481401010059802140d181d040071a411541500b9401910303070600b0703030343c0305590718454280b070198101d18003401920400e203c007912061290034051909410b10703640a203000412a0b0207007041c800301d66030300c0c40034011340503034011140700d40d80c10381604100c0e040003c0c41d0500c04c8030594a80c11202038203044c0040450024 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 538704064 1250 538702814 538702819
    0x80307270f060f09171b0f090606030903070221060906012610020f04060207061727010f0605010201060806061809030d0212070e180a0e0a140c01180308040b0702 71
    0x2050b000445d014041ca52030316421450000d000000201075150062500c041c60580c4605200c04012040c1d44440400701e5014a060b00d4103541c903181d0368032a0340b460182c640d0084d40880c0956000301da031100c1c1d40d0048042c91800301298040e4450b400ba20b85c50742c3d02406406103800c2002e03a2070180074010400c902c810020141601c1d040d2001c441d0b02d10980e880800d101c03524102c0045c0801c04660f041103400018241440c0142d4512020394600e0900b074009022400d11070b2046240c900501c80e03921400c4030003189440204100084114042d010340414818540594641800021040d001180c443d00ca104018a00b0500d080c1a42c103030281400c01603c04400c4d44000d00810135603001e640b0051408c07180d0b40c00407020038684448000c006082d988021400f8501451820410b810301d400c9240c3c02c0460450041024450304180034546903a490780540401056194502c071002e021541c0d20101000b80d80380403421401c2882c183c0d0780b40003880700902007241048200200500748010b4880d880c0300 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 538705314 1250 538704064 538704077
    0x40f11040906050112020a060801080c3c04050105010c0201020a0816021306030c06030b010c030e011206090213150801030609020f041103090106300807080307270f060f 74
    0x25200c1c0b000b1143c090300205a051081280c42e000c2d8900300010f00000c080a1038013030707a650305006905461b03d04c10700e01c03240500d0b00c20b14030703400d1050041600d00c1c1d02003121030b400303403024190200500014819007009003e180390400106480d4490881c9001890701a0001d01d02200307169692036030740c0d1040989111000c0b1850003440181c0c4e0f001148568071103c02400f01d02d19046003051102e1300c1c49980131030241890a4580c00d1b159800c0414600501c0c0c1609003800403944540050f91900020301010b41c7d0a417400d98089506030480d800350210345429a4040341198840c40c181000501c092030210228000a004000148598124030026480645224034502d220804282035801c52400504401004801c00101d104c003403103030750b0040048601200a107890340c40c120607008545000304c40e0b048151a00e07202800855401c43e90510b60122826a407442e2500004241c031030402c01d2004100c132051242c150070301c403016034002525007806803c4010740c40e01c00107642d00e40d04c001f220000d0004 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 538706564 1250 538705314 538705331
    0x702030a05031e0112030e01020118020d060f111b070f1502150a060503060f040206040612020418050405060f0f01090f0b2817120a02101e060e040f1104 67
    0x40c3c892141d0300070300c0c4094000325060014079014144440c0c5850356811a03140064510401410327409403808150151640d0304400e4417810114003911040d0a034101c814101804889a58542d07130040890010001c81d181000001d0022a41c03603041603c2104a0741900a505101440e03440c00001b223002420300460b4140c0c84012110007a91008688039510700f540c1c0c40c81000b040c10705100c40d40d8000c100080c440c419190942c00501d081c001c50044408002001d441c04090306241d60444000c0e01e0600e880c0d03690090013030403070009004222004c5403a80203050200e50700201303814180d030164071805003012107a8207001c441d00c024250302c500b1491468940c0880003035601d0b06400c0c9180c2a00d940d501110b007002c104004049202a40e1201c4080075140300560100c7e18041794020440042c03030081503403180080e800728904036410099402c01c500c6e200c80c000070030b96200da02d440600c208100a002072561084a820641800c8802514244c101074400c0001615508602a2034800500c002942c80703 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 538707814 1250 538706564 538706611
    0x30f010603060b040c030b0114090114121b0304110415030605130519020d170f121f08060a09060e0a0317060d0c06050f07060f0207020f090702030a0503 67
    0x1022907000341c0c0d01c07559522100c0031604081c0100102800d55041c00e02903c003407070000030545803005201d41c1c12510b0210714140b507a03101704510105e48030f410b0b99070b0b42c580301010100c0103207110944020381009a00c1c1d009150500b070300e40c02e8a1280d80c00c0245101e41340030020074000601000011602200c80c80034000c800070710170744101402610384030240716071210240351051404d42030b64140c0ea000b210101818006940b000d0301e40540591050102c4092034450220381c03894006d4511400c1c0009000c1761100b400e40604449070702c0340c00007130250141e1104e10b09600324a403413107000d001d015401031b4001525840d119048203286911503000041d1a003d1086000e09201104004400040c1440425030101c002c401d40a0f0304000c0440d07201c4070040d183d41c0c41e0880c1f00a80c1c032500b0240000490380010345001081a210059000359061001c078004d59081e50081d07200c1d003c100d10a0680382d15440c0d035424030381041c0707100d206a50011460701d600710b00240c0d45600010454490b00741c0b400003004500c0f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 538709064 1250 538707814 538707821
    0x6050d1412071202281b030b0f0405120306011e020a12020f10052517011511010507050409091407060f3b0111061018060b04050f030f01 60
    0x2503004020201c1030f00a82c0c40000e04204008101400000650800c0e41c0e104180c400c0740c080c91036101301440048110103182c8502d400b820344c4080d00b28103010b01008540140c046040344a0f61003a425945101c81c00b0540500034041562030030700103003140081241e680780840c40398094034100d004841031085113903100780d1030341c010042100040e001100780d1030418004208011403803072445010300441c5041050352036004c001c4052a54110180e4042c0f000450144081c9441c7c01c3c03600004030141e607100c80d062030041d0f0b01d410340d05002440d2110f0a131081d10f010720070300707014880315942d45141c0307031501521001500250b9025110321801c160700716103240040000c003008181350b8440c10708000d4440d41c0a006004462025460401c030500c030b504111407440424800118110465032a1400300001200d0505801c80e101c10144038803070500c500d900881ca0703d50111040d5807100b030888144208088240c615a01c00d00340400011300080c021440d24581c4080c8858010382140d00041e1690300c0103007035 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 538710314 1250 538709064 538709077
    0x10318081809011202040203062205070e04090507031103071d090c01020a03170c0415020a051e1f14180709050105030d12020c03071a010906050d1412 66
    0x4610000a5500d401090108200d82203407046034101074641c900359140802c001907090091080b64000b0000e50035580744180c03805500300d82411520342280107031401c00280000e4400364089505841180e086240c10701800300d2059000019141252540d900c9203400105c91007030036854054407401003a080c3d078810603502c0c0c6080f00c0c61030380e42c81c1c10096031003810284070002550454001090000c00300340c018155040300e401503000414981d807408086820390107a5006144a80c403c038002241466000603000c01c03550241042e0340003414415952a840b28440c0b0100c215a00034510801d0415806040350301060807401c0e000ca000c0958580112419004039000307900040c050401e0010810100112800b5080c01d15041000303504100c0001d50b00c440480f050420044122059940c03d8925015241e81105280880341c46140501d44401182c3c009200e80c1002c4541000018810070305000b240b080707035005081c40e14070300d03419101da000100011201c0c0103d44107a42070302c0c040490304401081c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 538711564 1250 538710314 538710323
    0x61c0201030b1216060206040b0f100302120109150513030c050a0203060f070e01020d120c020a0507091d03040b070305031f06170f010830040e060a0803030c18010318 73
    0x1e400034901a1340101c13445404c07a42c2158451010880001c4500481030b40110900d94800941c0c0d0b20710000a600345220b8000a401c1407400d03201107009101500401c4102d0300c104003d203418900003a28000311001111004c40c910120405003012070700420a0b035800c6070244059038180c0c0120f0300402d107464025540c0000c030008000c208490a035112106408002092000c1c05520715020001802c0c019403240030000300b951544001d244500811446000303c3e406000d69006581c0ca904110050805101012901c260f42840c0c2d50041d00c040115001c0d18041c03100141080c11030388084a954200410480d14000c00103d00a42d800c3c82c4400305000f0502c95544100266052400303e0707c0280c09030104200001c6040180311040c0e001c02e807407400c0b2010301028041c01e0361400d51244060071105001e07001680c0010046a480d00d5059054410801612100c0c0b440e540c0780c04090f603034442120064a027120078000802c2c151a54a013000306200c0516003c0790781451079510b008191083c01040702c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 538712814 1250 538711564 538711573
    0xe01050109080307032c04050a0f0b0a0e0109110408160317311a04030210020601032a210303050a090b1305030c0712030801050405061c0201030b12 65
    0x1666900111090140040300003450070426640c0c0c002d000007200d038400c0c4180b5400035046203c07540003044440c2c0b641d00010300a110505100d8040c0d0024819207101026a604003801c2502c9130416084460071641d19a4403040103038a0411500000c000e485a1441e1075801040000303216901004003041290540e411261554610725164141001d0008440007c06040c000e420705000d00041102da902d5201c2c682c03418840079541d800005007a50341029442552841601240145d03120182040d030344241c1c1ca00007030f03800d60b11080c1c7e42ca40f402d10008201809201c4000740314080b04114580000c2c3d42e200c0d0b00340341510f0310150104000a80d10707843d40c440325444840207060707140c01582e4002096410403c4240c00d551150402c0c08001003003802090403051741c080400404108507003441c01c942040d5403045032a1000c42c3e1000601c5401079000560103800400d1600c0c0c90700c038640c018031000b0314141250070080c2c0344000862484109a043c19a1090380e68003e4643c82612000400c2e80000342 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 538714064 1250 538712814 538712819
    0x60806010e0d0f0204110d0f0509060c0403080412030203210a0b041a06180405090d0305010902160201030e0124030b0a060602060c030912134b050a0e01 67
    0x1480c0451203001e06100342000764034480490f1005034101c1000741c040d6008507074000303600c2e000c16080c41074145003c021703894200e42c03803194403265001c2c85c01590804103032500354454940400345030042d80409409030404000030842c1c0d84074150006482e501c40d0043d00e00b0401c103901c2d680c0064101e0118288841b07a00000c01c9a00c1685102d071480c43c0ea4200d0b01040b040c0b080c4003a14418080500c000c90042e03c00180004200c416401e00e501e164800400a00c51460a004a00e0b211086607810501182c1400b0003c20507450728000d88400304c000c50307985002001a6001100607110441121001d5544d60b55507400c04000c03000c20b03000d040c45034001d0301481c0d403440c030300851140001460380450500c1c0c008140311407a4003141640d0080100c0303680f5901c07030719400380c1c03142410240d001e00d012400e00050f8a200e00f145440506046541c00481c00e03607241c00303a86484c0d4403030a03c40071002901d40c2c200311114140303100c03198100d10480062280c104040e15140407505502894003e10800d503011f1004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 538715314 1250 538714064 538714067
    0xe0730020d0c0f020a0803061003020c030c0a0210020c0319141b100306050915060c06070216090c0c02040c0509190302030105060316030809040e030a030e06011401020715021606080601 81
    0x80d210201c0c034520081c8401d5a0b01c0d00c07103100c54003018020b06e09c1403500300e06174071070300b8401c0d01682e43c0078504405517603941c02c02041c0180d840400301e030102e0107050280c5c503039a062400411144011080070f80500100040e83c420042900c400410844000780c00c80e500c42140001007184a504e09040c1b12914103109080c8100001d05100000030000c00d42050030502203503d640b90039540060001c0310a000c0d05101200240441c02a0380120b181c503c50314040041d5641d0000c2c1850f50744803a038102013521511050b4010076145080015004507200b598480c0c010300306a84405110707419440c20505004005000030701c1400c445420058080f2030082c02d2055150070b100701c0b500102d0072801019040d40c2c0041e0091440c070540300c081d0103c0c40201e03490404d13840e25013184c0d080d80000b00550f44e0f2004000c00107801031400e8042109517201d12000420f0b0507040900901d02c0c10301c143c0081800d286040c0c000c40d0150705030345604045020301143c0441034070300c0e009914060030458581280c80d10740300c0d00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 538716564 1250 538715314 538715327
    0x105040501090c121e051e010b04051b0910090815090d02070806150f0604030f0c0b0a35130302011107080702090a110d0207020108010e0730020d0c 65
    0x31030100744d00700d02da8000400c40d40001588038070015030388200c2509814640d00b0292000c86c0c450180c1051115002002810342c8801c440070000c031820041e54a900d40203801c00e030303181030040c0b00d0038000f005104000d16055a4608440c0d07030740e10b800140651644c1c691403c03e07644010008400d03c1c00c9060040d402c01c1130082e07c8003020305200070803615203006000c55507500040e000546018006031540800d8807510410089110050035481c0d43d00da40f450040f00c0c0007085002903030805129080030034051900011079401c880c0b41d9561a5140c20b08030400181a03d40303281101e16080007880d5507034070422988103284114010045ca034525051403d010742520300d40d00428100d17071020440207001444400079103ca96406a51150903070340e8201482c40109208025941c0c5d21310042084140e011032500180101407003a070300c0ba582d0b030b6038a401d00c186148040e101900801c0d044075802e04048001e00401034405100c0507074400c100a4449800e00700e0707106188840800e44c503640501c0450f0341100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 538717814 1250 538716564 538716569
    0x4030605090a020d03050c0a0503120103020111060f06010e030708012d050705160510050c180603100512120d060504060b070f0b0c0424230d0504140105040501090c 72
    0xc00703021145150f50004a03104240c03a0010140f110103c0d56903400c490030008000d05a92200489a44404804100c00300b210700348402c038001400d80c01c0091207541c0100e680c500075a85464005a036446078001540c250000c46612501803141c45000a980102400740f00e44988050046554140070103400840e01b144055084c2c0c030803030601091081c00c650100490311041c1d400c00c222440c4c124a441e00c0d03410195052103960a450401c2e00748088180d400e40100000d0000d00000c500190103103040c0006400220b8042c8107100040000300980e0a010745c8051550848005a41155818600c140c2c5070750000c2408015166441d0001e0095061500c079500c00b42540c03c02060038054141c0c1c454046001c580f4000300300b10b00c0100402d0100c115101074401a0100c082d130f085981c0324903418040c50f440340156000004213a00031150120403058041e481e90354118008902d880b505814803009040f0140089900c1e04411102c0307503100e0021310030f85014a11400011600030068106440c02d1325058 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 538719064 1250 538717814 538717831
    0x30905120c130902091008070602010b0607020d06061a03010801060e060f01180f0605180a0b040b07050a08071410020a0e0103050c1306080f101a1803030f04030605 72
    0x401030519800039030096450307000c880d0102c40004070700030b41c005020414030094011a5440500003120801e035620f20943d05042c0c22202c40c540d540008038241c0fa082c030711460300010100700003030140c14040c803074070002030250101096066460105004222644850700d001e00700220040c0407401c0d0130700400f4000c0c6130540c0c002c8903e0402000084c9a1a10261b0708c03070621400078074041c0c4c031000d8a0500380040c64034121201c1802c0e580d010161840e0300c110300f40380c4d0040c0b40464003011850048010300a503180e075110b80d42041d042c50b25200448d40200800e4441e4420901501d0000e00d600e0004c00300c540c881c00c120107118200c401307800d19202c1004404104c0300e0040c001c0d680403c3e40401000c00c0d03200309281c00301d211340320002c4240d16885101222014050030210104d011508100d009002d001100d40c2c02e8002d54074089200d410b5402d42c018442405460114401d07004c0902c0060302c3c0b84900300c0000039440c04004002407843e03024800c039092180700031900704180318280c441c2c2d42d13028592 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 538720314 1250 538719064 538719079
    0x20a0309120201090618080d050d050a0e21040503030d020a030e011103060d0c03050a050a020312030402091902090a031b060305010f050925230a0206060405060102010f02070f030905 80
    0x40782c1c0040d003603000901525003000503110142000c4c1103c00041d000401e16601a22160302c00c00c08000d120781d00541d094544503007002d0100720040b28512402c006600c07001c001c2c0c1141c0c0e980d000401c0150540c80b09031010340e07009020101c0c8640d8284001d00300001c1e980301c01a40c0740854034001e0241c90310f080144205915154064070802c4003202200d52100c001c4807414081c11040c5090884050190001f40191042078501c0041241c0010100c40d0359000301c0071900c2450380c3c489072515030722003258020341142090021800e50500e0b0030108030740242002026040440e50b030003252146100e40e200359000c556690480c0888144082144090000c91605004540c18403640486040c0c2c244140345c0220b41d0000014882001c0b94100301c0e20542001401c045007810b0500204506900c007480000441046507088a0303052500403104850083e40240c00e81d075440404010061500a003218150f5403030f201201c1510500c1e02c0102002c5110790381c1401c40010504006084503096000903004158 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 538721564 1250 538720314 538720349
    0x605070c08060907062a0f06271514070f030b0a05210a0f0c080d0c050604060c020708010903031d0304050303040b180913150b0a06050c0f0d020a0309 66
    0x3c022032410300b59000c0c0d0400e0458210a44105004802c410101141b40c032100940d240800036846840640c107070049000307101c0c1c10041c2c0f204181e4804501c0c21601080c040f0440c60000620301003030941080c2e0710881c000303404801020000c4c0f881500b00c520701d00148010740302925032609481031088110b000d0f1800d00705103080034045009a002c038107084144080003018290040800c0003111f195a83c0074a10801e80708891070045030703404070360040700114010702c600c1541407480742c0034a15800e600580100417545558a13608010090394035a0360850160340310200c0c1c20341007405810045807296800103204c401d00700780d075203401c52a2001c4034541c0e007041008004a41c0c000080d1402d4501580d080b03a5a003542034900040d088440340c025070410340e640c040041c680c09151a64a500d400703056000d0b100c07000c01400320201c0c2c0c20f00c0410384e03004075014001d111091180002e403014520000850b00c1901581c0b640510b42450031400000590000e2502c2c001c1543c0320400e1001840e611010044018 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 538722814 1250 538721564 538721581
    0x201090e0603030f07080c030c07140d2013240f080d0f02100c030b0f0d080a0e0118171c050a1202090d151413020118030c0605070c0806 60
    0xc50200c4c00f03090041e010841d80240700c8008100d41583c4540c10490b0340d41d0f400d8080c00303611508603126441c8440140d003003419982c1007005000e0704041e405800050030840212038461000c0003003100c580c00060500b05085110381c1d501c1a020350500000d441c0303180200070583e0505101d02600300008443d0350600800c020f10001505801c07a07966400c0c1b4809541081004a14251204410240850501008502141d0140e00c0310440e018103480d21540030050800f030026241203d10014201c0900308825600c691056210312510346051510b207407030140351140822805815003040e83c54141600c074070036850350100081094800c9070454140316080c3d070a0054541c0c0583c4c020171060042080e40350182035083c1e4101c440300000100203542c0ca8580313080151103013030559000d8036002c0c80c141140d82d0441c01c440c010380c401d284003101114500500d81c011141500840c1d032004c0c6516000e0004400034406114040c0a025259100e0b42c0340c003040c0c10042ea29400384c2c5e01c00c4129070000c0c0c06015114 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 538724064 1250 538722814 538722817
    0x160b1f0503030a080601020f07030f030915020c01050a0c3f09030b04030e0603040506010509101a16140309090a0207020102151f0b0711090c0301090f09120503040201090e060303 78
    0x3c24242401d01c69503485d00b00503403d2210703006030481c15003d038010202c20040d22601c002c04081c02551451b85650303c035800300098040640075840075078040d8104403101c0d8442c40c000c20b45100b9034600030000c0c0e1030302d55402040040103c405814041032a5501c0c01e25513810070103c05082c85189906c07220b00381c02c40d000c0c2a5819078040134101c440b4440014081c180920001241101e0103031046940380341c10308006845000a0007007510401020004c01c1c0340c001008500020341d00d01c0301441d41074802c8000940c146601407604440301c1e8071412100720200b45008525070010034a400510750740c042100070031032016001030040024500c14071105015036400513014582000f2455001a146c8800564241914520060640482d1076107004100c160303800b00a099440d21440c0ca000c0340911000420010304000c803500c03407100c1001c1c401049010200d800c40a5a500e400400142c4082d06403544403018206e01c51326804907070008140021964880000c100403c1c0d0b419442640d41030000000b6102d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 538725314 1250 538724064 538724077
    0x1170a0203062b050f0303071d040b03120301060801050a120201050702011229040207120f180e0103110a03080f0c07081501051032160b1f050303 64
    0x155902100052103a1240c50785508010b10b201d06882c28180c050f444035405402003e012151030050407881d200540000083c1ca00802d22521040c0c550701c10821582c9500041801003940151502c05040c00c85e10180044103000c00c84030b000640e69810414064450841070744046d00901500e1420031413202c104220881003a824600b856031000c0038001201c043c4903d50390a28072524251600303480300d0303500001c0c0c0e5645151091441140348184100300c102d004006001d41240c4102c0f88544003144244912800c5502ca401c0c80d00504481940d00108000d640d005415286020f40050040c00946050141c400004441040341a411684c2c2d8803101d001d081a41c041c1c0401c0480c0030542c2490920204015111031022107801c04a484048000700341c084c8111809010040d4005520714070803e41c0c030103160482c1d03000d88000c0482500c0c042d011069900d0905541d00288040d4080e580300300c10103206a030141d01c900b881420504414a003c0f044980840b0b012081d02800304202d0b2404420f5524 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 538726564 1250 538725314 538725331
    0x309010807180b030603010c02061302012010050a0b03030a0905040b040b031c0e01050a1e091e090e0c03060417040305030c010f0b040b03191103190b060117 69
    0x403980322210281c030140a90045410400d0400002090408508000d0b40c410801100240303c0d05071048803d0703888500c15203078600f01d2040860080b01650241c9500810800590086c2900581e4030340034a00b0702508400c0c0780c84450700c4805200e9058518080e541c200d98044024524001c0b003100003600b00405841740d2401152100400e481541e030710b40c0114510000501514480600c04c0ca681c0541c4240e80c0100012405d040078070001c80d403007042038503080905038031000e10843c810262240c1544404511604101000c2e002080c0c4100200585000f802d404e1581c1030024140b41405081e02c0c0a200440c204d90322007030b0340090741e40e0000340e083d8105030812201200b000d00d01001e960710b8070468001426520000a0750482040705500070b980c460724211003001074042100400084c2d80b0b119450703580c5503118202c1d4014410321101c20300b0441384503002d103210703035145140403909124407201207404410a0140000c24094020300d01980800c091a000c9543c0300009100d84903104094050b14 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 538727814 1250 538726564 538726577
    0xf04020906012609031e0304050607031104030305030910020403030309030e010f120e150702030d05010909020105030a0b0d05240c0309060c0c01060323010b03010b090613061a04170609030901 84
    0x13a58a4014011070700000520042c15014001d05e016911069000362404c46407449201b000602d014441c4c03056508841c540320130389142c146551400c1304c00c1d030409000c4003058054080e00701449143e0780300410045110761004214910b040c20003800011600c6e203035505101038003081c0c1001076480011340807440e0030510001070b811405ca443c1c6107411b000c211203a62000c7c3d41001d2106007900040508480240d00c1400d0029a0700d400034401620041c1d0740c02070200d4014000b20351840c50a422400240c0130142c502d005100b110f44031185000014848606103010242d1030006600ba4402c89507407104000e4842881c609064031070030742e9080000c0803208d07121008141c0d00c1c43d43c642074004000468124545e0050101d21014100c00440440401c0c812986494810321881c241030140c1c0300d003818018920000b9580749018004030b141c7c5e0310a00107405503161030115034102c0d101040c90100089400c00764807182041034014100c400e444448007140c3c00a41001a0050008202ca03040d010a2805a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 538729064 1250 538727814 538727821
    0x711010e044809080712021804020418060c020c03030408070b031b0c03040533090315040b0702190c0323030d0f0c090e011211090f040209060126 64
    0x425a074660700882ca000e10181031102d0000a0b0300090102c103496442094955690f5104c1c088aa90581c0c1840250402444503a80c900ca120025216031f1050000e400400c0040400c10031122012080d00c045a60b51759841456038903a40c1001510030582040d0011440c2c9030a0642441d5034103074a00c181c15188600000007481c104030802550703035490042c20702503119260400340546942250050a015044140c04521900a10552008151201e84001851418240101c200c540c02901d80c2c940610411b40c40f11481e11540d9144c0e07219a01484400400381009600242082c802c05c2d4542a4160610244400b10320101070f0182207a910481007158208000d5558a100e6000c401c116814000882d0000702e00b5440d0b003103000001c044000802030491311031030907100e04590380038a4012180c01c00052000062100900140e40e00401c60400020541c0001882e0740608560701000c2d0a044810700003141400c4140039009030007400c004800304450800445c1c485005282c6402210006020 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 538730314 1250 538729064 538729151
    0xe0408090f060318160b0901030f1104180f020a02060a02090423161805060c0703051e0f190f02120607091a03040512030405120711010e04 61
    0x14101c6410040c1c21030b03460740f500c0d20802140108012101d1014000d03000d4031609003140070303503040541d00c03010403060502c031003100110010b00203801914881c03642e5420245114002c240500001d1444004140f1071707818150b04001603610842070250524010f03c065004290041155075000c00705030070060f00c030360280c40040c000d40b00b5510001c1c040703003101c2d208205054044420700c0c0701c3c42c0340014000e103464803801c049804000f00441401200b224003c01e002c6460018001c06000040700f00703c1b0225910703625103c0c00c05139020214a0400c50420046003919001d001400c0c40c0080040640003000c42d503480d0f128014094000100b01c22071030000c0340215903540740711600c3c1100090032140d2034034103600007038000562070085050110800b00074040c075111b10012644525881006450505640001a404c0790805001160740b8010610b40c031007941e2800001d01030583c0501494041008800009050090240c0049000f2811f103811031048034080480c0c243d05103c48a015007885203003026 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 538731564 1250 538730314 538730329
    0x30c0c050d0b0601080f010e0c07061e090309080d05070b0a0912030510050f06070807050f120d230f06060705030d060509010f1203182106150e040809 66
    0x20380d51181810008009000044070b00600c0740d01c003a00d80c600151240c076140e48900e0000d21580751000504800109010307140c0c8083c001722440b0303950100f1a400507200460548880c44031103450150350311400c2050580c8552504020910b190191224017038035180101035214030000035040010f2840814235803600c43d840b03036500503040410a800c010104c50004d02030401501c0e0f0740d908290750400800e052515455905800100410051510b00565152016600301c1d10069031180500003c6680d800b005020034030401c10a010b4403540d45c40c0071259507040715603110402d03a0a03010a1041c4004205101d4015081402010040b0060352604006440c80c4034008000740240804140700030110a81c0c0c21030820b55504440441842e03882e0a15a9405251032080c3c1c10300b00e1441140a0210340140781e80c0003010044044100071607140d9207001103040703c004c43c6c84401038030300c4580800d0200780e20945680001079040d401e4281d20300032006000301c8010700301030301c03101000031799222a82d50f840 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 538732814 1250 538731564 538731569
    0xa0203100513060302090a06061b0203160e071706030a030c11030307030806040e0c0d0602130b0c16141302030c0d05040507061d060a0e0102101d070f030b04030c0c 72
    0x404224440c482d0002c800003074001807004030701644003480814516034541c0611403e03036510755140c09000d0584242c030b54000e41101c1d001d03030305406600f44040d035045600042002401130360a010b07a0700e0604c150000d100401805d208583c4101d0101880401d581c04139260000719010f20300181c50039a903082400d09101a2a00e59502d8880020501c0030544c0007811540300380300454007041030b03072840a2034030707140c2049e400c51590240e241107440740020526405810003003005000700e0713601a20b801250041e40e005400300e21641d84000146400c90b8040e01080e000307080300c3c01c190501700481f40e003c41d18000e14800000032040d00400042c00316520201590048441d4080c00d00480c2460700b89951140598020800080c83c1c40e02684058205064141c468402c0980b1b624601142d0700c00860388907022400e0380d81140141d00007800a1031060140e1242e080c40c41222843c5602c000604030f14200003540148042c07403040c1c5080000c2402e0392900b5a00503014104034168040b10729080e8000c0b41c980c0c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 538734064 1250 538732814 538732819
    0x504110f1504061d030c06070b0c0c01020412050d0c02060f0d020f030c0a140405010e100c05150a141006030c0909062411060610110f160b120a02031005 67
    0x110b030002d20310740d100c0310759000503048402e0721100f0304207803043c1030b26110101c900f503400c1201003207041d0000b25242c504c168488841e0f400d99003000e8001c01d0003401c4ea8401d9100c038280c00d0400b02d4100911030184101d0101e800300781404020404554003084e11405080c0000c00d072490045240070104441d601252124082c8441d91aa2490191300e05001034001c4580e0400083c800201c1c8075030030021204031401e4407816101d249036041c0314020042c03584020700080c1c0421580d04420300007c3d07410080c41400c1070500380803800500d80704d0714401c1219041c4101c100d100c020f440921400c4100403451030242e401c0f84c80e01096201c0b0100054402c0c10b140da01c03000c8a1403401c60001814000440e03000725501c4040c0b00310252052040e022949039038545043c0c8100e4002c04003182d03036850700c080711760030919503400c0044940740d010a0090801814240c20340b401d80040302c5032098903180c8003016024161002e4010308150f00b1171502080f04030020701901d012640040880d02030155a62503100400d0300 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 538735314 1250 538734064 538734067
    0x30706060f0f0605040806061005091c0204050a0207080d02070606030b0a060303030b0a031203050a06091d060708040f030f05040512030c0115060e150702090414100504110f15 77
    0x1540a82000c10300144550060b9051005010070030910900c1180e084440d000001d090a40740d000c100600c40c1520a1b010091210400915800352a03548000310000c0380e40068000141c03450061106450340144032500a0f841000030100141140040d28040c500c1c0800060320361056140c5a40244256040074240c000c240c4200841074202c0c6c1c0021044e64400d40c0e0901400c650b0800f40134500145010060410018041c014a214865400143c0c04141c944000c51030f80c2d03271072080c0701c100e85255403038000540d00c2c0361078110700703c40c108051070304282c1d1031400841915190311000b001c1c02510000804004000c0c2100c0900c512400c162006031034014446600c004241c0311481c2d481d80b141d03091841a50030416007462155460811004039a4140c0350b2003590442d440c00c018201340ca46041110b0641c00303101c0724015031034200303165100d0b920924440004411910b041442d003428012042c90990410080000050019100346100801951080c0d40080c0d80b40c0050076102c00b84941c100f002c40d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 538736564 1250 538735314 538735319
    0x16061d010516030c1104020c0d030e011505060a030609050114010806102705130c02250b0904091703100b07020a0605030601030e060403020c15071e1502040f0315050f150303070606 79
    0x2000f182a81409c003940e01c08100001405405e94217a031814014070801515480d01080030b03041100040141505502e400101c01c0d4450510a04445080c0c1007401c003054040300d01d0500f543c20581460f08800121407035440b844604400030044900d6130100540082c14003100c240303e42080036604c0241c00b00509070140e00443c3c0607400300600500300c008006215030049403e0725036014031245400381b80109802103460800c40c45480c03c0c0c0c4203201e00d58026654950400c0810a40c40900702c4408038030404030303540d040c01c80740e40c000303103c0c1900210020340c0100100307401a40d07100f0071070003203500314244240c0300d56a40780160000d00000d1a03212640c090750040104140d404201401046000c07a2030001c0184018400d00007401020b100501a113110607103041ca4058845c29502060b10402140780781140358181c46040c3d0300702c2c1c0d2020340e0400d5003100070301c00c1021003c0040481448404108000d150103d120515130358064001c41e03060050b28000070454805108980345907402c4034045c0030066 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 538737814 1250 538736564 538736587
    0xf011b1a010b0c060412110708030a17010803070b04020d020d06060305011b0e150f0a020c03072309040804090603111e010206150316061d010516030c110402 69
    0x362034030300c21003126a90000880c0c0503840c24180e4078900c0080006104a40d01c55442e800710505000d40b2a042c01041800f00b203000380d042000300041c040d19070146403105007452020b8980c401034000c41d00c0840100740140901000001940d034800d400c526019000c1d240e900220b0910b0f100d140b000384d040b6540d08070a0050050388e030070000441e4882d074001c020341c0580e48000510800c406520100103440161403480d0391030050a030000c0c0201100705140340c15892075004800d5030082500c0c82c0582c1001c2c4085400780b900b0303c2003c0c014003031300e41d4600a412022003043c41c0b4041e0190b1141c45020114040b0f000d00c503100c03042d01d0240a10b03c0307080024503240e0503d89100302c40203c14038410a1410452041c0b0148a448000d0250040e00100001c0e04c400001d00161400c3c601600c0c0c143c03107490ba60b1442e6190840d401c0000303041949800481302c42141d10a010050308020f105d060000070000e40f00c040c030121121003001500f5281c0140d107000949406000c0300300d203082c1c0c5039220740040f90401070038 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 538739064 1250 538737814 538737833
    0xf0a020c0a080102130e1005030313060206060102120a0f0207090f0204091508031204081c0903081f0515040312170123011d0301140a0f05090c0f011b 66
    0xa030110358000301140c0e01c1103054283d1040080d020b69280b03407841d0810400a0140031680c0207440c1410341c1129640312030210b40b035604603107050004603202600030401143c0510080d41c0000080c400380c084840c0d41d2020156074882d0201000400880c0441544494801d2111001600811100b444080100d50b240f8002e5005070190321415860300e406036400000e0140c01104a40325200918108406081d40f0000320400500a0b5189042041000c2300f00c0c2421007902500442c4101c0003d85102c2403c0003001083c00400035465001d01e480004441260a041141240da04507440085404c410405248034000c5510007404050804a40ba011581281d211140c40381e65155807031442e0b980e161240c02c4059404000e540c1c855602d00850f0340c55104014204160600800c12845449070740c002c282190500203804c41501d907400b09101107107045000e11941001c002c00d040c0228100500480c0c0c07600f00174601680b042d1482d0007110000e90051507004180041c01b071280c100c0c11014100b034400c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 538740314 1250 538739064 538739083
    0xa2316091109031504080f07060504030306140a031e060e010608060702030f030a0b1f030c08070c020108010b0901140d021e07030210091b090b030d0905090415020f0a02 74
    0x26090041c100c010601800a03100c904000800400840d000403c0d8100548806441502d61600801241d501030000d10700600c80b46101d0000003030286081e040c01021212240c0020307a00e400814200300c2d0641e141410001501d4004450341c80c12200b02040210007400254010300b22400c00b044c03800904410b41c4050b0889950500395041503032820b0040761284035448009a0300c074000c3c808500010f51903800254409005406003035010355000047d402d249094074030a0000c2d40743c50340000c1080c0d04c000d00c00d07080341d03560070861502c0b516030340041d010007014010440707054008103084100d6807080c204107800c20000c42c1c0240d910020404107501940c490004003d1030307180c4668803803a86003801d08480b5800c0c7c040c0c2c05001c244090780c00c240d0140c205050192000c9031001801c00d002115040321000500c07071001d000840c04d544805050034601c410180380d0510071540001c0006480e40c42304964040e500c1080f000c20340300ca030806940280a0380003038402c0c540010948071007150300011070050 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 538741564 1250 538740314 538740329
    0x110a18150e090607050a0c02040f0e010c0504050a03020105070f2306010b07030e04020304020a050a1e0f06090e0405012903100509030a0f11300403050a2316 69
    0x1899141d1004590010702600c403400243e0100b8002480380c0d1040303002d00803242a1f89864a00a803058001805903110030500c1d16825a0700c40900d00e07140b0b024862100500705d80e08005050038907000000d19000c1c80c1c1e100290501c04001243c00c1000443d0080c03011340c13540010000b0052400100707c048100c2c0c441440c9000e44646000410001c442009450043e5450b589030700711142c0a2003440301a4102800498000c81c6500c00450b45640e50700101000d041400030110780c1c1640d24242088401c03c9a202d0f04050319810f00a02c10350b98020010b034184d4111030700003403003500c8900d0445e0040c0510011654809071540244901c0f00400035421104c2e041103041b2003200182021000490b4030941e10401f0940c001c002031103080e8041c0d0442c4c102e1030103505061000c00720b001c0303e441c04d01101c0d01103d44400075200344c4601014034141007212000700403081c58106421951a5507503406014400350030950341880ca04002c81e8414104004c007125007064614001056410b144030100b01d000d43d48 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 538742814 1250 538741564 538741601
    0x16090c0315080330060409020d0209010801020307030f09021327030201020a0e010809071421010b1f0c15060308070302010504020306070c020307030b1b040b040e0105010801030f110a18 81
    0x1008084d801482c4440c3c81020784030031a0b07240c0c10104002082203880807600a04400903140140e51420354450003418020000740c0e130b134600703140018100c4800380518440340e072903c5190b001585400d03c0c20400300203981400100038030780c0704400d036001c0035404440b1044140710000c03c2c10941d040d0094007030811180c03248400303a03444800655030000101d64401c16680488410000c104018034980785000c0b01603c580c5d20315240c8109190000c201c104242d88580d1a50101041360400030580c01840c41908145001408050402401c0a640010142000110748103c007081d440b00e6000f400112b41c04440559102c40314a00a8042d02c801c030f03400c1c0e20a00170440025041c0d80950340348405641d009016180c0300b411a40d400d9806400504145061303004001c075400c000e2540002400580565901140c035036280c0407514001110580010f4100401d440040001446c20b03030203a00040d0f403181c0700350a60900440407030001140c0745d0004d80303c144002c10070380b4144001d501c136600251443d80c1d01c4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 538744064 1250 538742814 538742857
    0x12040303121103070c150e01090506060d031d010215070e01080a050606040303080903041505071704050108150315181c0f0804110303030406020d050916090c03150803 73
    0x41d04031100e4500d0548000c10820004024500c50181081c40620404208242c0307140c540380300c1d0860304008030091880c0c0d03480404409202c004c1025070742c41041110103041400e841e82c0c00604c0320300f10f0500100500031031407001099030300034000c0c3c00d24851000300c01300072803802c10801001407490313500140c0031490040204400008600a50388200d002411141c50140340da6012509403200600d4803643e070005000c0030542041405504030041520b030740340c82d16200c031401c1c40cd00c004d903070254800707110701d003004104101d036045000f05e42e00c801170401d00d28440d0912408a0308190080e9006802c1c0a440340c104920b606c03c21031140102c0340f84030111803240b405c00344440043e81d000c84640002c90107a036800e0643e42d00c510b9155a100784150030315001600034001280c5103030401e580c00c9a0007034002c0703404001000684100d591110400e002001c00009040001182c4255405030504c025205e20040300164069082583c41c0504d401c1c0c0244180d5582c48032580307e8100484c0c00c1070100c41040403 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 538745314 1250 538744064 538744097
    0x3133008040e0709060203041a0c0d051210080c0d03260702191106031b0a0509010e09100b18030714040b0910052101020304050a0c0501020d02100b1212040303 70
    0x10382910172940045192a0500b52080742d20404403441110790802001103060499007800705481c0355881da1106a10346a950703001d030070414001005815920214801040320400000c2d40504001056a52400c003403204d00302241c0304040c1071b006860ba041c450680751320a0100d201c140c1c0c0300d0307000c035030039100c5200000b031040e0780c04510001c01410b41800d0040403081ea180282c0110740001d10450700810005201d94100d000d0340101003074001003400404e9584082d600000f030b007801d1003001c072014456031130001a12511800d00d030082c1907643c90003203009800980500800481e040c4010211180700e82d07269010040c60340741001190240c0c1c24075603810240d08000b00b44c203018982c5000700041c000d05003014420900510380205c800c864802c801d203440d1030001e1005502440c002c0e4041d0103105600d04062070369280c690722550456201c1140e40103426030104070030144488603d400310301c5603c80c170300080c003444900035030303111b41d02a01c55004108a455001003040728032a440310b400d0184280c02 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 538746564 1250 538745314 538745327
    0xa09031101031e020c070e09060103020406050922110a08030304050f01050c1b1009030806030c1c0b1e160206090705101206031e05070803133008040e07 67
    0x10340c00124950f0360781848001e909a0040e1005c03000c01d00845249954800320441c202000381e44a0410750000e800520950500d406000d003d0001507400d10101e04003800395480c42c111046003120342c1c40751403c00100f00002220081c800703560090002c0c0340a0380759402507450307034029503003152188560494031440001c1030144521034601078071610704144c0502c00f0702c2e000e045410301c060110301a09156842800c04e80c0310725900203000e0b80c2c070100315190910916107803807001c10312180704010b405050f0b14510941c006070603c55030300204001c4641c03200036803107418a18031203961000852038010011400d20311100c1410748800d41e801c40e295915401085601d86909004030703034024440040c455040c034001c0f540f201c8105d440c03140c0000c0c620341c1c0392501c0e1b40c82c00181c1403890440c07200045d04028042d04001c5400074000c4030019511304086140c124005040900c41c1d001b61411006150311641c039100c0c0014021940d0344c6040580280c2440c0c1680341e07074403e01480c80c4000807400400d1000348a0b1a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 538747814 1250 538746564 538746581
    0x20315190321020102040305070909060f0902090a09080c031605061e0105011d0904060b10030216061107060207060c090e0601170a02160b0f2805041103030a0903110103 74
    0xc1140310302c01c0710b1000100400503003649060030356400300400000940c040108000900c0807440019685806141c41c0059071140400003010a00740b21100016a452020b00d40d0400100c10001480301960310342051940100c1110752246d0101040300181176020403808142c0510a0065980c3c583d20a112100803051091400c400800e00000600c120350080551845c000314180307400104112001c00604282d00864040780e8403901e40d00e852405040c42c4d6108c152540c0c2c0c604056003803480202098010f00d80000b40605010344503640c0001c8001301c1c0c0c0860305000e411400655407400a410150064658800c200c1d001032400c00d400a00c7e00038040703016000d40700594034840d01c407410985107080e07504c025100425041e03080205112040703c00c516000341921425442005181025500944078401010b001c1c6105d03510899490151548681c2c000502c2c0c1c5000004403920b541c2010b07240c0401c0c0c52031007605480700140028007244c01c00501011a807103807011805401466004409279180300 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 538749064 1250 538747814 538747823
    0x4050c0412060c094a06100e09040803010e01090509060f04051c0908100605010504030f0c0522050703020a17150402030712110f03060607150203151903 67
    0x800840010140e80183c031680d0540d2401081e816240c030b415640d903204030440010305030759944285120700700c0b080140504400c1c5100d002c0e24a4143c80424202d143c0003418140318801c10b848040d02540141000715141c0030107402403009140910381040349520a004100f0400b54810000030a010b41e40500c070311880424000d09499100e29181c41d8038a68003800407941030080000c2c03180410010b019000a94907107540d240307042e6181c48061810035045003044912079040100a00941c5d03080401c0354100ca9002c101ca43c0e164469007070846007020540c01469100b491102c0b0070090342d020300c04050300300001d07800812098403081d03010b4049101c2d0900305400300d4040d2400d80d0404407010303495984000400780c0c5908550384440001c080307a200302d8010021071b00201541d0964100c0d1b100e03419140400c0c0d407204d81303049640ca0203c0c030306000c010050341c42504001200010055007607114480b02460b07440c01e54407420201040c5d20b01a42c000c10460142c0f00c900d12244600c10310318198022240c00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 538750314 1250 538749064 538749089
    0x60a050a05090328020a050301090503070210030b21010c020a020f0607150203341202090f0d0b07030b0603010b0904020a210501062d08060a0906080c04050c04 70
    0x3000c4040d611a0001c48425900d40210b10892070500c0b03003d500500c890044c164110703d030300c049104104268120b50000340c0243e143c02e0321400050310000c00c8482c1e16404035004c50754090201c204074060128128525042190216406941e48002d03502d4110b10040100034170100501c04002c90355403094000196001455001e02c0e40c0604040000380169401017881d002c1b64610090750388180e0380290780f0264410000340c01240d07004030103010b13806503c1d2742c0f1400c402c1003130503008010803c01440d45220300e45680090081007a640b480f2009003000703805030180b0000c840714182507000341e104030358000c0800e00303291302e01d002868602c0c12030341030780c544003160741c1408060b405001c02900485140300601040a220741b0500c107070410780b1040d01c1415100401c05606000c1c00a003174403103002045810448680742c00a11146c2d0a1707041d003034100305140184580c0d95801c006220107210303500421010307107005000702c0c503644042000482c106080e03a0034000c544410804c080b1b07502c202e124181c0314150 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 538751564 1250 538750314 538750327
    0x141207050c0a02041112060105070503070b0a1e06091104082109150301090c050708072010050309010b010c0c03030311040e0a0b040b01020705010c0b2d0108010b060a05 74
    0x104080c200c410003010482d8001415540030800b103c9002d10009503120022544000307071810012019480320083c40c1840c10080349984481d5240180c200040443e483c01300012070318120b40d0300000500c8075040e1104840520b00b4500710007010300703006100c00780f400c00c4007180c250741c0084100c50440c0d0302c0380001d15112900100c4c4c1409280a0840d15074500d00410501c05259914400720304c0d82d0a1200d81c440c5c0e25490002d050007150401c940e03d1050200601000c404284110183c44401d0b400c9152258035042c1008020902c1414581447e444903616442c0804558010042c0d032103020208020442d1000080c015251080c203810003d0241a80c0001030001900c6500054180d12440248909144d1200541c03c80c60300116001680d8960325890b01990703180a006414001a0a0002d41200b5081c800024a900040e820141000d41c0d6940462140c040006103c4c02c14aa0207503908182d80c503c0640701808074082c41458160742c01c1035149491494030008403201e85087c0e4881030329021 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 538752814 1250 538751564 538751567
    0x170616020709090c091b020c030c0d060e072409120b07110c0a03140d110c011d03060115140a0e010806030f070b09011b0b011a0c0a12141207 62
    0x12015012520507204e0b00c00003421800c18051201007003180c501c0c8021100340c180000b40b8000d08014882e100764400540c05100e511804e4401843d142c0285000c607603544000c0216103044469031000480b120784a81034800c1d04003a08000360341e09055900c05c000a503480d804091815002040030b000b482c0e041000c124505d0003900c00c01e890022900075181d000d41c032040022091030542e44107a4041d03040c45080309031080140030b0203030103160740e050000c0384040c800aa0766030b54403488211418040f054410098004070700103a21a0048001c048494944e1506a01d0040c0e0358640050030201d440124031860b11851102035842940c0513990350211f4000007001101d50a40183c911a0140550701050407040c10a00000740600000903a480e42c8a196a000400062210418140710184410084c000407a01c3c14118115a22020811002083c103c1e001000d84220003401c903151140165890400c01584440c0c82000d04507101c0801d458455031045103d44559541d2114004e0a0390024500c42e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 538754064 1250 538752814 538752821
    0x6080c10030506010c1b090c021606030b01020a0209130b0601050715110d020307020d110d0c0602090f0306040501060810060e04320c12010207150b0d0606170616020709 74
    0x1e0341450a0000b000c45d941782e114411071004070140b50001e20b414284000e050500800e820380100348021f02e25148200c1e0365034001c0d860741c014401003588448802e0030581c0300b0071070a140590000c090302c11034207045000814842c002c120840c1c048071075400040c2198001e000b40c49859800052411100756196068402812101c10b51a000a814040001d0002c940d20242d44100047d0b001840c100b9001c0101406841028514640d558410418240307050740c000070030a1907517070001c40940c03158803003800180c2810b05840003527007510030081040b0500c00150041c07030803101c040058818120b60705422206641c40e601800515110640100e000650441c0707403000c1c010f1400041d0140482d00c1c203191510700503807101e01200f0b54032009a401c00c6142000e10301440490610086142072030b650340d07405e542140c82c1d440c0c41240796503601d4280c6a44a030300c0c110112f00d9212404125080d210300032424140b5048040c48414420380c40000d0202030040202c411801c2a03800070120281b600c0c500790041c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 538755314 1250 538754064 538754071
    0x31002070b0406022a0d02161d0a0b0301180b010b04150c0f080c1e030301032402090a0b0a030e0606030c100c0f03050306090f0c0a12090c0306060906080c100305 71
    0x41d4102d494620600c0c3d21740a40300400e1480e007001614400303485a030028900209044041c010390b10443d01048000302000b01d081304545100408182070f03a40b09200320007002d800a100303800d03500740322061201c140081c85a950061043c00104140c1c1d8842c0407118490289003d004d0b80c4d01040709400d481d2a005203104600c8034851090b58841401e541e580e480075801058081003103601030300340b0822203030f2281d5802c85284c6c091801582158519100d5841501040390040240f81c9107e4004424aa640d011500c00c3c080c09011606196034400ea0030030b441d03000b00c903c8000a86464104d042e5070601103811400703400001d00418500c44070b941001031046844190780203002e07491a40c01c0014200300304241649000f07469494580c6001028480f828800400d403901000101d4204640800c0304426142c40002a15010850a41040040d802002900d60142410812400c00420041203420035400d48580380000d006030340d035600f001680d880b000b0f142242c0c45100302602d4040e041c400d5108590 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 538756564 1250 538755314 538755337
    0x121030c0c06090f1e12081b030c19050615060f0c100608010e0a080d020c0703060606110d08040f03031d0616030e0634020616080c0921100b031002070b040602 70
    0x20f03103102c8a04d01d00200c25400e0f0785d1055034101042d90b081ca400c0a022408035042540700c1c400500f484cda5036103444071700c02001c02c40e4a100070000701180f034842d982078400e00d140003c0c1e078503a90b40b91648515681c041c0380c250521501d00f006400711360000306005810000c442c0c1c2000300700d00030440e5030b2071500c3c0c0c005070322100c0656401d101040741039004011220056004d5140061071600300324009019113040c0041740540d40c401c40c003d40c0c5c6181c5c0a284283e10540240340c41c0080d1800746000c07009442d01e1051144030b4140303800320708440b0031f000c80c1c12130051155121340e40c0c0000f00500268180c5a5040c2c0d07060250700807000295440c142058101034400211048500205c0b1000069070320000c1604d4000040c4e200c1c3c810403840d080302140c40401800241018022460f0030032800c881c901c09c602d000d6018802686004880001c00100c2261102d208010f0303440600855040000810564020320b20900c20700300018940031080c42251030150300815110075236038513901c40f0070281d4001d02e403421 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 538757814 1250 538756564 538756567
    0x50d0905030615040e03041701060509190504050a020a06260717040501090b0c0d24060c0201021005071112030601091211060406030501050310050121030c0c06090f1e1208 75
    0xc4803c002400200081c007a08c074006106540c44208040c00c6900035045103000312417580034808105c29040c9025045036052038042004d580d2803070124100300700382c44020741082c500c00c40850314640040c012030228001c000c4000013501d0b00d400c0508418819125040480d0300c5001c2246c11007881058a80d01c640140000702da10321180d40c8598030381c90102c0f018101d980c8040383c2051076041502510b00340c203041d000345101d039410809001551003190320814040c41581c00b040000c5900a100f903004c03103070340000100100d21b0688805000d03017000e1002d1030300c3c40c00307a900004940700100081d2402107006968245a00f0b08212409020008000f000d40320340100840490705030355403400030000b9121070303540403880354946001d06103441152000340f40c200f0300305001404145240510407203852200711044201c45481c0c2004d5452564420300a00030045210000c40c031103070064900c20403500b809440ba960256900408044ca045640c4004e1192880325005c1007001e40d094080d00d003082c010050305 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 538759064 1250 538757814 538757831
    0x901120c2c0d03080f1b1c200a0f0203070c060c08041707090c020606031f1104031b061103040303050d061806031b050a150201020c0307050a050d090503061504 70
    0x90650b80c55207001c50010701c41d94101701807040c007440410f070844011007202039040e900d800c00903424003e507814003002c0e901e03994001100d01d51940282c1424981003001c0d413407101522a1501c11903001c0c0005401140d00031101c1120f6902c0001250310f0380307402100c06966a410070004031980b0341001410346120358107000c0030034184036000501c000382040e0001031529510348042c410030fa690740c201c5101503412807010000307161800b0076051900c1d640c20b04140744403440140700c0401400c0004000320910b401003408410040f84402410580d90340c500c601c4092545c03181e044541420021000e0400c0c0c2051004100180c080c0020342500041070401140c101e0f02c40324039022050481c1c00c86805552615810818446c82c0c0c00582c01128180011041050401c2c012a4041c02244a010700d1100c2c01c58644460600c01e6041d60300c511150415680eaa07446424035079560006203501707884d203009541e4080070440c0100d4046013215400341c003519043e41ca440100308054803c03200381e82c000d5140c2208 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 538760314 1250 538759064 538759069
    0x60b03010e15010302010f0f050a0c02060d060810050c040f0e0c09090c07060e0304140f061608130e0402010e01081305060a090b010f140913170901120c2c 68
    0x250b1a6242c212610b400640c518000181354948000904013032001c0c0070160300a560744102111f101c240346080184a100d95440464040e1103203d101c120054940000820304080218115018000c8010184600c0e100c1804c581e01501c203905c07030400145a0f81c2c1041124142079441254044804000241000c1002020500607401120030121a01c0d002500404000561003912001200d10005604190601d40c1311245001180c16981c411291440d141d100d035030b5001c0c101c078001e111000c00182e01090900d042d503080d03000401000601c0881d0100801c00320307101c2400307070b1003940c0507991013582c085200015545000d025100910b1030b2000707501c01000c650108400c0b80181200f840024206103035083c400c0c0e6121060308203059a810403803007041000101880c0107002c81040b00c2a009a48910148504e4503800fa0b00007803054496007044003074011a04080d003807040f800e0700c81c02403800354801900101c52407040c600001c1080800502520f2048004059a51103030028800c40e00502000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 538761564 1250 538760314 538760323
    0x622020118080d050307030c08010503060c1b030c03072003030a030b1804050f0c01020a020a1e0f030c050108010602010b0d12091d0a0606050a120203060619020f010b0a050a03060b03010e 82
    0x203e102203100002440391140e0326116000b00d0300158a88203c665041c80c00107600c50b90080e03c000100000404d40c040b448203940422800e465005084a80d2418001c00440e00d13030300440425940840c261304400700c1509035009410705008000e015601d4807401385e0055008114200083c0c0d04511004145030002d14280c08840c0600c0c042c0000780620a1b9000b2818901201d00d41c6080c119040480c001d03006071141301486c030031f9414041c02500b48541009600c1030090342c41c0c1c00f00c1c18405036803800000303105100c0c10110681c1c000303a13500030f43daa8880605a090782c00440075590400c540311003500200395001101200615607241510200d9541c4004480e1421040c10440e04a0300391810b01403002e0301031103900c2c000c0040d420035074100505150302414003100b90308842d850741d4001000460b03d50703641044481050b01d002841d4840481108001d42e103110003491800c02d0740c40e0101400962400302d82810848100404490b4070a003955214400352680840c0303540c1640d00c0e4204c04001c5d00e000d21 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 538762814 1250 538761564 538761583
    0xc06031012050105010f08010b1509120607050a0206010e012102130c0e120d02030f071a0f0a06090612060e07091b0e0108060a060c140304080f062202011808 69
    0x10131254109445031410210307681c004042070b0f240c0300200140ea151058110002207854030b905884d40c0d040c90114130b841d000c1e0310081c06140078400c1003203245038010f0082e008445190b822560b444e81ca82c980c3c102010000c0c01842c80f06980300504d00c4040d140d002a9510f032510140c00e0040d017201c00d01982e015540d0003500840031800400001c0b2650802d200e0789518102c6600003400325032404403029440e482000d4216414890000e0104140400c1200c441c20401c1003506000091400d030050b481da0301c80c181c0f0ba07038072250b0030300e48000340c5400c07207000700c40c1541c140003041e4201c1100c554581008000d080c403a0046070007003140000d80c02c002c620501c101d40194064940c038031701c0001c40081c0550519401c0358140003c01e81030042645400340c0f480280d030900c2c10010301e906100e043c080032911404540508030300c07000402242c00203000c2020074048183d041101e1185d00c685202041c0c2007002c0380c00d01081f455800d029400756126640030a9240c0c504010f0842c5251512000c170f081040a4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 538764064 1250 538762814 538762823
    0x5010515040e12030106200304150e040c050d15091a090f040b0a050402030a0b090723090f1306060f060f110d030b040f0e0a021c03020c06031012 64
    0x110504010340c181030040301d0088804501034007001d24000b010845a00040c003410080000ca0014981000c6082c0045032044543c0c808036901d6a50301c074030503070f10400e03415451400107111040200c010b0400d4020a10940f029444190406c884004148000e10020b0005107619044400010300740c9060b1280e032003045001c506119038013401348144250420080c040034203c5010600b00000b040e1844401500b203079800320301080c81e48560000a28101030010045c200100c0001403007000840003a40c071003162450a9000a490042c0c01100d0781c0400c51101c0c50740000c00030001809800c84a102a83d00406010160031034407404c0e21050304946068110385413030f10f0111014410190002c1c0302c00c0840d55280740c01c0c541e0f181c810000755250440c0900e0a8280350701d13149540c10a0342c603a008003160721562101040707807011011011341d8441c810712099000300c0c0c4044800303007882000344040c81c66031f030150000c00554000605200c0240e000030040c030f6690100390404613500c56032039228848207000e07 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 538765314 1250 538764064 538764091
    0x40c0c1b030c0e0108070915081608060a020715050709120302031c0e210f18120a2607080403060c020c1e1e0d080a020123040b0a09050105 61
    0x80d460302114000c0c0b5500083c01c50007601d0010032207001c00060041c2036440025001c6003210010040ca07220074050340080245001e148100d6034a0b000c03441549003140c480d0340448159459026011080b48242d170f9014210b83c0c43e1402000b02d403203685d044550403040c0b41c60000ac01c0d0742d580301e5186001c0741c4000c08500582001412980028000401c000f11080007030041000d10030955405503948454405040c010700c000c040000e8002c1e48100340d49100c041c41d481d0640c1e54684001c4802c09200840403903104020321800d601c1765080008401d001503500883c940038207494003a004560000c1c2001401e98400b0402084000030885c2001e04000c6101d8800030440d040d13445270103400e00c0304012946001d181500003810385038005d1068480480c1084d59031018024844850705454031f800407c4540100c04060848101305100c00200007400440c1d008000302c0000c0085407004a0180c02007450b80e40160003c500801c0c000d05881d81c010458107400100075885994080c01e60300300b100d036400d09024 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 538766564 1250 538765314 538765319
    0x11a0a0b16050a0210110c011e030c090510090915030320010b030109060911090712020a0309080a0801061709120a0c1b1a030c0f0f07060504111e01020606040c0c1b 72
    0x10824020180c0f02401e00820780403010701d4a509c01200302540100f019282c5400d94101400380502c0006000060315000c0c41000005000e401d458680c480c080106140c42244d0103441008880706042c0da905035696221030400500f2000d00e41e252502e19500341d56103c8000415590920891030084d05c500c4005c204070980b03040000c0441c40c0c4940311401418030204001407607a000d1413600e2481c0c41203c0c0184c51b51036061040b802480344480060609800081203004550070000d018125100340e03480740d814240c50103403075035082829640c040440e4030540525250002e00000b4100c800b0080c0340c9840702400075107805082c548080207440036101c1e8030f58103110380000200d2556501481020311841d40c201040343c103d80e4818845124011880800e40c6c085aa2010b002c4901080c2c00c28018005070619003440c040d00006200c0d00d910694011094003011580040e00c0c011041058010b0a1a41c2e140424800540a51400d1030100098400070300c00150b005481d01c58001c00b000c24100003d030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 538767814 1250 538766564 538766597
    0x7030c02061201091b230d0e061e06030a1707030521181204051203042c060409020105070209060f0402040e0406051305061602031b011a0a0b16050a0210 67
    0xda2511004007041038014002544105c1e80003040c1e10811201d0360261b8904154034040300070312341c0c21000341446c012101406045030722800c512405020340002c22050f03807507100405542d20a1040000d060150122600907218001d0014204440c02401d080785044480384031a042c8001642481070014504400c0c01654a40c0d06200020408210700805441c3c0100c00d070005c1ca07000d14400c81c0e2184101e1003000540003030910541c2d0040c044070350007003201c40c20b40c0c13041c84280d168030480c8260501d4580008031149000c0c010303402d500340c042e100c0510707180a5400b4840b42c1013004041e02c5e08404800c60f81011525244024402014424100200341c10300e03140c4801940d001a02c41400074220382d03e0750000c600c01240c4a50814240c1e82101c2c10503811007016801c0d03006018003d141008a540651404107040d0016040c000d089450044100000000c000050744c00f03000b100050305003400402e402d44e00924150410a0042c2e007219010710603903000910b10000300101000060014050804a0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 538769064 1250 538767814 538767851
    0xf03050a1a01050d02123a0801060c0308060d05030a09031a010305280609031d031c0c0c0b030403090e0c031501050315040501030c0f060e0607030c0206120109 70
    0x204540322090594904000a2800e82c1d0a04c0c01078415490a865460085010041401c0862880081054100d800c10f005000080b00820f440e0150300041001c0950034032440c1e045050300d5031612488680c1156860450742c0500c0200130035001719030220a00e011078010030141501034481e40d211541d0360f0540c80c2040c0301b2892255a102141c070904018400100045584508082d0b600000d00d0f2201d2490380713100c40c84021100103440686052180c0d410700d94480c0c8200380c42c07105010356044081c6450107040d5144a2140c840c5c1c0004006c2d03c0c1100c9080c4200702e040403850048402d40426078442c000800d00354001d440c03c47c00f060100344100030603400e090100d03520401c4071440f0b40c2189403100040ea20700b00010801c60400c40c0000c000307410840802c0e40d007405000040c0080000d580c503071400f8400c0e10210701411200030410400020300c94800c44001c0031a800140506082c0219070340c1c1501d455084900032030344010203005608050303030030741086402040300b003502080c0390444103c1c02a41 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 538770314 1250 538769064 538769093
    0x20916021608163213020408010203150d02030d0f0e1e0102061006080f1902070605150d030c0b0403030905100b040f1103070c0606170a0b060103051e0408040f03050a 73
    0x1240b01425911080d04640f845028020383e13407224582a40d84400034071648407041c0002c080b90f00c042804034a40030158055441901d140c60140c911211441c00c100700440c031038030002e600d82e00c903540110415102d14001d80204215041030781001d07d40ca400a00e40c103200780403601c104a5051020402513904014841e004007d12002c540841d061103002010003400900300304144241c02d012406101c010310010b030080c810303004115203800f19031030203e01810b001d540c4190701148070500c030705c541d04e0721022480b0300590540301c4004d003c55030784e0703203034450600208180c044c980d64602080c0890028040c1c1c0d06a690301d200000354110464081004540d02c0300d0755a6403140ca041c01d1448419500011250461110300f003c071071003086498070307201034070300380e00041041400464042202c0c0130029501030382900c1040342e500e555031000e0044040314411580c44410910158620a191020354105504203005541c0d251800380c42e10301580305030541d5072048030b0b10f40c0a400e940080c0002030114246 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 538771564 1250 538770314 538770329
    0x60f06190512150d03030209130c0507020f060408100506151b100603080315030a0203030c03040314010203040503190c020d0308040303150e071b021306030212070302091602160816 79
    0x40300c410201240441c4c40a1380020b0601d50b00141c06009580d90010540442c0e03c0780e0420301820036250001403003504581012801040c811100891503c0c1030400d450664140c403000b000d95030032030401e8130301a000c042c0138681c2208d4035011030b07001c0800c034034001c05042c2c18040c982e4800350b04100400c0e03d85401001c00c1d05195140620a10001d0b0052040342c0d0400e9240014a100c82e0503600040e007022810100250f02d0302c80061803440e00c0c2000700c09071046a004400a0b5100d2801130051802d0b8842220014180c0c1c0007040702000c03111109450000444032441e0a803001d021036400f05400c00100081900403d0540042008169040c0034401507105d003100b803a06040c5c81c0c0041900e50f11009820113080c00901d41c00100c0380d03001c0c1c801100c0404d4004222084070801b05144000401c032900069002d451a032340001d655141c00503588041700e6001c2c141929075590450318a80c0741c00503040480450042c2d50310b10084000c001101c0b0080e1003c4800380c00072443c0b03400408440034607640041da = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 538772814 1250 538771564 538771591
    0xc030306010206010801141503100911120a020a060f120501090501032901140301020c12070204110f030103060207080702040c020d020f0d02070312110303090a02030c010e09060f06190512 82
    0x100c041c110666480d08081d48208a08d01c0308a4440000e040641c0108c002550b00d1074050400e00b8810f0f203040103c50b5200a07103510155000781e4807070341e498844180c0d0203500418800410464144070740c403502000402460082c208660032031003c03050720380c203a11084146480d00018401d006c0e000c0c40e030485042850b98020840c0702c3c4d268096840c00e005100d035500c00501d40c030a0b8962078a080d01201c4804454800f5105c022140d000c940c0d0071034020076400c0e8011443c0070050f000c2d00f0442c40841700000c0d4940c0400342980c1c03031991410040d510108044585407014426003006840e0780c081d404503180f494010b80f1001c000c1c10002031414207003580c0d83d002e82d03010441501d034041c0c011079003c080d0303030f080203921902c1b4000352000d07500c4a00044180d81e042c03000204003c070f1640c011811350b0100d0700c01c406903200034400c03000448034048600d12035580981c000002c00c0b51071601020b00d003a0340801070300960500c00702c07101000400862035100004101c00180b01b421000d640c40741c00e03510031aa0080b00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 538774064 1250 538772814 538772831
    0x905212a0d1505280e0f0a0f150c050f0a031e05040b060f0f15090315090706021c0e040e10020c070e0106051c180f030f0309080f0d110c030306010206010801 69
    0x803090800c401a42d01609945050410020302c05120792043c000152003140c0e01d04d43c4074502201e41c803223048403d5036401207840c410068420700740500060b542090752500c0c1002450070022800760f00006282041c942d4424882060b40c2d5004111090004c1003000000c41d4689814041c3c4020001803a0600c95180c4600c0e00360b4580c0c4580101c2d01d01381c0245d40b06402d080d22100ca2011034420502d44550520448000c10b5080b00080030252041c1074031802d40e40d02503903940003a40c1d030380b441f10f0071030800d02d103801c0003940b60030311507087c10032503500003400460b0800310113582a05281100c0040c11402c2d80019103131145030701c20048440248a0140724805561526100508038012070741c0600c8841c48405d2603a030202011b82048400c030101103480280c0b6186031400168481070628100d022584c1c141c4c01c0c0a1060091295140c0340307400000552821588050000d816888405a41c1d4a1681c4a01900c001048203020700a0001414000c5a890030070100183c40c0c0700c8141c0c0281c0301a0b050081d01c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 538775314 1250 538774064 538774111
    0x160c05030a0509040f0203040c031506140126101a0c0d2601140423010603020c070f0f061e0c11061204030905212a0d1505 54
    0x112a9081c507946031040d03d950030f0000050180c003964110941d103500200c1480140009551180d04981c03003902d0300254001e994000d101990050310400100d88680907600040354000d0704c4180740740d0314580340744c680440400b6428015070030030313281c10481c00ca102d1818800c60b000c4002080d2400f004100c56070900c0c0919503200e95440310b07140c140003080741801d14410761070620b61820180c41541d844440c50380d0707101c400b42130600d0340c100380041c402c03030422000485510150740c0880350740594214405050f130034840300350041d5205030481d0500b0b2141c0030001801d00c0003c04a003000e803040e080071022042c984003000740056490088840201d43c900c11454140380c02c203003408016988142200e40707000c0c0800005206014a04421800003200d0040004040d800240c0805031041122040700e0f521075040b80c0b91907803d11003280704496210500c03240002d0064818408a60740e8031620f482014480c00c049089403c2d9040101c5084210410318003100702c1c1d1740105948084060004024406400358 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 538776564 1250 538775314 538775317
    0x9070501140d09030215130b01050604030b0402010311090d080306041d10090f0b0109051611030706050907051503010608070e1e191404060801140f100e0a05160c0503 73
    0x700d44807940d40c0f21103482c10140207010b03500ca02d040c0000d0b8038546241c103201d10300c030b011041c21044030b40b09108000814149080340544d8141ea401604c00e00c1c13556a0b50340154003d02d101007590b141e009007403289560603912288043d8640b4850741030700d522402e00c14140300c1540c14030050350110200c10448135280c1e007400122400b0703004a164021074101154101800b0101b10040e002c3c06410050001140c18082604080c0c040d820031000d2015809a0900844949900330381280160704100200400f00365075803c01c40c0c003c8041000d07141800c0d641d80009803105008005140f4032080840100f00e5182c020105c43c0c0c0c040039138101a005190702d0b00020b21000c41031600d4200c0010040260700c03890f01c07151000707510104086103005e10700d0745414030b504012203000441c83c0301c1d034180000440c0c042010f00400c00f01c00d07150002210680c503005000120107c0017024881010900080090b5085014603000e001d001d41c0440043c5904180b00d00fa400c003550075080e001440f034089d5840c0c000410000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 538777814 1250 538776564 538776577
    0xf09030e090c0d0c0309050c030a0209270106030609140f061303210f0b19050f0607050607050a03061e0e070903050a0b0718080606100e090f0907050114 67
    0x6400805594403203001e401c0500400f5580c80650b4640440c0d0800307590160700c4540968019011900e000c40404205542c58050903c02034104609101168648074000c11403850f910520f50b414441e0102c1c80e40c0d42d0300b1554a54415604941c480048000b44050b501107041ca01540790301801c00c1c00121580c16550b2040a0b01600000c01d403401080c0901d4402d0702e00201c410503c0074080c440d204044000300c040d01807044414001e43c03401c0c0e0040384526011488002c1300c050013030300d00380e01c5240c13504000304c0071504070b034680c1c01490800c40303240090001d1000c030b84562040e0b240d031030726400500310060490380aa04035095040c035a00c2e011501d442c00390f004a0455010013080c260325954214101e500244aa20003030491092200303803004c20040ba904117200d4800c540c0c504030042003203441143c0e0700e02103100d01c46081e0404000f041d00e030b00b40340050300d080360b10b0b03802c10844c05692039000c00c80f01d10f030071200c0303200000c0d804080c820245824404d250044c2024a401307110380642d443c42c40e8040c031900 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 538779064 1250 538777814 538777819
    0x60f150c02010509100804060f20130f0b0403060c0503041a0a0e030d0515010c021023040801090209010e070516020312040e01090c230a110d09090f09030e 68
    0x11089808680c414811a9000b03800a48100c1c0c1c0716005d0400641a103405550446d0810f00303040d0748845c00d685511072462248504800c8180c030034400e048a0615a002001862409080b07640c00302d10300c05c4200e1604000c0c030010a8030341d03803980380d820310b5000c42d40c05020860030441c0400a000103d01d50021460f462600e000083c0a280c682c80e90400040a0050b041c00a0740000b041900f00c0404580c8002d210f0941c3c0103412581a02d04001111821507100000b9071040f076081401445600c640c0e100315202000501ca1400641480c98103005508583c0c05405070342e449616405c11810030517425401001c01d83c08060050901240181c21402141800465a20000180e1040d5a420810403000c1d0382110b20b03031641ca40d182c0c00c49003101282405114101418a0000c0c613509105a240c1e91500c45c0700012805410154103507180941e0164440e801041840c00598011240501000348007a030182c840300c400518100c50316007600c840c0d80e5210f00207031905c038108010136004003000100d640308 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 538780314 1250 538779064 538779077
    0x7050415030206090a0f140f040b060f07150615021c050d0c0c02150712050724090614160e06040504050601020a1a04140102070c0b0c0304090906020d060f15 69
    0x8401700d1800034607a44622414402a072001405070f00c165602c40c0d190300180d0b050030240f48848184815100c41c0c43e081a04048104001c5034035501800c0a0000c0910401c411070481c0d4502858500740c488a03004620858118200002c140e0340402011101a44803069045090907264014080d03004840c0c00a18140d1105625401c1c030780300d4184000040e500501a980c400210420907000790408401252600b1009a0001e00280254180c80710154061815041004103030040c0c2c1d00d011590000b0098507460b55180000601ea501401001c007034018038070042440e0000e56040c403060609800400c0c8110008920001d40302c0c141241c0c241d0b10281c90100c2d441d1141c100407850049160303005000d512840403046030700240080c009000b98000d4030340031b00042c0d144071000e00702d21030401c0042503400d10f034030f08020104180000c0c2600503900c4c4d082d80c3c03c0c155500340302000e507160080d00326200c1d40d0008402024200d40e10801c00034204214140d54103034201074940b00034800c10405e01091211 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 538781564 1250 538780314 538780327
    0x1525053a2a0b0103060b010503090c010507110909010c0e040903020a02300a03091508040b04050705030a0809030601090608070902030613091406090313060c140105010e0907050415030206 82
    0x5070940008000808000c200324906042c0404064400c1c042110428100446444150310520540b4062a0900040d0104c000840019070b05548420743c00c42d14821240381c88807059680818151150f000a400440c4048100f0302c01005421455407a600c100d2901202e180401d50005400d27070000e034103450f40754080d03500d2110600c031001c0240002103000010042120604800300e40b1a03100b51085d15104007441d11034100d03034090388208801000041c194000a404101100441504940502c080d52007907031b26500481d00701603003100243c3c0d0202d800910040faa00301088202d0042c00714032030404c042c1341801da00e9500d0354440e1080700c003c40d8020000c82c0e5940e03503400d642082c84191440c00c2012804606c1c041000704140e00c080c03a128000c66001030101d000200440303c050460202c40c1008909100b816920000300724070035624060344096840484009100305806003e0401c1080454074220100c02d14052050b002107006034204a03905d60b00402031103061045d26411208075480783c9 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 538782814 1250 538781564 538781597
    0xa03180b04050111030f041203030c02010b150a030e100b010e090412080910020d0915151205030904060617011e050108070c12030b0f030604021525053a 67
    0xd01b00381c00c100b008005000501031195804a8034001e11a0301c0600000100b003400b0390807161603110345c6070041c00304c12607140c0010845009000800c041d0800240d11104904c2407803920070700854000015139150100022581c202000140403a4110f0789681146007a40d038241440c014040d0580c01d00030103070040f607403000c0f0610101503c0d4502c02da0864442c400703401000060600c0714415521504810607040915034203018120481211020034040c083c0352100a0300c02d6000d640041d181c0d80418400c1d0031303041c0d032180142001000241d440d402d006113507a038110102c44040e402800c002e01051002d02000a00140d010220342e001d0074041003940d5801c1055132407071001c00e00140030125160704084000d405901041400d44165451b01d81e0040c0d00b802d05590f10401c0e5400381d400040681c000441e8005440201a25100303806031206142040420174801001c0080c1210650003e6150313490003a02d0301d4503c0300c2032000c4800050700c05a00c1ca1240c602903046082c2d4020800c10009015010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 538784064 1250 538782814 538782817
    0x70e15100c05060403031401090209030705270c25050c04090311011d0609010c210608060109140a0b09060d06061707090608060105010504141f020a03180b0405011103 73
    0x181c1c0203003d546103880e2a20b0020001d003403944010401c2c3c4c62920010480d15080e100b85c40600ca0050700a2400c0f90030300c4108141c010600780c0d141c6c480c40c1c0004114038588890150540039000380868691214416002028860340145500307190710545a50500030600010b850384550300107540005d00d03006141400c0341c4e03456003490340219540c00c2c003500c110149000010000400030341805d6485503151010b03001d083e00d40324142503000441c030080354042010441c400b90303042d5454140c000384050340c0b40c03e6a401d22600b40d11204400b03959410301441140000141030380300c184e0840c100040ba8000b0001051802c0113411103028402c402d4100c02003004607401038003c0c101c01e81003209042c1405464542d12a42802014002420100e00044059002030601d050300c0d0141c460b2802c1c035051071613042d0904040300610394003007150081c2000060440b00d40c4070319101540e0280540340801d0901400810075250b90040a90b4983c408028407400001a2016218246420480b140160180710300c3c5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 538785314 1250 538784064 538784087
    0x18091104092f030a110a0c060518070605030708060402040e0406050a0902041b1e0f050a1403010b070218040210050a051e0c120c03070809011806030608070e1510 71
    0x40c0034010b44501d462900c1c1c54095441800140d90174040c0710000d0705070075a00e01a416440010461001c020301c002030041e0842c9521860b41885004401442184280f03403428940c0440042a0000300380440030f5031214405038041015034041d850719103080f84441004c00b00601c050300b90380c6c1e1600400c001c0b201c1a00518941c5400502c00c3c080c011407a00f0001e000308200c1c0c486001309224500e40f186199184070880d03d114406c0e142c14035a03445038001604c10303500c103000c003204110f021952000904ca50401560107800002541c0b41c4414051040c0710404010140000e101d07802001000010f90b5071229807000044246070060301c842d2541802c0e1142d024204a0755500f548a035908850740b80304102500c034410b0300c10304481780420030400001291051040f03421b0703113410421249000c21070110060545203010314045144428240300075420a41d02d03002040000d454850030070101e02d0401103c0c0107090b07542e400b10b8150404010051014a030705290354010f1940d0151250340310700401d41c6c2c1d440c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 538786564 1250 538785314 538785371
    0x51005100c1703090d03140402101403070f0e01180311010e09040605091c0e01080c041806060f1b0212010b090405030703080f0411210703031809110409 67
    0x455590700307600d805464208913400e01e090722500c1d07a0802c0e5244640a01d500c9100d1850006569856580a02940404410000080c841c80d00c40e81030010503080c000710300c5003c280d130790032400381440c1030014901003283d0b00c0d1904001c84104500704110304401c2ca0702c103c941c403070301c41c070103208908005850721079803100701d9980615076404010030b10074143c009520482403007094501e114403540410941e40c1c0c0440301d00002421401001400c0c1d402750904540101c42c404550f4180340e80c0710000c0c0684081103c0318185c25450300c8040204036040840804a00ca083c204a280403000703039800950800b0245010380305005441101c13100c41800e5004080060000d450b100740c92500e4102250369500c001401c400041800c00080c207a010b030203031100c0c000c81c0d000c02c000c003c101a402c208000c0d102e160900f0f2140d0000c005d20455a42000c0052800540c072030346a8403108005d0001c2005520702c140e109070036060800c4400c0c198642030508840c00e840484000150008144540c45455840c100d00712a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 538787814 1250 538786564 538786583
    0xe1617060312040f0513020c06070e030a0609030c0b062d0d1407060905040b090a050414160303080c0a020a03140c030706050a0506030106152d030501031401051005100c 74
    0x11310f5524000d444801e40b40c00b520000c5582c1c050100b2141203206480d40100103800203408a0005071254240b0080f03020000d0854800e084582c65420440b00b8229081b0042003440f80140e04000003461100ea00841c1141d4a2046c4503030300008040003204106000c1e00b01400920320011030ba1403c20b801c82180d0003040080b0400b482c500c80f1613482c5200d0185401180e054500020145000d00807004000005850141151640300c00c110180030081d0085945c034680b01e0350082c0d203403400c00441d04250802c4101c48507035891410003902009010300402281082000702d0741c4240d40000341d4100042e810702e009120b801441095804901a540c1d00c800030b4000001c0c0c2c04103021346030700518007500600c00b08000700c0e10b414041608894943c41981c028201081c484035600d4001c11b10000e000740d41e07035248000c42428405181d4040c40a20001000c01e81c4c410061060142c001500340384401450000c01c00c504080e8002d5489141e28800c4600c6660401d4010321450b201d50b24441c00c42da4400e080c031 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 538789064 1250 538787814 538787819
    0x8040c260312010614090f0d060b0d2a0e0c0703020715050304171903050910050109020c06090a0b1603061503060305190213020a0c021008010e161706031204 69
    0x1060342c000e081c03041e60000303a196036000300106074000031075401c07000081079154448004001c1c4000384031000e1040c0c0c2c0e1660b03904001c4039992100d1240b140c13824460140390350f144c0403000d240140d91035010040300890143c010240545192108290781020004107101d13194034003032400328500381c007603000003c8d0000b001d2401c1c40e0083e0814003540c041c5104200c40403e080380400700d20640e00a010110103030403442030190010a0203035000c290844070101c2a204040003020102050340d400380d0005d0701843d4006203c008200c001d200722a00251590f001d8025062603481c0d81c407910f240600700d4800b104403061103242840c082e90105006007803491716030400e60340700c02000d001085d15202c1039a04e406000340c030500410300c03180301d6003a44e540280042d40341540b011480c4002e4200e040a5800c4c406010b880d440943da401c0b0114a1459055450344e0a0b58186542c00364007900203004c412000d070704044036500e481e800c1201c2000702c240001110165644503400a442d25030054440302c207a01002401 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 538790314 1250 538789064 538789087
    0x63008070c0909110909031902030d090302070e060411040b13050a080a0213020316030f0b030717071d040b0601020c0910080705030c0607120e1c020f0108040c2603 72
    0x2100140203180070804d6400e41307020b000346620200c40440c1c0a070410002e0b00c516095113051041450160710441342010000c1c40001c0403203400001c280d01580c0100400c0000c8040f240556078810b101f42d906004811084048600e0340c02980561003445001251844c1e0b0015400309510040100602803201766594600381038580c03492050590086c81c210140002504150007140c1c040d150070210174051584260046008203075440c0c43c900740c142c441214101641d0200400c0c0003504e00440b81030004a1591059840c00d03005a000004003120703409012000c0300d184e8281c40d44136070010403500340e035030300c40e40100d080c6440b0b410480d80c804640c901380808180c09075210000d583d030700f0707040700da1b205e854130201503985510010b640d030300c0501000410001484c1991440620415041101c005540c0b60001030745410310b4059042c048103544044000c2d0f1030702664040000c08282082c1030241444c0c2c48611410400e400384015107180505078490322800d41c0383c480940e203081001e0b41e07103900c8a01c80 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 538791564 1250 538790314 538790321
    0xa0503090d0f0b04061b0905011e11030409050106120e0c091e01061d12060a1119050711010f0905100c020613050306010807080312101e09063008070c09 67
    0xc0104511b50091078000710140a00e648206846058607030b103000742c0011000c1b60301541c0300b02d0a0801c21461b00e40800c80500100f015101a1000c0540418158100400106640d107040300c108283ca083c200800014400460328210703400701602c00e41c40694551480c803840c2d40c0780c4041d070101c98041c3e0000042c50b81d4002d0000840055a00c0c00d410b148280c901000110070703243c11209807640088001c00c1030002c6e01d5109442282c40c030402c0606041c40c40307000030100f000030031408001c56400100d0400f008048c0d04103503032000d82420007509860092200030071030303c160301a141c01080d80b0408461030501802d0300c203003070a078000e02031540d6047c540421500c3d01070307500c1024000d118107000401e002c0808036101c01034030001d400541c10074241d480d140808030809088072003030990001c0081a40d15600ca8078006001e40c01c503002201601d803650b10300c12181a58002c0740044016003c100880005101d11400d50001d5183c0c1c0d40010707220705001c4020312501d03600421704040d55000040c01e0b903090b003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 538792814 1250 538791564 538791581
    0xc1401140d0c0e0d15020c160e060a091e11090303180301050109050417072619020303100e1918150b01050306040e1e1506030a0503090d0f0b0406 64
    0x90f40c4102e038541100a020320152458401002918800000c003030041195000c0c043d40100c1c10708460b600c0d8080d80340c00d201c40ca490703040300d5100d002c100100300b603604091a0b0400140411802003012821001100c000c0c0c24100400554090311400d02c00c4041c00600240c84158400500748e80d0b07904070100340c2c80c11046166200a001c0d501b41000000c0c59425445180c3c419a004991159000450483c540c80c50340800422107110039481c0445102c0c0050f03090080d00c040e0030080c810707680c1180041000392144410701d0760085500402c20440000354020403074003162041c08000407551034051094040805006042c0c20a074071740424101148215064201c0090003a8081681004d170500100151640d000d90f05001c80d00030008101241080d50145100718481800c2e80c880584100703440c2c404109400064525a028520f0460343c03040a0820a03008181200100780d58603003542c0b8151217001d40a81c042c400d10307200d400380c0309001e0304c42c00c41d40a69a00010b101514945850003070010203001 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 538794064 1250 538792814 538792817
    0x9130c0b04031a04020609060c01060801060e0a051b040603270302010c141e070201020f011b0f230c1c021b010c24090c030f0506070203070c1401140d0c 67
    0x12540b04400c0040f00e954000d58010344010301d042e5105052105591104011074075a41d695100010b400c4800c0c0724141c007401e1074400705900d604048071034405845018010304517203070350350440340c1a104030381e41201d04584840c1030106121800911800c04244c000b00c1100400c5541007a100c1059810f601003032a08420341c46007500c082c2c0d41200048640143c0500121058140754403204c01150380c409002450703c144100c0b00b003086480300c024251800d40319070340e400640d8881c4080c1c1c034a400c40c20001e401d4800d481d00c000d840b940d0040110030301d424940614018480081d1440c1c0e02803050219040441070380003042d40210a40304025030343d60303d8217004250300601f1641006150311640149920b1600411000881d04200c50343c03030fa0944e060342c0b01d4600940c1e070751070120000b007a00441100450082c00c00d07007004112420040c3c10104002c0000f07003150010020303d00015691181030302038400307404240c1c03208000200144da020001d040201540c8102184c0a0340950041e0885400103145 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 538795314 1250 538794064 538794083
    0x160506040201090e1003080904110a030b0915011b062426031210050d050a11040b0306130305040b1b010b040c12050c120c07031103031509130c0b0403 66
    0x1d445549013201d1003928040100d18070340f08104040b40492024005100005100080c0080d220035120066031060444101203900d48010340304030301c1e0248200e50720955080c0c684041c1020400000c1a07030580d1004240006002d0480009000199201380d400c0313241b640303100713030200351903800741b410044a4072500113100e4050402451400d081d20351f5907100003640e0015070410a8600341500a00d1009081c0802d202c81580002119901d8005c03030b414a90040d400740c03c020040d0700b46102c460300c0c0302992a00441c05c000c9121055200080d8555200090071040c0b10044030b241b600310f420303200d6136111185401000c28004803603490305c400165400b90070002007141c4076880d420720007038032040304117540412805d1b01044080d01c1d8035004030368400442c0510900c0c042c940c0381500e481680a0300d0a96001038041408030416801512041642044000035815880d014038801240e5800514043c0210707122008034984a90400f555801039a21040c0c500c038894035030103040015001031005035440001c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 538796564 1250 538795314 538795319
    0x80c010617100c12020c0c030105070c020a0f03170705010b100e120a080406031a040c0c0203060a06210807020d111c0c0b070c030c0b1b0d0e10030216050604020109 72
    0x3010312403424140d0458442e113038100f18000660009401411603c6900d00440c1c1128020355028461f9074805c4100b61965221000d0600500c050310500b81c01c070140c0541c0c2c2413010b00224000030340484a5120204030940d45200d03e181403805040c45400d1550482c0070f460500b44c0701350b0020141980942c0544140c545e01c8080c400c6260303144441e05003e8a40d000800c81802424426040032040f000e900704803038108060200441d0071141c06060603400103840350610b0301186810300003c1e030440904181800284e05100600070003a000001100c408980c00c160340c4100056603040c0c901164004200c2c00c880180e9040c12103506d03a060381340c00c3c0306611500b0891074003480c05000f1803c480d0455034018603642002006055640504015101040c41100000004200445c074402401120426584a100074a201034403038601d40e00060803034001d980d070000402d9001d0282c000c044c07012202d54030300038141d80d800e5000f0b00c0703041c00c009c421f1040f1091003400d0010005d9800d000d24801c1c2e882c80c0d0603a9 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 538797814 1250 538796564 538796593
    0x191d18030702100e0f030604060c180f060c1a090a14032718070302090a05010504030203030904050705040b13031a0609010308070204290117090a030c080c010617 71
    0x807500800030b600400a010040d403440c80b800c202c0e85020000ba18520740054000300081c0303442001c03601203400649420b031059040717600c0900c280b400505c45101c0200c40b4281141c01a5039140c50041c1d03410481122403034418404656803e034031074003240c014000e807400d0800255480d41c804920542e1103544442c0003081400001044400e1130700d01c0c94101c960244100303000360140806c6503895038048800e01c04840343d400318220640c01034460740c40042e552510241400205142640110b0502009010400140c1c401000310742c16400210307070005d083d566002c030544080c0a03907045075000d000080f070200c058002c9030480d8801d4030f00808004003410680e0780072160100040b42c2c0b1540200e100b40c01040020a51000340c100d061000b04003040c00181030706200f400c030700d106d80c0c0e000011040d5412840103503080602d0f0898a194000000171034a407002d4420390740e00d16018000d040280815500d014040d5610030349000250300c1000384079041d9a030004c001209100b24000416020b007510945464 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 538799064 1250 538797814 538797817
    0x5030411131d2d0109050105090a1a0c0d021303170d05101a0d111201150801080c01120f09121806090e0a0213180c03060b09191d1803 59
    0x2191481a81d40e81001544081c1550f40300c0c448000039a40d2603600c803500140080c01050f201e41c280d40000c11743c0b1006403e220a1041c20850b14002d0302c105942070190340114031080780d40381082d0304400f59540c0184403c04078410b8603640080e11803549000d80007501420031008011184603000c091100d5200c401c04040c01e4685445048c04100351100010600400c400140c94070510401000825508103240d890040e80702d541c10003050640b2000500440d4000c40d03265001040c1c80c81c0051882d818003c00c1640c03031800008080c14000c803401d00d4850201c054000840c034500b020811710000342d16141c60803034600a98401401b141000312480c403049000003c020840c2e103142d45003101d841c41c10001105d400c60281001101d10303002c0101d03d441d69052400c90700181a0103000d01000010080c640b000c0382e8007151200101404e002d41009000201d400f62070b5186400c44da86581200204008601e4030403131781c8030090100744c9160890500d42ea41c01e030f00788240c28078401a00c62004c42c41d00c05469 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 538800314 1250 538799064 538799083
    0x1b0301110901140409021c11030603071e08071e150206010303050304020607050604051b040b012f07060507020f010f0507030c020303090a081b01020a050d05030411131d 74
    0x290300382881008103561044190900040c503800c05146000d48031107850003a80d004d2581004814a01070302d20864501c44d104400b00308141d002118114104040041d0b110601845030521403590070510712485080e10700c160004007850801c4581181d503d400e00e50b80603614003175000000d15441000503a800e4100c900e600d040c1450741c06800182c1c03d550302510f00341c02c00b8000740d800440c28404007001503000c020842c000c501400013003a810300c0d2401445c44100b1074503105070155040c150b482c108c99030400450041d846041c82c041040e90126001d000b1113141c03402d00b5040034802c181c3d0001300950008002c103443c90007580c1d0001c0c081225001503401180c5030040c03200040c03007041110040381c0b20300394414403140b00030141ca2416034807c000031001e03000c0360071440650b00070b0755002400788500e400c4000808800c1c00a80146000f64685944401a0a00c40f000380040040000c080002100c2c44030312611b00107107850030307245c80300410314014902002c1a02c2c0207205048050b041c1003000414928 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 538801564 1250 538800314 538800341
    0x8120a0f050a020307080a021c090b0d0f11031006090608250c1407090605033903010c0e011710170a0503031305100209100503090c121b0301 62
    0x260950111001c5500e903210604034000c41c0018803450000a000000500402183d40d005240d0342e07404090041661008078142011b1016458003000400302001c140c8444038510340c0005945d0b0454030295010713180901c409a84110004100813800603402c072800180d411681d210460151610400d030b500e10010b444100000c41f1034001c04021490310140c1c481c5546184c5094840032685a1711028940000002a00260801942441860030520030b41d0010b1a00700c00130030030b8104090062030340c400c45c0000b0301701c10326004800081c1d06070000c11081600c10041c000b0004825107000c0102034103620304c07070b140c00078100000b141c010102c41101a40146812018010f1951509520088825040031060030314000c01441501060703003031000d1441066450000f0701134143c585401400c00041c0301801c1009441070000380030540f2042040c0c0d007861147e0601da070b076a07120700303407854500b0500b000710640c828400780300c60100680100308425254850341d111308e40c21910004160a03a03114000703900 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 538802814 1250 538801564 538801577
    0x609030f021501091107020901080105150102120a0f11060c1c05070806012106090e0705090f0609060a080d210b0f131b0e010e0f1f140a020708120a 65
    0x20180305d40c0105400104490814a001a2940851a0030409902c00105655140100002e140000481c04480a000d10207010751030386145012419001b103100181c100304803030100303403e02ca010b01d0710031800c2c410401c11903071246009202a5090340c084e06c03101c404545005000c0c020051107026040c0030300b96948400c8800d5554500450b582d03000d9112900030300488100c2941117000e00c1c0305080203000510804641c14001c0c8086500c1d1020a81c403003400b50003a601000340284180d4880c80c0c004d032084035404001c0d1600e1000a9641d070658002081030f008802c0c01500302e5420020f05c8000540728000b5540c400001000d403001c807220304403c20741003007442c203d9001a1900c84150a0742095a03000001c090b0300c4807800d0507030810034000c000085510b0004000d400c0d80c002800c000d480c5012549030095403e1000421a0002e8501b8031895000e910f00d801d03151700e401446407088940301040010b86407400400020b40d103400702d02c9000300c580200e01c40c22404e0381240003105c108001e5910b606 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 538804064 1250 538802814 538802819
    0x20405031e0d1d060c010e0708031306030c02071a0a080105030c0a05010e0a0e090a050f030412021e041a1f0e1c0c151205151e0d0609030f021501 64
    0x550300784943e0840f003c2e04200315401040070f69241009002103191240002504985030b081480c9008210b401c1802c0d5940107100074600601f1404202040e11102c0c80e01058604001906030700d00649600003640703802d0b2200000552102c90006000e2182c600c1e80c4510301641d0707903c00d168031441d0703130b16420340c21020f416014400e650080c0080380204801424900c84d841e03480548030300341c2105841c024610740203400d040b8103001d0100090700258100364041c1d032415103045c4a0030440c0c409070340b00074042c814801000b10404400032481e182c80078041d00030f00c0302003032410219070882e8005200611441640400401440c1c03810540c0e00748910079242d040c016260341c0204166041032003060100c1c2030112890100045015511000038100d029011509260707410015004180c4c801c0592044c92800c42045141035a115280b2201742d42540c0c07004a051100e60000344005c921500e503078020a0f400180c804005040c1d0100341c016001c0d41d5505100380590034102d1301e50071500c4c00e404001c100c2c00c006 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 538805314 1250 538804064 538804067
    0x4150807050d020a030203060426030106020c120102310b0f0d0b03070f0b09010305060d2a0801021c0507143907090e030f0f0c030913020405031e0d 65
    0x80b21060004100c00082c3d9039980c0004d140c844112070407140307004003a400c503002400c2080d0354901301704030b044803604643c14150002c0d038070164190454400c000022058000300020340c1154520b00d41ea0000000071840b00c0c07902d0f01c0c96505100d801d45054000e0f5800110b0301041810344001e500141481c501c1c00b20358944001c094050350042c203515000b03d000014807402d41d100d2035402408070628052715035103001d00160440c0c07002070419001d034910a504100141c20111060304440d903130000c1141f940307400d000c20740c000c92031600040300c0c561000448802c00c50f100440b081050040c450305004503602c1d900304460610340c42c500d0140004c001c0c0002080c081c6440c1047c0b0090901d60200c01303800c100c1420740714406241510340a0f8a03044031a0903c050310060099a91241814000b14581810429200b8440c40340c1022142d4258010450b01c2d280a003e00482d200ea0b00000c1c10401036466071880b40c1c000b540540300e501e00c617104910001030400280b20140144011440c042c01120440040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 538806564 1250 538805314 538805329
    0xc082103070e030d03050f0604090201080a0e03040f0f0806011d011503020d0507110601060f0c02010e03070509040c15030b010f05031308030a020c0f0f06071d06040608060415080705 80
    0x3488042c01005000d0340c105480800030401d080526580200d0743c2e05041c0e84441c0250380c050241801581008010000350341c104000075000704070104006202107085002c1c50030f5003c2e540200c0e5000750510000a101c0801c0d805010a4034400d500742d401c2641c0c0c0347c136004141c2581d8840003e9807038a1000400140b010004000104086401d000d450412080c1e003c50894808403000c50200d00404c2079010b4050b001c0000e14050401800c1c01c044c815490003014040c0f000d1040001c0c1049080c20700f081e0703144c8040c01000010000074010006a0400d80741c004000034140c00746a01c3c0340c600c1e06206032894440d00650320700c240c040e180e0303425107840410100c401340d03c001c2c42009000a00e0b01c100b0002500440290b1040e804210010f03168007080415034100303840060a416954450041c0700c1901802252050b0400f619090030f5070415030f00901d925104410881a40c0c1c0600c02080c00144540c00400c118840c08007200c080014805908104202658038010700490354448803040c042e274280310a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 538807814 1250 538806564 538806571
    0x3060a0209211002030a06081b010912080403050a060c12091106070812070e0319080f1e0703020132010e070e06160c21080a0c05190c082103 62
    0x1d5400043c3c82604000903a8003d0b21140c502035980d050402a6805c1071140c06071803000a0505d00500320400b00081010383e00e4028115510f0b08080d001c02000a2402107e00440d402416a00c0ca20014200000101400036141012034800f940b03000d5171007614030845034140e902c460381c1c0c002800c03a0418071030290000001102c101d4020000e00020b60003480546101e001d45075218480b403c0b0803810f041c201040ea20415559610441d60140051058800e5a40960310602e05903150390120b0800c1d010f0b0000b624401484550000762101410703819042200e2020000480d0040c0c460307884072429042900c8404180301551910050244091001c415a080130040c90003021842003c8002046d03a40400d141c11211421801031030204842d8082800c0100b0350441142444581e00d080114080c200000c010111a07000800400036400385d004503501e690460115026a0008040c0200060600e441500c5d41c0500e282c4c0003a10b6840000e2016604044000ca03084041e82d41880d21226000135 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 538809064 1250 538807814 538807879
    0x1b0309030305030406140414070819060902010903150b270a050a1b0504090c0c05100b03100e030a0306080105090a0201030b0a05090f100801022b0b04021803060a0209 73
    0x50742890103081d000003406000d03501a00d08d0210030081300000e00c0c600f01090703110701742d55040034024040700340200d02805a55130b00140c0100d10b00c009403004171740780065078100900c5102d04003403e02c0460704035800205151000d4610240c2c220b058080003003a00d491500081d6611a00c8001a0040d0308070341005030091100b25010540301c680c95600760500382200b9945e0300007003010500b008002c02c1e50103000211105801c058a034a030040c6c80e03245d00c4562440c0303000700d00e9450741d0303c4100580b4100400b4407424820744040040d07203903900f8400e880380d001000c0c00c0d0000c0d00780023021840c102c040c440c0301d00521410300280300200e06d981c019400f0705003868885500c400600d00c0003a458850210480c862684060500050328040700c408580c10141c4d002281a03a105010100c41115000c03441080d401c0c1c003403c00010304074910036480c003030b000300b8106903040b500108204403450324a09254283c14000c800340c5016944143c2040200d000d580c414a50040201d580003035518415000b4117030080c4135 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 538810314 1250 538809064 538809071
    0xc070306020d0b0a1d0708071e030603050f01050c18040204030b040c051203120c1c1b021b060301170f0d2d09210204110a1b0309030305030406 63
    0x690300d03084101d80210040010158640d18074011510303001c101200941524800003842c4200f081d1801003010f0010320a000740041c0401103411140501c1d0b0748140141c0b805690b00c048210b101004000e00340303c4c801110a0b2044860400036060180943c03840341c0151000e0500b004030b000d010190b44140392000300c0d0026420000030010600808000c2d20031805000c0354000c491070142031291400994030f015001c0d80040c00f08041070001a0551034001c001940740380d032190900107040d0502c9241c00b01c0c80141d9490015800b4407401e800d13034180d0300300d030b065026200c69568445800c1c503100001c10880340e112a0410040c800c50300345100f0b203980d035904001110280d002072040640740c081405441e00118101100c81400021078070543e20b0380c1c1c07103241000c0d00070300c480c0c120241505415000720b08200b05044038111401001d10065040b00c2e800400c14802050300088040580c0d01c4aa0404000f80c411801e44401b1004204030301501a4540e80e5510003a2458a007203a460308058411a1203546 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 538811564 1250 538810314 538810319
    0x121f06152705032401080a17030402150a020d080912041a0403080409140a1404030f020c130510050409030903030507030302040f030312051f05010c17030705031503010b090c0c07 78
    0x301000034040040440e1030644280422441201310010140d0140c481070b4040c000003000070703070700c1508a01c501e04040036480e101d44992000070050014840010f90702c00002c1074018034150f00095403482c000790b9841d0185079403501d5038071a4481c00b400c508203290010400082101d00e04902c0101e021034200009141002d8481d80e1381d02d0980d10a0740500700468441c5151650509280610b60f080724801030100034652031754521071f10031b01d0010005801d1102484d144139a0500034003c00082d00f01c000c000440106005228800610701920710ac4150284483c003c02c042c1081e201e05103866806840f000055861a6030803a141e5200003c1141056000d120008a8070b4200000c60040d6201c1e444850105607282200f50484400602d11420929044105d9680300c0303042c544003050350820328011401030701a04040c4034001440044506e448800030410940c41e80c810041d41c02514410507001240e00340c18205400c1e00c8080041c0390b800600d03d80400c0c8118a000700a2101400a10a4644032035 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 538812814 1250 538811564 538811569
    0x304060f0c11010513030c08131517090705242104420e06091e1209012106140112110f09121f06152705 46
    0x5000a200d034010800055002e03880b48001e000f001c1d070105001030030700240500c0da140145005400d0760054550240000c000b1000403178104a1400b070700100c1100910b061001900400c2c031b4100c0d817016411400424007280ca030700c001081b04401c4440c002c001140c0448803418061000c400070482c502400c01c04c01c000f501c076075406100113104040e9203170080c0e0540391604164945200e00d03510185204200034072241d03c03a00b07040742351490760101c00035000f50100103e05035004184032a000f010a20030002080000c0034001022a034000356040c04802c2c1d0881c9900c3e40ea901d00c9401070582c02c0c0c0c07806009100140d44a4000d80f218121380120441d15190b5071100743c0d08803640760b00404100b000001d041b6255581244000c4185851410200000c4c149480046070f10300902001c565408000142020b0b0381e03488403a8061515288003e4507002c441d0035060382c80501803c0d00d1220b00c1402d003032000920360b40c0001611071a08a5441d040880784070f2400300c40140e046240080c9170040781c0342c80401c0a8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 538814064 1250 538812814 538812821
    0x110403120f20100506040912030c0e060c1c1e081005040e010e0d090311090c07150902130b0d030e03010f020c1f050408120c04030f0516050103061a0304060f 69
    0x2400d15001804500f42c2000342c14040e5580104114006c0d8140440c03140000c0607900001d0340301469140004000e040f440044550002145aa950043c400b2804000e5070790701003075400f052402c001802c01260f1074414183c903030000c110180c644044480903480784071405a021a6800502007000302c4201d611507000070304440e00e030980115a41e644a0700a00e1030304041015400d0240e1600f0541940c0303165903560132806d0803408075103014040722000300d0b8a050904050707401c8682d020b440c000c6400f0316500080011f0072450b00c02e078480e00c5186110300300b80c0c03c6407091502012000e0002131400c1c4480d1015103500882611860300741d982c0d0031440303c152040c1d00c040c004d0700080d0b00107881400010b64101c413603040c80034560100d151a003802e02c800070700340b44100c1c0c64402c0d04008208103952420181e2000303000319400607000000f42540e14041182c0840d015400d200c88240d020540703030b100c03801102107455501070255000f21107005c0d0102480000c1c043c40e8803070b100d00b1002c00c055031080301c1041034 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 538815314 1250 538814064 538814117
    0x9020a050d020f07030801051f120e0d1e0503061e010c0813030212030301060206070c0f020603070c06050a0b09060d0f06060f06080106020c03120c0c0406031401110403120f 76
    0x21201113001d00406601012050040408032746206444160841041250050f18000c0040c00720314501a041e2210303d4202e81220b441c0d501c140c071001410944081c10764841204440703004013000010b881101d0145080c1c0f4002c49014000d05a405444508102c1c8081c90344461070502c0f44c6211000009107040c0020102076200c0a04000c5052135407044c40000342003032072001c82e50b80084c80184521603002421035480203032440c00c02c0b10a2042d083c4201c1f000304031a006034003c44000100708442e50070101c911103040c80340600308030654404103003004031190f03954413580c0300f8515004a41d8a103400552060003178050800c3d0005c2d5035040c1d80301401c0703c0c2607602c259841c01c40340310200711564019400600410307560010340f186091401c0080d48584008000006280300440c48803e150410444280c030100080c000f000400c1d16414490085e00b002c581782481582010041e004030030742d28041e102240c0c0d020f03407542c80c08200c011040d1341c8a008441c00e0010481c1e0684400e0707000740d42c24410b450703 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 538816564 1250 538815314 538815337
    0xa02150115023d020408100e0a06050709150822030e010f0e1f030e030a020606220515030f010c0e1e09010e160c05030a080c090411180102060f0109020a050d02 70
    0x1d40c5c0385056041c034103080b031751910400070910b0b11002c400a0040481d1000046034400e500081d196201c00301034940325019040b200700441940e06e00d804041c1c10520b4640210105070704c1c4111a10180d1031041030b0b2004442c010005400c82140d10184e50092058600340301050074500752448441c0e02144940a001106280c040c0c440a40c9070b0445415101e2a40360900b004095498a000310b0340c040c1d0b0b038480188c0302030b00640c040402c1030079541c2045401c01c21080c250809101c9820000110014248203041d694424000c611903501d91440510583c0da00081d5500d40542101c900c0042210300300895506840c0122008281c0740340c0c3d541c1c03902d543c0c041c1c100c2440d006038904028080c00100c60001e8204001d006441400101007107000040c0d0b41000b60a00d480d0415035940300c12150035000c0d070f01c0710580182c104074010306030021140180000003e0341c001c85980120840049a86400558000c41841c18101c010711803115680c0080041c0d5800b030404134a4180300780039641c00c03030340000f20009 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 538817814 1250 538816564 538816567
    0x9050a020f0904050604080306011707080708011e06030207050102210a061e050405130512070302011103071b050a170301080c0a0e060f04110a02150115023d02 70
    0x3146000901e05000341c000b91a0b50800d80340681c0e90030342d61900940050310240c404000140c160703118142c909820314107240e48000908190700301600402060f40c2520204003680004a00d0b40c18001c00414618180a182241c442c5804020b4000307611001c0190307610754003082024608006a400d805960007150090390507440c004100400300c03180c6030025040c18050096964040004035114010b94008440000ea1511202001a805d44c0280c000500768054516210b92181706030003e060030034040c1e0001c3c00b2a00d51b803808240948422907070000481c2050306800140451ba00c90340c038000784070b081115030010954450101c07071808514180e1619000000503c0110750a21080085550540724200420309222030380d82c0407440101854040c0b412072007640b019541c1c80e000707143c20a170b80034040350350f6140c43c0c60001d4480c80c42c003103801074420710340c0000200781e5000040c5c00070605207070340034107000d0058102e000c03d41070032960041c00080d16484085840c4900c0200c82c4480340b4200c0c0c005 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 538819064 1250 538817814 538817833
    0x4060b12070903050601030201030b220518030c0a140a1a01050a050409050a03080c0904061d070207060c06051e090c0901060f0c1b03050604030324060f03050907090905 74
    0x460a1240c010203400400800890810005000183e854150b80d070900700441d0028012001c01e6000809a40049204600e0302041500160951103540030740000e03101000e01d11200d25240d55240704403480c1c805141e1110781e50b2000303d440c000080b000d450340c0000381d60144c9116114400312441c076542c6e4050312520800100a40d250401441c00140000c5e0703400d110f0404242c80d06510790100b114080c0500500400040380c4001e0001240e2003100001c00070040692a0f0340012407200c480c0d900601704078410340101d5282c900016644040301c00698802c02082050740e00e900c041c20000d00200c4550782130380e0415506440303001d0030601c00d8041d0802062081580f004104040c0d0040e804078051018200d1b000c03020030790000c64140d820340c0040034a000c0c1d07500d20016180e40d128903440506180100c20a00c01055499003100d402c003031214409480034020f18200c2003941d04648296008a00002d40114106009820043e4041441c07030645005075680c0c40414162100e00f01c080f41d540d00b1241a4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 538820314 1250 538819064 538819087
    0x6040c06090906141509040f06050414060a03110105090a0e070210020301080a021e04020304080c07060302121f05090a1d010b10050d02211501030908161104060b 71
    0x4603000304004001800f00601c0c19104000246588407581e014022179030300b028059203100115004940042d0082107100c1d400e1921000928403400341c2881942400c60390b334811584610344502a0b500105110019442c40e6521a55600f24145032810300200784203001c129546e49070000c1c000c0c079040f0f6803d000303441c284900a0410b403000700c0c00c50540344148014024004002240007a880c0d0580300300d003c41d034203000c842d0103055220115552150001081000708242c140c040e05103a20700000701c886190f1203034002c1d400d0740120100440514441000500e44520034401040c0c0000c48e101b1065049403102e01041d00d40d40c080b5100c019040e02c40140d40c180b42c0d04204101d10040040008201c02503101d00014905410b284803070b007c005010503111805030f0300d9412588607034003914124181800c03070900142c80200407540b2002030460496401c1c1d070b0303500900540d20f6003039010170a58505606844222810113008100b920b03081405103080010342c03614840d00c0040c08a19041a07201c00c0b00031103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 538821564 1250 538820314 538820327
    0x5040311010906020c0607080d02041203141801030506040b0d0302060723030a05040c0b040f0f0602010504150e071701050906070c03020703062a030902030618070306050c0c06040c06 80
    0x210346040208201e01005403d6010528601244045134a80e0384c607100c03414910054010900f40d00c1060b4400240000ea00e0031442001203a18402d448010400e5084548180d05e80107a1054040c80e03452040010410361080d400303142c2c0144028070000e41144801c1c0840c0441ea040c0c030b003c80169200c00c1c2400138081c0c0102030191000304461141d12035180d01480071600e404003030072803403115032610041000c000308480224080c084400a441c1c40d1542c071760f400c204034103a500c180e11100b2b1800401050561040c0202c43c8941c0d005203844900103114000640144401301460000e8003514101007549501c05d80b0044008682e03000104081c00e00c21035842c2002d2001c0d0000088c0320020301600006030300800c0c59070440e60030000c001030551090035100d40d0840d20a0542580a81ea804080f060b9905035001c07110140c000c2e001c42c3d43c070f5a11041e0403a41c1510b0590300f002c0326801030000704002003140d0421648003485c0e0306224101148422200d02c7c0001c01c0c2c9003103684003d05442403003460341c03050 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 538822814 1250 538821564 538821593
    0x3130608070309120c02010305370207050a1506061407030f090902040b030a0f140a0905120f0a021002160b040507030204020c0f21041707080f0705030f0c06091e030d050403 76
    0x2d0b6201d1f20401178100000c54007003114400b0104564ac114006100041503040d10042c0d500076003500d1401560703283c03000c5c0c0601c03401e103400c20031440e0600100e0441d101c1c9200c40540c5111007403a80c81c1c071580382c0741a02c0440890752140d00b04003a419021030315400d02d0000d8002030250318212078a034204204848107940308200303007251140c60000c80e500140396420a143d00901b400400180014107420020305115900301550404c1c0000030f201082105200300408800311150300b03071802d41c0ca074200e4543c1039200c3c1155a0380c00414111200f80490403a4030461f410612510803289102e82c0da40c08201aa0005903c1c80d482e0b402c80103076007800724420300a081a0200080169150740d00d800d450400500039409001207040002211183d4860100080c40c00b03000e501c01215a03501500c0750342991040340d03000c1c5a00038000c0b400300c5074990f08002a4020902e200400003410180312605000f0325070503655280701c007160480d4102546440600c074050302c10140703680c0d0341d0f6120b080d410081074400111 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 538824064 1250 538822814 538822831
    0x5040501020c0d121214010e0f090f0607030e0712050312070509012c0904050c040e0a08180112090f0b01060e031f2a020c0303130608070309120c02010305 68
    0x11002c1c03c0000c0c4084007409004100b810000302c000e65504070b030b074024854192000c0b08403e06900110340108508a018450381c1d076801110301c03655881c00020707100d54840304c035a0920703400000420a29800381e085279040d01442d0048400d4a03946880c1600303822042c800075585600006000e540c1d4a000d10b8800758841258101203240c201c68900007001c283c0051119003109501c0000c030760500c4410020180c61200080000503203003010b0074070755101c81c1644c00d03041c41240b5244050035148004900c024189400000c49800c10950312482d0460203078401280b410042601c1001411540f1031041c200d544c1d018001c04c142451440c54041020301e01078020380c042c003110104848880d540042c0c1c80c1c030310b08038607503501c0041900202c500c00580703032584440101246038201c101c10180034a406130300c0380c50306600b194100706c82d50b420f0544910900a4401a001d081c0d034050080c0c0307004031001c6401110b07a20b0300107256415501d403802c0300086404400300180e0341c0300c100c00c15980d03d800b50507048000e8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 538825314 1250 538824064 538824079
    0xe01030201090b160201031d100e0c040e0a080915041503050c25080d1a0a0506071e03020a080a0f0e061309050c1909090e010204061b021f05040501020c 67
    0x13071030911201110070b00d00003410140c890b541f00c03001a6000b28801c412115110450340e51000010b05000900006001c40c0c0c49403241e10030841c45c500c0c2c180608100520441c0140c8001c290030303214052982d201061071504407420110002000c0d10a0005100911207000001c02c5003c4c02d510040036100081e00711192100140311101e062030b003c405003001c00030100d00d1071800700703418030f0807a056000750030b04000600d03d03141c92204510b01c9544041c80307240c0110f654502054441003001003030702030704034084e00c21070310350311070050340144c1c82054820a4000d00407200500303802c0e80ca000300e80d401001c140c000501c400303040c103801e203800c82809030a413082210340070b041c0688854031500c000d6080c81114a000e8a4102003014520b1610441384822240b04ea40f501c02001d4070b01c050250f0041c4d12078000601d18180114004543c10f00c00d58054400594422030312890044000c1e280407406141a45d0185100e041c6c01c0c004001c00090b624190340c2c684605484a20308000641040705901510f80540318 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 538826564 1250 538825314 538825327
    0x90f080f130f0302061210080f0a02031504030804080a0c0b1005010305160f050a030f0c0201140f061e01120c03061404111608130f140303090307170102070c0e01030201090b 76
    0x5c4d80e2040c0c956940c0b6000311642540d170780e001d000c020741c500c1d9070055805018a050503154420045000b2000d90300036400c680202c82e20025070744080c00111009030000309550042000145440000d0800d44198a01003031424240d46412140d804145c9001810314a104000c202c01d5805014469010ae0320780010040c290780c98002409990380c40240c80304101c0c2c0040c0350b407229030080e4051040442c0703819080050a100d200040d00801520f1400240321046000162142c11020586480703100013401001f904826180c40e810b111001e04000ca041c0103078010071003040c1c6050b10030030003005110b50b00807c01c1d6180400b03105c1c4400e094400c96020384d062186190105446004445140c02940300100e0003520300d0616132100c4c0123199188110a0800d040000e86000d0000c0c3d10051341e00390013244106d942c902c1e04056680c450100c11540682180d801004105046000307402e0881040d4005031400d10140e44014241005e80c103c401d500042c0d1006100b035583c400d15160180031000380d801d15001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 538827814 1250 538826564 538826569
    0x70804060f060b030f01030c050d080a03050703090f060506120c0603060f0a031b08060106050406020d12020c010906021b0316111f0c020f090c040504090f080f130f0302 74
    0x44010006052292500304040101410754002070091441ca204151070b030410b1421089400c2c0288400d6a00b880707031801c08691480c0030400852203582c014031261502c6820340741074001d0100104400145642c17071001d500400c1c1c1440c40f50807101c0c4180000281840e00f6010400d501001030b040480f16845070344080030a4075140102c0707800510403149c211a4990080014503514901c5d00001c010303c81040d8184500d02450050400391103c98060301e00340c0e0f0f00d8480c01c841c1030041344510030045c0d03c500020b0b6203150040c1601840f9940074000946800030f40b821711400d49c0d072000800c488895002503d41080342c0d182d030000410f820044040c62034a54454040091102c05150241c407803229140203103510b6030b44101c0201010222004041d65400c0300401402c3c06000d00d07000d81c0036035402194504585800109188174592022a4074106400c105c00e11009141e030749011038041c000c502d040400318034004050940007491041595481003d13000040300c0703815aa1080120b1444c204050005a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 538829064 1250 538827814 538827827
    0x3020903070e13170c0a0b1005010c0c0b030603010e03130e01090501080a080c0309100815030a03080a020a02030c0703062a090302041128110316020f01170a0209150307 74
    0x2141c1082c50000707074a100500000e145c2c810f08000b2005031264002920400c0250b0803181e00ca1580d100390440c1465441d0300660b10a408020018200c91500300f0620a100507600603681084000d4000102c0c0701d40aa1118599805180e100281c419818002c00c07091014a44c40303405001c5803035050100b549010011941c81180c4100140248404265803e81450400948940001c001d00303800400c1c070300150291651100f9a45c1441000402d900d980060400003070600c00260305035034031100340c0d441d094110001d410150040003140800c0004540e411810030004002d14000c100000300310443d0401c01100c800903009400100e851007010008064200c0722100c01c482d019580880c0e030b1140e900725202c1c28840d070b1002c051407407160441d01e9500191070038001d68506060312080c40161280c04410341c0d0f0b001d108030789029070044011550040c00e10807450011007406040601d010141c004c2d685041c80c50071500100440d602007441029071400b41c08882c0d03e031100d600c40714030f182400c60004161 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 538830314 1250 538829064 538829101
    0x20904030c17270f0622090501090c02061512070e041505090a050a060c0507080309011e092a080d050d0c08240f030a030305150906030607121b03020903070e 69
    0x10305d00100e080d81000040d1601d40700c1c1c0f100920340000c0a1038441c0a5103000386800c0c05070100f040c0c5045000c5403d035000156a501441501c0303845280a004102045010010302c4400801805a000000780c1403080e1034603203004510038288616001c3d043c154200480d40c2c020130760f02d490b900c80c46a41001c11400300354110722542100000c102c0d51120300c0c0070f680c1841040c1c8000c0007042c00000f0015480019803101440315a0305881072016807021f0300d0b00050300e030761400240c4888030203004000059084100c407802203941c1c5400c0390f0710030741d5001d07102c1c00c11404a0381c24012a01c00252a1008413240c400c2e41c4d03002c012802d1a1a15042014070702e1070031905170094040307a43d04210301d41483c1e55a1900710020503401400c40f1181003003850000e018200568101c11280e5804a005029240200b28640710b4040a001080640c1d1094011142140f0641c502810503540b403c20309506120000c000d0025482c0b51400360ba41c54407581410300c0c00c240c90740050038041070440bd01c1122143c246c0540740 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 538831564 1250 538830314 538830319
    0x3040608010e0c070c0308070303051b090913080a020a1b0f05240c1509070e040b07110106030b190605030d03090503120f060a080606030a020904030c17270f 69
    0x100c07075071203c00c56a0103218201d406802d480d040034000041119440003446464869901071085840d8a03075198581070501100068500003801049500d091049241d03903c10214008400b9200c200c0e100c1c150183e10007889000140c0240302e6440a02c00c2380302010182d50f030381d00301c01007815191030042c0c89108020b004061007040600c48124042054408942d094401905400d80c1c540060b0a415650b8002006414802c14000002000404003141a4045072864101ca01442c0c0c0c0303540d02c010090030010160018800751001c1401442001d21034840914860440388011f8280301d8914050b10503560301007170446050090030f00039620007040714242043d41f81004206911140b81850441c0a40218400e000302003408000000c0e1120071403501650054071400c0215881e031901a40b1140200d640c1d580551000d0842001800c01e0b0141d01c0d0720078008c0ca0311100403242c40ea504007003400c0078428490b0344ca0740490268081c13089125611b00c000105410942012070000210b01300300061040c591 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 538832814 1250 538831564 538831589
    0x10e130206091018090b01020c011106130c080709050103021201021905031305010534051e0d0912020c012d03020f0d0c09150c060504022706040b01020304060801 71
    0x290341c5406000544c1020f074030701c20b003485600d40300c0070004024110014154010b208160b04940d0a50080202000d51620381b0042c00b410b0361106203600c01d41c51030784801c48a1a030003110000d40c0400034400311015024001020032194954010401c00260740d400c0036840d40d20400c9400124601c5196641003c590b500309183c895540c0041c961303c0101c0e12a000d0495401c00307042151900c8048912240200d00103040004105e0070300d081d84095a14510041c0481e00401c1032900b4a0302044003070825101070721829140c2249000311405803182d5034000c030380b00c52040e8604907100d6010b200d04d5030300c4074003841c1000d01000520b06128289558501e4072030b402501151444aa600c00d4040b00c03480004440380503625845100c1100c02040d0000e55140054501100410308100b000310b202c9500405030f940500400840c0c95001c010217003d40105d030b000c0801c0001428043d81c0301c400d007510700800d10034a0706524055080c001920320071111a41190010007087c45440d0301b1421040c15101000c10b01c4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 538834064 1250 538832814 538832839
    0x313020904030e06040909170c150a0b130b2806030216050d02100507211a031603061104061407052805011b020717010908030906010e13020609 63
    0x90300c083c14030102060304680c0000b00801d10b00301a42107000c00600c100603002c08601c0e40007444405014a1020706040d4000300d000c0c4201c2d801c0e00b01d919411218400c00040c04180010024040c8283c64180205070b540340d5250403484e2611010050a1180d49403514a01d6200d54000c489819103e004001c281680410010016000251064a0180d100080316005241064040d503102d400100d11088035041c90300280c0c0413880341c08040034400007011040328080740c8100b880d0180c50040d1507002032031074801e0107042a0f5000c0248094086c040d50403a483d250460411200796840c6d150046007040c02000104a0b0a5000c4505120045086801900c4004a28102d400d001c007802d03c1002140303480c40c4444c1c1c2410180c0b036a030a124883c0c0002c0281d03080c0c5840010509400486280160300070f24410805910040d110141c0442110b0000801e01e0a03070340c507000340d5003066906101503440300005001003203150f801c0d00d4002c0c0b00d4000c0100c200ba0340f03034001075092084c018041c0c010201f50612 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 538835314 1250 538834064 538834067
    0x120c0a05040c09080d09150c0528050d091e0b07030c020d080c0105070801080d0c0303020f040e0c040302011704080304120908010216110a05060717071203020915031302090403 77
    0xc1d0f020b002103c090300e01e0101c3c144001030110000340a00c0c102c034007000c2c0841c1070340d501a000c50024103500802401404080030b081e99000d505030030304120106114003080300018801c1c080b28481c5140c2c2d46803c4141c50a00d4015000c0c9410320380e004441c010801c0d000c0c01180c60300410b5518603540b600e4568560742c40e0b440441e2101405130070050019a01003001c845000064008510501959075501c46507a660381c0c1d880c1d034600c41003084001041480c54003602092190700248184401d0bc420107280a03a100a4400000d608548070003c259001c40e0902c1150384c800c070b185da201421916030101074100b54031115240d1101800c018038507070400e00c071403405600444450004086040c000c40d00e03000c00130b12040011824100c101c4480d0881d010006d06840c1403003060b81551000780407a0b04280c182e0355081046845c841d402080e40100303000ca480010011104e056840c407160741c02584603061182442040074920313011900c0c0d010140f0802070703d8800e4105d9007221a404492095068503107040 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 538836564 1250 538835314 538835327
    0x40504050a050a0f110a0b07030e1c03050d150f150201180b0a0507030e0c0603060a0e10090c020607050f0310180c1d03071a120411120c0a05040c 64
    0x1000b045030040780f0000c0207116a903000c1a500e207000380101d04c4403a0844003044200c61990045444401d018050940480d20402a40080b00f034042d007069041c506102c0401101c3c0d54080b400c40006a00142d038065010090094042e0881d241006030000c4ac00d140760700301b071500c0354001c4c503541c8011808140003051007508407003d682051002c050803c29141000e892031841154914000ea04ac880410400d0380701c1d11400e0300319803020b009407003454240000c01040d98000f91140b54014420100400c04124042c0c2450141104200042c0d505240c001f1440c243ea10419040b0195000002000310749500601194081c1400007800b9aa80d65840c2e100c226240e02a0403d070441d0190551848252003180d001c0d224603805521022176601c00c40a2500152100392070003034154111040801c6410f0071443c0320308041c03120405490504202003401000705004031002d4611740200303019903560317090000314013191881e00c0000e4440d0018410115034001c00034440ca41c01280d8a81c041110588100e4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 538837814 1250 538836564 538836583
    0x11121070210050703230105030718090212060403180e161e030608010f060f170f0d02150105010c03020a08030910091b060908060103080a111507020610031104050405 73
    0x10100824145460000c0081a04002c000051080c1500781b810500301d54040c80c0c101c0d20001c0081c0b02c03a609200c40800e2240c1401f0b4020600d649801100c80182d9641c0074803056910040010080c51800c1d040090601a040d100b84503400c11140c401c0c810070004180d0035500004103200e0031038100741100f040f10700381540c0c580c804a41e4168500848502e44c1070300500111464038009004851442d5007040c200d80d160f20480070a100801400c00c00001c0d50356856109010031015650040105a0083e0411212010980040c0c00610241200e80c0e40e05a8244c0034020a00e00086000707900d0b40c0195a501c1c018801903c20107000c400207851807400c104900800c1103105051010500c60314140b000005000b41c0e92003000342c2c0b0751300401c485101d007007030b00d08540703402c801030540da440d50710b401d8020b0380003081000070062120940c0d2802c10003000362000d07400b001c4140c0e805624108000909203000a00010104507040b1800c00100316003c0c450a20030f0000ca030001202e841c0c610b01641b5250096 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 538839064 1250 538837814 538837843
    0x170715091127011d1605070c0303051201060809151807061101051803070b04060603021206040201091a07030e0303130e0f01061419120f0204080111210702 68
    0x600301260201c500004036035a80b4007210910311241d0f240c05462018100c2c5503941445400980c0002d1258001d003000c440d58030f00d607818124540b07262030b1600030b005c081d43e13007050f4041030740001c0e0b01101c2098a00c603280100310782e1800d003030581446c2c20a10703200e9115070329a55120003000301090a00c0300302a0b010019040801c12240c0441c1d546130040c184143c9000c1c0300352194605000181501f9443c005220038407003613009189031200a903140b991090b8040e0040d201303640d03948000310040e214001100e0f6114046c0008000d0f5240a20005040036920340205000650307200c2007481d01181001a0b508042c0c2c9400d040d00ca00c0c207030308003191660048803207139107040f40c0b64280001c1c0c181d002481d082c0912040707030142c0f01d42c0e0b80303518050f2844545215070450b01c0000300560401c1b505c02c0b140c254860f08651038804c0081a00900240a58030b00f0005400001d6000804002d90b1a00344241d81c1e010717040030326a50030f010f640710b416040c203100300b5040b200321840300d4000364105109201600d190800b0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 538840314 1250 538839064 538839079
    0x614030601120b0f0a06020a050c030606011e021002071a0718090218040207030509190806071b051b13090b070e190914010e040c060e030c040204030f1707150911 71
    0x41b400020350300e085150b1306651070700858885010f01e00700411498800d1206854050482d074102442c4000d06040005410441c01040f4049085104500041240d180589031840a00001c1e5140c01c040700e20281556043c0020000c0310350301c0900d401c80e2101201e40c03600c40140c4070f082060410a60000c3d0504056001d4030000345502059000005402d50800c1991003680200c10303103613070b108000c6140c010954107070310007000140f619104070401c9080440998005c841c0780200e0b940c2ca4a41018103a10301400c885141402a640c1000500880c12100124050040ca0140d468880110720060004e00401c1807501321503001e034540f50070030041032801c2d41000200f281d031050040c009010100399039102c01c04520002941403014180180690342051800108910300345040d1080103490820b546c05004459400025585a01c080e000450140f40c48601d900740d6031030001c035401040c429a5446910078840b240c0801c60b0780702c003100d46c1c1601d000000f0380800c540c1440c40c503c4c11500b207402d510060 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 538841564 1250 538840314 538840319
    0x203010314060105090c090618060309061f061e02010b0d080306100509010203090405190204060908100e060121080406210b010e22050f010614030601120b0f0a 70
    0x51948007481d40c56084103a44203642c8500812035841d0f030695081046001c184189003442c5800801085002100c100c0c507a24581c40f00003241315074004407500c81daa41c00400c20440c10540d400070400c3d4241011a015207518208000076100c000c0708000549243d80c0c400304565020b0003544400202000205a8825841e40303261041c196801208e0042c0518603400071400464000c00542d030300c2c010140c000d076040110f182e09201c010540100b40c0f280c81403508640316030361580f034030050010740305a40d1404107050800d2100c9140c4821008440e00c0345c2e15000404e10300302070202d500350640f1103090401c005403042101001c4070014585018100240016001610540140301c40b25407412540c10208400c1140900d101143ca0415685003c920000b4072240c0310300d0132890f4001c115055101003003501c681402c00f801202e40485095601b20314520040c0305154100d12a1a01380d070740314080303a1540c508500020300d4421074022480000b80c030390034480c910b5507d400011030f03400409000c0951080c1d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 538842814 1250 538841564 538841573
    0x50f060408040906080c0108011701090803090a11150f28050702041d0c01030e03160308010602060f070e090a090b040b180c0d0230060103031220090d02030102030103 73
    0xb4002e03c035124029207006400140341c100070850300d00000f0140c40d5143c240c1e182610030520307100403050244655690341d00d1000001c2042e40030318082c1d00a90300078036140c0b1540c0340c0401329030200ba072014814902901d02d04100f202000482e80070f1784000c1c10707032615075150b444110b03480f500010b44140306c1030011481140041d84040502882070007100c00344550244d058840d40030038904c02041a40b9040500c04600a5000703800c0f8507001013030350007241d10306801400a203000c5441c07640210009500c19004101041d410482c407500520118901201420080800303409019929030346070145a5460005d20041e005034445450980c1100d243c40492405250001e02800c1c111510020003c064035030307400e04000040c811180030000307801e45e14004459020800d10f25510145c10101100700300301c07908000003c0c40c01d008a00c88200050a05504524001d007440c048000146e800a1410a10461821440700b556010386903000b100c50350b80300004045592540303203000194156000000020410 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 538844064 1250 538842814 538842817
    0x40f02010f090e04061a0108070c0204021806131508090703030f0e19360f06080a0503120f0f0411010201060f080604020a150906081906030807020a090e031204050f060408 75
    0x844100706c4120091800c00e005407245402580c140380000d001c98a08401410079500030444080383e1201c84440c481420009041d07030303100c1400300000806180082024030b040448991800d07034142000301d000c0c0b614450711540d0304154071000d000c1008a410f519002c0c0d01402d6160a4101c01400702588080c01d8201214041220b10403001d02682c08807012590503c4030f09006ea07004e00e5440f60b0034000c00d03249100c4d00500419184601000d58400000410f80e404214803182d4901c104060740d00d810f1000c49101220000520002070304400c5000c02598000310122903500a0307001e800c20701f0b80c1c105800100e00400244c0c200780d000548003900403903020701c00184280b0591003142ca4000154507150ba030b19496617211640008141d1194060001a0240310300550000188005000740036820700110160340d01d0f90300c1900e002000148440030350405604940151261590500ca4100340034401980c92003081c031441d48200e0340101013000c01101307014400490541e0342c1219698181420140001d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 538845314 1250 538844064 538844081
    0x4090507020a140f150a0e030a080103050105010b0301050901050d03030f020a021e01020f1225030b090f060306061e0301050c0a0207090b01020327030a0c0f0905040f02010f090e0406 80
    0x20b01c01803500303000504000074041305501800d034060a0b20328441480c0c8040c01e14003800f4104015299060202c1c1d6080400180113100202da4841e22594998181075085460681060200985c108018030140d161880c0803070445070144c0700c10f1207581981c20704400800e010003a1114290000031071b003580680c0010760508034000c1c4108100300700d854024840c02c030300c2001c0d42903681c141c0500c030113030032004112103083d485414001e00448211403c11008841c5502c6807848000c80d58a107900308860410419481e40031060b0101c0100da82010000a66203100007070907240302e0182d0321820104a64041510400110041c3c0248030f01c0c00d03c00c14500751034000c00c00e000010b1041c40c2001942c1a1310303003d8211a200103030042c5140c108009654480f1440303024828005001c800500d481d29101003002034440da00616000714242d04003011075906041951001c3da00c50b09050a01020410031404140c0d1294242004058010580c90650710040d0641c0300070381e0914804108030500c2000c0d0018600d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 538846564 1250 538845314 538845323
    0x218010503010c080603072c0106031b0221031302120703020330131502010b041d1b0a210312090503030a090510111206060f030f06040204090507020a 66
    0x1c1c581c40e20000704c2d15543c00b21001545507100b800b04002c01110a00d003440c0b4011440c034502c0440c0480001480e104500f84d00a500182e41d50540000070400c505180300001c000d880901004054510b1103131600544d290300e42c08564000000c07130250340c480c5a800c05541c1c0c0c064050a0f006a10001040d01d4095a1000b80e000e40036001504d290981e206c0c2485000e010041380034143e51a040c2607101d0340340c000c2e07900d0f40c2103051403410100d8002c2c08600a07912012095002040d80003883d002d10040d1184003800c1040d402c204800320380440004104400400c0390b4a13082c0541c4ea058200082000c1410b0b80070150078600019448007003132a20003c021034074066251420704502640c0058102c0e600c40ba4003034459003003480030600340303034040d00200c481c680500116248005403072107081c21507251501d1510402000160550111902c5072441d500c140c0031200039007001c0e03140e62521280d01c80104940803400b005030000f2996584c81e4150b401901402d60b0400191400100182d95403039400300558 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 538847814 1250 538846564 538846571
    0xd0c020a06030902030d05030402011206090b0109091118040615080f06100c1506031707050709060b07020105070507030803130516050102030a030f11030f07090b190f0507021801050301 81
    0x540307203001e4003802c0c0c0480e9000d4000c1022075010642100e8503000903201b00c0c108460001c410806685c070780901005845220310010344400e81d040050400e1845511103854542802a2035950380d03900002ea0390303c8005003010341c08840101c070000c4c00401c01500040410354100b0f42051085a100604903c0340e0090302d02003045171204400c101482600d001120001b5100070b20031000500340e03400c242c0002c0104034010031400e4a80d6034482d06c0d4900504451511900442c80f1400e101c4108600340041c0003040c8108441802c1a000484030310032103801030b042c85400240b61080010402a100081d904032011907142d091058000210b03940f000341c1941d040c4545090325415000507901c14080b01d030160000c2d85000444081500030b442051000f800b055958604007011680400045218001850100900e03151030301e40500854055007010f039004800340004d2102c049004a52120140203003001e80001c5203a0f91b00320750702c2c400c0c41070082d0441c0002d0a9501031500e0400114182c440450091 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 538848920 1106 538847814 538847819
    0x30209120a110141070501151a0a020601090e0705090a0221040f0b4215181f02030702100807080a050c0c0d0c020a 51
    0x503a5182907600091603a5a800b4400114030610705144c86800c0c25402c40004d2214983d40b40d0228602e90301d100604005201400d071400691300c980280501944d05d072001c5100007107845040d2800c1600380c1c980d101203c2003400d0700c001070030a0340140a182e203095088009000d40c02140c0c0040e02076a2004030742a185c41c0d0300300307208103600100940e0307d0f0000348010050030101e41042c2070104c01c9030f0501000a602c1c50101040d04c0c0c002c407840d07180b84c8076015448282c400058404150f0304940c0c88140b4401c4c0001302e141842807500310703240d007120824818490351400344051020326a03c01c00c22040c2d1903110784840200d0202c0a0441c20442800d054080c010340c2c40b180c1280c016a1010034040f0440c6041040940030304400e10f40720072103040508000d40340310381c0a81034100301e51325400040d200c1c02000c4141c0d404840000200c3d0328030101900702502462a20074140d01802e21034001 = true := by decide +kernel

theorem cover : BRFrame.Cov 538669064 538848920 := by
  have h0 := BRFrame.cov_init 538669064
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538669064 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 538669064 ≤ n) (h2 : n < 538848920) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
