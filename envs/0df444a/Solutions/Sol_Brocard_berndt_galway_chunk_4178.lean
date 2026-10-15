-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4178
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:47:40.176301+00:00
-- url     : https://prove2.me/submissions/2f91ef16-fdf8-4621-a2f1-dffb5bbf9029

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 751258992 ≤ n < 751438848 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 751260242 1250 751258992 751259009
    0x10f140915060a14011106010308070c0902280e03061008160b071104060509040605040605060103020a052a0f03030907060903030e090a0b030304081011090117072102190504 76
    0x35901d000c403004920313842e140c0030782e040154201544403001000c01446000314400c0804e281d98041134200b0603c400d0184e001429124010090003024600c41030390071900c1481100920441017103520709031410000e2017a01a0107000749810000c3c104141e003629411107114005490920034500649038600105004000f00d920041c0700d942c0120300711440d03c02102402820001e405a11750000908040c01240d00311760240d119010002001818001d16401050038203096040c0302c0000300c050400d0041e011003605503241c6d90750050645040c60f2416034400c1d1003c0a481048904180301a182c2d401100d03090881c1c07041900024840b07201c6e00c8400216505031756079070314023030740c0104101a40002500009040f0348a802c401929a401d00003400100310480c010f00d1501e501c03280700070546440c0641501d00740c6040c4401509a6000f084022000c3c4030342400b41e0040c0d0307071315034280c80300600c110b00b6190b101d0144c00e271b131004100c0030f5000342094407070181038032055243c40c08110f40342c2c411401007191 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 751261492 1250 751260242 751260259
    0x50103050a12020304051c11090114040e1c090608090703030c11030a081801030b04051b07031106040308090c0409110409170c03041a2a010f14091506 66
    0x1c03036040200120ba4182a20640b40b400da42d03280003031701e01502d043c511804002c01c00410801c0100d030a403024108c02d001d5818041c60f61501c070001002d501c5100480380115242c41c0c4400c4180c80c103124131800c494001c0640541300744080c0c40101456090700610011544010104507050800078429003140d41c1aa07070012003d0603695421074030b218854189415100340d114040024885c6005000d601030b0401031307141118010000102580c010080d218015483c24003480341c100118460300c08480c0c800c5074646d40c1c0d04417500d400c0794101011119007070180642c0d01804101640300311014052038000d0100d42d8400c484000b040b04981c01800000c0140c0d480c44080400d50401d5084483c2d0207000c0c40d108111034000c50048a03041d485031540c00c10075000050203010040c0140380c030303000c041c1e00150918100010800d00b0310209200c10400700c11060b6003e035003100d4140c2504803074180252a9070500042e00568103400031910143d502c1c90302400340140e40403003a40381d0a68944501001000c114 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 751262742 1250 751261492 751261513
    0xf1c2303040b160915110f0601031209090b0f010e01120509010911010518190503031902010c050f0304021c0204020a0306030201030506040b090c070f120e030d080c03270a0812070305010305 83
    0x2903031001d00c90f1084980d8012102c031f440708002c1c00c4c0b0046d0f00a43c01440003520480c240d21000340090f0450b00b1000c18103142c0307403103e00240c81e0004a10800c078020700300940003940c0000180c41007005c4160004005e8204010021280019080b0340752880c880ea81c658092002c000c01910349000754070100540210780c40c3c0c10003d42c0342c080c62019081e102c02031441c41d0651208046410341d400174064202405644800001d007070b03424800c1010044103894402d0610003c22121041440b001c2d00103440b82c140114501d152030600ca107211a1148d004000f150f95282c49140500641340e01c0c030041c0c0c00300e0300d0207002440310308080c0103044808000918840c1e280e9500241c00060381c01042c0180c801c4440c211b8140f00040d8559001ca84038001610741041c0d50845004140c50700101040d900d08022181c814851041d0701e002c00d4030380083d81281000d82c0081034240c0300644107170391118114a4400d005865080c080d41500619000d0181c0b503004045664451054003500c00030710000705682c2c0141c4040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 751263992 1250 751262742 751262747
    0x40606120c050c010f05010311031f0c12020d0b090622050a0902030d020619060e150f0402160c0f0506160f0605180f1c2303040b160915 60
    0x141e01c00070340b810110300348001e800030355007111505824001d032150f4582c0180705018011403102ea86807411801004240101ca204070412001c00c40000c10042d1102c0010347e1640c00b619042c01d40c0c80746100c0c2103495100340c10684002e41082604c5034040c2a00f00c0100b05c6900703060804840c0620826a000d00e1440080310120090400514150603956250342010050b603040c44013460080e040d90041105040105840240200c26000d450780340d80740c03120400100d04504140c42c0d1008405203860300e6150b200001c107a1086441010540c040c1c030020b07984011502d21081803411902410240700760580340c0c60500444103a5029182e4842018003a114040d090002c0c6102c81c14031034a90001c00c6e6446540b90b5081c0c490560f15005205c0c4051009100c0b14403c21103009414000802040d010740d00c000020514070040c4400402c00410041104030410050906042d280700e494400d40d0700d24260410414040056542501d82c0c04402d9000c03020f14460314856082d0b0781c1c481c1101040000c0240705 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 751265242 1250 751263992 751264001
    0x605220f0e0c10020c180106020d050a09050f1306090606021b18041e060203070e0f0d0201080c1b0601080c0a1404022b0c120c080c071b0b1804060612 66
    0xf650214400c1d11955226625440202540360149a00c0ca80141d41800340203403e0424280d07a007410804240030081000c0c1d486001402200c1050b14200300c04911030020a0996180c00d01e114521400c00b4400185222298488400c81e04036600382d40c00e05410480702100c44182e00d68071640010314503d840a8048408103494200e4030031056112070318140d641414003018018010745034164007008000182d80c12503250710440100306c68103000741100d000041d04040d940c240103410450b080000035001c5001004840b20b009c0841c03001032100b507c803c2ca6940c1c0d4a424000d010b22401070036203016060604030814401d0740d441b04060210060004203003c000c3d08001142c06150002c07002081040000890301c02c4050800500442d44c1e05100c400079103489440c00b602c040301482c0c8413117200344651203000940c200b900102410350340c40180c204210054600305035090040303110701c000114440d9150041c0403a403000a00b03c0b4003806860104800c5820511400000c00e40600e4001140c60f000c0c0e00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 751266492 1250 751265242 751265269
    0xa0f02090d03050319110703030f02210117010203160509010201110d090c05030d050d0b031e060108060f250201150605120c0307050714010605220f0e0c 67
    0x60a2251032030000e5001610001c003500407460010500c480b8007950107601d40c800003c8038081c0310045002ca54041c440c490341d00050101a42e03500074140440040c2c040301c01e180306195556441400505d10041410b400303100303d519465400c0f590612900040c02035030300c80e0000003548054880c401c0c0b810f0b44c0680c04210054119503840396403181e450300da038026100f043c4070050001402e060030301d01140c0c8003820b60402480f0303034070446c060342949901c0300856a0300100704c1804a27404902c0350101c0d2070a19100601c07030003102030260f020f419942c00070340141282c0d80c41044034240c1d101c0802c2e4041e051400d685541c41c1c0b610041e0708101c4907e0711411035045115178400011926543e01840c80040015081103000030380c0003c081d02003c0d0070042c842d41100a85001c00d14600308424094100e100b036020040004c0d5034280440101e0800794003440c010039000e00360071103900c0d565144502001e03030040034070115440c140401d1010f480b20b00c50580c8503058000102100e215240801c40c000d1107860 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 751267742 1250 751266492 751266521
    0xc0a0302120c13020306101818090503190807090305071511060108100609020f030612070909051005070215010b1309060306151508010902090a08010e0c1005040602060a 74
    0x80b2002a42d20795a90012401904120060310303420200c080004041c1c0242c11101042415600d10b002070008035085022112140b1185101440100c040c8010344a034032401b500c140404a41e44607980701156144003025950303034409025540703a0f60181d40c011003500000d4600d074051182031061102500e040e420b05026428102d69603c1640c9a00d03262080c2600300310f661b41c01c0541c10b202600c14078050340300544500c050a508140c24030805e294a80802480135104101d002d20040c03100e2030031321220010b4078041c0c0007031040039200d040c9640c0d9200d100502e240c61618250008200620200b09c280c145811450b12503c5a441c1c4040c510007030300140012000c3c840841c0c000180001c0c070344258001148a204081003001c805e06803014021501d90010b400c0b2203030410440c0072103a000d44401c3c1035400e60440140c4840c15000400c00012640c0c111940c1d540ca041e4520540b05800603015800c9101102c5500e403c4d0078401049400d40200d1240b000503034844000700d0040d82c21500040030501480 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 751268992 1250 751267742 751267753
    0x90b06092202011e0c03090603110306130b060a0503040201090b09060912101e06080c090a200a03150807060f051e040f090516120e07240305090c0a030212 68
    0x8228100b01681408004c008076500c810034908140e00510944000d00317590400b044111201c03080c1a06920000780018444d05070010081b0402209904c1b00c80484c0024044d2a101c0165510242c11a44244d82c241e002c50206000007802c0042d00c002c49060740d6000d4101810f0110322028011000c0c0b0081180780c0500606a5a01e010801ca100e00f0b2002c204684c034500700c0c2c2025205d5070303007150010741003421b282e0098014507400351640303070015070414428040080d852041ca2004000998000300380300b1300650005402c2c40c4103515401c900e56440c01c0203c903090903503540ca11650f4501c518440c07280401d903200c848412041c040e4010701212241611001d44180c08000d15810903032054100040d4001100740902150035030307102c1c07142d011301c0889996590550350305001d80582c2100028441c0c0383d86a01410103110801c0c4117410041008049100044103a10f40013500e4103074903d032450020b40b600000842103180040c07954a43c05015100795501404c44e000d100c4c41c00c03002080c203442881342 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 751270242 1250 751268992 751269017
    0x10b0d0e0307150203130213020d0e0304081203040602040e0c042103120207150203010e0f01090504050a0f080d0507020708010e01050c0d0509070b130617040c06030518030409090b0609220201 84
    0x10108c0504043d0101580103990310406140401100c07200c084e403034443e62041c442030003c3c102c001030814081450090060705d03030703a0b24034050f03010f0f03c00d5410204882c0821741c107001814040c00060400d40b01d02e08412000300c2c07900001e000300c1c1044444003500213244110710000301740b180d038000e050150082c175505031a89150130004081ea4020303444040800d10070410040f02d04046044903015205440040c0718500b025111180d4070000d41e400980761813440840c80c4c0800030441c003203800c4015502c03001d10071803916610281d203400d4540b1506e0450350030115030b503130040c00601c201881519145030160a01184810725401020020a039118511484102280642014010f4040600466104000d00e8144200103281400101610700c0021102052000081c2d180c2805400d40c0c17800c0c5030000f02581c0d06d4000690b01c1848070500c903042e0000060114819045401c040e40b000e0096000050f00e481d001c7c20321294410864a005401c51400e020017190204890b4424420740149840c10b100501e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 751271492 1250 751270242 751270249
    0x3250c060608030409110705100f0209041a100e01090b0a02070f14030c0429041104060c110d08040b0f040e0924070509010e18010b0d0e03071502031302 67
    0x446030011582e0782d0000c90100716655460003107503225481c8849841c2058040d6030340c1d5071790303541030710f26001c0c1036890b0a000749114940354195040000f00803c2440020600c0507010400113200c41c2e1140251459140501064000d01c0200180c113010b94600a00c80e282c403071842040d40110984c4011401020310006204a030001c44c00064078080303100d04401d06024040500e0000000c1d144d500440c2410b20f514803d501923015440805081003892000114810001e4010308100800d91065000401c01203140c0364045200e00d0b20798800e09420951101410400c0301700712409030018030082c02000140000a0094003a1003541064200d8070705160b00c07107a4158400f0011583c4017100e91040100398086207460550010610b24881c0c100803070300341404018902e104180301541407143c2400740c00700c0ba03140c5040808501c03d502e0420652542c4554100b060f0340d0000c44d0701079000e801c0c038882274103248010040307501da035604c100c80d40c1c40040501d8040010350801030081750000050681d00e405030f10b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 751272742 1250 751271492 751271501
    0xa0e060628030611190806011407020d120c0204050f06060714100603211815091d01031202070509150303071a010f09110433020d0e010503250c06 64
    0xe20030000c0989500b00c0040458940303401794020b408002c42103007404943c3c0d03007042c4a0368481404044190f03441c459400440d4282c102003d0040c1044074030740c2e052031481d501042501d45240b00300d60611443d03d85080002c040201607911560020381044607500007112800c007404035440700c105490b0303940000c040c0036080b81c203140d10035541c03800c0c0d43c103c408072030f02504c440d000c2082250a10440e180c44c850300260810301e0031301507011a980800000300201b0f0003031440d40c00821010311103455030600d111012500740300a00c0111403030101f100b907280180d0b00100d4890b0035070b5009401c03210f4070740d6080051002c1c10600c40c103081d0180400c120304004030340ca81c41540100e41d88491110410351416281c3c54040e0710710340c80200854507100c9400f07807010700d402c22a411282c14510408500b071b40c3c51401c2d110389582c02080990312031032000c0310055640210750011051b00719201d541c031088420005503041d20044031120101c03a1800c0705141010b040c2c608400703200e0f00d1407901c1d101800180d6640000c80c0c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 751273992 1250 751272742 751272761
    0x220c080d0e0a091404080d0b06030c0915070305192703050705151b0705180118090201021e1014010f14010f0c08090603040b0a0e0606280306 62
    0x4407221499452414000d40550040c800d080c42049000d400c0340307000c060100c000d80b0003404107900040c000c1c04803440c0c0d00480d1214500501d40340e50390600d6400c284640c2d01086c02d460080090300340f044003403801d134421b0b40c0d0308940503156545401030501c83c528885401c110341c80c0c140b142102c04054a42049240c0c01d944003228540712907001c0c00c40c24601e14150581c1e00040c03240800741c40624000c09544141c5501e40d0204503150420102c072842d031b03418854103410181e046020a1242005180c1450070310381240c1d0710450300b510b0019012081400d442e08030f803002c0c0c0540d02c8141202180291552400e02c01601402551959009034860310309542c25841c00311181322005d0010700000d0750004c960720091071204054440101d030760380080c191044403811001409002c2a80609211020b001c956082000400d801da603494607181c0f94400c0f10003580c0b203100540c41c00011070f11115000528601600009151245113840c138040600c900b40501d0700040b0b541ea410400000190042c000c00410 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 751275242 1250 751273992 751273997
    0x30c16080d050405160f1a040e09100b09010509060607060b040513050f15270d1706151603020f010e01050103210f03050702150c0301170105220c080d 66
    0x10b500b4030303082840c581017480e10f2110008108070720030408098054407075000c45405049a1011000a00c0e41c0e40c8a401564482d0085182500070011015408109203400180c3d03004204015030810b0103101070282c003401000c1d04100c000001c02c02c0c030302c1d00901034a0346074800c290114415042d5002310381039910585141042010007170140301007101c1848032603092002c0b00d0040c50f0100030b0460f230030740c901400f400280350900000000040c0b0317078154102e81492008042101e0744900c42c440c000b81b5203103010510450010120001c14210b107040c0000101503805aa030042c00c00013071400383e46002e550558210103500c100014030121030020f0091513289540da200014496246003040341c10100310311a960000b0000c1c000102c403040c2c0009400c54001e40030300d400079496072402c030140e14116138200b0250b4246824020030122012880045068030142200d8002400300d984000c1c0c00c1e2001074540d03950101016074110000907406910000361409103640d003800c142e980030001c1c1819401d5112500 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 751276492 1250 751275242 751275251
    0x91209180207050a060c021e10060b160b0a02120f10060203070b01060c140a120e0d0f0620031005030c09040308070c080f0c0109020a0b03040305030c16080d 69
    0x1500c24005500d21450031030340015490503860b950381d82d0301c508540380020100c5545054400e182031003003200322400c101c041d40c0c0316141000300c01c2c25561164804107840b03240341044000310784080c6a00c00d540410750040c141c00101003841d0f4500c0c2c0100340003020810981e600380500a91111001c5005002d850034404400b51410100304440303c0c4002e41d00003806640c03081001400060010180604458007458060400d091a20b03020003254004203410305540704034800e0500b0300020320000c1c0c410300a01c1e100c00d00d59000c818140080e101703201c0400380036420300741c8121000c50020340140d0401c65404140000158021103503050540060f1003841410906c04800c1c005810100300102e0151421195580a40780136903008000840050070241008189000d80307003040880303c143c400c0100800751080c0c680b0704c1c1040300c074001c3c0fa40d0300e801e03807003842d60500020302e124506040304e004503090b9403130524660304c40008600603844000300c2502c000031030148070046000e50015213402000c0140c00305 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 751277742 1250 751276492 751276499
    0x602220e07020d08040b060a05090c0316181a1603020a0312020708041701092109050607052503020a0b22080c011b0203010c1707081003020d0501091209 67
    0x4014290051081c41994895104000c01c1d603007100708250b010380c0c030020303506056a0b818040b6140d4619640f119800c081daa00c2400080314203107004d1071003040c1d20b650220303c05880c000201c43c500040844c0700314078642030900f80107039568688190ba034895086104d5240c80e84a095810640c0103c0100780d00507006400c0700420560301021a1207914450380b000c0d41020001d89407644140300d14803560400d01110058440504e8007074012000c03107070b0440c00c003060320303851010300ca444003c6103080c1c41c000841840c0c001c0750524041058804080e0070000900409180d0340d0044c80104000880807404440102e0000069480e0380c413010142c0440420a070b15410070080c0c078602c056107502c504400c43d01e510ba0600c01800c0025003150f4484092904000551075401c00c548034060909019405500304041c0110140d04604c031600e42620300b21f11419180d85d50542100c030703410150340c040a8407213411070410140ca01021610881809100005080c0d0800e58507049240c00c0030340c181d404910b6075201007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 751278992 1250 751277742 751277759
    0x8030307080a02070201120b040906110405010f1d0f060d0507021c0e03060a110d061d070f0c032d030e0c1c02120a12030b1e060306010804060222 64
    0x700d410000300390303003541480e089a00207010441184030444886a840050700203035503a5400035000c1c150040010041482e22500c0300c0510743c05402140c1c04038100b820510002445908114007241c4100520441d0701c010108100100210b000b41350740c0303c4402d1104941d41d40312031080501400d02e54004050808000409910054004011209011074001d11259948010510540c089110340300080c1c0481360301d20489260090441120503545090340100c0c94040d140241d910081c0f2148403d0300d903507a054801c50300380c100c00074508001903001b008a40020f00a1000c09a190540281c1d40c1000002840c140012074548044c01b00084c0c841d021884090001c0c84480380c1694140c0b0a8104404516001601e0b0f861068000b801902c580710340060038842030009844583c2d05c1840d00310302c83e0300218010082d0030284440c070700c902c0460712022580502084200e07486038019001d1401c542d103850040d11005030050058a400c2e07004c02080b00680342c0c9286e1380c40700746e8204244401203420500c40 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 751280242 1250 751278992 751279007
    0x2010c08040b0a0e030408010906020c010b06091c02010e1201091703070f0c17070c170c0a0303030902011e05071a0105061e0f0f0c010e0a02010e010c06090b0108030307 74
    0x21041400140c40900000c14880d9442a9010b001c0c0304000c24041481e201c00c41c61849161702c8420507500c0e20041c07108000c0150000c0c030048104c24024003400440c0010010700b481201021039118040e004801c00d0003400c400d43c4420305005041506610b400100402c070b0209000b2941c0079241d644051440c10002c10161144400c04011f0310705082d4039103038030b02805040c10340c03242d801400b0300d8020500420106052031002c4010a946107616030a051409180040c1280a1148140d80385c0b1041820010005803c00801c02c00425120603107146840030307801491000800d030f040000e202d8042c528609000303106582ca1080fa40e949a0304c1609081c400c0c400803405000001c2c40117030384c0041042d503598400f507407400140c40e60f40c1d00d041d000c00840f0009502ca01c0a9400e8680400301e4500152707815007014040600c005002407040d611507141c0036880e0541c501000f03011a2552018124a520661100b80d40311304c81d840006061405131981d20303904009a01c5400c0c0b80d840041000245a0700944 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 751281492 1250 751280242 751280261
    0x603010f09020a051c020a030506160314040305070303140412020d0903020a03350306010e040507120f140f070e010c0b0c130b070c0509150603160c021801060201 71
    0x302004605519400a1a0100c00e4484c06200b050601210810070315000a60204964000c2c03520728099500e19049840e400e0071a03c003101491010000e0710800c0c003c1c064002540c844040c00300716a0365650b0282c58903000a40164105540c07002c980140320b128150313045c0242e010b0b82e100386010011321402454003094107218010491401c2d0100010f03110054100c090326440102c00380b540851707080e811403040064a40c900000d140c84640051128454000d50243d042030740c0310034076510700b6003d0005981040e1002c200007802c0c40880d0004690b10b42c03140c00c030401403400100300b03080ca40760b2030480078034240c0301c03101e01c4030241007800345907a0003103030000c1c1259007801c0a8046001d03517143c5d40e00d07a540060030280c5004002881e03c0c0d001c000e080030346002c1e0402014ac41e0b00c130381040c1080c0078211240d000780c038052003003400819802000142101c868010040445155a5a080c1c100310740320710646505043c4803144200000607581d002d021418401c0d000c1c04203d8035131510707400034299189400c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 751282742 1250 751281492 751281521
    0x18020a0f0e0627010906030b1006051614070816091103070302071b060203070b0a0605030d051602040c12201b160b0418110405090903040b03040b060301 67
    0x400410940540400d10742e888101182c0448603c900311254110b80004014401010002c61002140107040e582c0042c040da03000700e01709101681d841d603a000403948580510b0002c5a0305104400100000c50309c4800e20910a480280310491030702109c034649900e58201c108160000310056a414646400180c0108a42082480310501032419040e40d0303c406420301c001c140d00080c003002885030850100b080c8814030120184403641c0d4800080d00d80d0002d01d8110b58111081c0e000c140c61641c0f5000364016548002c002d4000c14072181c0050f619640300751140d4201000060020000d60384502c5103040c01c6400f51182e03a017202c401400c680480c0e001300c1d130130b603d030300c1c110324000184041103020360f80c29142c440d1501070a0105407030710910304001e03542640c001446511002c150540e0010250081758403071150840042d8001400c4019038041700e54049a440d02844104600d01d0090002a0410011fa00391791505d42c0f50420007840b580220380c155407d51001042c00ba49060900c6003209140464 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 751283992 1250 751282742 751282769
    0x601090b030a02270a120c03080310140d0b1302011202030c03061002010203160e040e010501260f0d050f0412061505030a0213051008060411011701062c030118020a 72
    0x2e1000485c4a005805001d0101c645260f003001044940310b8410702030750f0400c420988910b8110f140c500704003600d01901008010350311401245041030410710140c0e0354004c86142150f920b030003810021100800080e4100200000e031909450541d100440c007694441d64a40c0e503a1600009100c2c09011002c080340440e0300c100200301041d503c4004c0c114245402d4500b080d0200141ca0004001c1d003101d00a840302d55103030200024840021401c04031000001d0004d00b10f040640700750264985c5002d441d903990076000451041c000f588600001c15010318002c08c0d40b41407a4544c1c10307114500020302800c84401e6581c40701c0304180187c440401008290440c020b0109501c644d0119001e030ba41c0b01c807406512500d44021070314482802075000050810301d0101c60451409082103510888140c14590101d000c07001d42c4102664409030060688000d81c554400c51016405000034040c01d041d8515035617400b10446900681c0d00703005510400c02c0451002e01030030090300400004ca0030a90181c100d92011 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 751285242 1250 751283992 751284067
    0x6061508090c1017070c06050c09090109020702010215010e0a1401060c030e040605030318090c030402011b020a1d090d0302040f05061e070c080105010605120a050601090b030a02 78
    0x82c640410b00043e1081c5080007070424068400e880740b01c0d515124500301c1c00c100040b041d4000c10351460303140611030910172510355118800441c0f2540107117a800071074440c01408402401d0f001484800d2061044a401e04e2850790416070100d4281c1000c010704001000348030b045502409850928054103454002e44c6d45840409801480c0306100101030140d0450b20b500d0350b98880d808031005010140c01d485c3d0b0303501540c42ca103810411164406220300c3c20100400c940c0440c10040e40d04c12a810303142d800f4010003241030000340321030403402284d02018040020034220000d9000c014401c6140e0b5417030295080c001c14960419481841d0281010300c10b0008012510900000e4030440310280c40403a607801d09442e5520000c0c0042c6040700d10340d40c00181c09802c109508045c9012601e010300200100c0c1d07200e0b20112400c0c442d000961010401c207401103141f481d0310f035001d142c02031414142140955a1850b642c0c005820455102928550100e41684080115501c51b6900c170110004091140013 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 751286492 1250 751285242 751285261
    0xa0c060f022107110d0c1406070903140102130b091815040207060e01060b0a020f06250c02041a0111070f030b06031f0501050f010c120819020706061508 67
    0x1020b840542040c14403004120050f00075003194402510481c2614000c040d844805440f6000320001110304035010102c0b40e1007244003082e01400340115030345581060b4030350b441d841c4281152032020165954200540c1d03d03415503c0c00c01d04000c2545e5410b46859844040400590001140c3c0120800018400308040f20b998041418514503044a0050301c440240c10310000a028000366842c03958a0100023040045680d006003803c1000d960032102d0f404c101c15140d503292032064400b51030710540007400400380218095050301d116030b91300d0100101c10307140e00010241c03030001489100a040111107103d003541e000390395603102d034070b0a4001d0802618011840d04400041c1c0b101030444008580460801d0750103000405802000c0841000c00e2039010803018020002842800c1c45804070080d08c15481d4001e085a000290308000303814246482d0020a07260401c0083c03121000da81408420781c2c0002c0c0c14406050a5402400c0c001801401c0034507449104d0781c22041d90050042c48010031003100b0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 751287742 1250 751286492 751286527
    0xc021915022215083607080a0b011703120a020a030207020306070816050a02190c180e10060312080405070f14030d05090a1a0f030f061e0a0b03060a0305030a0c060f02 73
    0x109281c0c050400000311720068140fa20395000400e5500440850805100c80c0340b40c9207051700c10598600c41a0409110010303564800ca00c1580c0c02d5400e21400108550b846a010f098800c0040c00c001d03181001c0341d8002800d04008440410225100c2c0051100b014001482c114001c00b6a003412454401c040320080e503920390400b900715080500300106d20400c200f00c0c3d2090000c003021004a000080a081c440c0045c0c100841030603454400e038100c0201c219100c2c0290404c60343c10400f1243c400c5007030340c01154002802803043c0c03240c2c41000c00000341e4040c5000944014401240300f102c40a01d1501058148005002ea040822205105a100f142e50b9401000100da2002000b08003440c0080940d0046000b2035950b003692510100800c4007105455207540d01c204000c4400d901c0e004560000ca29101c01c10030b007078a40080241e40c050080348070143c0203503040f100041c00d003241c0c950380c0d580e29861688140443d030008ac59949042081203410b0240c8803554017480c80030f50030441d8010390030b980707207 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 751288992 1250 751287742 751287811
    0x4031d010512090a0804080a11010f05070609030e060a03090b0105040c1407050f0109120219032106051302120c18100509030706030c02191502221508 66
    0x500700000401d0703c00d1030070842d500c1c2c80c5a11000d12078545995a0703840d80c460b00501b01c1580c11000301241903100390310071203042070364910b04d45a01c2d040003082d13142e980c002e1481b194110706021400d200035615070740d0380000d484984003035030303003c11480c44074904143d20040690099004600b058030408030141c0050900c1d0740005540d0400d600c0c0d10b11420400d28003400b003050908a940b0b0650384400b800362040b84040408d18075022102600030b5000111100d14148001900190303400c100e03803511aa044c0e0002c481603144803404500c054403100000e017160404001303e650280d00081d1880d414549403100c2d130b4005280c40c05c4a0510301c040f01c000724a07154030b8103039a208152140c890380e040390089003540d0302ca00d0b02400301c0d000705441e00405402020b07490300040140c468600903010480c1401d461502241d40100c0307a82c1c86400000b00c1c41702941041c21070704e4030700f428401c42d80a1405004542c500a0100d0f41e5075000c05106624051b04684018004003c20f40614000d5080c4c040c5c1c84103031203401c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 751290242 1250 751288992 751289017
    0xa030905070f030804172406030c060c01020a17041a0604110d0b15130510210209091803190504120303050f070305060306040f0203011d010504031d0105 67
    0x2102034909541412240c0e005aa124260664040b06101c01c1d940600281d03040007241c01c0aa84c01103845ea80c0c5c40d070404906002e8018043c0486400700c80c401c0003590804009012904560340e40000a034182d0010240c080e0030740e5010480c2c1031043c0d40101da4104400e01c241c2200c9440c00d094132000903285c114410400f4150349040131551540701c42c1e00520768007466210042d1a0410104000c014103010007006100b00d44030200542501c0400301294600700302161180a0540760105101c200c41c0c28020401c180400c2000d10011521074090316201ca400c0c1e89001a80d8000c0c00e0100403070b4080c007600707403894600780c441d92010a03400002200c404040350215200c28401c40182180c4a1046820003000310008240c24020150140c001501800c04000e51490300d030380301d910850445000b00d4500c0e40c276078400f6001c01d01050384583c200034824000350012400e104000600501c1c0e0083d00c8507805160354580801c01415800448050041c484031a41ca00d1120164002401030141190203c031 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 751291492 1250 751290242 751290251
    0x41d060a1e021903060b0a1706030f0a05030301090e0d090b0d0b151e12070c110405040b010501080601110309010318020a030c0e10050306010303030509010b03060114040608030f0a03 80
    0x1d0307841956105000c1d151125034150340d2161405660500a541501c07100b0100e42080004142903a81c04240c5420441e141e5400045446443c0e11411599000d441681c05000d802088454144144692081316000c0c50095541f54949030346d034404c440074081801d02a8028980396510664806140002c545002554903103400040079108003d081003031300c59078010b800100794003921421a01601d42e07600010b00340300403894032810704600352244c1308203101350480400004801600440000c3d070300078003030f031074604144003c10702040c215513003074a003a100c545004004014a49e400300034580d01010a20b01902045100b01c082696405164441e50515031a540340003005100f110800c510355800516002d001c0da92420700c0311016121303018440240482100040541202c0c143c0003007100c074003030001c08103a881c54400300d00400010313001131865500d0300c0750000c0d5035804101d4240a011118202d1f203141450800b0401110042d0b071110311b40b42c109004810052000806541050070582004139 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 751292742 1250 751291492 751291511
    0x11070303050603011404031d01030b0607060216062c010b1e06070c170c010912030c060b03100506030105130512090a08031b19050a020f0f0d03020309041d060a 70
    0x313025044000301d0002d51981c4c0c1080100345940b100321881c0e41e020380305040d080342542100450594201c2200030f40c12540410440300010301e82e9000b8150341100311001211400356a652109551492020105108a803943c0c02c0071100b01c00301d0241c40b203441d1f0008201c40a003103408101ca00c1c80d580322598241c42c10488c03500d00c688030310049452040c1c4c0010f12400b5a929103490011580c540000c2c41414461107000703007900d5004020480a40e080d03041c01d040400303259035040300d60207007041d0300302c541507150010b07085952030800403500840301480004c140b51400034181421a0401000410315124500710780300810000708525800f0040520059502c2031000b000c07070b4031072566500400711032000040c0404001c1070700501d201047c424506640d08000c030040c01c680c1c442c00201c17015000d41c0018508000500d400c1198001d4040007502210700110700c54002141d5883c00141070f40582c000203494941458181b24104592100002940030f0710a0301400300d60300c8200400c04080395680e030402c2c1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 751293992 1250 751292742 751292749
    0xd1104021c06150c020120010f02070311010b0105160206030411120a05070519050f030c0604120201030506090c070f0809030109030504240509010315030204050a02070510110703030506 81
    0x215400640010615100040d04481e5401400035206400da1a894000d840c0b007541c1c8584030008050350140c0d03a80e40015989103094030001c010380b080000a41d6106014010b030313225400a424080c0c00782c0ca070b058a008000b00d8035800d580610036071a041050030800c205080e440d8040400d4603a406032092520f039a43c030b10300440300c0080050b84a0780705c20b0501202950440004007001068424001d40d10015668000d00250308085480c1089075690701d00140010f080c500e0041c8000e410080c2182e096040c00c601146041d0700c03a412140e000320070310320843e0641d6090300a0a0b0000003e40b000e144502d4003240698207806410300090028000749004000d01200d20141e81100400078000c2104240a140103042540148074240c0030301ea891f044401c88120443c4004202285074940529013501180118020201101c0000d003100402102201503143c45c420b0354030598141800582d1040641845441c0c06180400c08000c00c1c10901c40d0700d80d00d428101074500c40d0b82c0c5401d010a5030384540740007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 751295242 1250 751293992 751293997
    0x9010c1b0f02060304110a060e01020c0d03120903021c1707050703050705100203060906030d020718020c0105010803040306060b030403050a0c061b020604021c02031507090807080c1306050d110402 86
    0x43d61100c0c010092000713009920742d4a9021030401c540b003144040c6d4a0400b80d4410400d1180c41b80582c02c0110318113940d00700344172644e0300184280381a481401c108102942118150842a001a0b0000040e8103440707200000c00324021138982000140b001c10b14210320a180f4006002c3c008000c0e01251080806000d04180c1d40d010b6030290603200c00003500b03841ca000a402c1210580c0c030410040011660f80e05010601c403240b28060b0780546000b0b8105440c165030980c2c0741e100740c6a800c0d801c01401c501100f0030310131305001e004090041e6684034503508004098500580212407e88010401c3c007001940080885104407102e0034107441c032048504118008160744241d04403103100c409801c0348100c0e40412118441c03031003210410444070a552001e10a5098044000d4150344a8055881c2d620b1038206400c1e4445000e1408000d02515519024280300085c0d002c100d1640c03080100351610310303000d40262480c008240e01008068584800103a603900d203030310302408003072038500300c04800d4903540c04 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 751296492 1250 751295242 751295273
    0x914194704060f0605060711060910110c0102070f140a150503062803030315091107052104050112060e0106120f090f080a1809020304050609010c1b 65
    0x20256160000303100940140200320703401ca4940e440c0000a80e4a0390306841001c042c1c660190007035060076000c1e034800e200102141d10030343c1d00072414041c503000b961300d000101100065981c1da075450006449429031a0802c001d0b140b07419500114070070b0108071641801d000032038204c001d5a003200081503020481445107900000600030440210487d1150800019401401d003070710740c41ca0201020904802c0044400e40101c1c0380e074040101080820f119801108060714100d815105c9079965400c001c08031040081c0b02008242c0128224041c00303402d00c41c89242e440b03c04141018402d10b407414142c20f116a018160602c020403903418054000307680a8006081c0c040119005543c56250240003001914a1f901d082800d0502c009900180d40c000c841d0000d502070784900c51809503958041d040c1d000700b03a8070740c10800c0c00100c00c0b50114061300042c0007040888070069507800d090401fa418041d004101c80c400b6810810924034580e44800c0c4011426400d0801c0d2150301e0b2280780c04200d2519941 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 751297742 1250 751296492 751296593
    0xd0c0b040609140109060207140a120c080d0503071e1817010f0e0a17160807060507020d020d120f0501030c0503161406160204091419 59
    0x100800c215070040b40b540161102008001072440400f0011503581506020314401030b003081c0400c11054404c0100c0d010b40d44001400d49081503242c0c1000440b0f01e05e14001521b4003200003408108102c820703c0301024104240c5012859850a020003074183d800c0590f15042c1c0e540d40c1000006124400c007101c07407550300110006010156100b0050110035080500400954607280f03084168107410f1150581021503203001c0c10502c0f00301c0c0c0b02c1c0300360341d07240180c240072004c2d0400a00c031001e043e1512100c02d40d441007680c00e441d07400c1400c00310102c0d400102281b0640d481360350761415981e0009100911105946007403500314613140781c40c00140c00030f014400400350420002204103e4040249020b6509c00d4080341d0a2a103540c01c5421b10340240c4c49003059070300c560b000d684614244130005107020240c0610040b030308441a40030400301c401c42c40040d1510030ba070070800b1095440c207000164640e20f40f00800e00b42e24190f03403a114804c540105100080c1c40088202000749004000d0300036800c170102 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 751298992 1250 751297742 751297747
    0xb040504050607080a151203030209090a060f090e2e1107060f06180b0103090c030807020909030322050a08040e010905060312090d030201092a09090b060d0c0b 70
    0x203107080d80c2ea0b0034041d0303056808140080300041e40940720f40314095610f000f0102048030b480c581183d86003403103000407040d020950200900c60b92078980c0c200c02401030381208400a006031400100085503480c94015581d01410240034400c03c08001a18a080c20707140001d6038011010701c03000b070760b5035038061100104d02410881801c034a180f502026041050007940b0900041e0416903c810072903005d03010b0308004001d003c0f5042c04054040e84405103a50040c18006080311341c2e0703295488103142c1c5500032145610000b4a440840c10b0a882c2d9a4004100388015400c600f01001f03c500e00e183e10b0481001c0001e200755141c4140042040800c030b42d10b8000501e55610740d240e0311354540c0701509008941c500d50825010034217a050000300080c0a091724080e00e420b00e143c030010410021440c02d401d404540d240ca070a140890808021348110040c01380ca40d10032841807515050401e00990b0120a90502e003425403070100350b108000700c1d8040012280e2503442d84c2c09151211040041b60880030043c04013 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 751300242 1250 751298992 751299001
    0x6060201021206030a0b070c050708060c0306010e04060303050301210213020306011e05040603020a0201140a1b03140408031e10051819050a0204030f06020301050a12050606130b0405 80
    0x1075008108030082c01060341e20540d180024141c0c0c1e182c41903030041ca1002e81000140400c1d214100820000d4402c0040d94407840d030707640800b4a0201c00ba555240442030000c1032007105d42e0801d40d1018000b5059900380003003499518080c0c40da0005109030117016140079121445105941800089142c0c0102a8050b100c0201e81606c025001114094041441c0303019030b0341c1e01c0999030070200280700303143d13142d5141c81d052400c01c0740a90000d04240043d5034944000043e00000e101a071807280b400e41c0b40015040c08a00101d80414183c8103040040c549001c440152100d40840140e6100703410040890303813a100e036a80c0001403000300641441001490342800640341007040071904881b0102c5620740042d0108a01912030417058034410655000400e018603058020703040150b21071411440142000c0d525100e414a90013501b0088840b40ea000006000a2405007000ca0242101c0c80d07402a40051642e14207980d00d07406801c10707110740c030390700600c402015080d0011500b194015200340281d050 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 751301492 1250 751300242 751300247
    0x60f09450b18060c09011b06180201020d0e090109020906070803040c08010b0603091c1e0804140303090316150e0d02060114030703022710140d02090a0507030f0606 72
    0x50907280c1c885015003a01031800112000200e041c06100d5603138405103820522401540d010020009800c40d84a11240f2200881e05510070300600c030319004030554034a0082d100082c01c1502035680641030020382640f1400684072492071a0545091010059807039485100107401401031030030090062600208210070003012408a03400c48401c60000d00c40300c181e42d82007100502045412401e164062031014802070002c0c0181c0c102c0c58a241040c5500a14044602800044006490010171603000a0004205c02514096015a4644044c50541c200315405503240d101e142c0c4105424480e00c00310006000a200c00b1804800507000108a0403d1b4200700715110018281c1c2500540101030000414948010b03010480c00c00050103081c249045508012040000480c8500c2130a03c0c210559590135840032400d0141a0918202402501c3c0556410082d80650764541c0900306030404400180ca42c42c1710a13800c800e0040c03001c520f55880b80001c40040c04081041c05110342040000200740b078 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 751302742 1250 751301492 751301513
    0x12030e060c010c0525020117100e010b0a0207053312010603091506030201081803040b0a080f0702030f070809132a030605060d09080d0c0201060f0945 66
    0x21244054071807054000e41c1e102c0c0305c5e69140780039012940c2c0300c80300d0700d60070850040305d03a009481d1020b80c04560b45400b2603091690090304000c2100100040c401009501040340380c0040804075074140c140d59810404001d002040d03041d0900c400740c9070160400e800704c04819503000703442050941c0820360b9200c1c0010094038000c0c10942c2c08415079100030380e52100d14014102501c0d010385030020036031580c051461444a2021a401c9240030a000c0462801a0a4010101000030344c0c0c600049040207007a50040c1803010b42a5804e5500820170341551603551020740380f1068005050944502c0e40c00e0100d008600e004180320700b8140f034030307690440c02c0300110300003200580f01c1c8001ca00e034002954000c0e001c886482c001d05a003c0400d0000c3e00100c94107030401c900c41071107100ca0508004510150006030b0b00142c0d0300101503510f6180034007131801107424401c000c0180c1c10042c094200c0000d1010004030003144d500f4603207070300745d400c10100d03400fa01c1640c2c03e8a80041a0001da805083c18402981c2 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 751303992 1250 751302742 751302757
    0x706090b10081617030c0703060203040c0b03010602370b04030f0201090203100209040207080403080304050d0c0209072f031306020d080c030a092f060412030e060c010c05 75
    0x20003040030041115103002840385000284252148419411310310b007400910000c100114081c40304014141c4c0000301800f002008600c142009070322803c107840c040c40c10707805a4001200501080c80100503040e8009215007031050300608000b40c501c03e07401500c07100240f00311544135000300034164500b0819200700c0b4500c514080e666070380d0503031600c2d03800702e003a40d403410406503140c1c1c08100c103d00f201a103603000709007030040200010328150343c80d660340c40307103400030352094882d82d4011042005100f03003400489015034a924104600c80015400100d01c494050149020003d15045035a20380160024441d20915001d1a0441000c890180f0b6681c95000070108801076421800020f0501c2c0005846c2d4041c030141e40350580c1c1682c5034541011349420042c89191600d403103250010204400c100c14090203845540114507440c11010708070800f01108110740c0c002d074000c010410410810f11140460b05a151070720103920390310b17240001d0b820f01482d9440d8070385519002e1074a801c25008070081104 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 751305242 1250 751303992 751304011
    0x1b0b010806090c01030e03092e0c0606050d02090f060d050f010c02120310150207030206070605040b06010810090b0103111204020a0806010b090909031b011d0309030a0206090102030706090b 83
    0x943d40084011000c5d182151446c80e2641c0c403d1000c50480d21740b800b020a09401c015400081c04007402000d5040f00107142608000701d00c030083c01c0800d05c1114010072014103c2a0364a0030303803921503404101c03040d60040c10a04007150000205110750380c1c08104c0c0650300e402000303d030490b0340d00001c3c050080c800d2076904c030b01500c02d000d05400c4007a00101960300c00e10713040b500c91211070304d1300780129441101c2224560071030145440200043c2c3e240c1014028150091100041c6c0b0b140501d4201404e48001d42003c2c14000d40100708401c0c098628640d03010f4030041100030451031603510040e0007400021100d030004a0005c2900826a581c2c2d14100e0310032402101e052006607514a07801307442d80001c0c003501800324820010501a400c1c86074503140c00070492422649844014048801442c4240c50610083d94482c0c2c01100340340111130701d2101c01f110004c051440c0c03c940400081d55001c0f4604002d004800215507201c55a0090090b10b000c10381110003400001ca00d46440801c00f6411110001d1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 751306492 1250 751305242 751305253
    0x303030b030c0901050904111807081902070203070b0a020712060c08060d0506041b030b0f060f040c081614340b04110a171f0203161b0b01080609 64
    0x841d03142a9081c0e138100d0304043c00c103003d1601c0d46d84a50070710103600d20078503810a07100e0140000d0780c002e4003a8584104401e960b101c2c81820608400d2124084e44d9244001840c010300481c40560f4000c502c01003194a0114480d030b456180e903509905150301c913440403540100c890400c0090000c1500b080113411481d54400ba0942d45803800c0114402a0b148042c005d5841030000800040320ba0903250b02c00804017500340026560f075555103911039400c651010280701c52b4410300c181414200d540d0050b04030115400d11140860f6240100501c3c0c000f0007030090780d600c2480c1458410b02841144180e240004102641d802000b407035a144503204120030004108a045d113100195000007402c942540c0c4000c20301c000382c4840e10f409901c0000750040aa10804950000440c00c0c80c5c22201b01c0c401105001030880001b003d014007041a4107071110001c054010010896139101b020000c040441e02d40c2455030100031084c0408109540780d280061400340440000300d1100400036070700e07200d190500304449 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 751307742 1250 751306492 751306513
    0xa152d0803070812160903240f0b0f0f06250813032a0b031801180213020f0306010c26030f06030703150c1e1e0206090307020103020d0e070303030b03 66
    0x14810084028540d0029035006828800200e00e18221149a544111400c05990b4454244011600c0b49d0034109900e641d1400e42640c1070812014164102a0490344140c003580c40390081075040c442c41180e5000f0418805030320180020500c90941e030590400550f6841d41000d090340350307403141a80000e03121411044e01c08010f169450300111400c4440c9040440c6441c03801c0c0d114107a541016080c0c4156401e000c0c1d1030388400d1001d1103261000c20481c030200104210500501011010a104010304180104149500c3c20b4080048980202d028603201146510501b005802d031004a5600c0c420b441c5c00301d8400c02104100c2018600402c1002c04103007090b00c884040594608140c440140600052112201c80c408150b10081c0030340c2c004d0520011040030b84184801c40c0c45405401400b140e8417a0340410b500428041d14000043c10b400102418207088400d661b99000b8000c0003810144c00007143c0c488004a500141c0c40d4203840801c4075030070741e124135000e00603040700c462460080c030a1011303a0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 751308992 1250 751307742 751307761
    0x6080a050d080c0304030e120102091206070e010215010311011e0e0f0d0f03050d02040306181403030f041e050d0207150c020f0f030a0f06050a152d0803070812 70
    0xb00c1c02940d0585075034000c0c1c403000702405002043e441c2342c000a9542840b2100d0103450f0b00d400c1c0c0b000d40c100c2101418041c903044c40054030040c2c0400a8904662104411030301100b40751030300505682c2c001102d8240051100d00485424140c07c0d210014500c1c0d851500000941003140c0c03400e4242e04469029456030060144130502185c150081e100c3c40d0f4882100000c64000d0b802000d0810f641341000d403605480b51102415030300114012554040d50890481c140500d182c0011f2420303281c14040c624509050180c4140d12402502c042d2402110501c2d100050380400494812154040b060f40c140c5003056801a444018034420400422107019164419910419111041c141c0c028618440d1901000501621401071040c05425100c0d41c11450b010440300401e4520b014402c12000c1418a070188903002590786003404c40b06111911f00c02440950315011138a02c184c0c128602880201201010303d80b0030700c012303600000c110f0100103501d1091205080050415010060501c001d1362105000d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 751310242 1250 751308992 751308997
    0x50601060f0c080706050a020f0c0604050c0415031203021306200d020322050a0e07030b090c0f03060f040c0203070c0e1515070516080c0d0506071206080a050d080c 72
    0x344004402c00080c00040c217144d2100e45c01410b04540141417900404441c0850760100c00c0208865104a0802003000410001100444410354090088644100c000c08003000c80d07000040c07800a96800c008629071003541075030440700640760303090000c580e2101b0207045001d01401d00710314400d14580f4a8208400041c0c80c000c0120140e0040d454101c1071600c01070014800305501010902140000610f5a13030100410054941e0600345c15050900c4840074044800b0744800e24050010a000c11000c19503500544140c2c1641942196a130303540c400001d040f0013690301520740e00600e0f00303041083c07980d8004090b100e120f00c03c81258003100e44030083c4c1c00d1203001c02c0f1415a1f00c080f82c12445011030400d107003a001040c19078000d40741807250640e0b40070308045080800c10482c0b9980039003003103045001c200d1a68081c500343d1b80d00c54000641d0300c4a50312032000070808c41c1444036110181e10308104030f6110000500004041d80d602035420b1601ca5101c1a500d0540d03800034480402180c401c0c60002c04 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 751311492 1250 751310242 751310267
    0x605040c0c1203151206020c07060c02030c0609010507060509030919030c06050a020f011a0112021201030305090316090b030c030d0207050405102301030e01020f0304170f07050601060f 81
    0x526400300d410350000c0f03015000c420780f004078412440074005007084401a080d0000b9100d1040980c66030b8452844034501441940801c041140902ca218050385010400d518640801d444640d9111030810058400d4031030381000a0000b0714207000c20a00c20008000740100c000100c0d1000703818250b0060702502c1c54583e0002402c8440b503050b00b00540d82c00b8000a0460801c0c0f401941c0f031170501d1900050840b9440807422800d0903601c4650706d410b681c042c0c83d080650003c26000c6003448414912032121181c1408001c003801030025508809a4040155004d94080c16030401481c945400a00020304400c00d8901e01078440c1122105203480c000c5408004a90990b0050000ea45040200009014090501d0390720800080e00480d844e0001040c110f07111320b07800d03111503100c030300704000400301c59200d89958a075900c1480349101401c0450100c0f0780007504500c42c0c2c150316002303800002c450b01c036091041240400000305002000b001140d03c5048800741d1b01e40c4591010f041605444409070103c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 751312742 1250 751311492 751311503
    0x1090b0f0909040303180501060315020315101215030605100b0d090819020f07060e0d1106041203120c020d0807030504030e03030309100b040207030c0f0302010b0a090605040c0c 78
    0x300c0744a103400e144800c164483e02a103004218241800410300060b00e4809040e40c9594440d4000e0042c41720720f410680c825481800110b14500c7c0a080090341c25107107029403840b031007054040700f44146c8500300f00c005168000300d0411840ba40e0a1504601107420711089031940e04200010301c2c0c0d0b82182c941c180403070b0603400d4000e1410104e5a04800117240c1800300301c880740010700a1458200d0303c54600c0d0b10b0700e002900103005000b40c1402075494100d09030f00c16000c100d21805008840d031105981074200319484034110340400118030016020b4003403070304010345039003600000405240e480704401c6540c0e040354200f00920700040700e0403078580385c859103040d000c580414081458948030b50311150344203000e803915804290030040000e085500503901d0194540c0451b0069070895550712448107020b00482e4114540b00d8960f03400780c070030300840300c01404040694a40340c0a0600070742120441200003401d184545441d481106d00400b10b81c06000c0c0264688070304040414000d4145041454100 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 751313992 1250 751312742 751312747
    0x10030b0a2c030405220203010f030311010506220906020c030301030c120c03030e1804050c100e0f010f090b0c1e0102030708010b0d090212060114010c032102070f050c01090b0f 77
    0x82030210003502c503045e0203c200b8580952402500c000e102560180080074a103920481c0745050003060b0210700405604640d1611090104980d103e0030b400b036090206c0b6803085001062601d059009102500000e041280002404030744484080000c5058030702c1140003001c0c3e542c40d603600c001501d803900002408800ca001e024008607000307603042010f401008000b010107207841035113140c40b803100780e41c00c6030720b03902162588040780340c02d0620f00c4902031240350128840b01d02400150308203007103400440c1404a01c1d0540280b01d4031814808020f007040a00aa542d610180d2402d42e0b1030701080c088404850010940360714900c8107000b1203001d00c0a80d652024180d01b000780e6444168003030383c0080f00b40c03507581c00324a005849209210440b007000c0e6020b4038540d8586034000e803840c0382252480c0e04001e40d04464100280d0080c540c3d408807031107a010040800318040b07a01d00240300d0780d1009001c03400014042d004001d400210f80140e00710a9941c14400c40c5d03660886860740c044d45280d5a60100d0a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 751315242 1250 751313992 751313999
    0x2a0b03090c0402030606040503010213140d1a04051507080403030c09180b03250e010504050601121a0604080d0207050a1d041a040b042109060810030b0a2c0304 70
    0x54014641005c2c0062031313a4601390b550400030342241d000303c40b90b800380c01e00e110302001a1942482c50300909081a204000e82078800e940d0000040a1400b180c1d803d60103141c08103060210400054a03000c0000070580c842d401e0400016050340008c440441c0000e0820a041f03008a00c80d65a01080320301c10490210413410b440040c501818542d00040e40500c940030040291240b61424104030310000e820b00701526080028843d4a194140c100324021030500081c0080707a64490701403040d003810203c0000d00003a911001154212441c060380e548040d010401003410007022980b07140c2c40c100d0340c0881d42c64965407403d100010300c0c5446040c1e02c0190303403000203501312061108907601501c50003041444600c0b9807043c013010030b001c0d036040e24500c2071001004104581c00c01540d00c111191120f8409070f00c0e20b210003d1042c45c260255a04018400c400b064010704401001c0d009143d200c4110b039194a40030600740e006200804450a44050300c412485041c0424801004800018006507203094207 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 751316492 1250 751315242 751315249
    0xe090405010f020a0f110309010507150209032d15190b09100e0106021203183f071220100b01080a05161b2a0b03090c 52
    0x420540d815502d500030000b01c005548020000724845845000002c0003941e401080400c4842c220b18259208000c000410703a00002030380c0c03006600440145200c031b600c2c901c003000381c0200c0c044940c040c8140b40a41c080d07400110a1070080001841e810340e0b004030020764a03a0b4404082800400150b024400b00e0084407210240700c182c0d841c61000410406241000b051003034200b02d0f0485280d07000071400b0711000c01d4100005004080510045c40018903036440049240b202034050030345400b060a0020000c2e4013400540328070b08070804c003d401020045141542502a004460056040d52050409590000c029985540e0704106441032141302c071803003626084201c1038a00035048035924501006401041035000030714803484081221180d6000140a1007406840b01755042d00305400c0003800e4a801d40c26000402d034601d0041c45003c050101405501714040028058000200240010165121440c0318140c0280003111000c0c0c0d49100c0041c039800107480d80f030090741000207000d4040c074 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 751317742 1250 751316492 751316509
    0x70e09211305150d0509070f260604030c0203100e0a11030c060a020f0607031a040c12061d090607020a0f1a0a0c09090e03090d060603050316051c0e 65
    0x10000c1440c0e41c000c0d07101c10008600221100644004901c0000c0b000e114a03014060a90800c010340c00811042e41403030391481419080b4081c01c0103803610708000e1041c440440e0b40030030501764100f00342c650a040c1400c004141000c1040b05900a104000c00301e02a540c062056a4400c034460014002c0c1e0282a80d41443ca1428689100c1d458030900ca030368405591800010240051f080e001029001c1030050000d0800d41e006159000b49490480d58071628084800c45203d0b2000461300090f2015482d10255449d40300d070515000301900c0d0030720208041070007403540b45002c0c03000e24504c00c85580d80f8551590b561001c44039440160007007401c0c1000105541d1103091121321a941c020b1a91890b240c51401c2c0200c22a010307030390140c0340e5004842194200054401410301100144136000742d9084c565a203200e1940c03681d0240d030015a4110a1203007076480303074000d1984001580c0e9a003085603031100300308480400c140c403180626400146821038502c4205d06254054480b00840010384c0100030703850 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 751318992 1250 751317742 751317757
    0x50714012f07080a03021504020609010309051011130b04470a18060f140702060c0303010501090f050d030c08190306080d031a1203070c08070e0921 65
    0xa960307040c403a090301e00081c0110009456103a00604006541c0d0034000c0c500f9520300001d00090011100340070250b2608400c131448030400b07080100760003000d48fc1c014540b10201d4078203030520386000c100707410070043c4400620388801c0c02107042c200940c494400c40743e248114410ba05040c29050001d0300718801d00a081105458480d240d0115400c181c82c6400c0c480310100542e0000c844001244490785070071200400d01c3c0c0785903c5c4078180b11030420001070710750115129110144002110740c111181080d074101c412041d80600070a41301c0c13005402090b600d0b0000c3c000d0031b02140d43d001c00032a140c65501c110314101d43d030041c01c1100300006510141c03458a015081521b03035505c10422440c1c000c0512030303040a401c1c803e580c00601c0c149802d9205091250162440c0d0401d030600e449000e03101015003484104241c00c4403c03d900814110042e465881101c00083c1081c1841c84005514074020994100b1a590705403d4101075803140041c50704c5d520710200102245100c001e0307468590f4491307006000c10 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 751320242 1250 751318992 751319057
    0x1903050a1d1c1401020d0b100f080601120e2b0f02100507052209050610080402041d0709020310050d0209190f0207060b1503010e040f020112020c0a05071401 69
    0xa44805000e03e800ea901401810751070503120300c01590f10b802d02c499140c048200380d2600c580302ca504050001d010350300c080d1407141081504c0c0380070110380c1040d5021f180090010002c4500c4010004a400c40306a25403480d8104a0600c80e80c0d43c0300d450041000311038008490b4007802840120900d150003c050207421401040b0091201c0ca8000d410101003009083c150100300481a260040280544400802081c0035004c07040706200c02681000078030f604150704460206d2031003000c0360100c1051144000d001c800e40b003420000280340103643e001b14001c100f40142e00740016194400d0040c0004024002900300f480c0034000750340d207040540d0315400a40010341c042039800c540d126410683c3c203d80700507122950b80e01405034182c680301c050386504070400707141181198507181c5040e040060050002d0002e84511100b6421607100303a116000c054602e100854a950088250396542d22a41c0c40844492080000100b005500c244070407d1000c0165119010040f1403007503213003400c1030303540030401 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 751321492 1250 751320242 751320263
    0xa080118080c1504110301050705130504051e07270e07030506040914070f0509060d03050a03090606091a04050f07030b0d050a030e150403020306040b04051903050a1d1c 74
    0x102c3d000320310b01c1d0a018a000e135000202545419007094210748001c0e0582051000030841c0080079035100384140100c44040b03800080340d07030301c000c000c4803a02280d19440d0b40345040b9108200040d9044944842c00c001c1005002e0603820000e01d06619240d4a400ba01000c14611000900b04605c241c200030b030b2209002d0300100d11040c00f03070f0302d080c1e03132084421120707000340c2080006000380b100b910340803c01400d04441c0035846042c880040761100c3e85651016081041c0000c0014805009402840303944d54426010000c01c1e6032898420014a0300220300b14010300316009603080c9250601035035005440709450040103885045d0180c000b00f03c61100e0703d4001040301c0140d00032407070500c031002419000e5140d600030302c0c610104009050244140d0345a69090501c02032002d40c0300003807001d500c0703684a0200c0701c3c02c1d05c50b1b0074007902c1c018110b2248842003914403001004c01d6030040103030011202c0e0751604024501c500014407500d0b08032441c3c05802ca0039000b5071005105c5100c40591099000347c0c14000b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 751322742 1250 751321492 751321513
    0x1806070203010e060c31090902031603060603030f030209102106030c17190b07050c100f051e0402150c030f210c030a0905030f0c0a020a080118080c 65
    0x40c280f000850b00c4001099001c61071420048894461004003005010b005c4a022009943c410b4910380c6c500035640f16955a00c0c2c500110746041020060024070622038007801c0e40e40c3d1800b20050403081c0003c07000921140c0000034218064000c0e64041a00140014044034449074200da1004c0c0f215a5807408450381549a00600c01310310501018501a950740003c5a09118081c00c054580344843c440942c8042102c101c5003d1803450900d0141d07220b40c0c82000d9031200e1900711800e00456840c8000d600911f1180b0ad200c0c980c82d8411418003c100c1c5d814000c560b101070884034125901b445400200c1c411200050061408510003035110040008060501c00c9071000075155401c8211113a080c2000019000d0340d8a1441401c505810300034000c4000d9480c00110050440c040540120002a291003240d401c010003801a038000001c10301d00541c40c0c10492a08a43d1580703a410141d006901c1a00c001c20a0001801200940708012200d0b030000d0819542d41009a031000300d9403051030140d03503c0d14 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 751323992 1250 751322742 751322771
    0xd0f0c08060d0c090c2c0901150903060f05041b0503070b0c030c03040e010e06060a0e010c030e04021c11071110030e070f231c020109091113060302180607020301 71
    0xc00c1c1d844015506d2144a902100344d2a41c845803034000b80354038900c5460b034415965070b00c4682505460465907104240044d20700c00b52450015a00010070044c20101d00c4182c40c055544880c0c485d902881c40745c02240385c0c80e00170705a40c4009028141e0160007002c42400105040c5008110f002c40c003030100ca140c10280c1407102d0031600301e034000c0c502214040004004803c9040c0e00380390011411102a882c0a588400103880f07400311400c0c081c144000104180107042c001c070912a1007a0000e00305561350001c02041b01443c100300d100c0103503207614043c0070311041050f0343d0550f05217652140c0000c10031014038040146000038101e5040c205500c4103803101c5d4855081c8079010061515118002810f82418a031611240640e00005103070305c0d90f20703400e65003680c0300414441e858190b100354031100b801c0c90004860440c0d503034201816250507c0341c43e02c01800201c0007482e00121816861052948680c0200e00f03a22407810070200000c42103040342041d00c0c2a500601c40b10f403005000056141c00c48018 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 751325242 1250 751323992 751324001
    0xe01051e04091b030507050301060e0d0204060f15020a0503040e0408041a04260d1b0b0c03040203071d01090b0402044b091505150d0f0c08060d0c09 65
    0x180000362a00644000e001010f000300c0801c1ca504d003014803030b03880c01550080103070105200308010003881185900c010b0f1114901c0354050390b000b070010301015458031080b6880d041a0b10800c02c3c60b00211030f1282c41148007084190005e640400a50301e4141b0302620a070703480c4009030080d42c50250030840040c9024110f81c02da650701c0d4181103119141da00d810303011415550481c0130b0031b54010313580c501d0807488480031412000b0207059040c100a408400032004001d1408800018030080c1c002050080728036003203020310b2183d4421022115019103a001103a0749250003590051700d9030b04000107000684081e00400880e02d80980300600303080c0c1c3d42044244660b64480304d201c48000100c50300400c1a0354041c81006800f0303504040c0e1703031040c411040c085402500d21602e28520381c4d80210242d03144254035100e004200c01402040f071400c80c00c00d06811948110046c2c80528039221a0b50054461030003107160701003082d101e056141c1d84a409001c10004040e400b110014030307851001c902445103115 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 751326492 1250 751325242 751325249
    0x30d11090d050c090a05040f0b0c0c030d140702240901020f04090504060f0b030d080903041d01090f060b0a2d030603050c0d0b06010f0c080406170a0c0e01051e04 71
    0x700043d24119042c08902d80d0040c00c0a0b4001e401c002c2040046900940c01d04001c0c0d60110360180035503900319000140c0e02500d411920540400240f0300c07249485500450f1f40700728001c0c1404c2094139079420a980c0e034065004815549180e40810081c0180280c84003680001a13400251404041d120044610350003a0003418510b035a8405100912405203c0e01d240c56142034020066501d03c0b400103170351400c44203210700410032038a0025000031414025a0f00400146080011901c060840610b441c1401d0046161152170103400ca410702c6d8480c00703031034111401006078600c5c221101000f1030300028001e0100080c500c140c468640442180c451680381a101583e0004040d42145002030429030800015881254254400b5006c1031004800d260086400d08290b04c48041d00035082e207494410820181c590358010400144d03081d00015000fa940c101004400326581d1018018000c842d00286440001a400c0c401f640740303540940c00810031351075214400d0040032007003580c4012642c0140c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 751327742 1250 751326492 751326503
    0xb240c07031203180203070b070c08030d1b020a111018081f0b0303090409150612150e060a0e0316060b0f0a1413060305060901140601090503030d11090d 67
    0x2d096101c0640d1510070b59400d44402003882113015100d4000035519107040c003c0001c0c4035400a088400c1002901d41e040007415418260394849081c05d0821000b0a00709040401c207028044100c00d6071440414000310301e40d8810b2030b2240c540c208105000c010001548000c051000c400c4004081d5510404001d006201900042003d41c0c1a101204984150200400703801c88c02c007400b2010340ea42c007000b0350b443d00c00c0580380001c00310740c10b0800d180500d40e0b1125050403d8900800400c28102c0081e500f03160318086c41100c005040030150a4044400d10680c90790a500500c0100c2c42c5846185c20204000800004880c1402d05d0541c4114102025000449229554402485160410700150402190708580c110f00a07494081182041c500058005100c1ea5608900045140c0c5540c888409160040304680d99403910040107402441500c542d10400c103081000215036610402051081c0d9002070091402d050f40c4880f40307000380603908091a10518240400425615840500001d09000e40d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 751328992 1250 751327742 751327763
    0x50d030203152d0a0308040e0403030603120c020a0510020319230415090b04090216080a0c0203010b0a060c15112109011506052101090b03010501090b240c0703 70
    0x8511038441c0f50f0b0300058150064036032440400c04940d5800580701141c0c011002490159914035040300103040d0b82c0c100400807080c0b000c0e60b145690b801110120402d00c00d4404c1060341d512103007001504d0030004000f1005a10420203c0c81c034030480ca0300305408200e18200304584201c0e5081224500c0c814824442031400013050801000b8900700d815040c0010a081208071107080a115400c0b600c218000d420950f0740000d5260501048984a0b4100541098680e62600c004150041107001110020380c821341c00c09580c0c00e5075160900c03580c0200d407040d481d030b02000b2600d60b42d9000c41c4558020008070030740d503900c1078101032480c00000307002c4480a0745031140540362240c0e080e04c0c0104050440601f90385044008070b5119011013600d000e036050350418584440822411800600e002604144407560040c000990a10107810103d401d00c000c40003804640e03210311400044030514290030b507101c140c101c1000607000d5206005403d220300e046e41a407422040e00852032515201e40c0c4203c4805018 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 751330242 1250 751328992 751329049
    0x10c020418061413030807210608010f060f060c0602040b04080a0b10080a06020706240f0905041709060d02341212180c050306070c050d03020315 64
    0xf440f400320980b0012804450384d0a08841e2481a00d10140c00201440b280e100401d621a00501507401240b0800300c0c082d00c0c1c80030f41058100070380180d02c5060015801c00000e5591000796000d203c0c141c81c0450041c0a4580c600395080b80c039126040415281345900f00300106000603104000c20240000d40006c0000759441d20b1b01000ca003500901c65200d40000340000d101e01ca1010541e0390445810400143c0c4810721801d1a400900040201048004010b00d0401c43d06001c14840800c454038020079150b45a90303081c10030107070381c070446006040c4144403144040c102e0640010b002e10b00070140c001030402c0c210520b480101d9200c122689070004e540050b4040803c0351500d00d09543c07290b003440812120040c0d0350a400382010354501d801348aa501e901c860460800e03405003107407129a442c001d02c031a41c1070400a00da034855001c1c0034000c3c0607020000d40124018039142e812942d02c50001d02c2e4090b445c1104070000d40001e40308031224803903641c0a070a1a580d008404044550068091001198 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 751331492 1250 751330242 751330253
    0x613051c0b010b0304120309030e03010516020105070207050a15030b0604030f020418020f1018060302190c1707290f0108010b0d06110d02040f170a080d0902010c020418 74
    0xc0c143c0c403c0a01100c00c000b004001a000d20b881d80000d4580e04021446004924041e140d281d520f88907150990b103064100822007030700324418910600c1e81d8000300144c6e15212070807601c540c0da0740225600489090410400ca0307110003610b1882c00c01926000841a45a5000440700c0d0f0041e4000e841001e0000444819031505105010314111100020040040c19a01092002619118091140c1c036681109418240504c0368802c10300d00206d81c3e1820640c40da04043c000750003c03000201c48651008116401901442c1401103007034002c0341070150366001c169140d40d140c0c48250200d5244076946036000350b000c2c0c402075512400198001110306441c0005c0000085030b0160f0110171142e0600040d8000ea444100503e800540c00c1000031880608039007498001e84107004215104030701c0041d0005200c0c15141110b0140d843ca40a4802a00a00403210360303503041640002d041080c0c200800031141001d684020841031040c1070010700b191447d0001021204c02c085101020034882c1550b01c100003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 751332742 1250 751331492 751331513
    0x1103030f0c0a141507030906140c070c0504060e010302060705010204120c03030f031109060901020316081b1f0e160b0307030c05130b09031005090106031a04050c0613051c 75
    0x406005290b4003441848113040741e180540044181642d0700480741c18440c094004c0000607110400f901c1b550f00b40040c080303c00b5400b45900b5112505000c0000c05c003860640900011035183c0304104030540d0960302000116400b00070200d40565081200054035015101c00c122303102c0c05030007150b015902c1c5040140031641740d900d200c01018541003d081c40302c10150140d580c030b07034002e648250312a044040143d1440c4100002e03800014031000c02d40303040011000007440010641214140ca2039440b201e066075031070100050300310b0311040c00c00124105105920603e00420380904465a00d400c10401454802e2550460b0a04480000400c02040d07014050300c15401120b00d001840c0400d47d805103051811103015a85003100006952082075408000301d203103039411151304004a090520341e580c0240100d20085a013000c0403030b04804000d084281241c03140790450041d00c50420784508025156114185c4290103200d40080855591500c030f6a0310210f507400e0000c0b50f0141174070300301114640c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 751333992 1250 751332742 751332773
    0x70b01150f05031902090f03070b07140607080a0b0409020d0501090b241207030c1e05092712040e090f0c0102100b040f0c030f05060306131103030f0c0a 67
    0x6010020300800c2c1d101c41031240c3d61310403031400c01600c1700f8000000601070b04030300305001d9151040c50008a5074859100c0184441c2e88100c0005d4601d403400417040d81c8074201190189c0c0032078022030002e101141c99401148081d40021300009a501d017030741c00103091b0b00c0304d00d500707455980d5a200218100100514065007003c1e01c0884c000102d2241c0d0801980030716000c2c0c2c82c90140c0640000d42e15220001c0002d04041e6030300080c1d00c9945a205c81c8071400070f084400302080d41d9505c6500000f070608028042074000c0c000383d450200d40364007076903284402500c1200400814030809402000324188600a040581140c40544980e0309103040c40328030340380740c0d03030100403041e040b034125460307140e80018010368aa500306001107810441c10300006c2c018011111184941d034202503280040760340c5584140c2458940c440d040089807a884241550303a00c080341c0080303080d0904c51244010845540d5402410403004040307900c0c1a01c051442c5809410207045c003400d07644040d14900170003154000030000d4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 751335242 1250 751333992 751333997
    0x4090207030f1b03031d0a0f0c0b040f1401110d0e0103110310032307090203040203190503040924031209060c0c05090705090a0803040f050f150f070b01150f 69
    0x141d54400e400300d0f0641102038402010715584054203c0c0751000f1940700303d5200054010f90f00705192038105030000b030404002c21201140d003801d0100724081c0e07002c103840a40701801d81c8420481e0602030400402030340034002a0500c02c88804c008050f07442002543c00d6140907075102c1400c10091000901515800400741c40112028410411520500e1203d402143d0b00700252070301c414004615885500074001c035480300ba003d5a1000300d020713005a001513004034030903401c88200c1e1707510405840740300035841001030964008010030800310480380c10000c200c0700000c29010010800c6602c20351f19040c50350040390400789034818240560741180403580181480e0506441d01c018a5807100d14640e51801034a10900c045004035504c3e510910a07210344d020060001844281c072001000d54035009807103080991505803402081a05203643c3e1400c40c004003404c10041190b500810355859040204910b050110500200300807030380d07440b2054003c0405211408031255030000c001c0031008000c021005 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 751336492 1250 751335242 751335257
    0xc0f18090408222d1706160203130e150d050601080f0307030806010804082b0b2b0321050601080f063106080f0c0d0203060c091504090207030f 63
    0xb4034240c8241900f000c0001c0c43c207200d8680032141078060316240c617048183c10035404203000610003000241a4010318050880d0505903103030350b404a13624442c0034800460880244c03410003212000c0c07000660030030a41d030461082001d0140104204a4641c4c10130303955540404010030007040103001c121500b5031008051072a098494030003030729901d005015141000325800000e4140b20071602591441c0344001000e61046540c0010502544140101c6121807490078124007014589422508261000592100c0045d58600c004240e21039003240141c1c180584a030242c2e8081400150464080c038441034001a00c3c101400014000d5500802246503030031040248840d5654010000c00589100c1490a010070000510100854000040390780d2041c107104001c0307404980401c50840300b540803022256032200e4101001580e4241c0e11021350540c00030808204804235020003050f103098094000c101100704800900c240340d1007944083c0079036a0104104003095400001c050080c115442c0004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 751337742 1250 751336492 751336499
    0x20705061602060909090309040b03030a022802210d1409100314270615010f020102070b0103060f0e0c0303040b16050d20060c0f1809040822 62
    0x5040d8403031040038114511841503150215568401101d04402000e044000c0a0805c41e100c0c95498020003601c1d4031a070700700340700e2206a00b000029030740352642650050488070383c4410500d00c2c3c036030449024101018038980002c05601c501d400010700454a1007103c0f42c00d955001064200b2010400d00707010001d4203003202c02c8002c6d480c016030f140e0f640e00702c8100010080c00c090030350003400c017421802c00c0d101280081100c290849061248000031880d8544007030704101c0c6207551601c100b10b940c1c0039041000291008154881c9011070b56800490000500d002d40a0303ca1200900d03090f801141c03c141c45805100c40c8000c81c0c010040d80031350f004001c02c201302900307000035100d0180340540c0b41d80442c04541c00504111107441c200700a9040002d89451454040d4018000c0c40c0c000c2a80d03110710341c102c00858bd14032000801c02e00c00d02d80c1c000c4031800c217401c40c1c0b0001c05541c05481100300b46250340c0001d8005a4809034000d01036486910400e940d10105009090045600003140b0401000d604c2c042 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 751338992 1250 751337742 751337749
    0xc030a0906032a0201021606020a0905030111030103030806060730030c0c0b0a020706020409060503011d06040b06120f06160507031205041e0308041a040210031d160510020705 77
    0x586103603003d03202038810041496802ca009002c1c0003090302d001c2e045000400e0500c51168001c0c148441c066a5003144551510145401c2c0c400000b103000c50f284042004201003071050800540012005241c1460401c0603110802000302d0010403d1041908440005c2c40700c02c8a42100c044000d6810300707002260742500042d0803e100c2d00c00181c60030744c0c207600141c840d101c0d5a048945496204204540b43e58403014044010515130040902039032034101240e0842c00301e5410b00e1401e06070900140101d5070350307039202e1040040180103541c100d074440ca14509030020600030100380b2000c200090a9920b00f41100405074504210104217020042003180b001c82d07808900c07110380360441000894262034a240c6074140c01d600158614441907100c0c021020181d01075101c034051741c0650100c1c000210003041c02c92480c401600c0095202030f0075410b0700300e403034066007101808a1001c210651940c4080702c400b410000d071403c0d80529400e070343c1d006020303c0c030703080c6040b01e8130a21510080803d01e0810012 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 751340242 1250 751338992 751339031
    0x3080703140c18040b03010c030b09060405060a090b0f06031e0711070909020d120512090309090a09051c1106010b120403180f030b190504150b04110c030a090603 71
    0x101160643c1510071261103131216040b40c41002c1020f402001841d044032001002401d80c0ba1909102d03214020224002d880c090140328050500140340000c1c062170f01d00540e006051002081d50082c82003100802c05a4400014505c10940b41d41011ba4012002800303510041005000000b80b0403240c0004280303d0000503c0026240e11010000e40c000f850300008400ca06901c80091a03c03040004408840e94043e01400503039005403200300d00da0315914190345d00d901941352000e8001c9404400101c40d0b000c0342e0000c104841c090803c0e100080103c85400c05503c82522141d4040307042001c030310180490401a442c010509060301d14100510100c0b842030000001c0d01c05000c100455807440b2460303246104410080c4401660207010560324036000b90040011601108030114042d0984100003440c080d0301e100700d50050000c0c60580014000c800108040c1c0318058000740d690307a82505d070080b01d0009004c04a0224000c649030703440c00c0402488180d803604010109820300c4d240d01d1400500707854 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 751341492 1250 751340242 751340257
    0x1d19050c0c0c1020121b12090609040b0609040f06050f01030b030703081309050f01030c05060306011710120b1f0f0b401d2a030403080703140c 63
    0xe00354081030b01c443c01380e0700d4518621282000110002040b007407542e03050400000c00421ba5041e500c4020420011a115002e5045426042001004030305000e14059000000440000b8000d50030700300a503011030100c40c5480441d591084d0f6960051200d07141c610000800040300f4130301031040041080201ea200c1c01c0910000b0035518000c500503c40340a0301041d8005011400c4040109240048581402d00b000b840250f55240c010071022440c4d051107030469201e6141a1241d00130361104141ca008100b00051203011180035400d004600304400b80400c04140340030340358050180c00c01e0303049140c01e24840b90340c41208044410081040d410030307800c003004580e0401451600e03a20320443c035a09801030450703000d00000410208030440e034031058000202c1c0040c001c42c624400e0b115000700600c0100901426404c42c15007002450b00c045001c5004036529041c3c801104c034050f40d11162610340c00c1664220080350131442000b11a9a05210710303008406500340111442c02c002d0005011440343c040e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 751342742 1250 751341492 751341527
    0x10080a0b0615091c02040b0612160507050c091909030c140703031205310b0c03010b090607171209060702060114010516080d0c020609071d19050c0c0c10 67
    0x40d03004041d5525a03018006107c009810113540740302d404c0308030094400460760701002030035111161282500c51420b950a065129001305400c0c081081040401d40c4010414103800c22041e04003241c40305d0754020000441d1103500d8040e15111700c0e18000c00b845c40c0071410b07007c03a41c0c45030108001095101a03a440702c24403c26000415840c1c54000c50390014000041c0c0c040940040c1c003c90310b0010350100c034a080c80c028021405140c0701e103581d0810f144420f103d00500d002040c042c2c81079601e06040200300c081d01c0b905003115491030440c02000c180d04079101c0c140b180b008000070040001401e20415a0051031440900410340c10940c26080010710b0311840c4c2d040220200300d0b00b4824070034420b40340ea01d640002e8072035110074003100b01401038182020254018010b0101058000500050b003070191181da801c08110a000110b800c07100742002803112000c90300401c412844c0c07285600c5801d0207001ca1406156840440d0503000d80b82c1050452007901030803a080e103003044254003600c4005100b800d003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 751343992 1250 751342742 751342789
    0x5060415030b1b21130209162313080307030504060518030106080115170a022e030c170f0615040519060f021f0510080a0b061509 57
    0x180c820500035100034011480b500d400903042064500100c04d0810070f41d0703610781c280101d98030705461601d00c101d6654001d400a1145000c030710f801100c81c170702c44540c803030514000c0c00d41120503a41005200039006840c241101c00910451071034291440d800103000c55400544c03500c1c0f4255002003062003103224060403c0408540023070803c180301d2604013168001402401070302e8035648414000d110018245054019a990000d140115000a44402480131001c0d00f8204829001d0008490141d0182d0b01d407d01c040c1c40110140f6011211000f001420b075070002904040104040d1081920100301d1362842003110401c248000e0720742045070710100a607480010710703208031740d20301540c0290340050341d102260004c0c00807841c49105202c811168156140d0500740840c030400da0b01c41c2d10480c04243c9040940b0200d110480542c1c005940101004103140c14003940c0d40c4001e410701400303010480310310183c4401c2c40814030303154105446072800380345003910b4151200b0020ba01c0320043c80c01904441000f = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 751345242 1250 751343992 751344001
    0xb06060a052215020c040e010b01021207030203040f08100507110c0d050102040f330c060b010c08220b030c0a23030c07050708011e0b0310020f0d05060415030b 70
    0xc0144100060280080c603c00f00141d84001a40342d0f0181d05079107000340d241080704558108140500e40e0314402c1030300641035026080040c0241c03a440140c0c1501544410440055884c5408211500800307050001d001020492060310055481c007500c20070070000d50b800101c1c3e08080100d00001403c000b141d89014072700162030203d0190103070381c0c04041c01d080301040024020700d801c620707103000c4006060007450005c0650f00180c1440c246c2c2c0320101c0080c083e14084400603a580c0e022182c2944141417030709440c241d658915030a6401682c841c0f01c40350006090350700ba11482281c2d03002600803061203078118600301c1400703451402050084410000e00f044d6494107421000301e00340100c142c0f11100b80d07403441c000142c144c150380000d100300e03020300c20000001800e45042c4104003804e84001000040d540b4004c10040241c281c100e00b036903141c002c0c280b404800b90540c0c4028481c1402c00c080403a10351204007080700071070303800a2076240241d00381101d03030dc40c044600700c208041c2c80c6d001c01c0401080c1c88 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 751346492 1250 751345242 751345297
    0x19090b1f0f06050703180b030f0411090103150e120a0311120c0a02060a1802130f050702071409010315110f07080327070b0c01270b06060a05 62
    0x1a5521240c540600c490340400e0342540300e0f008081c0540261103922164000310591415900c1c14801c41c40b180005002085100c070525880b03d8100d0701640780c0f0b044001c0e00c800020101c7d03400f80e20403600c1000c64009440d5034440f03800b40814091070314014240301e440600941441d482040407485c00c0607035401c80070b500c14450200b550203448c0781c3c02040b0305c189000380c08004c469000781202c7e8050311400b0b000941190150044445002d04581040300605c4140e003880755043c8800781e0740003140c2d180c0741800b1101090303104a42c86015698010095075240c0401c0102c000341c6090b1407400740c07408000503c00f0480440b100484452100b50001c3c0100256450103c6070040a0036160000f000003241401d10130b600c800766000d03802070182c455a00b0800294203442031240d0500503280e0304214802c000c004560000b4041225140c400270550348610020b201c0c00c840c501c1400c50240181d009644107101c0c07139608282d44244180c03500c501d0040c81002c0680f0320b0049500880c580208900091845030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 751347742 1250 751346492 751346551
    0xb0d12050705010e0a06050c04060203040b0706060b0d06050a1d1f12030519030501080a021909060e01140303120f04030203070609050d022104050906120706050319090b 74
    0x64202c0002c00142500c206299120110b031a0107079003a90030480822058410482102c040721459001140341501c0e161300648581c0080c3c2c001d035001941e652000500b00400c5000349030b0bc40100000080c81420300b020440181c142d60084c084010000c2d182210071480f2980c1d140e008071194428401c00301100080303121442e8250040101c000144081104141e0440090447d04c01c5d44410b807121020107020403001c0f41d00034480c09101e07500c013142100c0903092451410308002d106004140390075446000f083c0580d11542d001e0b041140041c2c0041084801e0362030340c00802101140594034000690803401204400580b03804000d08446000c00e04041c0200216240e440d4815024804c07441142000c80d16100c0e454039107000f50090b90396904451403009044c54901a41c180043d0800d4180ba0510041c00001408250810708205c0301c00c907040400c1100a00421440d9562a501e02c4c0100801402d40310040f9406034050602c1d901c0b10020300120303485a0b01c0240050480c0710342400803144007400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 751348992 1250 751347742 751347757
    0x20a021f1104150318021513080111090a050301060f0e070318030507051b1012020f040f050a0608040b06060f0d0606020d1b0506010e071218020103050a0b0d1205 71
    0x2000008000941c0089001c5102c0f5241a0352400c1104440313a480c400043c0c0f4108000039404400103941205078044540580b102003003100b031040c1200e48400c2c032076003140c41917541d4441078040400c84620178a8400c1492002e403805a0081c01000d1400700c0031580010f4170301a1400031a16000000c0b004c61107548081c500e01d07c0d030b5994900d11941ca0030094481c1e40883e0040d20640980024061030b440d001030f50150114001c1d084907410560040c040b55003041032003003103d0346502003202c1114001a4409040038050150034030901c00c1c58401007006079030072640808140f150302070810001c1060410920380c0301000303503410b69581060070009540340c03050402c01d40d90f0929112021070b40d994001100c3c284c0364401e490315500a1440308201c1c010301d0076101c1c010043d502c082d0040c040400348005654001d8114200484462040d02141080d11006290101d4402d202403510095603410300841e5002845141c2c200f0540350440c01050580008070b001400c50f054070700000d14014459170845802 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 751350242 1250 751348992 751349021
    0x6030412180308040e0f0f0c1605060108100b091905060d02041e0c0215160c0b01080f100603050c090403050f0d0608011505012003071a19020a021f 65
    0x1e80c1c03a880d00f4a156002406500a158042000507001c450891704450285c1c190707040312601e658540380748107019070040c07500000e07042103080072100145080003414064006403015201810002d070100c0300310b8080100043c4a403400da01409400c2d00c1c01d000103502083d4440010400b550341c034010848002d0a903500941192407c00084080c016040700e4541c00c0d11605070a102a504c41082280c0d01c80129800b00f4611301c2c18004540300b2046062040c1c00201282407042100302151580c0c0680c0009901c420016081a06000100042803242c000c0d07250303501da0b080003480e0030354035200d42e1000d080b00c495000d4554140424245401401a2044124008a0300d85c0d01d203505015500a0580c622591066600b00034802103004a604406425580c0c107a4542c0030000c01d003004d900b00c11034941c04200e00c5010800511021a900c00300f4180c54801d203444220440c200100401c40310b40c0481c141c00d107124814880604003a0b0f021070b5020225038202d1030980701c200c4201c40302e00101030110300d1488 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 751351492 1250 751350242 751350287
    0x705060a15030f2102030d0f05100b3a060b030f07030209010e030f0a0b1e310317090721020310021917060112050a020c0706020f01061406030412 64
    0x135107580003004242510140701d040c8401000040000160f035015200100d514a00d040f0034412070000350050300d40041e0801e00d4102c9040590491018500d20640301d06500c4007100180413034407603138040c01005000716503005141d0701e8009182d840b0100702038180300c20560000b91021041e8841d4000c151310b030341d008050783d007801c1402da0800e070364040002048507100360b028001a81002d400c030400c420505d0380c644100280e600c1010680264a6000c40c060320030600380c4032814001082c1c0c0075000c400c0d129450b12851640300401800082034000c100440d070754000d1405005d00c110300182462604004c403080d1040400d1440001d042145901c111100c041c808030303002402490000c071001c03403951580c482a2407221030080c0c419402d0f1044070b10601003840c0f584501d00419160344078551000c1c0c900001814800c060b1100e81c140122988850010b901c600d80505025a013840780070014042000f2092002d403250011864500004001070200074030f42c0e86800080380a1003ca001290510001c5030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 751352742 1250 751351492 751351553
    0x1b02041509050907080c03070302010f090b0c0102180d050a23010e0d0e0102030f09090c0702040e0706020c060a0e0f0a0b0313110105091e0a0b0f0705060a15030f 71
    0x800510b03040780d20440511540900103050200400c1441e030709a8090040c10354281143c005441440c040342041d410050503d80000391095440302812000d1481c00004da03540321440003001142d044801803902c90400035040341300190000801540c0316a0003d4110103155003d03d06c2c440501e0850342081855080000385240c0750300200300e400070103880740c64650216500c2e030012640c0307001c0e014040301c0c00c031410842c030965450030000315607200603800c29040c03400c0b50903804901900c001c45c151040aa000c50810702c04c1c1c54051026202d03101d01513544d207042c40151200245610401403c081c0941006a410403040e210041001c0240010200c06a9681000c003050040c1c0310008100f51402e030b1421554629641c8200121021150010700102505c500c0920000700d404000c031480341c0c0610801000100c0010710005001030784070b80c0c4030031622080141401420901e006200300c020b0391805000b80789070000c0300342c2003050303d4000c2a13805940b0712a1420b0202c000b00740404010b100c0301c4074902c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 751353992 1250 751352742 751352759
    0xb12010501050a0b040f09023603012f03060607021804030e0303030403361202040e03130b0c030705060115020f0601050a06180306051e0f071b020415 66
    0x10704070341041c0c3d48185451358401460034640200d01079a015000c042000f040480c406401422130060340e240c4070034038a1300d201c8001840000914603440c904128200e20401d070700d020310030001d16050098030b550341d15140042e60040c0c08458602d60005541c0032020803004d464600c241c88165a020380b04900f40d800050310100ca442040f1001c5002800002c4164902d09001c029603004560545402c010090b84441e005036000b02c0d0710b24280244e0402d18440c910001c20000c00005140340c0358500e8800e145030062005681104640f42c003039920812908803e0032146010400321500d01800301c0e21400401d0880f0700314030031044080d105100f80b0340007044604000c41805d80700003454007124460f80c9a03c41164942009101360b81c1e0000d10b00208000742401511101c2c0311496403003081402c185c032035464408884091b03c4240201d00d000e031850400f44191030007550484a80b811085803480c11890091040300703410140c0d8401112008810300b1910382d0b03000200d4601c1c0350b0307000301c1c00c5c00d4662009 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 751355242 1250 751353992 751354001
    0x30f060914040b15030709050402133e040911070b04080d0b01020c010f110106031406010303020c1f030902040209040504030e030606010e030304030b091e0706030b220c030b1201 78
    0x40e9280f4400c500030441c0441020740302e900118025000d4444146400e4080e40202402030013a40c00c10070060415255110606c82c014810038107103081447c3d4070225001c5261442041403000d025010480142c1005908409840440d040c84070003056241c000b55401c1e4079800740c114002c03c60040041448108104003000d0300301c0318400e00041244c821000c00480e902c82a1080c7c5a000c40e92500840b41440e204403c40031100c451500045526556a500e9403403184001101c41c0064101e071005004042d4180201005000c1c101c480486c2071440f000c0d106031a68039400700c2003d05558130010001c64a440d0142c41d01d210006100b08110b1905042c083c0080c8804010340b4400d004940000d415913004070f18020381c1c814003400450420b0f056a840b10804400030304048403038480c808001c8180c0c403048050071004070040000d0400c06141034405425214070030060703486a010103660803030310400300c1940b25800341d036003101080340c400c8071400350002c0c074411000c9508000032180004803102c05400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 751356492 1250 751355242 751355251
    0x414030f1e15010b1602043c06030b0f0402030c0d03031a0901060e040f02070f1412310806070e030c03030702030a03121e090308090a030f030f060914 66
    0x2642c4695030070030311040340320303209004580070342c81c080c40018410440c8462a80f60303144060b10000305032240350506a407000705004000500c40c51070503250354907840b0b100d04c1c07804418803450a106017070441d51802c82510300203007424400d081c0703580000c09555041102c090304200c007410503401c401c070505004002e4260100d07000410344070348944003d68200f001089040307844070b03078403150200342490030800600060505178210640074040c071408201c80030001848144210300202ca401c1c1c001c0c0200e030a0040780c0c0c43d8800546028070098040f581c9404103400c403807081e0b6042c09441c00c0c0c903541144407082035810454462268808000e4500d800026040c1051011412144842417042c1019901c0c13007003520003505900f0241415000074050400301a000c0aa20404220964040c1b5a0555080792080c842c080649602e1300c2c0c4141178210754000d81001c8000e02030859105641c0740034002e80e00382c1b2880020940c2d110507400d00c0c1c030100d510200103030007200004c0c0700ca407202c1d18008240c400e0566 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 751357742 1250 751356492 751356553
    0x2202040e010e1005010f0507020d0803070203030403021c0806130e0706050d110301140f06070b0f0601030516020a0314040915030b24040c110316030f0e060414030f 72
    0x80c0401d00180e60303483d07801c0844005030340780d0784040c0f0711200444807a000a04101e800640e0b036110540003910314005507208116650007141c8910301802d00070718040940102c4104285c0d105043c996042d401401d150b44a0300c20340300940100400f0541c0e8004000e525105503150080f1100410180c0e803140c020106c0c0002004140850302c140c05240407548002c0c800d0b141c40142010101c802401c00c00806121428010030150602c919a00c881c1050300007105e20400c04560401000034540e014810b00313800410030840000902165840a503507408100305c040e062020001001950a01e035504079000b4129218007444906d10800e4400c1002d002408221001c0f00b1034000200542d50256110003031007003030034044141d9118036003888020400006050208522f4094100c03001e1810402418241d400c00c003582c4e2482003500780200003944030300c0e2080030400201603001480d030781c1d482076034181d690b08a401c640b001d00c2c0c80000307031906090b0328180145002e80f2802781586c05031042415003240102 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 751358992 1250 751357742 751357769
    0x80705060f07050c07170309031009031815080c0405120307022e12090210110f0105060105180d050a0c0306050a0b06040b0a1404090f0b0d0507052202040e01 69
    0x18035043e5030701e0054040701d40d02544161002c2095030b400503086040c5881d04401d4a281600d214003180c10000714001ca880036940721000e4800b0503034020070b02e4041c03a16000d594044c1c1404e042104414815464402d801c005034040400c04401d11710302203400500c40100014130b81c21000741300540383c1e0412202684154000700a020540002c000e08201700810090780307140d0341c03001c00c80c103690b01c0c10601c8070f482800340d40d0072032440161602c000b81c6180101c945c4820901206030303a08545460361155445220307905000912180366040070a0b07d44c01310120310900150074041000c01c22500c413121025004d40702e007421a500707222800e1400800c0d01d00911041c0100d50714540580241c90114515540100c8100400c02c00e50070400003074003240303042e890001100d801461188401c5c3d04150003100c2d0709076684d440525406070503c14490341e88010b461850341d281040d11501d0315180d00307200e404e0003080801c0718092283c140340c44a94801045142c00c641b500d0301c1702c41c0c8a103a16000d0044030707003a50b0b10 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 751360242 1250 751358992 751359001
    0x6081009021b0606030a0519050a120504210209070c020f04050a020901120c051b0c090106050a020c0301050f0a0902130f09140303040c09020d0603061d06010e010b0a0f0c080705060f 80
    0xb01d250301900750020000c04020121104490742640b01c081d09550038025031500f200019644d140c040bd4a601603920b068580742030105000103005283c01d01041c08041450a4006031280c160207644150b0398140703012541da20380003003040000e11410040d4090b181c0010450080042d80c0a40944031342070b80c401c41402103510340142160020a0054085a01844640b081c078011550300409580d6280c1035450035045000800c1c1403810030f8109401040300401c2034081540d0401804580b038908800a203c90308011003d0464040c000d080302444a803a00c1c060310941d1140c4071196888803014208000d08646200e04400030f0071410002c8a0010b0201969880d21500009481c0aa90000c2081d001c09180203c02d070020751000c00580c068545481c40080481c01600c6000b43e21000c1e044140c494071054038446040500503001000050316000040c82a04031201c140c0703040381054281569003225101080d50f98020b001402400100009440c40c204080494203d024181d04e44041c14562038 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 751361492 1250 751360242 751360249
    0x30f11030307050304120c122a060e0f0616060e060f16080601180605030a0b0108240a0302040e010209150c03070f0c0506120702160302060406081009021b0606 70
    0x14241d001d4202e500a000030b02c1a001082038200c0c01700d1048480ca069141d548e10422410107082005403501189100b14001c0c581c000d2070301d070350705003111000b1801660a145016103a80e500401d441e003d58560800101301b40c40d18011a62260080f04458000d05040d14001015242150401081d4010070000c100d45d2002141004e000c0d5510381031554041d100c41383d0840307007820300818082c1000a090310078042c6908030412000500300c41e94406079a440c0c204420404c0ea084100c3d004e04001c0c0000070040d28a0000726004a481200040184444080310024040e000e107a00081d60041c944a00c0d40c0812505500505200b10700382c40d80a841c08143d0305408103402150416800ba80040120790002007031070805400c032610440103440f0964840010805680205600980e180941c400303108115404101099982010102541529045501054890049206400900042c040450112109081c454002d0184e8103011502d4004c0d00908010324202d16401b0700c00e13030081c40c010904509 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 751362742 1250 751361492 751361497
    0x70906080d0f05030103020f060d060905010815090c0102030f07080904020d0c081f090e121204032d08070509030f031309150e0714130f061106060111030f04030f110303 74
    0x390020000201d00e5608c000f806078646c011942d0f454500ea40b4000481d69900c18072809010b009002e006111150004120100c0107801a020741120ba0184900c80080daa0001c1282c1000e9108643c003a22500c1a00d011080307070240d2580d07543d00600104400e1090342d119844882c40320416a00c8004c55120761545c04012071180c40b00d00001e0079081401d10102501d5003115102554030b2007100d00b041041c260072180d030303005202a007610003a24010f01080c160b10803585113140a04503001080c0b80400ca80280280741a25005418445010001b4001c1c6024009459010340080c0030f603850b443c0c882e2455500e0740c0c080100a41254201c200104007880c4074407400f00317042e10340051459958240300080d55100802800441004010211075404154143c09005100943c03481100303a9070801000f18407039501e0f0340001e01048951b181c5181c111400050703450300107a084c01c0101010800040c480d0840c40341c2a500c000049002400008108200040065142c003980450040d03814803010140c692 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 751363992 1250 751362742 751362749
    0x210e09070516030f050408070b12010f060c06090311150f010b0703231b010b03010501172a1005090a120302060a0f02041d090d2f070906080d0f050301 66
    0x301c580c1c030100d0029000e039449216130062410a5810950750b50411440c05009801c000310454000c102c0d0380d400a40c030701c4c0709405003010076440c40d6801e0520300020506a9090000f82c40e040c1c5aa284405060048a81404803149001a02d0100c18400e45500201100350754083c038480384035000280d480c0c00102681c14165042d0349048010380c070301d85070b014041101ca104000302c00c42004540014100341d4451000300c54818000318120403880109401c50304160702c07401030300d0f20494408e120703603d01144494012105080380104070300c5602c0d40d290555082d24066802181281c806181c46421401900d070800e0121101c0032480d84030755042148103150f48004025a002038080303040300d1001c0e0001000d069001c01d0050800d82d542c101c05510700c0c00c504070244102401010320428000500845404207014282400e001080e0410403484251040031012400d0007a603404510311000e00100004109240091111035250340b0441d0300d5442803010400842d20181c06008014056005d0701d048 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 751365242 1250 751363992 751364017
    0x609060a1b08090c030316110402090a1e0b0c01091103070f0b2b0603020117060604060e040b100801050306070c080f0a0210140a1103090604020d210e090705 69
    0xd11811105072030212010f003076954280a0116a03102c00c0c0c0781000500b070074100704058401c02e2901818007101c0162800c11403030081c3c1c0104481815278a170391104008448841404801c081488640c40e034107261b103608803110510001510b90603031941500480280d0340180c03045d203041d03445a0109070b5124014800c0000c0e44030300b09410004c4400e00c1c0080c12102d820543e49680780c9541c20054010002000e64801d52140d49840c144290b51340104da550084211070341c00c94072800c0c14030008920303004074800d1004001d1034441a400e50b8a55800c0441d9408000e000003031074954a91015101d61824000c0502a00c14003000680b034900c560421400305800400b0245486510240d94005500801182c01544124100ca1a604289100340d214905c00552601070f06e003802c2c440302095070050290303558107400500074001c60707000c04151321783c1180d4121342002c09092540740940b0000c100203031032805c40c04c50b10403150180d90007201100b0151000c80d60007085507550901502d440c001c11813040351 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 751366492 1250 751365242 751365281
    0x5060f032d0a0b010f030c0902090f0909030714210f0412110603090d020f01020909011806030506131a090a031404150e0f0102010608060411060f07050609060a 70
    0x1007040303040004020040c90000d032407070440180c07100c000c01d240070f0b80300e030305c2400800008100740541d5140c030201070402d20b04e003549007141c100c3c00250488205101141702c0d465007404101145030400484104507400303e62070b1742265412410b640c80300031480380e929045502c540381d104055100c00880340c90410140c2018207003400c10010740400c40c0040700031180794100c01c0002c80d42d559850b025504c215000c800600360300c407011200a003001c1682c0020f0304140c1c0107105c2d81c0303000d6590030407041c10359a0300402c81c4950190700d1140c10260019620141c1140106000d01080b40600c1000c100898001c48503800e21000001042c1301070341040b1207000341ca070860058a00000d1244004964140e015142207050540703400065103182180c68809010444c00c445444a0303081210868031159001d0000b040414900407042c0d40b5208014002401c4502035074400e075031030f0faa06080e00d000d02c000a0300c050722001103150280c2d9540c400e03a881c003100c1c440d9000040910300c1500400000310814030740000c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 751367742 1250 751366492 751366543
    0x302010801090209060909040807170f0d0f020409090503032406120601030b03010c03060806130507151107030c23150c10380105070f030315060305060f03 68
    0x80d000403041981c010010850b92413240e469030b540034004c8e8010403103280d4500301c2c0d19090703019000340c1c502080340b004144000c500c0480c900c81a10801c0107000c1303000c900c45071310b1810796000b4400c86d005248400d00c0c11000f0002e02c640000514410381c8008520706255012944c01400e100e180d400d00350b4414010850b4000780b81e0752081603038126806040114540358580d000a00b914040145000025903c2d001003040c4142004000c4d003150888240002c90040c5442d02c64403581603010760b100c42d03112580d6081e5014850004040341600401c29240b00c1a100d00d04030305920803510030010740d01c180340482c2004100100c018411042e0081901803d9924440c4041071504031101c00b0070180502144046481c8203030040c07220440920803c106050b02c00c05140040d040400b410741400407008580d800c00340d80203801c65008a402180d001c2d00070a10f031400724060240d901008102c00000c40c40060b4460300b68028900821040b2100313009036001100b89a503543c1061000503c0070189100203 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 751368992 1250 751367742 751367759
    0x19050a090e0d02061003321c1b06090201090e0a2c101d0307140616020d39020a1a090402031f060513050406080a0245060108010302010801 61
    0x84000c0d88005101164401c080c98040780c180e07d240c445090350001d151404a141103a105e400c4200c000e4104900c0c2084244500c02204002140c0100b41c541e40315096402d5a000392500030080264241039651454110150f50180c05450300103225404501c0d4420030440741410340c1100c54450074000d000014000403201e000d0000380750749502d800307191000200c5194061005100d05030103070020403605c010180d04945032020040c0140104108084010b90003036004c070321540c000b1218500141190000105001141c568254807211800b01c3d0316820021459030170304000c0c2e54001c8038034085031036641d072040c02416100d440007070701c813202040001554981540555001440c0e0100b100041d0580c0181958203039103504400007040c8046001d04042140342c8080000d841c00b56000e10010746800d04595440c10070710f130f00a102e0302000309481c10f4041c0881c00300029001061020b102c0c1e144401d84420406110700c0609070910350751000401550082d23210a040741d6045e91014020703031914816 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 751370242 1250 751368992 751369013
    0x304080712030e100203011518231e0a0905011406160b0108071e061e0e0405070f11010c0804171c0209130501080c19050a090e0d02061003 61
    0x103807018903a0360100b01c1d00008082006503500c0f1610000140c3d00e5040800400311045951400070402441c400c04032203001038602240101c501103501040701c20049441c04107080001105503422421081d01d00740f82e00208603258901142c20340d95040000d440e0384000c41556000d0041030880c242003001400f150400600030009020310361600744980849507180300f0200000e034401000e86d030010000380302d1854403141601c0281594003410128601d80700c00501650490071094444400480040300103602074043d0721001b01006104000c603151110026121102c1c1840030b40000f0507108060b0004e060503c10540c500017651030f014416030341c41e941d90032452101e03809440020340c1448406030758202d103035082115028000c03001d0389880b03441080c03020340c0075030307141880c440d0341007a004203c050340c042045181d018051316060707004000c1d141e8001401e01150700180e000303040c9000014003a2090340c0011046582c80094803520510500101c1e0388240c15103242c0b06441c10040c0810025015000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 751371492 1250 751370242 751370273
    0x1a2a04140a080607050c06090d0c031b0f080408010c02010b0a05060c0703151b0e150306040603050a0b062404290c30030f100b0705010903021203040807 67
    0x100701e541e4654019030f04146043c4c601e9004600049500c00d0004005d10170203500084004c0204081620014010700e00010900081c00380400c0d003501d0790780c088410321400d01054011981490102662410180c590321501c50742c00309511f00341c440300d101441806512915000105140202400c1c036080104682c05404241c12522500c81c00000141da003840024000204410000d40303100c020603e0074030040c80c1d41680b000c102c2660f0b03220342180c0d03801507070343e800f2250400280c0d120395401c07000c14010181034201a00510940d552901042121401036126070710030741d00700c0f98000c0d1032090b5005040780c00030900b4540d1000e010a0004038144605803081d1281c1c0303481c1c081650102e418145181c0d006546e0414190400c40f4480e503402d20640560b000e60341c1619080c500a80c5440c0e07443d6040c08050035184008d08050003103040001c0c0e00320300300017428102d583c00c0d6854016181050082108081c00c0f00503000e0200043c000411840581c0d101c0c42e00401d0003807400d18555100d080d80244600d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 751372742 1250 751371492 751371499
    0x118051b0f06030601110601080d0207151b02041d070f09090206070308070c0605010b09040c0e030a080c010f1e06050105120f1806161103040f0303050310031a2a0414 73
    0x503480200146d04015180c0203004600c040c1602038000400281004c240340c008051341b08407165044541544143c1c81c5494000c203845c0300b0005082480040c002e0542d032030f8160003450008180040c00c02e030114000c800c89103060001070205540340c204805480072428082e512241c24014a40428060031550f50301c14030b1880c019210b0000340d43c0e000126003003a0001800014082201036045c00c2610940da840005402d000141c07810400000c1d681c0c4502d40c3c0000c03c203076408940140403904c25000000140c055a00600100841d000f60b8103001100d031031480f0589007404000101540100d04907510164a1a540c1d030096803144035004221030301034003118006050400315590010b0030700465000b051078107080d25851f03180b114028100c4406018072030070f076001080200003c0040d20120000c4a81c90b003003d5840ba41c07121718000b00144154000340006030750049902072001c0140000e8840ca50165202c0c40d1012043e000d004000c1e401c0003a40303103c2c00304200c20b004284c1e540c450310000c088002c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 751373992 1250 751372742 751372757
    0x1207080a0b130203060c0304020102010f050123012c0a12031205042f0f0102061e07050f0c150109201c0212070e030a03050711010c050118051b0f06030601 68
    0x40d030104e4580101116200120345011007400110740e428081d103410030500d001c040c811541058000b0703400035032092013008074100c6610f00344031990103000541d01c040450710015502804044080705e000c0c02d0014054822142d010000c221601c403102d2510392590140d0742c4464142e041382d502d50040c40c0207807045d102421010f440611900003240d0340035801245a11075400340001c0c005020580d14020451030540d00440104551034058502c0052030610001049a20740c450003070a9030ac03440396444a900000c000a04460b02910003e0820700001880d85511203a03a42d800303040003204d4505228010b5604060144115000e401010700201010104096484243e55170a003041f0303030180100040f10036034101040b40081d08040d8000ca005401e401414240440b41e03002070807403090282c02403008580d44501c0c1c4641c1d1044a04080156010008012260400300005e815591040085601c1c1c4141a0310070a00b03002a10520184080586031028420100317040103c2c80d00010030803410025031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 751375242 1250 751373992 751374031
    0x4030e0d0f080a03090201143405070f0e0c090609010e0415060e03010f1407081b040914010603060807090911190e0708071209021f0302091207080a0b 66
    0x20700401c90f0209036140054402d00c58400508101610800352000c0c02c0c0071700c031402199801ca80070b040d045034025008881c3d1000300005212000382c29038041c0c902c0c801c03100003140d5083d0b240504d000f43d4a517603d2082d5641e5a0608100451244070348840e00007030103000d9402154019041d031300349054028000310743c0714114400c048030200d0300d6007c0380001f441070807407211504080c07181001c413011030b000500c0719103012446212090702c0942000b042102820001d01407807901d000030089107c1d0710b4002035860303644120303400151803251b000c0c54412503940b0000424074000d11880c8229203a601c041c203d0341e031912001600501c800c1d030b03060f40c50b1144010800c491340d880070071101c40380b002c07407142d0301080341030100c050104203000b0088420700c030380f01080c010792036001840c81c0c00001140340d012622007800d1011500668020400c20300d5240360b00c0110300d0341e03605a000f0b8044810300713540c2d508800c6085000ca42c0c1e20b80f02e0784121002a0004040803011982d0360180c15440b8043c008500d0620a9 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 751376492 1250 751375242 751375253
    0x7090e100314100f0207050712080c0a151406090109020a0302040b190807050702090a0e010b180106030b06040312111609060906050f100f1b0506040b010e04030e0d0f 73
    0x5401c0d0401c821600140d0040d8604070740784c85160801c040c040d4045080540d1a65101d0b07484032a409043d015911850540003001400f008940140700e5420035a03082929074038007141424080414a0351403401e040711402d0f03c034558400240f10703e50046c843c84243c2d00c1c1c03924510081d48155445003c15800300300108402d90208000c0105520640c0a4440c103142000010080c02e0090401300401c00e0400041015907940b4800c40c0c4c000c1e030009000100314203016a06401805046007184e00441e940c282629041180d41c49241250442c2e10103100d0401844200001c0340b10760b0100a00180841810524091042c2d90452040c3d0308030302203c0038040b40c00c4490040512641c0300f02c505980310403041c0303c140c031180144801481e0a851070a043d100e03807400103880011141c441e00420544104034060350344201882042d06075043d2444000e4802400e1940d1242c6048406403540b0003a080000740220000a000744502c1c2c1550342c1d9504440901d04102041075035580680d5200200089903020a0f07 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 751377742 1250 751376492 751376513
    0x6030b0a030b010b0405012309222405010516112209050c010908031c11180315130b0403020c060409050f010f060906200d0207090b040507090e1003 65
    0x22944d844035407201d16040c00140180210005000c1d803071f00303070301901c2d10054216040d200d49407401c5800c034030000c100411500030b40800c8001110440d0500e0b040d280440c4451800d00681000c0c00e00903d44282c50b4001900c280c401c5035504842c8100743c40c410804101d04103c2074107882801000d40e01c0c00701d604d401c4881d01302c6603100a011810356654600d800c0001c00c001c3c3c1c0c0402502030a2132030104c1c0c582961141c1ba4050600d0401c02001c0d0140d4840051001e40e00012a642050081644450580030b1143c14020840c8030240644650b01c1523169810350301b10f20a10070244056000b0400f10745566940040c84c1c050400c4096110f1020862229030f100c1001d840546007840c400222490f2400c9500c400e6130040e40f060003003a03900b0005014240c1d0104c1200b0684049080c40054400590020200d1a40000780400f90340900314030940a1580480c0000440703aa030501030150b01302c1c090130802220001cad07404001040a1242c2004966440c06840b82d021140181c444e6400e603483d00c401c0b6511 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 751378992 1250 751377742 751377749
    0xc04090503161b120819030b100c0507120b0c07030504120f03080f040c09021309020a05040302010801171b030a0b0108010c1211030714040807030602040f090504050706030b0a030b01 80
    0x60b109124110f08440400b80300d801400740e1820358160104036100c0054900c503064440d121000c01d0710440564601030380051001690145c030030b01c2800f0200000a0031580c4044085407107004080000403915040b142842120f500808010b410b42c07035140d041c440c0c50344081e104406104041c080003402c45419401101024010351742502980b81d686801040980d00504d41d141640404040c040031907010401d0310240e03103268000594a854235006840c08101d81d0b4842004d072800091002161035000d0094000c8a200780c0b64502c1c56600c46600e116418040c40c24240c2c16407002c0c09511500388848403203040000060196042410580c403500c0c000b080903000810030382e466035106404503034046001421402080c004021012210386501405c1c030015102d40100410106803451985030842100d0091119004a03081580d40c1c0ca0070344069000340c0724001c0080302c81c1c3c90000303d40700c20340540c41c842c5070300501502805003444c0b010b4000b000e01d0492150415204100800010b041d0010103028 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 751380242 1250 751378992 751379003
    0x90a0807060903171c050a090219060e01051606180605040c030b09150f0411090703050a0f0903020309100509030106030606030203120c120a03020d1a0a0e090c0409050316 75
    0x2c060850901800040c030b662a2607407002020060701041500c0c4036004007405941150104243d00e43e242000301030000040e000e03600a0381a10204420300e020960309080754070645540e001d10401c0030040d03419004131603002c1e400761302c100c0f00300b0005182c590010841c6c0000901e1407031903200684802c4101e0304212000c9072002c25468043c002e004c0501c5640b030340300c1e002c4401821031005c845492041d0a40180c0300d42e48015068000c207081050503080c83c0c8040c3c4029140400034580020014042d2a05035400091203203000d100c0394601c4000c1c0188400c80e90103030000c5140c82ca00806201483c040b60584204000c0144019012540d0a004120095010b00030116120303007140100750400200440303e05500d407003017100b107042c144040b5911010641d07420160744c0340d10300160241e020340310724050040c845107085100500400c1000e03200c1241e01c01034507641d4800b61244450711490f001a80c2c00c2c8103039840005122000e26180d0808103441c0d2182042c0c03424002c541e600060300105e0b0ba001200d8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 751381492 1250 751380242 751380257
    0xd02030903071502040b1204150c170106020d0906050c1e01090302100605090c07150501030303091208070503012601060303091a04120201030b04140f0a20040b090a080706 75
    0x40c003150f04001038030050a20000c5280502d0111000c20612801c01944c401e940e605000400f801400c04000404041441082c000c0200b008c8004101103444c00d030300d0079911403600003c1210f5100040b1112600c3c403a40714018401d042503000c3c2c91a40085a90800703511650000103506030b0200c2816010324590000440c4102861030081c0c01c024282d92044021031811004014980d0b51f03009907078000d14401e428955400075801d04000581c00c0184c4030700002d007060000010154550300400400d0f00901446072004411801103818500c103490300c50024509100520101741c41070307541c003902c041d030030007644412205100c00c0d42514469030065002c1904228104070301e0320801000d0ba00180750303d0810f45058204032842c19040f90740c4001904069640e5841c0d90303d0b8503541d00036a0b1440050050b681d544c6000300100091520842d452602c060500c2c003000400c10801c40d01c0031409001c0d651035403c2905010036103200d5081103020700d07440000c240001643d0700341480000301510035a90390a0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 751382742 1250 751381492 751381507
    0xe0c0307080d09050d1101030207020105120f190c08180708010e0d0e01021612030509030f0c1f0206065a10030f020c1e0d0e240d02030903 61
    0x102285890384c000d5000398464501c9100150012000964100c024240180c580d0894001242c1c1401214030564104413600c051000321240c5141140c8030b9841c00c6409144c4001c411412401d403059581030f48042200b4802059030303d01070b80002190100381384101c80b5455903511081e400e41e400c207181c1c01000d0300101c5140100a611500e240c821020a0000f810b400401596100c00d640d071521490401200452007441014482c004a44030b00d40020116070500d00c134030420640b600e0250001c1c5102d0300f0601030150503078021760303400103603ca00c035009028250307205418001d0850081024072582a0441e40c010000310100c06109090001c045c0820001d01d000507d100d680d0904030500040d4006480880810b40e0321403012201c2450340f441c0204009484625060103401808200c21850003980100041e00301500d20400c0700e4194041121440138910000344ea06120303480805d60021410100d00d40e184010032948404405801401490080144017580490f00103a400503030b103030400110007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 751383992 1250 751382742 751382747
    0xb0414011112090a020a0b0a021617010c09050a031e060903020d020709110306010c1401020c01020d0f0b1008041407060e031e0d18030c0b09150f09040e0c0307080d 72
    0x220751103100e100042c284019117400160514006219000301140700240f100c08040c42408410540710707001000d02c0950340c55060300440c04141f04080703621341d0302c0c00c2d0750324451a04c0703805c1031400c565020b40303d0700106046440701080f502400d5100b43c66149000705141c00680ca41c446c1c403220600035806460103a0f45d4680c000e0800c51107034040c5200074103182c21346601802e07690859401c54403d007400c1d51040710500d04903c40d080408400310440d44041651403c010b4190018219030521150420044800340000412581e00c1c03140648c1012011005480f03160040c8441c41d08140901c045003520307140200100d250000582181c400240d003180a1010b0b03090420a0840c48c10a45c4940030b00101c1e6500700c695031f038005404150030000d0b00e44c0d203000c94121980d8140040c40d006240400303003603142c40480440b0b078407100055004941c0300c0c5090310303220104810742d0b04804403200c10a1501c0354040420000e000002d0a441040c040c08403c10f075103075001c10004008090200c003070041c02c034003507a01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 751385242 1250 751383992 751384027
    0x10615350124020c010e12010e1c03020c03030a02090a0e01090606080f310c0806060f06030f01030b0a0b04020307020a060f0e100e2802040605011b0b04140111 70
    0x803000b08610301425000c0072034000c510070041ca08203103409001c40032020300040d2107412034898050a07510303100741000900d0004c41c140c80d940c00c25001000c000007007200218100d00c41c00140c01b120380c0050001c00c00520b0260024520280028039003c50b20703494504003400d0f840c01380d0000d801c4560305c603c10481c894005480030340c85020034055408078070b00258440c400640b07a00100b402001c0041420b0304542092110318003880e0030405440c079003038840c0030f296510301c025a0740d20720503407802c220031000e8613044040302e100383ca42d07200017003d80c3d1071980c909a40c880b02400314424503840b1000f01c1400c0e245c9101540c032402660f402131440c9102410004221609000c031102044d082010404c0c003020002081c1e4000c081e940c07070024a0318010342d41c0d64288086000e000d81a241d19400c0e1215851141c020094024001c41c3d04000709940c0d0401580e4112110a44038020001300b100070000c00d00c2c1f6111240e0043c051500f610369042001a41402c445c102c88241107005000300317480701108828040c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 751386492 1250 751385242 751385279
    0x603010e03040b0a0e09060f0f12010f0e0f061009050717070e040b03031617070f0c03030801061d0105070f0506010b040905090a020117040c050604061d030106153501 73
    0x591003043c1c02c0130400700300403d030504e64250064684080d120341644407491660ae000e2240d00080041246ca49151006000301010140c554440e92545080030794011a8241c01681e424080071841464148820b028000c010080c2c424012602d05280e242040c40c2e040a00c1116651f0341c0c544000308032020403084402c0d501886000f5070080c0700580c1c0b08000040c0d4094004c0d00184a40020142c40011b1842442090700040854400b8034008040083e0040c01900fa24401d45a02c0641e80c0c8900b03048840c904450248046030b07940c441040703441e501500040c41858040e0400c44107110041c0c03100c0307241800c01c7c1c1c8001c0b103264000504010b200c0a03442020b80004254000c2c0031a5480343c0c00013004081c40c1d02e481c00040d0a030f0340100741008011010000140409440651203681d24080603026103001041420241d4a07100000d840d89010301c5010251850b200e407880c000380104501f1078442030b101e18254600a00b80e046410440794952605030090303400c00325480300e5030400d800054030581c10302 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 751387742 1250 751386492 751386499
    0x306010f090b1e070212061905150f120616020705030c0d061107050a1a01090b03070e1008010e0109021906080a020a03020403120309020a06260603010e03040b0a0e 72
    0x2028010030500348202c90100510a8100c1041c3c0342c00340c410181c034420800000c1d0310010f0320b10510041c03800482c04a00c1001003040c00400380450180c3c038001d0307510440d40710405200c80e43c0750401c68a0103c01451b40340b01c0207086c0b08114010500301c00e280041c151440024000300603041d02000390f0420a41d0090007095024001900f80030001c5000031795480300082040b620703010102c050f200e201d01999801504201220140d0030325062010031246100d24815011325004004a1940c600b07005a52242d0741c058000c1602c2403415451381039100c0042c0100c47d016000440000e040042401038162200380c60000203807680c518030400412441810172410310700d500b0403080040a0300040764941c4000000c5000da079800455800718000c0c801c03500008e240c0060120b451041a40c160310006d0410b00c29126110205e0301c803141030302d0111140110180580800b0036205481900500041c0c1046c0090004500036000c03100360380c19500305820003985024003181d4008410b40c403076100402d10200f035 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 751388992 1250 751387742 751387757
    0x50c0708030f0f06042f1606020301140d021003090302030d0e070807061803060c1202070b09010f05091906090b07050a020d031e0b010e060c010606020c060a0e011d03060c0306010f 79
    0x1204403085e0304d1140300c500360410400d00016075007482004100c555503082c02e1f4503080784165600c1c25900035002030159504030604021081107609000b030f000c0a105d5002803203410781c1d21f8048000c0303000c0c00408908404501083c4030185126546001701941004441e010b0b100917400c203d285454000e850344510104444482c00d4100080759115a4050302d401400100780c440122000b40e401e0604681035103216880001c1100500000d010705601034442c601c002d11081041050b4041611015a04c940c039540040445026144044480303441d078138410f44010076841e2140c3c582203100d170801c0310028041000000c00d0302c440c0d1f80c14082290001d0460404100c0d8000a00c04c01200f144050f000d1b400700c0303548070b1f80070b002c90703002e08c030b224402da0b10003441282e07146d0b2030519140c00303440c440c81424003521411641c14400c1c6041130964051000d60340d40d003e0a00c5494004481408161020851b41d480e0243d008043d51014070016214906180c522660b0b402c09a0005000030040e0100504200b075a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 751390242 1250 751388992 751389011
    0x215030a0e06061e0112020c0613060b04060b0a3b030d180e0405010213091a0a180c05041a03010617131101110a06050412090f03020103050c0708030f0f0604 69
    0x2203d0700500101080c0390580040841b203c0d814002d11550880990030311171041000f042900261420401510858003403201203047e0701408107a441600940255040502c5000003482c401d02c0d090070341041c03031134580480d4104003407180175040c0308880b840c9510028131030714605400e04000322210200b40e031030b00840d030058013091071650b0039260081090002c00c480c0070405010f425016280c07a40c545181422140d940d5001400051015080c5440a0540d01d0205807031842d101030164200d42c142108a032220442c440c40400030910400d058082c00014440030846943c61a04200c050b070103428807640d00d5041a10140620660000407030b4102c90300300801214800104480b101d50b40d222034001c451060200c0160340c07c80c0702100f04212072080f0501c420a01401d50400c1d4082d600030b918010a03c005c80c0300482d0386154501541ca807407040f440c810070044d4407070750223180e00c104000c201c6030500c1b0b150382c0c528005520545a450002c60320030180101c0800c15980a908441c04480401c04c4014 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 751391492 1250 751390242 751390279
    0x4110301150c080408012f0f09040213080a060b1f0c0212280b0c0c0304060804020103091e060f02031005010c080903010e0d020f0114040803040215030a0e0606 70
    0x7064550000304402401d9001c10800510150307806003051600a0050480c0590080301c809903001e642030549480a141c1d8408103890340c1110002491540031610b0140c140c814000a9803020f50101002743d0003071800965210288010681c2a10548011034000140300c100a100d40c4252101e80002030890091140b29810441160741d81c3da0565841145c0c1e00d001462a0030034041071200700107116101511300390344044044d00421035105035040f06a5886004002c0018010f0301c070500344560080205101142c000c9410950042c414500801c4040840d600d02407200c8602041100080038100240204101801307455120001800c0441c21450320300c24480030343c1441d21610741070001c0c6107410014011420122a10454041c00070b1000d44200a940303569003061030428401809003d55001040006004c1e21202c4188080241c407030b500d03107403a10380d12070340050000c907400310603850140b0541d41b0b103402451050118640004081441114681c10f01d20000c240920072000b0002c1051400c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 751392742 1250 751391492 751391519
    0x141c030c0f0804150603020603070530041520040510031a0d03110303100f0e0f01030803090313080706020d0801050a2606250305040c150512040b040204110301 70
    0x11340000540980c024100d5410000705410b03000690811000401c00c122581c10900400380c42d545011755a4081c0b0a01c400808002c0c03810f81d480e2004012207001c203000c180c1e008445c1c0641070358a000020080c00d01d00c0d884c8100840c080e02501010800b250400017460300042c0822034508a040500a0fa089507040c2081188410010351042481303203112805d05120300c13020f40c0d0b2a400038046030343c0d0f810503400c0886440c415200c1d61765181c1a602c4045107d40c01102000e0007102d4240301403410781d003165121001600010043c0655200c00d000c52080900841d07112001480e0780b2015100803414808000d08050115401d001130100c0300340100120380b6098001012a0820760040c40c460000703aa841c0c006c201405c00032a00752244109001490311401c01048455600003c0490a960b58580075400d136181104c0142c00c802901d20100107890907104000260805440d2081c6440c1100100c0c603040d54090740d0580e0001d1000e030801c411810684100d04500c010741e83e030241958507204400f200b41 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 751393992 1250 751392742 751392751
    0x606060810090c020703020a0906030519050a0330091202010605030c2412071e0e0f03030d150504061a07080f04120f0308060603010f12141c030c0f08 66
    0x565564040f88194801c0c42180040c40d4000c00c51400310307a849034810094140c42c08152140d000c1c0e2600c201d66103103661060040b0700c1d800400f901003041151000d8801010607405030084039118200c502200034028206d0003503401c40c0e000083e0070b491908040d149014000001419a031509a0501032650005001c5000850072280f40c40804c0e079102600710043c0160075140041c0c071003c90070b10218200c40305604e200780e00c1d542d20994040c4014800c0d0304410000354420340400d030503184142481c00c290499080841300070b0112840c140e640b0344901d007200d151010904480074070000c10b102903c3c040c0203020060046204840c0c0c0c0d074100d481d030100c0301c1c81100310061105000246880398800c080d030607100145a540c2d4240610304c2e00d0b0402019501c50904210006417030440007513030b545040b0041e24117803548400c4141400703003840e07018030714400342c9182a07900410941c01040f4141c010003034010000d00780314440d41d1200741410040c040e0750300c0b402d00c201446100a84080103651041c3d8240e0b00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 751395242 1250 751393992 751394009
    0x2010b0d02090a0b0d052406060d020705211206060909180109050a0b040201260106050703050c0106152607030b060d09030e011407020603010521010501060c0606060810 74
    0x210707280c0140703000084ca104000c064200c41408031003030a102000c904481d03200c50820710087c1200b103100034800c4c4068101c40040d0302c0f08083c44840c8801c030329035000c0d200c014800c004450185908045103c0c40b034080000c49071000b81c000071946c020646020a0310340054013502c806082180b11000a811001c0c02810f90001c2540003540c046a004250400d03c81c1d13580003030039505210100c0c106100390040c100c84c180d0116a600300c0840541c440004884440e444601e007020290342801d00449a0398000e550590802000b44400a002102072246000604150041c80c03800e916450025102c0c0041e00c8800101103e141e5100072140d210b52485a4002c55a280c00103a04070300c0320004109020f2120b40300800303450030310140c04054104007100c02c080740907260f000e23560b060503100d44039034442c1c200025000042840104098105995590500940e01c07031590032100c15005c490342145d00990001c800070b140b00da41842823001520800b0040d11a5203442c2026180800441030351141600c60743c00c6 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 751396492 1250 751395242 751395259
    0xf1412030d2f030a0b010c0f0605060301110c0a0203010506010c0f11130c0305010e2d1003050d0309120f020d0c0c08011e0f02031b0715060e040b060102010b0d02 71
    0x21803a40700d40e59503030114411050012a8007003103401d0610b54004440b0031203083e1070701503842a10341c003615020322482d07484070102c80c0003812640e641028080c05842c0640540d00c07801d0011071010b034040640440c0d94044002d0080301c00c00d004143c00c0d10405480c45060100f48000030020925074103030556419042160b0881d8140300d01d01003003032044010444040189054488040e10398276403c001e04983c1c9180d2059a07030746850a041601408140480301004a5100c900b148145c7c4503078600c0e03100c41c0140c2189a90380d6651136041c00c01c113403585244006a5503d10040c104401142880f0315003019241030307007086040c40d078040e42d01c111100b510030901207214000307130070040e011030308102400304c1e10020300c04ac0f01031400c2c41d01d1a90003001410041800d1220300d17100c002141c0b007a01e11450f400da000c02284405601c481d61554444e013819203160038110b008051117110390141c540144200c81c00c460f91440c00b41814280103002501d55411a41403581280e003540c1e40307030382c00718003543c04580045 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 751397742 1250 751396492 751396511
    0x18020906070b13261c0908300f07050c010b03030d0b03120304050705060a03020c03040f09180b0114030a0f0506090708060c0d020d150f1412030d 64
    0x8086000d481c50091401800d501044200c42800e044030108611400e04582042210652419560000c54005001e03620a11940c43c090a011905807030100c0d090070b0002d08101c203a150303150147e1095803424071000c0c60500d0360304100c0107020b4844580741100c14065079401c00c80360f00034070020b000d80300204105010490001d001c0080d4003a00e6259002400c580d99000e50009841c0900f400ea418984030b0300510301130368104210310701182e00c11a80311000d0b0400904120811125801905512007016400e101c8500c1d041400c000400140c25200d075072131002c1c1d140c020902c060310f0048900884200d29802254005411020042e0544800c1103400c0781d44079100700801e14050803000b01a000422440c0c0010a00502081d214082d17604503050b1a40355444c0d0b89039a960f030f14103a48181c4a80002c1066911700080f650240001c01900031003c203420380c10204c1500c021440f504a00c140040e01c1c04204080555108802d012001c00c0e2098180f1000c040c0f4508d0b141c0c0106298018010345846226 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 751398992 1250 751397742 751397749
    0x60901020c1e040c0201020c2e09030818031306050a0e04020429031501050d0e0102180406090605011d03012a0e0f0906210a050109120504180209 64
    0xc9086001030401041c2c0110110030a080c1880c200d2094003c2c1c0ca00100156058418001c071070600b50054000c1c110441c68180c1c814880c551700d1080e440280b8880c0d0f140308418071600a00f4010340c02aa91400300341803041011004c24441403025890f9441000300c991542560003103281240c07118144941c45808001041d0740c04980c0e8a03560354824400180498081d592000100305a400c1c26401082c4003c001c5207284507100a0302c136038004162040c8446200e40c404c02c020000028101c09c0842d000901000450a9810207620003d5a00030611007440b182070274800c10b4001c001d000c030240001c4c0e2a110010713203001d40116105030f1700b0902c0101c412458909400c040f080f00300000f9002c200c0c01c003c01d4000403041c02c84514000180c0c500351806114501000e1925400300003c0c2107243d50340b610010012401d0400302a5244400114035481e0613010501507001918007450011406c400d482c501f00700e00c0710b042030130341c07050000c18402482a0b85110a001c05180b4440800580c0c0303c4011000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 751400242 1250 751398992 751399003
    0x50a0315050a0f0603030203070b01060504030c03060209130e0c121b040203100f060f080112030518010c1b030b09010c050f07030908100915050c0d0f23100602070501050906090102 79
    0x80c110384c10650004105a4004014445240602c49550282c0d80300c3c1c00844031886184000382680741540c2d03003800411001c3d4000c180b042402001001c0f00400c8001c4001694030f42001c110003500081807035403141c103100e07030020030f910f80c110094041c000f1510140c1210010074034049006c0c0f98088009120a00030001d518050103140e454544a81c0e507661000707001a02c0c3c1000b50300040c06080c000a24000d410954500c00342c1d00d070f2919410101ba160800c91000700040034103040024025014000c140f5560107410030707040003801261001d0460605241c00c19020f043d4450f41e80c0b4124980e844254000152100c00d503d8020300c0e41da0702c40364281200c0720758090b00540c2a9018448040610902d240d000184052103000f08540280300c24101400702c4004480301da480200c00c00440c034803070003980d201142154403000c00103102c12440f6200550042c501600d42082441c09083c042185407542c0c56100504c1544020902075040c840028420f02412180700d00454002c40e20346100e038003d100 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 751401492 1250 751400242 751400261
    0x80d15090905010e16080c09040f02120102091908150c04030b010806061e1008090a0503070602030702251208042106270b18030a110601050a0315050a 66
    0x200348403420190800c94000c09000c4d141ca40c46215480b413440180c141c098003c0100e542040162441180c600c0078481c03c540d000f002114102e0821385890016503819003800c00c040340d20070006848903841c00c180200025580700c1d2800246c0030340420042c480b000074044440100e102605c8003a61920070032100c140c01140c0004151628240001caa68400058131030b2041004403070000f5020712400c080050700309260140ca40010900e4048807500b809480010f4100e10384174121021001c0c00d440786800d58015040841e2100d400009003c1519030402c000481102d050202c13801c001d030040841d2805420700c0c880c40f03180c804290801e07010711500b03d0030382d4001d080d031007030010050040d02240340c0e1251079036000701c4800c0c1c90140040b441d07581c1e00183c0303030001401c84c080c50000ca0b800d032200d8041900051080c007210f01543c154051304103042c005007030b00c00d4071902c80c1c000e0792a014403600d0411405800c114011002194100041240a01c1c1400c060a00c0c00707002444c0e071141e85044001e0650000b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 751402742 1250 751401492 751401509
    0x6100e03071814090f060c040b0306091008010216150b03060a09020a0e07020a03030c030b10030e120403031806020a1e0620071a100513090204050c0a120504080d15 72
    0xc3c00c004d10341c003010481c003014419100968840da5a01d2805646900032405080c400d40d4090001500034103103141d0340b68026660302501d01803942d40328162426a800048001003504040caa203030100031840200c905980c1404900b4446c0b41084000300765220801008480101e03250790341c89066403036032007403600500300c6402d42140030701d40391030041d50314004c45800304e002a143c80d02407260184a48510f0300c5191004056540c0840c4884049001e0094880b50f014503000320a031402c55280c0e80e2004100030740c401d4451400c00350280065001e9030f4265030000041d500050030401c0095540c0c900c880702401802c29003030f1902002e050a400030b15003c040c2d1034a810410b80d900a080541d440a812490322584510102c20f07820110f8038a0714505582d4044400c1c100001880140f8040d503035900803161342000050320089070340009003641c006881e441124070002609180d06540b0400c2074042401502e8244050b00781651502218800c41444000040d62036210810185003480c125004040c0344 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 751403992 1250 751402742 751402781
    0xf030b0f070c330501030c05060d150f05030f030708030106050c0a1202010f0b180a110f0f0d1b08010b030a02040e0906010510080c03150f1806100e030718 68
    0x800600e4060b00b0011900c40d6240f03d50541d016120580c003905040e00c0c1c1c0004c00701d04091a007400d1021681200403c14481500c3e40b89260000700d04075005001060010b221589403817030281407508008030300c0080008da0b001000600042840b0208483c1190760506c0c00075611800c3d00003050600428110041240ba4140f107504100c95054008202c0085003a008211041e0103030204104002c54002c40c402070f5941000141c1e4800d03072a40a280a1491400300314540000103000014640c82174044050b010004070b80448074403800d200d140c251020300074101d03140314054a000340201c0014401c10340d100c0c42c00800079410740b0490f0151802480040c400b043e00d8105104a6130f2159002d025950241110b03a6440325841d201d090749600607400c0b000110300c0c6450b000c00b41a840e0740014042904240c02c1c54009859440d01e83c0c01024004c118145020740342040c0007003080140c81d4000300c004106480c05000265500072994004a42003400040607264034200b01c40003800000000d50015180c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 751405242 1250 751403992 751404023
    0xe010f0e0601120e101d010606020c090c04150224240a081603050622060c090b030702160503160b181f09050d0f030818120408070f030b0f070c 63
    0x13242c10080700090348050151040c00b0f0042d84600300c682364495200145d00c1443c081105041c6179140340d07000f10b812440f992810303840b03c000403081c0c58405505801a4065001b00c0342500c81d03400c80040d00c01600c4105282d50904080951000300c00d16134002409840585c400b00030703925803007600d00414101c400e40b046408900600107120100c4d02c0284d9040c016240000e0319041c070356007034400c0203a0b00f40b2600e104100c40e45644000f0b200c24050071092040c42c0e140400e08030f542c0d6002e184110301e036600405a4250040d03800c9a0020301c1d50045000c0c3d032002526101c13103102191004260381050340000d444040b10000300c00300100d00c10100d5000402c02282481c542007428910000c10b071140c55210303020760307a4002e10182c60070400000e04801d50080302c40c2d00003441014010f80146401a5082c0d28900d10b0302c0803401c1c84c0b81c681a2072161140050108551081801b5100003402d91391052401c5e2461525621034001d00103000c140490021400511898040d0400c41561074000c0c01994035140c6 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 751406492 1250 751405242 751405273
    0x80307020f06070c051e07030b1f260706050a11010b04020406030209120303040807020d2111010e0606060307080714040609030c05041b110c0409050105010e010f0e0601120e 76
    0x844101035038140511151444401a0424000e1079540c411b001003550b5451915000007031000588448010020380c40c03052285407009600c0b401074200140200344e101041d0320300140324400c072078034038505c4c0c1c1007200d04210b05d42d000401e0301d15400603820000c260a407040c0145d03004244047c846a40684040303000f0940d564117a000d040410400c1d2560303440307070f4604240181d072404200c41c000d2840d0010069040141051550045564441c0000011fa102e02041c0d1101d00003070b001e1074078001292101c030041003003024001c611070186a0005030160b420108003003005031000400f10814000100040740e581ca103e6109030101e0740c15040340944403529039500400510703892009031a10282c03101b0201f4146031034401c09010784411100c140d610221030310266401410f1851145450041e42410004c80e2118054030440500c1840001059818454241c24442c011b0b00403802003050b125082c01281c07082c03084282c0188090070069420100c0c80c400c44040c00b4142c44540315801241a600d40c14103 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 751407742 1250 751406492 751406507
    0x5061f090501110c180109052802090d0213141b180a080a03090e0c0c030a033b011a2404030609150e030c10150e1e07170103080307020f0607 62
    0x407a69003050001d42c90301c440000906201c14480c4180c142c00080c9c0c1c00900d4400d5008210520303001e40300300c00d00c1c02c0f503800064120410380420490303180c40f00c50202c40d000f140d604a0350b024804004050742000c2424030240b085c060803807a4071600341c8440d18140b140e42c611010704010015501111030a041c5481c004001045a01c5406500751074030000c105041c1c524815036000c2100f0300000c0d030030000160011000b5041c0e141a00190102002c030807404840c2c1485280b0300400c0c203131802c12007950340c0c2c0300803400c5881c0941250351319201c1010340311641d0b40d00d00c0390f01854007243c0210240440c1400b10f0141030310136540000e0003103203024028010401242041441c00720308903010403d25401210040d100d100c0c2c0d110440d80e54025000b010400040c035400305488002044407040143e031a01c41c402210f04042d0381c491300d0426244904580070441d2200c8650085251600b040c0107030322036441c0d600e41c404c1030100034060b207000300008902d544204201e505100510703044a08a0038804030180040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 751408992 1250 751407742 751407749
    0x1090f0f14060f0a02070606080f1e060c04050d0312021605010c1707050c0705032b140a0c050312040b0601021002070b0105061309020d05061f090501110c1801 70
    0x1d000e80310394003981c00041101ea1084034409400e0f019651001d0f1080003d40c070001007200e80f0b5075a9000070031450000c10010f500e0100c000c00a0040059004030026901c0c0c244405a650754007007000c1000d450f240e030f42558101c59003035170644078001311440d0954130001503440100090707102080000b00a180300f152a840d49002e0300c02003001c55120f40c0f048603410b0007441d030ba0001c1f840040c0807481503403284000341405410007041d90304032900d940000703041c0307041140840502591040b507030175850945000e10078154943e080c21609040034030b1a010607401a031442d1000c1c40500c0302c0301320510a0034801c0300c00d0460000c1d0b9885107841c0529241318412421f40d0558010f03c20401d6168038494644211a400b50300441031854680c40c100c2004a60b520552004149620b010000504a02107002501400b83c8104001c140751800740140400d9010a500940078110101c424525003a040300350302041e0340017843c0590106280d00399680c5440500e080035500484a41039543c401d46080380c6213410b8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 751410242 1250 751408992 751409003
    0x111090f1f0323130209071b0c03061d0d0c080403140f070b12010e2a090420030a1a130207140102130605070f140f0106060302030c0708030901090f0f 66
    0x403a502c002c50a22004413900c1e90781c10180061403015191205007103a02010529090500403c8a801b00100c2d603164101101c464001010600400c141405000344140840002c00205070b070458503113654038641c261240920082144a209021751102110082c41d0484458040258041d942d9581c504e0950044055401070b04400f00310214640125071260007803c040c0300c0741d642416400c003000c3d40d0240880d001c0e6015000c00c540c0a0844a0311040e048641904590320740164070300303010a1340ca4602a0704210960001505103000a020680c3d41202001c05c3c00a148040307102089805000c1001480d40910001402270841c40990001c04c00e041c4654103c50030880c45c2d4003400d090340100319040e00c04444402091040d40d07c142c002d0244503024001e400341b41c10150301ca000c1020706620681c0d400e508841e500149a0300c2c00d00503400105090710f01103156151003408030303485014200c0010640c4e00c1c0003000c00c00340c4600350808222030340c0210f01e5400118051070266001000880d0450300c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 751411492 1250 751410242 751410281
    0x5010b0702091609170f0105070203040f050603160e01030b12030706110906040501080417070c151d0d020607021302031b070f03050903010207120206090f0111090f1f03 74
    0xf080302a0103003003007006a4648842c0805800e00c81c9501a13010180119050343c8180868401c014400340030369809225550040d659a07401d20342e650043c14102d4000c140030b4039003007050008140c4440d860704c0805c081c2c2d01d00304c11483c8440d00120f01810198514130380c41607020486106000010000701100717032164504010340c4c01d0794110000c0c280502040d00b035010030300384810801940141c0209521611a0034612000b401442c08904c15401c40303c401d0b83d02409440040c81080509486442d5801687c10301010f0130010030307000701d9024294940d042c0514020856503003191a0f12056900141e40144005c0707d040c00f00020000070740045070b50058007031912804900e0325042c8c004861403035401c100c01c02d9035070005850594980d40080c402d9901590708000c840c0c04a000b8980c098a11754041d809041076007404015a80361209400d008407191f4580510304040c00da2540850352010401c0d201000100c4c40080010f0300b8014103a0b160148920481180898503490307880010030b80c880540005 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 751412742 1250 751411492 751411501
    0x30301140a0810021c0501082406090a0e0f1e060105180412091e0312021b09040201050403050304060207360902040b100305040b0a0c0906031104050405010b070209 72
    0xc00e8000d81d101e80d00c1036402c0304280080350f6895400500842520440710500c03142c0c3d5070010f1084450990220080340c1002d684090b500c0c090b15140000c01c50b0800b0901c102e030614800140031401c1c060b14141c50740f0742e540c25103680d01c0b070284281c030200c0720301909650034011048100604284038408600c3c040c080c080022841c0c0c9081da6152001c203010f401160504c0d80c2c3d6076203030894100401c6085061200d02600010041061402600a000011000c00f4854035602e440003449070201444130640d00980c440414540007419007500c060400c9440040300d454900050f941441103400c044c000340000940841d20580019001085038810443c05655242010018405801d620700990b4400e10505d40c1e004030301200d0b0450010b89000803c00149101e1840000380e081c5842904031000c01d40350380800003404642c0102561051a00c80240144001039500a1201000c0c0c003426090554031000c1c0140452910151030190601500c10007155840d400c01c90025005071600700e00c264200030004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 751413992 1250 751412742 751412749
    0x308060d02310c090b030a24270e1504020609101e17060402071119170f030703050304050f010c0e100905030325050102030129120c160b010803030114 66
    0x9500f05d5144c43d85c5a0f0554942d802d014003e07004003503400113800250140f10b0040003048020300d0007800d851107044001c0e81451800782c031000190500c4107a042c076040c2c100d410f186004c1140c2c1c01050300a04500705c10b907034a20004600c0d0140c5c1c1c0c0c42e2908203205640b140c81450700803186017440d2b42035444c190000055100c5c00c542a14803907481d04070300030b41c44c0040b4042e402d00e0f4001c0d0002510820203102a0100b88001c2841d400741c0305000f4200040c1180c00b0041d038003c0c511a036400e000c0000280c240c0402c003103511503036407040f10001800c0080000028003030103410b00403400001a14802401440d02d6100001c140040b06c00516115a41000d115407031b81e07000f66030b440d007100d00107400703182000b448101c0c802e11280815101c0d000b20035a6984400094000e100031800380600c0b4031031000d0310a12140700c0894000103500880d10038020490300b00500d0724901d02c10f9000b0f1540224542c1e0f4940390003d8454030382036080c0280890115000480c9024011001d1810b850401071074841868214040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 751415242 1250 751413992 751414007
    0xf090c080c070515071b1101090b07050304290c01050105040c0203070317070507151a031204120609020d11030c100503060904110306070906020c010801030308060d02310c 75
    0x1c2c0140d20080d40340d0300c5400e040c200340b9800082e41c1000c5140d06c1c440310524503404204031044481070204036a1180c0ca40c2c00800d9100a80701840040b418440d41c1d1760f403030342d4034480d5000e070000c09400402c045500f805810350701141d00700005402d40e20b9001c80f10100e40a44000e00569100d0707800d0075503801c10a80b001040e2400960160348500500401829003003101d240a030008040000401c071000c04200004241d9400791000d0f2000204c03d04421140f2001e00d000710400c0d4402e80001c3c0160000010030b0083d03034199060500c50b03090960003451b00c0c0c8000d020407400290010440600380c010301223a0f1520385031030001501541d6041140608015001e280d0a81e0800407403818008203405080c01204158424400d0498030b240e034603400300291815a08485000016032750b40b00c00d20500382c3c1402001d000782c1c42802c02c0c103d5941107a1303001d00501001030246024644680100003555100750b8504c040b0448541c2c114000a4840c90146010b4040b22408403003078184250201c4481c4174040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 751416492 1250 751415242 751415257
    0xd05010f06141b12180a0e0103080a050a12060323010c050412020d0203012409021611030109060f0213290a02120a121a0a120c0f090c080c 61
    0x3050300c0e140c20f01c0020200e00030250a07560040c403031000040fa200075410014404a9581e01e04403440d000307070a00308108541c4a03080080e1080b0400010400509103030f00791540c082481c03e205840303002e1100300310382480a9984c2640350506002000007801484e040300300e41060f000c3c40c51801c040c424a54242614001e01040000940401041052402000440700c0d900d00c005d1611941c2c0005800003806c1d61117014038104c0588040110100c010b406942c0d02004008107501582400150310300170785e400405450150040902c0c0800d1200e44d50f0a52002081d01e6004104005040d580400280250404044460b5041100d00040350b03603280651414810640540c2e413103421514142c0d800070f0340d080494184198071841420a00012100c0b01500700d00a0544e9240c188803049440101552401c1c81c0300a920f0355000030700c8040352216001d4506440c00380080450102240c03030300b034080321880c1d806081c2c1495075480c081038206168000302503500700e17940c440c0c0040e00e800100300d0f0140304260 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 751417742 1250 751416492 751416527
    0x51213020a06031e021207110c0108041103161e1a09010c08040305010e0312010509040f080c0c040203011d07051318060e04141c0203032a0d05010f06 66
    0x800005102e0b4210030600c200b10540344c460f001c8010300ca20242e030000d130f91503e800d85d8141c04009045a1000c0b03604e01e850040802054451440f1001030094140600003400c40d9400d401c107580c1c5d9480401a076481801300f80c0740c0c1b03000c069892140d0031140d03104409900744500151400640d500703840c54883c0d01002000c045514107044940150303048408550111130044041c1b00010202d10207100700d0011019041c05107613500d610440300d02c40e02c90305801880c420780d90707035003800f001c07880c096090390b00d482d80040200d41da520b89004141c6054028290164494000000030402440300d41184a8110b171034550342481d40c440c81d40a0f03400307004030302c80041c3e2000046410068003015680b04600f521103504c0001d101621290340d012050411107007521100b441e20400f40240c8410440205496140c200608405441c820000e4503448090000d40c40c840c0c03030050544281c41d220340800130800d52080c01c0d95403141910202c10280000340710f0341072515450030300090414040e441200050485d403 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 751418992 1250 751417742 751417759
    0xb0901020a09140102120c0714120c010f0207050d0305070203100204050d030c0206090628080618252307020f10120f151203050702010c0f05070605121302 68
    0x48003c01e5984500342c0c24904500c115001e0940300b0460400600e054691200548400f900340002c00f80ca101448849a00500402000070000c19022410851607a824680503401d00c50340003040340703002c52a402c07942e404003a80040e101050b403c04010038240e882642a502c4040b882c240756000c0740500e1086941004500c109800003a1103640034030f45c450300c01030100f1304208001d0041440e0ba000780300e02c0d5002c0002140c008030029115182d003d118480e92800a840d85024008540c9002680d0200d40d00e211480c03020551594a00700d00c2c51018040009016022800881c01094280d0401400100414201d07003100c0c60b500103c100e4142c0340d0090300c0030686580540c188410b011004c0c10410030840c40c2d584400b0110458010240e4549100c08003084c0d84006424521203910381d5400301c0d280104448403140001e40040943d09015024208090481820708140450030746400c03008000c2d004111011911581003805440e60140000000c461a41d540044c0c0c0035086400002079405001d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 751420242 1250 751418992 751418999
    0x80f070e0d080435161811070809100e10050705160f050f01170a0207051507080a0b030c031b0a05030f01270803010608040602091306030b0901020a09 66
    0x510108a41c0300300340c2c451806544040a074000c8a6111011030301d001560a045035400c1c000ca080310788103580c00c0c0541100e1659440b05a9078010314031819040c1c00600c0444624a04903074003035003101e180c41c00c14696a06080c1741117100c41d406810080c1c800c40010030001e003042d04c65000c64402d40800707000381510b201d4001e400d607002c1d000480103d440344200658000c100441d154a00c0050000000000d102030800c001c00890410246c04541004807803c4e890600c00c0c41303440d070250091800c10380144c1e01d241c42e0a1072418080301203e90743c10355848809004041d43e011400e64402c2e029968100014010601010345070b0aa1408041c0d05600c070b888100d8510900c0300301c0b08860580180030320107681d07651020a003001d030101e004103e165910301e104a8100303140c03204690244424203100c04102d60a5442e50014001130041404005240c070005007000a144d044800745400200380e180c120700c883d00110040c0481d408100c94862420740842c100c10014002e80e8a020380b81e88038200060b04 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 751421492 1250 751420242 751420249
    0xa080a08071106040914010504360f021009050a09061214011d070e07090605070305030c13030501090c06110a020f0d06060b1308070f050904030909050a0c080f070e 72
    0x603482e50b0340c0074504000005528420344500c0700000101d28203c03c00358903041c00c100407208103403071642003150381c120110070407140c1c5181510314000e848a80501d0481c6400c0040c040702da0140c0c000d4000d43c0660144c045203420421030801c48004455404e02207413960000f0041c1ca80c0fa1144031000c0301e82109180001f10344019946910551b01c00000704100b840c08100d0310f00a158000c10b140703412035802071000d0748113400c0082d40910103091a81101e0b00e0400d00411602c1a0314020782000390200210360805101c07404c43e0051010715048003101622820580c1c001c2200c83c8040341c91940740c00000034854003400c1c5d181e010161510261408070700c29000c1c80032002807191600c0e4044460380c000000a0100c0c811400548110403c090b114042c210b05d0f04401c500541003881c895011400401048031904450b9055500545141e0302c1741e01d5a00c0c003a14080c03440d400514902e4109008c0014016a80d40706000c00015984c03404200e4881c0421454852010746107140012200e1914400ea0b08 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 751422742 1250 751421492 751421513
    0x120c05130b0a0b0a11010b060403031103190e030c040506130f200c0d1e0e010e030114060a14030613050a0f03020105071431030516050a080a0807 64
    0x242500c001050524082000945440c00c64100c143d40d0800860119030741648080b0005c59007460030000c0100c5080d0b80000740c402d01552200038104001c080a0003800e03141401911109a80c2c8a041e0380200f1100c2e8000d40800c10151055000c0d1007000350b828500e00e00b90050303c1c05048060103c004400002c8240c40281166071075000d01140c40b450f0340021080d1200c4131100399011140e1241d12902024030590802d40c040c0490740030868151191075243c40c00401039071000032981045903681c0380490041c2e0b144042400540e40c0342d46410703112924148000c660611030b940440d4509021071303e40ca031402100400c000d000743c243d0b2088001409181490240064141c06001100c640302c10076900c031080828805003c80040c0d440c4e106100c049500007840c0c1e00d81510426007141001406610030a802c1d070000151170003440e03902009142200304c0c51102c0003958214003580c2e034a08581180c10078280c4140303c0c00380144094440042c0c0c1110101e44e0300726503503024101c0d41c5410041d40344c044441 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 751423992 1250 751422742 751422769
    0x101818020f0a0803041707052202160b131511190e1903030206130201020606010c030e130b09060315070e0a0e090f060c030907031b0803030f090106120c05 68
    0x8140780494103c0e0200090001000410408030000c035070000c00e6400c103010390b805540928280405032841c0182e0030411000300252440058840486e41400000600805009044960010203000e4040c2030152140c0082c4d0081c10100d03003c02c46034050008440c550b084001d4508014022810766401091590591039601d1034101d15400e00c1c10006000401c102c604100380f240901c200704205030f0140555a401154031002c09942e804d10f0300080e49583d0024603460410a200c0441030030580504680794011402900780b42c0c0103001c0e0003c0200801800c1c1c1003074491020040051b40d14900012808141c0340c01105022031512100c5003a1081d2a0400986500520b880008905400c6c0410346c40d01c141c00c0007008000001003044654206440600a00b5144000700b04105090700001034405c120303a4405000651030b18210526030f0b80c18580d4200c113902d408000f0510410402c2045e05502580f0242e00802c8000d0f0f0700c20b800c145000b20400001d100c0322000c5810483c5280c07803810031811 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 751425242 1250 751423992 751423999
    0x40e0406020d29010c03121d0f0705120613033c0e0d0c0510020316060e070e010f0e0a0f0c0201021e030408090d08040905101818020f 59
    0x82c0024048024180c4403010201007800040c40c41446503000700c0030003034203a02c10038241020300c00c045840051004030603240008031a9180c1420f02c0f2114190200140c0c0c6a444c4d005031104d0741c03902030049442e200b081c856140f04204000c001c01500c00c01207001401030b816005031604000e400e507025038111145104200230b50200856190312308100b14101013441c5501c440c01d00c089187e0003405804251550700b420302a410800303002001420a0403c503080d2407040f03a5055400310303025401c911314031072a90322034078882003800d40404008032a000908e8100c1e80c00280d40c1c00e81e444e082eaa8400500900c50f1032020100d4407000c0007180c3c4070000c0d55810050304000454001c84080c07500c02030300ca5904060300142c0d030000d415203142402207502a9002048010303903141d401d154440d140d03c5d02034803949512503554050504100a1a5421900100400c0000340400d141c641041ca04113400c43c450028094259003202961000c20320400481d000b038015a0b0008407015000c1c41800d003c440c090a81 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 751426492 1250 751425242 751425247
    0x7030509070b0729060f062b02070201080708090703030818030315040c020a0203100f14010e040b060d020d1713090221040f030e030307020a0902030a0b030d05040e040602 75
    0xd90540c048001c02880d802020b2040a410000442c0d00e41d000c404500c01c00701c40c550105103c0c169441d20001702c000d41c6d003242e0b8540c84480c0ea0641c250444154120901c040148140d40e16862a082d0060280380b4002d8807868482d41d41c0d80020b17a0b0180c3c04965039007840e08a4507080c40068019a41c1581181074440003c8a0300c0708880c5a902d103034070680e0070080c4040e5030741c090450f9150030300445000c0360361403010341050031b0103602080e9a00c40c1820844400e64a9043d80340b95807146500105812403000052030785544e4520002c00101e2041c0d405482c80040000001c0003410204402440c0c140c0c00340901e0010207043d143c52a03404070700c0764818511132f820002518000c901070341c0d00000c0d28003010016603880420403107845a50000300c00d001a008441d04000c080703400070007006119a0181010000d04494800281c1035114011000703500101400c00815240d803180e002d90310405441c40104140c1d000d02c020103603501c41103041000051340030003080c030002e41d42484036604107201d10760260 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 751427742 1250 751426492 751426499
    0x31b27040c1701030b07031112090f0d0903230106120b060a03020d0213110a1809051b0706060e15240d09030c0c031a0109020a0806040b0303070b0c031b0405090703050907 75
    0x2025500139400d50a00c48601001e022100ba000d121250fa50300007c0300a1000c1540c407400580160240d10018019540c0c03483f072118100c400c0c2e0342c10071001c07480000030011f0715190109601e241840d41c506a844081e041c00141d05400c0c64148582503a40050020204031200d6081010b00143c840c840028183c8404450b1188407464000d418540403503205c40041c0a41e000b44007400c0c0e1400c0e070006d81d40900304010b02c40303000d05448100b4090600208071650300c010303d0821201900c100c1c0c0c040e1b14041c0c000001c00a5010031541c0c800b5400d070085070310810302090502c4c01c0e41201d524405441d841d80041100c01c41c01c0d28150b20500ca028070904014681040b41c0d100c5030880c40c03142c1c4c13080d076000d80702c981c10380381c030640c00b400361805401c40480450805a0041008250640080149000f10380e90251003070955800c000742c0c0d10700c0d13500c85120b4825144c0504085003035041640d450382d4040c05440c3d0606101c6a042c281c49c02c2d16000781c09050b5aa45840b000c5000e824080c18208881c0121900171 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 751428992 1250 751427742 751427771
    0xb01030b0a0f08121c0506061b0102040f171209130e07091401061413090e011e0207030203090f0607050a030807021b06031b27040c1701030b0703 64
    0x104014002c2076002400d081c54500c0031070034a2500c1295082d50300b410000c6402491031007640c001c03444c0802100140395601d0002113016440f5842112031098039400d10083d100505400910951340310f142e50045240ea07801034031030144003494803141d03280c101c943c0905207000104051b00100a00420591000b0724101040045980c044000c085075080810305100c03d05250141c9600701500382d45090083d031504000810301482400e0241000500045d2006401c44d1300030428090016000c04101e00d4505c2c51815000740b40000320740d610a200c00d000d14180584e640300f66030207250150051450045400d0420148a510a1203550b00500601140300400e1080000c4149a4400d4403146040c1c01c20b0000a031528510360101c413840c040144a40f402500c5000549402040c080c911140458144680283c03902450380d07000401650030410324403002c480502c205603004c00307071410070041400e440304a500b6580544d00e1089a0380e01001000041c180c400010fa11408502e400921011201c403907 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 751430242 1250 751428992 751429009
    0xa03110d020c100b010804020303041202040902040f140108030418020c1603230303060a03030806010e10021020030c07050703080a03020d18031b0c0b131706010303020703060b01030b 80
    0x9841035400350110602041040c404c2400d03804003420030300304a14040d80040e55920450003100450340300703141a0411502c0310f4200c4182c15030300400030320000c40c40b0846e501c0241a0104840e5402d6a260000200d40e40003104807815105242c81c80780742c00c26041001800b139030000758003040e184900c01002c8600d100c10b041d103038051803085c03407668040209100a0005440304483d1400c0c541c00400030f0280c1c0c1e41c0e8000d084406c40c0d0b80b60070440041d941d40c600503070710b44960350603e541041c0b45070700d0790f09000d5002c0b40b80c44c0c0301c5214440401401d11300b01c041c0860540500b2440151750307070420101d80c0071019103014000b8075102c0c05c2158a025220760744c1c980d17542c001040c040c012a0300070034000fa0101c0c7c5c90017081d010b0303115803100150388416a100180b495462120405030700842d02c00e140c00b4061852850300103080182003807950b450006101f401c02e800b95124051491040011444030b1210209090b4101d0b070b0154010441a81503440b80d4009042c014152410b140d60b51410135510b8803250003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 751431492 1250 751430242 751430257
    0xe1f0c080910031509060b030106030906020909040503090418020901050118150e10020307050c1905030319020d0f090b0d1409100b0103111b0c060c07050a060c03050a03110d02 77
    0x401013002690b14400314010b81641c1c02007240c2d03608101c002e20101d006201500d0460740240340125600b0b103135086c040300034072500e000b80b80c010300084104814842c2c00001040158401d84080040c5100c2c0311194101c2c030101f450003075200010700010842584910f04d8031403411980004040c2e55507440c0c50a5981e06508000d40b000b1030380742c0c0100e09c92032a060041d1029500140043c525041855460ba0380b40c034461040607106800040329040d03a00d0314405210040c01d4003034102c3e40c0d6014002c840314410485880c0785001031080740400ca080511034001141502e100d13841c0d00981744d0a103100706089801004076601c1841c0c1e00e43c907a500c2e40a4080e2894094105007010740a00c0d12071b450801d084d81c407010101e42c140b50801807026036030a0b10104403a1a4000c28000b0307441da81100400c1c80c107040e244111241d11160100341c04401c90b40208401c81141d5007121201c2100e0341e80c0105881c003000c00d000180c0030860902a440c2c8141c004e4001110074811a400d080c07800400004c503800b01d070000344 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 751432742 1250 751431492 751431497
    0x51b430f0515150904050c031504060b060906070b060102100c0804051e120f12100e090106210f0c0b04140a0f03080a2a030e1f0c080910 60
    0x84110041c040c050084510110301002c01d0549454034811580440e050711030868096010440010b00703220090009200300c1d40000c00f40c6140071608032800c40400b00a50741951841c0c80c14884864618000701140d00400000c0c200030700303040072601c9020141c0e00c0240540c0c10350190f10030001000c600c522417460002d8003900d0b56945820641400703490315040e03950b5192001c01007068002c03080000a1a800c40314800380c540c40ea0346148200800c0c190088416503d00909070700d06119500e2080708001c0d003074803010020b140d0150f54100b40c240c02e0f54418481c0702c01440e40340150305459010942c41c2e20303200c0d0181280505c00d80d41551520240034199004126807107000c1810301201501000001c82d1100464500c1121400c03d0002e801c1c0c0d840610004100b000c00150b51094030f40240d0741c400d0046c40f0100414030380c1904c0400a200307201c1c804011000910540d244051602c6d03d00580740411440368100080b03440c00090640c1c11a5101400740c800c1082442000e119544e00103401180c414160b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 751433992 1250 751432742 751432763
    0x8010e0607081812031f0303020715050f0d020403150513030c02030a050d0210060503071a03041a09030406093614040c03050613080706020d09080d051b43 68
    0x85241801d03009a43c4030710917001c0720806c10400300341d0004003641a252584440e04200160400c1170350346108144151b600014003049103030006c84a507015008580c040c991800d8180d03854020740c400c60b0402c07200706580c1c8040c104900046417003104900d01300351014003207400c00707140740d107540e840c0c40310016600005034007020031050201c9603401040300802d401d0300200151801c09100d51185401085405a05c100201c00a0144044100c492005000d45070b03a0200d20706040321820b032a07501a00511000c54401500080d1800c0c0c521050f148152814a0424281903159201621110955000465182c60740b03008401d0354030941ca041d001d5807160075805040c91441c50401e0070301500a1407207404444000515000c02c40480440d12000c0c0c3c402c00041e41c0360b00d944002001000451009403005a020408140d01e8001e5403109010714084480c0207102801c3e04452903c80c0300711074509010800f4484000c0c0600c00e500c488442c4008000c41c060745407541117180c5c4951800c0141d007030b076420445 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 751435242 1250 751433992 751434001
    0x40b07091203080103020f0414040c0509160507060905010204082e0c0f0807032c01060902340204110301060e010c020a0501230a0e010908010e060708181203 69
    0x26114005000c0c0c0c1d09514101030250310042e10020051102a004450100f0b44001550351603102c41060f00c0040b0300b2a01c03038101800d000703a0320300140c0a0940900040303408202d50a24011500030030741003907506d1514001190b620a805040c00310004c407030940d02031002064507034062088442005c00147c03403070b02140c1c07065165010301c01c1140000400c030f0310303001d02d0107100c503030001c085508502c82d828010310036284c1e800114001c10440c0703510b18800901c110303800b80010b07032064000b07102c418100c002c1c0100d1307450702c40d214101c0c490144120105001e1400786071128a8060842452400c110082c002c015074580102d01620012000492030000000061000d5074110922203510704080c40d001050f02003660100d0103c2c2d030300d030060606000310300c0c41c0b038130040c02c0c1c0c02014a80301c25a140040d448211600d0064003403003072509603c1c08164000d001281d4200144100d021003241280142503e85410300e0a032041000600f2003c0307201e1030091a6174501c0d03000c04c00e40130019607015855a803807a0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 751436492 1250 751435242 751435247
    0x1502010f020307022e020304080d0b09160f0318050309031b01090e06060705010e03030a0e242a0301060305060d020a140310060e04030219330203040b07 67
    0x60881245900a1041c000d2000c200d40c0043d08a0500348601003001200c0c001144070b4001d5000c8030440c0030b651b4000401c001c00c10556001030000c4442d03810302840392180c2c00341004042c2c0d074202c400841c601040e54410a40502c02e0782405444052420700007228618250002d0a00300d100c041900c00340c0c00020f1140a90030701308460b00f03c4149250320084a21a1400000c1c0b01e204c542c45214506007041d0007284e110f03503070801140d5204d5032200080105440001c0c0f076a8980c1c20403100c07007503410714040e004900300c80007103000c0c0781d0044145d0b607070f4442c5a10024110107804000d085907102d0321551841e2581c00c407124031045103030300082c2034180d129850500001c0030740380700a001c2402400d10754484801a19520400001d42d001144c4040b070126540300842d1906a070000101c002d0f500304000090f81c04056141e03036004074000c0c6d0950301c45600c1074001106400440400400c03e9004c2000300441e001d1080d41e00f408004c0c442c001901000308500d8200c01d0340c00984054502c084d003503051048030b0b41c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 751437742 1250 751436492 751436501
    0x120f0b1f08090f0309040209060d050f190b060d0e0c060a03020c0c013b0607060906050603160608100506040311030c040c0c0f0f05070e090c19061206030507150201 72
    0x6444200030883c2100c0544880e45034001e40f054680603c0c0c000c00c0b940d115036101001c0d5011515007010811692400c80742441c1e020205850321402c0c91404d4099401c0000300380503900005002038411864003421418240081440340e44c000c2060184000e8080d0781e56130300006042c403500c00c1d600035860740000c0c44403030b040c41d9000c51414180201d0140d46040d08030549240c2c0c5445030001040f40c010301e40b081801e515510300382541782e4440000100d40041001f00d51006004d00c0c050f000400c00c5550320000c1c1a0780c0c8ca9410b001e9000c11036141c500b0001d191203226030715404800e11215000032580d62000c10341542054208860750920001240e440e400c0800c00800101d60444051050780c181c4500617080c407212000c06808810004403900c00d015031488944103180c0e01404864240b69280c1c1411882541500e450109000e40c0300740c0c0d01c0e1403808142c400942c95140c041700303a00d00c1c501101601c1620301030003d407a5058541d100000801c4050000c24028940724002550224803050b0003800c46 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 751438848 1106 751437742 751437751
    0x312030f0e070e090a0b2415090f0a0501050f0a0c051501080d0923030109020904060b03100207260c0f07060e0f01120f0b1f08 56
    0x1007000160481202d20507040d80d0500d031920310143c0d8030b03040c0400c0b01804490b0b621b004260349003000070b590724000c2d024030010181000450081120a02d005d030b416660920041009503050800c80800300289100711600c1e80641d0030240007801d180520508400010030101c1c1c11103145014440030028580c103c0200c9007908d034041d80d14152203030300b4080c0358281e000340d026810740c80303008103c000c040e90180c040301c66000541c02e020310f0910303801d40b05080d49507417101000409078441e00b1806000f9801500e0108030320300f01800b03152500c01d541013045c4101c2e10401840010030300d012011004240812030084500595a156000d1801244da40c1c0c0b017070b4000c54961401544000500078102c80303054a9001001011804014010202020850104140e401011007003100c41c1d20a40c0d002c7c0c585000000c1c00b1001d600440c42ca41c0740324098466003601d10307141c17809040e0000e00b0b0f694071 = true := by decide +kernel

theorem cover : BRFrame.Cov 751258992 751438848 := by
  have h0 := BRFrame.cov_init 751258992
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751258992 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 751258992 ≤ n) (h2 : n < 751438848) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
