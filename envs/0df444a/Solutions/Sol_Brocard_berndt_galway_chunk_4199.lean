-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4199
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:51:25.819221+00:00
-- url     : https://prove2.me/submissions/869ad376-68d1-49bc-ae2f-58de5c10e186

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 755035971 ≤ n < 755215827 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 755037221 1250 755035971 755035997
    0x20d030e0315040311010f0605060702240a1e030207030801030b1003050307082d190306080f06042306060d080f1306020624010807030608030f0306180405030a03020a 73
    0x10702c0300015581100092540210426408020312903503c030322411071000d20548d0b1402c40010484c0c024150301078820640d18054011288504041003000c85c1142d102e103850303c00800d00504004101450100081d03514100e00107000e10a100711400700d641500c03658039a9003562505421040010322010280c3c0840302d0220218104001802c4010300c182921a5114a800021900c200c2e807048803007820b0400412404480340c1203001d8591640c0301485401d1003225a0000b1005010b1760b60010960b4041c040b4041d0440d038021540381c0c444e9002d810700c0301c60407665546001d00090342101a13400c9820201c0882c00c503140c00d05c81800300500a84184e810206074413004c14241d480054850400c2110340c10070042d0b99014000998041d00d0100514610f030000038803095a00d221401e403604000802000030056406684804080c00004045075105d4110a90310942e41c0d00030303607295104800e040300030a00000d2500c60a4841d03a4080301560900d249a4021707000b075040300180005100d8000c60706d030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 755038471 1250 755037221 755037253
    0x30c030c06092916060518060f0723030f040302070b0f0702090c13170609031312300305060406050f1512130209070e010e060d0e010c0507030210050103020d030e03 72
    0xc180c140500b07000105030500a4015550741000d1f038400041d5000740d4100011500c25495850b0b0103046418135988140c841030034081601002078068440c40408810b1110340070004140340c0c8a81d10039000c80c1d00094407507400c0091350142060000110ba0200002170050a0000c2d0340e07508044070841c4a030030040c544440314851030701d80c0c108942d2560180b0a891082c80f04001c0560041050400b6602d0b01d080b2490f69210002d241c09100034250030414000c040005058903000b8241004080403210b0180265000030328a4104030400040d0501c0080f41052819106840842e04000c01c00c3d07000030508004c1c041c2035034000707180d0084101c040c44888500301c0a15a941e110b6440361010900c2c048492041044136200548a502000003200030104142d0b0001310031924440c044403041d85030410790307560801421b082c00440b01e1a50801410b8402250040e029045c0144a41c007501c040c8401c46119400f1110b0910010390300034601d01046000c00e010350720305a402c1c000a02035800c030b004007001c0d0f6 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 755039721 1250 755038471 755038507
    0x40510090620070314071e210815060f040303030b120109080a080705030402030a0206361005120a020a0c1a01060e040905070e0903070b01030c030c060929 68
    0x6588002d070001501020542c2c030880c00c040f42401040b04900303044541d20760f418810880b20f1068824070212841900344000301d1220b0b0550052030026444043c07840d60005d280d04d03410754940c0303031811202c69032120078540701d0140c410201e04082c1c0c0f18105491928110082c1c21003140f0f254012106034100b0003c00001c1c02544202e80c041e210720381c0e844203810001404010014001410081c050043c8401a0340205804002a404503003031764840e0010003801107001018007612500042c1d0407120180c00300441700c09801c0080444041d8500e8403c400e041e9803901c28941038040008000000503403061441c3d02401d1604024a028580032410740e607000141c20f441c045981030709070188010000d056000c0343c961150710060b1810300000c00e0b1039503203d0b501c180134060301c540081111300042c86001b0400a4171540794009001503500d5a49003002d00c804507140c00203a5081d03400d600b000c10f01c3c90058a20303000711101203003a0b20a2141c090415100281700300e6480d0780c100c10030850100385c8c603c80d0b041 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 755040971 1250 755039721 755039771
    0x20f1c03051207110a3e09180d1803060e01051f05060711270f090102031026030301090605030f010b061e09060328050405100906 57
    0x945982d40414064003444803074018810010001920682c010841c0003164035211a030b070086801024500b41020b110090100c2c41d0034401c0c10345580c01c80000468003000045030102c00b074031203483c5512130000c89178a41c1400031003655039501c00b29500e104141304440b41d04c043e02c16000c3c000700f829101e681d00c00548103042d106c211903030344a10903ca00241e50416480d401d80b5405800300c05c0c2e514000108825001d08400901214080816030b0f01c1f5844001c041c100c0c1c030364104405895950380004440d0911403e580d680c080180543c002042c20505100726070256100c0820960030b1403811200e00551b400303d40c0101e0800580445010301c0110406c0690f005e4482c2c01c5c4041034180c02c00d000d16142001030450302c3f5803030b8101394810040303450341c81c11181001011074030388c082c4001c0c410741c2040c540301e4500c0f019001680041002811401e1300031038580a401e581c1808e241e1002c500350341c0d0540380d0a6802402e00d410208a44120340d0255010010007485842d001c5155100c01d405c1a03020865800 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 755042221 1250 755040971 755040977
    0x3022a460b130617061f050906040e04030f0810090b040209040e0729031609030f1203110a12051003061b171b0904020906220f080307020f1c03 63
    0x40c1801101d401c8400000d8001c0c0c5600069011302d01140041c601446d0060b1b0034080110510350a41c5840c03060084a00104002d001c40341e46c0c0d503440b0441034140004035030540010b20a22080c64581e0f02c100182c0e40a4110030130980e02141c145184540103040130001d4550082d130810036588261203038001c0c1406d1107552009014080e1421070414008040e41800c2e5001000b00700300c0c02c000c0308000082d40c1c0c2181944c6a00381540650003000e60b0313820541e810140190800c038946408004501c43c00c5540c0602c2950f05205040303c808241350035004030841c1001140c503400802440c00926032103d0b51105541802424083d0f49489481c00c54105507022a518150081562020f42c2c00c40840742d0101f21249072984245402080350b061030421030460020f4480000c1c140745d9070368880d01610100e12008020fa0b0366910401d11402003120070101204281ca00709070000380b41680300b01c452045071030180c051443c1120681c20040c0310030308102115132010302c503030700035500f0380c1000c0c126400644a51 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 755043471 1250 755042221 755042257
    0x30106270e191d0a0b10080a0b1f06020318310b030a05070e0907032102100b1003050a0204090501060f020c04110d020703022a460b 58
    0x32099400b0384000310148000c1c0ea040743c00c0b681e4044800a4295140d540100b101545615103041358400003c45511804840c41662525010b110b00c00c6d500600440d10000c01030705001d00440403100a48080c414907006d0303082400040c10104a0040041402200078201000d8054401007010344034ac40b04c0c400d05c500c8a80190204150006120f03941d900340d030880c002d12301c8c11600d58038156920001d00580b00c1790029100030890050040102001441d4001c0ba200d2203d40d80e4004441803940c4a4035000044c451002c03001d04006680c442c8280c64040074082d10300b58442c1020a0b00a040e0191928000717070340c00c110010711502180300746e0340a4135240d0340b20340d440b44481a009203003040788041c00d4400c500c3e216000b6a0303500001d0131150142040740015840340c8103130400380d042000c240c0a8210800c401540341004084a500c070001d00078040303584004d002203000c40d440300a81890b600c05109400041d01c011260030a00c0501c147e001c840c0c9100e0407040d2a0740d2a451070f50000c003001ea0401d80e084d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 755044721 1250 755043471 755043511
    0x6040b0901020709020c030306060c1002040e07081008030a0315050a0311090a15050d081317070b03131103120d05150603040f060f2403030f05030106270e 68
    0x43c091500141280c010540c180040e0380c51403070302c0384009030085206505c0010543d00c008414000300c60010681003085403030f10b07070f10000740c40c0700c0808617038030400030b81c00000223040300140440380030542c1c24180044d070414031008401d400600300300b450a04542040e00b0005100d69a00d95008099881240d02054440c140f5080c410300e441d02078081e040c818240b044512900c0c01030480c84080f5041101d2443c070411950414040303522840c841240704055002002c92282c07894503209942c0851130307085924141d0b1b240b00003402030000751040c1c08203056411406e00420014503101104001c01403d0340d00081031040200c4003588501c9855280702e031250200207070222401100403101c4001d80710f061a51801d5901c04880d01910f900c002d10352951410210060300643d405030940082e0810200141c0350324520a0a091005e84001c800180d0302245035180c884c4070700d094070b048440b90744440c607901481458220408042e02d00381d8040080400c1c002401c00140b0b11440d0290752082010b108111030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 755045971 1250 755044721 755044723
    0xc1106150901060203070503070206340209091b0907090e090d0207050a12140102090301020a1805030a03090611010b060d0c030e010c05040311030a060507080a051e18010b06040b090102 81
    0x8143e0001066400521810012440210448081340c1d811904181d50312074103540c84017094070021102c184000c0110035045420000642411494000c5601c41010341c2c490007000c3d50380b144881c1700000444265160300d202c2c02d104400079084081c03410501c00303003912100c40c80350b00d140480e4121450341c00a1100c02a00d90140003401c090a030946060140e50306019407003908200340200104021745e03180080200c40700030b40c1610b0502800a00a660b50039000704000c2810044518640700000c0c1c0100000d2907140021700300e19203c1c0d0588500301d285103807800c1a10900480d600016465407200301d00d99003030fa05c1c0b000822008402c2100000d80c1c4214a10007012100e02c1c6401c10007a030f24100b0000303020382d00030701030b182101d0303200d020314080d04048000710341062142640200241c0c202400c0c003610b00e03041131440d84a9800500c0400c0b031580d444206044841c100300c282d41c0102130a4000c80c050b03144115800401c401007400104581e403800300842c5c0198007541c8003607191b58011030100003640e8 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 755047221 1250 755045971 755045989
    0x9130206072105040e0c130803180f0a030f0f08090d0b0115020c1e0102010608030307080108161d1302181b040b0f0913020309100b1c060c110615 64
    0x140f501604081c2464030103000d42d88054100c0a090301c0204500c03011000350340b58480500012000e40380c80b188801e2a424440790b00d52203540c450b0404440300030300c0d410900e07c500104c0c0c0c0c1100343c035005a05242c9803143c03104405502907a08180030070006905480d0800c481d03d215115400c04821036140c410702c0b10440141c0101581150007080c1c200800b941c900d08280070b08003201d100c1110384a0642d0060780100180c0d845020380d13002c04030410002a400007000da0481d13001c01d090354460728402d00d0480925640340181104100c4035502400450354002e03c0541c4a80340f001c6581c9207160b40d40000714075280b009070520107012401c041007121500d104005014094100e50030341071030300b001200221409203040114100e8400f04079150b9580c1e9100c1c8441c1241094a000c5580e410040301107078170703040c07030400c1c5840e02414240010b0680c100780d1000040c0d100c1800080c4001c005541e10b40e0081c101038074010040000503010010350450600c0800d001d01e18040403107000840302c40030310841907 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 755048471 1250 755047221 755047283
    0x40b01020604391211060f03040321050f041442040f120804022805121615170702070f1716050607020913020607 50
    0x90416001d000010304034903801004491511001892014180c007042890002e03107a40141c50395181c50001000c1c9950901c0c501d100380280c0305c1d0320000343c0c1d00c001d000480c810a00506c81c0c22004100103070110b4403d003500041200b88058001110003403241030b200b0344100b81c0e401001c0450041c288000c00401c0c50880303080d01e81d1103000c2e002c480001c054001400c9144541d4100b4502040860240503c48000150101e084100e510681e41801d0610740070300e030700054084880300c00c1080c00c014002c0c0070751000d51107240e0080224620f944041112901403250b6501031f0f00c00c080d010801301d2181e5071a5110003400c11200000d19041751310951401c90b806007130f80518107000b81d40e44927018881c2e01410040d82d0b01c1d000c403503924094540c140b0480c41c2a80c41d41c80243e012203118030206404000d5540c1d800601e04110480d03001844000141402908510030b503075010b03404008408c0107003001228654131140c49038030002c000b4a29000b06d54035a0040b0800c486580b081e2100301200041811640300030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 755049721 1250 755048471 755048473
    0xf0e0a0f050a0c03060f061407060603051c0305090c0604030816020312182403090c03070906090c0e0f040f0f02040306021b01020a05271008010807050102120a2f0606040b0102 77
    0x5075245c604042c1070042c48c1613034002d1404000079610203206603070300950021a882000c481c81013640f21002e031254400c1b02c0786200040e0918020822030100000c8270460314000401d0700f442c141c81c50b55002c000e0352083e001080c8041d008084000540e60500c09001d00382c00380a4004d541e08034012182000c40c41d520007075880b0318950080c949400000d0708080341c092006c9500c031941e0b80c032200180b5250008990003035a051198103004100c092071600198119002548244040700100c00c0039505140168107d54008400082c1c0840d175181c141c011030708004032010005840c640180041e805c0e40d10171b80050f1801074001441000100042c5141e0b81240c282070021800d01d000e070f001c02480c1c2d100b00d1503014842d9040302c107454401c403951800d0f1400c01c038000748034000708820b0b0003011f88036680c248600c181c58024070400003580d50011840b0060310304480c016901c0d04140000959196140c0281142e0280e038502c40c1c0e10b1264000c00f103250007014005c001704080e2a10404100507200440130701411 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 755050971 1250 755049721 755049749
    0x604060501110a0f020d06020a120608010b0f041a04090807020909031c02030402012c090c070201140a051c270206031302121516090f0e0a0f050a0c0306 67
    0xd42c0340100780c5010701584400c070a91140410300016a100d1744904010300324903c001a80040c00f50428440c1e000070b640d205060080d9956a40d00500320350340d01400c03d0b08124441a00e42186c9000e42c4061010050010074800b4020280701203011902c0480f400c6685450024001e015481d0070301c1203903401230b2288000d41c60040c1c2011140e4400d1040080310b40c0d900d40200c0460308681c007035164003a9540c04c0301e65424004000500400d07c1c0d656608080d40503503414408100c82c1e00185040701c0710150107031030b889218a060a11182c040e0321211005007001030902c0b803c90715680604c0c580d01295003100d008248070042454001103042c151505514004e05410380e41d00503100c0c6030075039600c001188030003000820f10b8000303d518600c118804a02c4ca000c2c148045054001c4014641d008001c0420310160814480a00b5651280d032030060050200c2c10140400c040103c00d103a155200748218408074800550030ba0807002d403802582c15094039a1903010b8031030165410300c1002c00405c1c9a51045074 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 755052221 1250 755050971 755050997
    0xd230a05010e16060e030309040c051209010c020a0b09010b09100312030b0114030a060f09060f1509210203010f051f0501050412030e030604380610021005010e0604060501 75
    0x750002c002c4c803465092050801c0b0003103c0b82e4080c07080d1032032010058024420100c010200034a2948400618000510b500008c156480c00500c40e41d001070000c0e400410700d070181629000e21280000300351b40c500d03649800354200d2548a030401107000d0310751001140b1903103045240c20400c19140d0586c14081510b0482000f07016a448110b0812007000f00740c50558a45501c00c4001c00303412560800350200c805018001001112607100508031341c034100852455580f1038028050340407003203040030006030360b1b0301060203d071403400d14101c54000c00400c5c0810701b070500c0e070110b829603400c1400e00b6115a6600200082e40120001c902060700d480e0180302081410080081d1040c00f490041c440e441029046400405008000c2d1600f1540001d003110054030b0a8901000000b003604a8036192944041101812491956000380326501e440402c00e000e40d5104144500b0701400c58813a81140708883c0b4540384080c1510583c2d010301280320210140c1e1802000380800e0780d009a028a04104500100c10 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 755053471 1250 755052221 755052253
    0xa060f2304021302030403110708031903051b0c030417011a0f03060f0603031c090309050109080705240c01090512040f09020904091a0f1e060d230a05010e 68
    0x15004883e44100140c9903142d03810300701c1e00707200400c50480c828400e580e4081005140003001d08000c0c03003403900c00910502c4c0c5a008905680040d5501200145154424004104964081c040700c6481500300e80c20300d543c0301508030034010040a02c3e1110b9544603c0e0036002031410345441c410401c02d07a03000d54210301600101ea0303100350040042d03441001e800d0104140340da0510440b0303242d0f220490801c10307040c0300079090002400c1481044001c100340304800500355000c0c8040c102103500c040041c10074245030005200c2800c4006c1074442045240e00c0309810041c00d00ea010341000d00c5c3d02000000d10b01c003a403618070310b8180c6c1035402c00d002a4003400b013000b401c4d849a40f08000da4814000160f12581c402003c41c020300549200240b04c4e1b01c403800c000f491252100030701481a602949420300c0d070348403621000d040c072803900184404464800009100d81c03c1c801d81084c8100e10800c0400c0702d007a4259a1078a0480f00c00b8404612500b2020010f82801001d015056801000f41d02410001074814408 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 755054721 1250 755053471 755053489
    0x51309050f0601121b0503090f0a0c1a1b1605060f04050d11090708070906030207030807051b1f230402010c05010f0f06180c051b0a060f230402 63
    0x80c10444d01010010500074a9000081c40d4540102e040a03c2d01041c040640729030002c6031200c0007441080305410300c1c035200003016a07070340341c210f00e541e0841814400c0c0d6900019400982c00c01c126410000307500b40b20104e56800c42403045a40c090310302d041d40c031000d110500c402940400c0c419275003404884404c0031914212001ca590880da0700d01c85440360302d000420301a0040202d03074030500b10f1081000a80c0c0144d0058480d04940d980c19010710f031a00000d40880c01359081c0070b8001800c0c180060522801103004150100e00340758910000324180c107425280041c21401c1e00c9404e146101d503440c01d01603d00503000e060a2100804280c1c2c908490880c14103200140085d0410060302d2103201801000c0d4031a03510761140e9081407082c48060340805000d40320310710800022500960701d0440d000c80311b120702c0c0b060840c0c90b55003600d070403000c48480c140b24081e035440c100c85000c1c0120510001c4e0f000d1151301c3d03441002407004184400311741940352000780100010040c155914040200580c0da0981c1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 755055971 1250 755054721 755054731
    0x14030a080910140c071511030708030603030c010f0606030c050408151308040906140415050f27010f12030804031209050f150a151412030a051309050f 66
    0x100116269070722204031440c410843c500782c00e008001401a9000901003040016107141400c0460300382d10800d000c031007a0460603815001d50300180894400107030320344011030700800014212810040011150b500719800c81440c2110981d03102005c0040ca6003600900c41d00b0302450404a05213880c1100e07032134950040b00322500c2d4195060700054101d80c0c1010244010355080090151240e03281c14440004101034025450f2612504804e240c69203070034080c40000c12041c2404102e181d2070b103018429900010b2883c0c070351080c1c050744401290803c0501c00d44c0c40c04e854510380016545849141a000701050b0000510300103042010808130b41c016600715009a898608040001801c11182c0020041c1d000000c00c14042c0d4070340404100c10005000c1245a0130541c01c2c191034581640c4030b1700300d840402030808280e034107140400c03079000d9807031001e140d44c0b401138403026140c00000b00f0310341150700c60204032011590108181c2040c1c103152552201425074201c041090b4189518558154180244 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 755057221 1250 755055971 755055979
    0x4030f061e0603020f0603041e02130f0609150b0415050405061c24030212071d070332100b0c0309041817032a0414030a0809 55
    0x1100504206899111156505860034168100c0c040c00e03209102900140c40240d11404c60950140954501b00c0102e0740503a521084103c9100e2006c40c02c0304842508080c10b90f4080d003030814600c40c442a9014494001408000000c1c590b804c000c8007000710ba07183d101000c082011329805002048980049038180c80310042044030380c0e000504115402c1c4640c1e0040c0c6e42104000c14014182400325818014540d128601401446d0001c0c07142c144640722080021042c000b000400c1016040040111030f007180048144e40c1001c0d1200c956500c07a280c2c9501a0456a00d010100451580c0c58400c100040040d0400348000d001c2a180440c00005401c6161080e41580404269601002c81101004205204095456080890070b090300d940143d41c01c940114101140400c030300314044030f42191164003c16148141d0410302424800b50002403070040c1a1814441046540c140803100880004010174025505e42c10b00c11424807804004a0b01401380e4440221a40010108000d541481e041a5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 755058471 1250 755057221 755057243
    0x4031106311208090c1305010617060306070509031c110d03020a1d1903150e0a0510050709030605010b0912011b03020a170a050f06010906080a0c0c120807091a0403 72
    0x8062203040c00100c030300c00c0741d100707034417495917841b8215640040d8121820703a00e03110110f880720400381800880445500d645030308400000384006001e00060803201c2c7c8041d00311400c010b512461491b110103920b03280c1c000325200d0310b00541c052038100074644002c60a40b0303040d41442c40d40b0b9809031003c06a002061503041408481e01955211008448405c400c08050340b01101d03900d092000b480107010318000045030034000b10080c03070700000418403206c43c0d0040003402d4002006005900804d00909448104200340e280040480d100e8000d15006c0c20005111991310441c440401c042d0b51204201040340e40d0401d4023038029800d840f40d81017400c0c007050401503031700c0701010022030740f0403c00b5100d1180402c051043c40210229540030038401c1540a803242c280e600d4040c010b4031700c524144210400980c40d20002444809141c20125a28403c0d0a0582c4024500d030b5524a4090b40010311400040424082040241d440b075299002045850002013403807844407441000c610940c040a41030b10303125 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 755059721 1250 755058471 755058481
    0x4020105090405071d0f0d06090c08030d0507021e06070c140f0703050c040203090d0c0c030f08030f013510150f0503060708060904031106311208 64
    0x210100d80d2460030003042000f440c0703090900544581e42c811907401079440205403078041800c0c080c4c0800c551050051800300020b00665504003e4a100182102c0d0b501885000044000b802c101800d00d2194510001c00c951420703000007440d00036190000007040100806a4007000070214000b40c00824070710b0020031100082c102811200810500c001c0c1c0361103503412800b114030300030400c9802e03244103406a0b800c0e0711f40c0710308200c1030f4007007551040925045100b01405a90181d10800d000904c101a881c4203142d50b41c481c461400b90728003058450480000810000c0c4001c40c00150151804980c11030a280185e40103040d0f43d8001688140e07204101c9020076801541000420303d801050a01440100c25141c1da204100f15a8490003c84203010304001c22585400301b40680f05074100c0e074035501d07903035146410071031341c410003401c1601800103044251448030700a1144c60710407003180000e82d01d051405103040000c8048582075801900c6500d0b003407170015201d45114501d0b440c0c2c910785201c90f5165 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 755060971 1250 755059721 755059727
    0x7080a03080717061216120b061206070f0314040317060301050f01050d020301150b040503061803071101030b0a061d03030c060426121801020a0f03111b011a0d110405040201 76
    0x1200c052800c6d20b01d82d0003001502c01d6103144100c150b18441e0f94000f03801e80783c1106001c40402c284500310005d40000e40021b00e00b600c901610080c4401919002c03c020700c0e05a59128940070031b881c2500050408a5492106403405001ea900a03200350001c2205160410b003001c403018060007082d20071326109035000b09541c0c0c01d401c1003a0b0502c1601a0102c07980d520207410200c3e9005214081c000d0260340d001401214805041c02c1c2003100c01005140761501c643d030340c80449940d003001c00c1d040c107980d06440381007522000f004001900b03141e2201c40c3c2800303000b108100720300c3e29000b40311b20070b5008011258400b4408600e8981191380600da611684462407561203210301c0b0f01e4110b9070320003404a42c0721030505180caa4680101d019101403c802c0b405c0e00300c15400e030301c210b14000d40460811840341200a00c00d51000d83c941000c15550340c03c00804c400d00c1040300d00c61a004c405980c0d11500851300c0c481510303141c8101d16004490210341d00315075940e518022014000e4041c8520340da41d00144c10740e40 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 755062221 1250 755060971 755060983
    0x9010908030301090e0114040c03080307033308010c092315070318030809130209031b0a060320070303140403020d110303010503100e01020c07080a030807170612 71
    0x30030900340ca80325a11440e005004144903004090b2960904041000218100c1c0d1124022600014106101c41c11a15000026440a03110317900301a0f80744600760380d07001103010a181c0e0900b81000c1c40080039520b40281603055654200e41c2031645415031200fa4070b90069544021200b040c8248040c980c40e0804082000c05c4160030305402000c1505c0d40704100e1501e500030001d0600c640c07600c5d003c81f01e01e61014208105e841c04010001e03e4208800d031454a041e600313058041c215540c02515000710341d00460304117546405191f401d0b04910140070414030303101d55854041c1c900352400304049a5610342c480030b00041100310703024031075000800c40d091611907088508081010300b40e0741c48900b06450000d658a0507a2143c1e000a0b191002d10340b12110301000301d0b412030710014003c1c50f02303003107400b501e200812100300b1026056600b04a1201d00fa02e00b0b10200780205080c00c003500ca03004031414050200030001b40028200108690030040402d503121103240c000030281c881000c0c1c2d19240c425245486 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 755063471 1250 755062221 755062229
    0x8041103060405031e12070509042a080c09011e03020f1605150f1f1703040617100b031e010e0a0f09080315010504150201022703070b090109 62
    0x7005035801c11003441400401010b210704030310b100c2c01c4440040c1c50100b00c1806400702d401c02260300c41010800c00c621441c080c01202100030400a840705082041149256000080071035042c50342c0740c2450040c0e0840b00c800e03840302108503014900520b12000810040c046840308110604940c111410310340300340e060390045126075408983c0c803850325100000001d0000c0c004c51b89413250302d06072004840341c18101400b903214110800d0781a102c002518000512504051001009241c80082d40404580002e0240340468001d0b65580c2d06110b0010803654440542540040004c4103100c40d10501d0344040003212030040003240c4030307240c03819003950802d50b10200e404126461800070414040f40441c20f401410301050400c50780c040311801c5d0341950841c1801409032641480026901d40070242c91441c49041450201e15043e160118540540ca00941100062f980403d41200d5800350b8415494890440900031000244410000c1d5490519018002d08400c011801c891264081c0034480094 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 755064721 1250 755063471 755063473
    0x5130b030a0605040c0203130902090d050304090c02010501060206010321120903090612090b0402060306060702031b0301060b0301080a120e0a060c0209060405040f1101021002070311060c0a0f08041103 88
    0x303814040204400740102d4010144076900d046880036403e400001150003d045010800c65203074948100c601c020340100980c141c102021421060000d03000b400200040c0181c0d8000107800c0e0042ca00c02401c40c2c0b01608241c0c00d541c000c03001800891640b6003100700d0480c94410030410080310740001c0f40e8012294540a1180303040c10903034001c260f0481c200c1c0c0181c4416941d240c0041008411175001e440340c2ca44050027404880c0c0204016007811401182d002e103010303103003501d0300ca850f034046858aa00543c103410401d0982805280c185820b0090720300501c4800d44880c00d550407d04100d0300c8140300003000381001c0640c00d551369000d001d49915000d4040c028030014000760307101c8002e00445410901203101c1e0080000050303a61415108950040b40c04c40c800c5980c8420507034a9003407062090803d85d05610580c0328646151215000030002a44a035692201460f02242c2c6170b4175110014002d041c0c400d1041c0440042030768000c4800e29803e0540c50300c10785a440b40d003011070820b1100c864031501 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 755065971 1250 755064721 755064727
    0x7060b0409171b0706120917130e1e06040b0102150a1d030a05040506180924040515150d020705030c1207050d120e010501080c120601030f0305130b 65
    0x1404101c04058035080440801c034030b61801c0c0c283c41050f240c0529001d81e5020030b07680428002d00e80500e82c0020300482c864600002c41490680501140703400901c0301e200401e43c00e00d404d2000c814003018841d08605600c03000e04400c2489004004d6507c0c000b482d4030b01861750781d500031780383c0d0303100f0040300c1e024011243d813080701420710070005400741c0315203824a081441010200302c0f0b000c00000c00c440c044480742d80c0d018100b505000401c51240d0081c0c00300b416080b4200904100c1e5520f18100034010b00b400303940041e00e142014030a8840b140c8451000344900e140c2820020000c40100198010b01c8089032a000112404003210103030740201545e10220354400324003401000700000c002e080c6020340c1c3c8101da01104480703604201c0381c40303008001460394100c0d00142811602404001c2005120f120001c111f103c0301008150841e2000d9000d82070341e50100c210302c01d882c200480242081d164240c082e0205604603220204001d259607002402c05c240000c040c0c0e103a20080030f00c074003c0c3c5444a820740e5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 755067221 1250 755065971 755066003
    0x90b0102030a2a110f090603070e072d272106021b0c10120c0c0618020406090603080f09030f060103050f190b0a0f0f0e0106140d02010507060b0409 65
    0x8082142945014019900354943e081141b4014920038414500180140652402d04019442d0010080c2a05042c0301d401d5406a610440d255001f12140030f03100800712048496040082800b001c16000b042d1070b902c0098480400328107060703c20103840285034800b101030074003450032050540c0503001400d00c510100300d802410140920210a110301740c000c80341000300d40c030100511250310032040300c04641900407807820340145811800c2d050088e414a003441d0f8071140c48010035103000c24882118452484c4d071a00444c9030501c0340c0710207000c80e01c00c1040228159600d41015124028910322440004580100595020001211400701003400da40079942c5d20300c0c2160796214800c0000005000d01c080350009805811f0004900940003602c5507180d40f5a00d04040041161080051251f51100702c2a46c3c12269801946420400ca1000040d482d140102c4a011040c0d01400140f0031641010003102507a400380680d0341c1b044d004100043d411600c407001800822540d0801801500350100e268 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 755068471 1250 755067221 755067233
    0x906280b0c0c01090803030f37050a05010f12020607230d030b010e010e0d050f150c0403080f03151003020c0d0f0206013c03020109090b0102030a2a 65
    0x7581044200c1190741007001c080054400101d80d008003400b962040c0009840165181c841e41d07000b00240441c11500412200d01c101e16141c10158103224030a042c4010b604a0110301c52070798007035280b4104000c19410080301441c155024842c607850818101403400c207540e24082290f888581c810b5002101c00d50f50a4605403038003001014000900030405203013401c1c2e01900a890300c2c080141d45160040e9100401503820160030012590004880748a038400294104006c9841158420040c289a04500e148800b1488010b12814180c0c105210820000343d00405132150800109a55074480d40c9412419107074030702c009034095000400c0010143d909030542d00511490300014140c6410b0312820307005540f860383d02100d100050348043d004100d52074582031116030410184000f0191598a010503400d4100c20346050900700c4108030702002150381001000000f4008800f00780940b18000e80041e40300c0c010610b1410901460ba29480801c6000c8451079885918440d0383c0074400ba4242001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 755069721 1250 755068471 755068477
    0x912010b030d0c080d27060515031f0509030d06060305100b03060a0314010906021908100803040e07120504050114010b0702090105150403020a0e071206050906280b 72
    0x1806070107030414542c2580d1182d03564030b40c2c0d03982102d0b0892905100201c076000170504071992444a405512000c0c1d00740122021181d00107006d10004203060914003140c1c07015414403140603201f6880060100c2c02c18900300ca001e4204c80782460009425600d8030802c03800e41c0f2803945c484640b1898400c001c83c506406a110b54021001c3c84100e212081d1034940180c0148001c0c0c5d01c9039400f4030610300401c0024005800308294a011000201d441561b40e40c46105031703045110492100798442004110059120401a5205080905181001d031505103410b40324421800b8103d01c2000e0b031000202580e016844005444000364410025072030141410b90081045101640702406030034000100800417009a138400c6400031b000380392607403134101004000d8503903843c82c42070f01c00144000005640c40e018a28018007e00d08150014034140400601070030110080254561520b0300c10312544d00ca4640c015404a0150307011b501e01d0710740700c08212440c80f110780c010101440b441c0000c11822100c0c409 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 755070971 1250 755069721 755069741
    0x80115090c050a080f0928200f040c02030904060f081504120809070b1b060105030f0d03022208100e0303010608070539070506161b0e0705070311010506060409020d02091201 76
    0x240300c13030100c841040e00c0c800b902c1c2c0390302303080d84109040b038404404c1c5005d5000390202c181c1070048914103c0100c000c90155901a400380c4144106480d007084020820f00441c0140081e001504140d031605a85040c544e00c0304c400c45604011104001038000c2c81d0400011000d0001c0b040d00340d840703083c00481c80800900359541c0040314003c1000001d0b1038100065018040e28451000d01240d1402c2d01044000350081000004182083e500c2c6295440709440094090140707980605824040400d011087e2040c80005204580c001c00c01000400d44c8051540d8110a07075180c000c1e65061464104000d0301421241c007034440404090751000d40e6204030510304030391005800d46001e00d0340d41003003007018010340c0783c58a48907200c035100500181d602e4011a0340a1802035007140c1c4140c9428180300203020032100350005c5480001d50400f07142d00704030045071105035a0028403840c078010002c60b690b805179108030503400360045001d6440c002a80c043d20340a000142c000060381c80c26032429800303044cc05032 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 755072221 1250 755070971 755070983
    0x30a0207050f060f16122a08190c02010221060f04140c0901020a06060b280c14030c1501050a06080903041509080115090c050a080f0928 60
    0x4546003650b8808180b852240340f0891351000700e07584d0740140085180855a110041100c02001300c2d400c1d6000744101044054001c406641c0102c84a0034481d10203101c21800050111000c00c001011942c00f00c41600c1c45410903020903812801007040e40a030250740c00c43d00c403a49010844241c118880c079921481590101da000e18a405807000740011648440401c15628004c10002040c04003200c0081042c0d100604c1224113001ca19100d82c0100d030749640001101040010301c10200c958030b82016501c0482020841c1088410101d0251900046520090543c002078102200100081c001e861090302d8220698040000502419031055001d020303040c861460000d003c282c191041c19083c3c0710380c82c4000114070745818109000925105000d00c0b80c10801340b02408a0900c4080c026040070310f1009100f80001402d10f080302c0144d51903000c440041201c1400025a081d074081e0030076420030644049081280c542d4000607082580100f1107200440c52189010503500482040c43c0400340038030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 755073471 1250 755072221 755072233
    0x20f1b010f0522020913080309030913060509060103111605070e0f130f050115090f0b0105090112020705010e0a0516290309070e0108010207030e0306010e2a030a020705 74
    0x40101c12501d448030724003e810354116407614014200319000c42d410074a07004400421150b50345e83c0c1e10b525407044840600c5034001090b80316060401110817594103801682c00e021440c200030115000c5200184498101611542101000301000c0d04491030050344d1039400025801605025030b0300ea23020701c510300c482280c0800150b000344020480e14040c031a01080d10000c410151500705502c4100c0006607100d55845030203440782d04482136020000c100e0084003240b24594a00c803030003160f42200f08541440303401c0003403060301ea1344038142a8601c3c0c0c111400584801c1c0d142802401068041c540c000c8070321540350460248603002030b0000c544640d44000c0e089960315003402c401d400160150550104820803042d003a40b18104001d541e011090030200d0b07400a548044000040c1402e0340304000300e0354001540c1052540c40f1012500120003600100304035450280f02c82e01d4220018040d50701d80040003070700c03211504c0c07030031450b12003d0303806026a4482c02c069603680d00030b40c0882c10894043c0b040e0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 755074721 1250 755073471 755073481
    0xc0c0112060f030f03020f0a060504261b03070203010513020909030c1b01111204151107091812170919080d0603020a0305060a18080d020f1b010f05 65
    0x503010740d505850044000c04501843e40e6503801600c5296142141940a42040e80444120410130315103c280038000224503814281020350b140d603d48038000c0082100d003a032075544d0070b440c001101d44808000821640c500e481e000d6031825070060700c400a40c1035080205000200b05c0b6039410004c054002c030341780c0203130746c0764641c0d050364903c901684860baa0b0081e4a0f007000071400c4003104c10400c1da040c10180b1a42d50071103112418442012226081210041014840201b80100c4140700a02c0da040c204280c90300c2c101e2160352002e0610403881290344413141d6006010600004071005540304005000030728204201503c0000401d0340c0748000081c00c80026941c0700002007000f03044040c0c407600030041a17181ca070000c03103a0280c90280076603a2906000001607c4403019440154003034002b07000e40e82020005402038076940348540310b010142d02c100c040131400036821a00152001c0000581d12480194146c1c01c0d405411550004060100b90649402c071040d0084851403003001d00400c825522 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 755075971 1250 755074721 755074757
    0xf03030c06060a0b07150f0b04020703120b01051213141203071e0c0605090c0a3c0b0a09050907020102070308060a120615030506090f150402131503080c0c01 69
    0x601ca17005000c0e0000111821242c0505502c0b2480000740e8410218042080102041c160b0340403207401c600040030706103280401603962045412140c806d1074054a011800247c132080000040c0220702030520a040c1d12040280075102000940d0507134058510743da0131f45a10181030342085440d040421050754034000c2400b88244550071913021038544c0b184904c002d480d610001c100c0180760205c00d20499042c24226070760103991800500e040002e1070321024404480c0e940c0728403440b0001d41819103200040360b441c0c1c0e0840c0f1041c1560301c040080c98680d034903208101c49030705180d400b01e13030860f070120280244249d044d001024202d00030381781d0007529201c042c00d00115034003910074524069070803510440080c2c62a000003141c645425a03852019440380c440904114054580c17001c80d80c07000c6a0600d14800600c1a040c0b20f0241007001c150b20310305500807800c1019464042091655110b000000b5204400d9459014507002040a516540200582940c4540c80030440d4042040070440300c83d1040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 755077221 1250 755075971 755075977
    0xf07060e01141b0a0215041a09090103141504081b15011e030b0f0103050706020708060c0a031b031e0e0c06070302100f051806070c02010e0f03030c06060a0b 69
    0x76403901c2e4580780060445000b8103030252440c4400c09801002400c4000d80d580180345d4482c09a5640c05582c2d0314908425007025050031a12401c29070402d0005000c0f540d6181c01d840d0449800010f460001b06120029604100c400107415448414920030700043c840a0006041241c80c0c1241500503022046030841d940c10605c00741c5424000203100502c03080200200c24030b1000a06401240c4207622540c8100402c1d0040f142000310451100042041c40780801851000301035078000386c980c1500b80354040b91610b200800c0c50240f820005441914180f1907880204540c03c04616200030343c0001c0402409000d02e000000c685c0d03425540e010440d032455220700710a2100310300040100c2c1280b10b050151a800400301a805e6005208401072800f00034010040f40303000c0c2c080f001031185400c4401480301e0312004451009d9500c41010004529000208102c01d5502400c001c0d440021080c0025414071003e03160365007500000ca00340200343c07000202980141411030f2000d0180c3d80f00e1852030701d02c0c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 755078471 1250 755077221 755077247
    0x3006060f0513150207030b090d030b090106080a150819030e03010c0c0f06020903070902120a0209182d060901060512181009030e0a0f0b04050609030f0f07060e01 71
    0x2540700081048440000010f1241080301e03801642c601c25965203c000c89403c080701c0086a90b04070985030024164148a50010303030301c0132101d41d1425410301c500200742c010000e01088100f40d0722903600036450540600300340104682001c446110101c110800302c0150b02100c00c4010803110341d400040c925044c02802d1900900e42c1c1c8140019940da1aa4081e800ca024000c0d0b030455400c2240600e00e8400b848042c000e814010340159a810341c2110303480b0841c2d001804200c0c014070501c0300c000c8660b69a050640e08044001802030b00e0340b00c111000d034644050391004503500e800a200c01d0b42c200c0d40b4a9402e48183c0c0300303d817030244aaa13100e00a44075031103010b68400c2172a1004000a032a11030b0007103c02c2a0320280d90803100c0003440208200122515050154003103201c4c0038601c00340d4a40070b175141d03003d803410b0704040394905e140c0b07600700318140601e0040b24443c20012134030400540f001c01c100718072403084a007111402c0f04820300032621381c2854042e8000080f41800c0004075540180c2c9603108003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 755079721 1250 755078471 755078497
    0x504060810050a1b050d06030f0f03080705043206032403030a1407060b090709211e051603110108010e0720030c12130906050d033006060f05 62
    0xb2a80e161130449203540030b08045101c0585d6a00c0110110301600c3d00303240542d00c50302d600c918111560034040d1660754002c02c11010014100000d1180318441d2040c0c4100c4c0b010141005030805801c0890181c03800400e403601d82095011007040390261454100c000001c5481207080d00d002130540a00d40c69100d0394400c0000b145803411040e0114102c04010803180340515000603e506818000541d511002c1c3e60900000300300800c20301c4031441e501050f1103c403025056000410720140d842c174041c0c40108408100040d55800d45005100c0240811050012a1441c6290203a1240b40c20904000510261400103e2104c000b103840354040721543e005250070340f00c008213405000070390100c620b2070f0b1401d4a00b40c0410300c2803610b0f04208000035602491110a010344442661800c0b0f8003c095603844000790604114041103503403140c40b041c0340d0312a0545040d646100c2c06500004040c205d10361200f509006603c08011004030030b60104040d82c03055510940a4101113100301e5560040c208481c0107 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 755080971 1250 755079721 755079761
    0x150902040f0e0603030d1811030d0c0b150909010e0607020a08030a05060d120c021c030519020a080703090501020c121504060b06041205060a0c0203040902090103060504060810050a 79
    0xc030707020b800d8083d03800038004040701d02e0500e81e28211003c0e144102039400c05181640d070fa101c100308900080d110700440035070007400c0c14a0340c85002803001100311000b40c042040d450104240c80180005080a4500500300d80c019080800070741d40280714000d01c24425014070000301e40f0141c0b0100e04840710542042807103003541c6505101000828001c1c11590384285590400300004498441d100d51026941e1662420580c050052201001075038104100e00c0754580c4000c00000d4000c000d59808481040c04a070603036200708801d0789025603a071800380c1500381c007107134042c02c1651121584003035940c00c0e401d880305004410103102002c2e034401d26542c1c0f5600142c00f9583c131021410640f03684107000f00d101288054002d0082010340d0701a400030107107202114030f18006d1120821030503030405143d1030204007240c10701034002d480f40298012044626000145842c007a84207030810006004c0040c410070600b40e5642200e03a5843c2c1e803100055005090000103803403200180b00312a0701d60551104010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 755082221 1250 755080971 755080979
    0xc09010507030f0e10050306120c0607030503062e09090b101d060c070602070b070209070c1b260d1d0a0f0806091204030f0311010e060a150902040f 65
    0x40c0342d0441c0f00b611810050320454a0481c0d5681007003240c030420954450980d24101030040c040408e110404421081e80400b507621080e8540408a4608035014580075449480703a00000c0d07440082d4010420304140d13062403400c1064040d040345480e0b1400b980700c0c1c250b460f945010b15802d0720038040712183d110b8500020b981c4024000d00c0300104448040c08006030035040e800000306180c000b1002c00060703502c82c2d0014080c554040114002428804000b181403065650018401c3d1400030b102000700005804000f04110200000e14074030116055034119143e203500f14403040030070450204c401d031401c001e001240074002240003d42c2e0700f01d650b43c11020509203000e61004042c41a41c1035002004488002401c3c3c070503d0000700a8142031303020b05040c0c1000c040b264070342030040e034524208540402007000080d40e151801d120f01d9601d801d02071499841d1400d01030041c030b43c5414421550140300104070b20032000317900a10300317980103042600d10700d9100c03000e010803800780d40604000e405100400380 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 755083471 1250 755082221 755082227
    0x409020f16050f010609020f0906161502070209070f080a0507120e0601030507050603092d030c06070801080d120203060325050405010905090a110303090a0b0c01050c0901050703 78
    0x81200382600400526090300e010408040e800d40410584103074001c441200407441c0c0a004803001480300880541c2444245811600c0c944901d6000d68803500002078004007000480f00035003203480e040720020400c031001d000014007a50003080201c0c4108003440014025902418414001c20b80c10f83d510802541c07520490b000800024000a0a206020301c500340e400b0f403140155540014940003514007545540390103450604aa04158441d44043c0108080460006600400b40a0009410034184034000c5a9060140940c109032618080040c5c4d82c9141200014618016180c550b01d1081d503070303650072074141c844507000550800940c00c0c4454041400c09a0081e54100b04000c09888a5816800700c0416240000c3d141144a071034140080115240500c80c0a00404041a00b4040b81c5401c0601b203860b1845020001d0507072881c04001c9030140c0703042084d0f81d078101018211014182d201c105c0c2e10702c1c03034112200106c09907080000285d021503880b02500c6515006845e15810030200750303829 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 755084721 1250 755083471 755083477
    0x6061612020f0a05010f0608190602030705130b0304030f0305072003120403080a18081210151713030905090c070515061f200106093e040902 62
    0x10110720032401d5a110701e5200303024150f60a440b403000042c80000164404d000d076000c552050403e07400010350041c44906445a031658581d11140050b0782ea80c85407802c0d84c85014144025401e40ac0c5050081101204440294020b1740240c5802121408071a411400c0d107000300c60090001d620800000900a07910351000c210354070070400e503810124609000810f1240c121410f0b000a0408030030300034161450310403413109010310660450f628210740c50b840d4142c4154190b079410440c0c0c1c0720010748840d00b0740004c54090007050911011003402c00034000d001081c928003000691100c0c1c400b00f1040302158921040b00759240e210418420310f08001c00c88100c00062048141000400410001401c00d004042a400340c00d800c80078281068810b0081c0c00141c40d0290840d5441260071509458000303003007410b113411b00d07a1061000501030180342d001d48a1a81329020141c03d01c52241503403100340b00c1c1000c41e41a40e81d0b051061180c90b0b61441c200900c092460b034404c01c4200800d0010034055001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 755085971 1250 755084721 755084753
    0x150105090f060918180d080115052b060f080d050705100609090b1612111c230f0408070614071211280e030601060c0605060616 56
    0x1e00e0800d485840403440c6003c21020341001c13050503404205e00a00b400c031800015054081c0200b8803101400310282a0b0b14040c040e048100603041e0394008480e200f0741c2118460040c0d80142a0042c41d80c3c41310300881c07190165482481c80c20460046524809803020408035078903640100301740e00401c0c000760748660103c98180d6050154010048004908e4020364004105c0d0780740024050b0030505000d80c00150241054080032020240076070b81a030b000e51559200c0754000c1d800518811121002055441380c0d03c900514101d003101241c3c80c200850340014030031102034401000038801c0300e17012007107900c007124004004448040840c020407000300150a1030f034800d803c00181c09605d036001d00c41c00320045920400064a03446100f656180602518001d18a518092400e04200441040b00100200940130303800715482031080f0b440340b04480b00c107c1c0e0381029065861a58588070700411000407480700742d89a46c1050003059840c1002c2d41182c000070030307002c1d081141500c50b0341c9515007103208ac00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 755087221 1250 755085971 755085979
    0xf060510080111070206210c0403060f09020d06051909050303190b0604180908070b070201110c191b0f06021203060a1e0308030c090901090b0607021909060b0a0305150105090f 77
    0x10403100807004451f160300a0403c141629215491450008107582c4401c8903580a68108402c000068444c203000024196110b0800300f400e80d00c1c006a4803415030310710f00540c00b513418003c2c3c03482401008001540030b0800d4400700d90100121704102c00988081511998215104210801402c0e02c100f8000e040e070141608017144010785500c48048903000301c841074074a41ca299043c04600742d024880c0080000440400ba4104003000200d140c4540103007943c0250f005800e080c040c1000004481080529802c0e448000e030705484040220100f09140100300162084031070a100a4000c3c1c1d007524402d54005201803403090414182c9111142442107211281d41c0181e80030000407007a4029502c0351001d2080952107000400800c21f07105410390100e0003c03440d103200c1d0545900c41d04d0890301003c1d016920b251110110346401c045c8158281e0004403151314052000c00c901c9000801001d020380140c1c1c05000d241c8540c100403d11188407030345540450710130004d581590a05a43c030845100c0014 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 755088471 1250 755087221 755087257
    0x307060f02011b17071d0d030509040c0e0108010e010e072a0501050a201218010504050c01111507030f020409020d2c1f090f060510080111070206 64
    0x1003141002140a48101e002041e0842c100a40007032000350f40e00e41c0000e891038401c400685241780400d6001406e800180945002c607100710a050094080b0b443c0e2000140003000b541600c006d000b06840f900b81d401c5800211500000035902d600010840d05032210071500880b01d0b01c881805030b402208804068250300303008069511900e10303417402c240038207000320008030707040c07a00811403400c503180e8906000059540300180c02c418041c4c017058640d4401d140340702000e10784030462211411010420032000715801d0208000c01c0141c0810815142c45080e201d00d052030f40541406034481100e503107066040d00b402c600103041d481c800c0d0000c011030403000800614043d02c510124080e40d0104201c0303943c0b2929070158504943c03148000240151000075080e00d00c600420409031a010030f550001c0b0b904050310540c007a460307601e620450320507602040155118000c2d01c0c250001c1e00d0103c0301c010041d400c031300b00010b1146060055021702d00380034025a10300441542000b480e07410568044580182c10 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 755089721 1250 755088471 755088491
    0x130213090b0118020a0203030c07060603020a0617070903021c02130e0102220b070b0415061707050901060504171c0c0b01060c0b040212010b030607090302120304050307060f0201 78
    0xd1003048842400398031414019810f0561a80401c0c80c15140d10f0481d500c1000240d6910b0390101c1502d03002030480c030446039074121505140d8060442e980011b944aa001480010ba454115940c0c1180c404100925001a038030401c0c251001061888040d42041500700501d0702c2d0111140c2c1a0324043c40140119180800403034148121500c183c1d50707098a0b0750016600f441c40e40c015445e2140441c1c1401040040390030021041307181d01414070b00030210540c100204d0200074080c0c4074041d110803100d01c00c005030380d601d058029000d034210ba81c2d85007501076076602045505254600038140d8130141c4681d4a444c1c0f07051890140c1006404080b6018094070340c00c034200303a9100245204138203030f41e51100c40ca4400c84c02c0c10b0000d04010707803100d000e001c0c68507030013400140e20030300312680305804a410070030b030608000d440d40c0585060707a100356040c001c400400c0035841d00201c4d0081540e0081d0f0b60b140c0450001c1c003d0503564415800303800c0c0c2c551f00c240000c001c109d00c1240a485102042d10001c20044030b0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 755090971 1250 755089721 755089759
    0x12050c0a0c062a1a0403050c10060e0f04020109060e0607120509030706080f0c07030e0301051f09050603030315121002180301150902030c0403021503010f120b1302 72
    0x525080000061049501e1050102952801d001004001c1c2e407001644941c3ea42c8505a40d1a011105540381801600040c14036004406440e4695442c1080d50351007841303104901c0007003003039005003c002059070300031960340c0003046410b511696040e11003210460402d04242e601d040920b9855602c12003c00c41e0354009030800c6948050804aa100c0035114180e04c4d04040c00e10243d0380210082040724402c02c00c0842c282e401c240c2e0005c5244d42029502c10300780c01c1c201da110401c0491950990b0a050a0007a02c6010700307452202d644200400e20300c8241c803084e00d00140d80b41a51501e6142d8010300101d200914604401c59045100501c0410155483d03100c1038102884030b0403116070640d01061039505010001d11200a46c80c0031002000b0102d88503402c1c4042c4d100a005080000d94044001492688080219009107070010000788842150320504903032640240a1810500d00807100011041d03051070340c10103042e6004280446990391010ac4803440051354405030782c001602c81c102440b02c04 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 755092221 1250 755090971 755090993
    0x1d060103021e120a0e0a030f05031b031311010c05071a0c0d0c03120603080a12181514071403060105071406180f121c0c080a050105010c12050c0a 64
    0x16040000f28018a441c0d9881411180f4aa1a050164102007150800280d10628902d82c0d0110341c00c04503140c1c1c0303c0000d10803205d2029000300070691400414803101d450110035881c030070391040130009010207242c401115a104801002400c03507004c541e013400706054000e895010700580a00c00d5081101016000c0c0c070740b0717040e40300840129040303200c10b40038140c2c861001c00461420041c00e20106242d07645485241c401c143c2410700304048080100f2035180150003901d18070803052907068802c819410f054510703a41114210b48410b2401041801a400c00044184120b80399216a507103501c00741d80034859588001d089904220701004030800081503410382154030707410b0900900d03091a020840750061144824400c0c0c2660005400544141000981c01506004151746039160455610010070780901c0d010000c03d024107104d070003050300d40d2007240c0310302c1001d039154248036a90b6104010764000e0801100074111481590300c03606060300440080030035201e490f0459142d07032a42d403500031039a4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 755093471 1250 755092221 755092237
    0x20a1202330f090d1a0109050c030403050313050f15010e010e0403111f141005090610020a0b04060c1b02100804050a020901090b0102010c210902010504080708010c08011d060103021e 80
    0x401c100c0c0c0c0e8a440300b1031701001c1405440e02c000c0820207424030f03003c030300620f0000070401010406d0000001c0c14000c40c400014410a6101045942240c0945501525820801303407002243d0610300002071000103c1d10a2070490b020240c003141383e5140e5403000c85001e1007241c541c0e94030384164040034800010700840c2d6600d94075080800079541c540d44814204040d4060708641100010300c409019603034400c1c8210381c200c03100b100c1d01c907482401408240d00381a281d2901178002280101007206011017a004920000900d988041c0c1b80d9524080c411901f194040021307400041f00710801001e40e00034031300560414010740880f1002e40d29075000901054003600031140c15500c3d1100d500507560240140303c02c1202d0f6090003141c2040c200342175110b050301048010b9000307407100d0b405815a4003401c100c0e0041d00159081d210807036142c2c101d070750280c940081d00500003548000006000303082e219840101c045401001c1020344c61b07850045000c0d41145c24480007540c0c0b81d40c0110700c1610200b000780b01d10 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 755094721 1250 755093471 755093483
    0xc1a0712030c030b0301020705120c0a1a040b07080c03010306050403110307050a05060a060522061505190503040f260a020f070911030103120507020a1202330f090d 72
    0xb20462150040584d200403041e180207030700601c001800500080349441c6018504014280c8400c01101414680400c11001070840081c000a0301c3d00e90411841840c8994018140c2c602c00d030300d80310300c100c80c01d40c0f00700c607140306100c41440144001240c98000039003050180c900100c4000c07541614500b0740d40f0880b002c0b210355100014001c101300040c042c03298810192501005000d1500c0c001c140c20014a2131810056181c15548454503d100da1100c000b03007240030f101c2104401d601a02410607440765400420a800302c101020107107105501b1a40b07d55801507100c1c0203450640d944078440d000c2d9210403d1000c2103040741d0314240c03641d100600140b003210b5000b02103000b51001407506044080d003140003030341c0c106807042c0d000e80314200803a07045030740c4030030706641100b00c1600c11a001e0260880080d48540206000181c2d0108656581c6c2014021180e0f0381c0500e110b40201000498030816184131003802d0403003104040c0c80400a4084a400c10340c82c90318003540d49001600e5002d498104444c2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 755095971 1250 755094721 755094731
    0xa0204050108010b100e060c0d09031e03050706050a0e030a0203040e010b04120201050d110f09040b1f0f11031b1c050d05041401060602070501020c0405040c1a071203 73
    0x15494140503041c01024050000c01c421185500400c0d140e41c40c1e08582c00511861031032100300d41d1201d50855000c4400401030351003000c0c03000d4000b45850035074032007582c400f1904005c0c03422181191048210316170f4562951482c11080e0380d16079000c1c2030300422040801c0e59840d80420352286c20700050402c03d80701d07405550b4450401c54030099041d410380050a005000340070500085a0004a81c0500b503024240240c50705140302a4101503c0000a00c01000c40c0200e18007541e100110301500d449841298207000078200c40c41800101c0c00541c458444910350710a50780c2c00310307020315105c0c40c40d000c65183c4a0401c83c4500fa426182d0307407005296448d0b00c0c1400c0f800d540c031844180300d810136450104c8103d030301c40910250000d14a000d0183e540894a1781c90f004102003001d0070464071086c03038500e4000d000ba40d0b940d610182d00c0b140c140c400c40d0301602504445880919062251301d128560000d60b9800050804e00d060001003000a080c2c0e9040d0410000c00c40841c60340c4940e0352100d11707150340c0456 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 755097221 1250 755095971 755095973
    0x215131e1101090801150b280c0227060907050904090503030a2307033201090605040e03070f0302010e0f0a1a010b031302010e0d06060509060604060c030e0f120a 71
    0x55000c168040340542e45081d803c20312007451b0791120001c50329224405602d41444a02007083c1000400054000e0701c801c00112800c03a4004601e500158001c443c1c044003d131b0348803182c15104a1000110303210800000000710035180c825141600b0115610f8450300303001c15440410102d6000003419905548040304211004c99030b4041c0c20f01c0d92038202101202c03002d84000303880078010301511100902d9200c16529155000502420341f4203248500c55154232070907202056074106080c00384003072290401e0804140d41c109405030b070010340e2540004600d000c4903629170007914081e64604500315500c800c0001d02d881310412000e00d02c2c0e803c010150007103042c0f901d882182000010003070804100b043c030040000c2c1e20341100f0f4a50058010805400030451840100d410b03204034903071b06138801c0307814000304140459988400309a4406482c002429120070301040301600481c030884000a8642111b2000a031144c1c03950000705501600407508400540009018541c03002e0880a656000f841400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 755098471 1250 755097221 755097227
    0x12040302030f0c1302091903080315060405130f0222170a02090a090201090302032e0603050a0201050f04030f060209030607090305070b09030a20030d0215131e1101 72
    0x1031080907110000300716010307a420100c0c04800101345600145980850740d0401d640301c4960003e20142d10b030740c001d4011501c2c0c3c540000c2c160001d40304000821042c1c0700400850904030101e03019200000c02000d17a6541c0f013403140014284810b010b2900e19024024814000c0303504068046001c500d602c407a084601703008411620501c01c00d008002640b01103000c00251300c030743c2c2da250f401100c50800800c014015000603141240d40b84d0000f505031003146000d07040d45200b0102d074031074110000c1d52a100396000c542810705840603400050055082585107070300541c00388008240d085140752483d414181e480d141e0080041012006545880e00020380303040782e1400348103c03039001c030b41c80c101208041c0c19515055909ca659020b5007001441c0010300c01801c3e9020400780c0784055102ea008141420001300700044941001840380c0a0b110f050f4803544541c1c00851005400310401d0003041950342d488441551001104000340c4201500311101681141c40b121080d010074043c0102900b4131601e28001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 755099721 1250 755098471 755098483
    0xf0307050a0510060506041202010e0d0b01090e1212071b0b060a170706030e100219080601090312030b041404030804170403170c07080a030915110c0d03020f1204030203 74
    0x194034040e10340f1105005c19954101500c007941e00810001c194103442d403005994466500952a07031100407c044001000014444103040c0c031000c5030103116001c20612525502c803d4134060b002e04503000e12900d420801040100e551040707080c64200d0b02e0b6100f0303d60451860350108000e880e501500710401a80e4249072400d00d008044050001e0042e0808070a0140c0f103440768007a070002c00d900c0d0405090802d404101080005840c402c04555443d800d4807043c0180c07209204507404900480001065580210480d02c00c40e034012070048030800310324508800030074402441c65806540e4140318805410400710315031080d403080c0c0300d0982c0385c102400c000e03540086c40060030602c504100402e0000560207410300e4844210711000c151140490300300c40d82050b1054000010511a1086000525920003407000031110703a0402220b1860503c503044810b100c001d19118801d41c031802802c4001e04149000b58003450007071065500c1c946000a84504102d03a4001c45440440042000c0c401c3d40303801c1c000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 755100971 1250 755099721 755099743
    0x6260114041a0403050d0e030d0c0507020a1e0e04030e01020c06160201030b040e120403030305151005090d06050705041805131410050f160309051e0f0307050a05 71
    0x11109991415969014403400d03a1009038800c00c0b640408038007018024002c1d0f480c101540403003409030084214200e992a00000f484c2d03003009080040400000d800f030012210059006001c0000650805900501400410009600000b54003000240300030401400c0fa00032803003695005280e0030254002407900d101c0420441c801c1d80100008402c54402d819940031003a421b08004c03411030030900005008002d80345c0100c070719006000d1000203c4100308002c00a07603219490400154584c03881c0c50b45068554004203801000624007042c450707024402414030703c04002d0040c500c4040d1607440c01c064a005035900c402290000c01c0030b0160304420b80000d40f09902049081007245000d000310000fa221109000d4030b1492450b070983c034608402d01c1426800359050a041c0700358100005c480d0904d41040390800000703030400301506203441c8680144040907400c035005000b407219003130b07108a80e040b40040005080c4143c9154002c0a0300030b00180904038011006400302401c40d041c82030905c024448 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 755102221 1250 755100971 755101001
    0xb070f140d081f0b031f1e06121506080a0209131b050c060c0f071703070e03010b1302031e04050a02101e0c020d0b1512010e030702090406062601 64
    0x280512600c0d0308801520707800304010b40c8010806000708941b900070f0342d0035003000e0511800c0c01010009050030f8081c10b002c6a8107561030810084001c4401030440e030102d11000042c40c1480410000300b441048160f401010385100149020950f800240945408140f01421161101d40300c004c10140b0194000140082c0e0804905d0312b4050310380c1c140c07079240042014159480200702040d607030032024186c070132450380041c0784004070000c2110200660412600f100024540411404050406004803d0512405844002e45034015880003019400081010181050b80400c01440c0303c0d130000c0c1c0ba8003c40c003480140c048000d90380180140d0901445508040c490255089001d0b00f41c04400341c12038501c10700c0c1c00100d102d0b20744002000342c201c2072405841410080c0038010a51074404520000301001c0768829058814501280e00740e603e460400401034006008202c0036007040300320a54000d00c42e460001e002616410a0241c03030340344004810110708107070717002c1403441024030400e002022200 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 755103471 1250 755102221 755102281
    0x15040902011b1407080a1115070f05010204181b0c1403070c150e010c110303040e0106051c06060c02090c040504020a05180a031223031f0e010b070f140d08 68
    0x1403110746a0f42401e104103400b40341c1c81074140c41051623007000e440c24a44d00c01c200c6010030322a410075078080d404c24054040d4101ea041c10141c40302507248200702600300002420141500405820342d8108826213040c2d42d810215421024043d000f4802000b4003413043c3e0000164905111100d84400d0300c69220380184000ca007012005a0b8000c2c1101901030703408100e514680b62500046820340c000d40c0e03c0041040843c00c00499542c4e0031801410017507d910b5441c041a01c0c4c42c004030300a60701035106003000b10740c9440a42c0098204580869404110340311038a00d850794030404074040340e00150b07a2500007880407602000c110b00405115500100480c1e24640760350444e01c2e43c40d0317018404d800f030303400b4040c0034030164000c040c090711000d9000000e1000c003912482d00d10308203d100c0e9091180101e44001410010804801d40d4298a050750520078040c0c1c10004503595090000d02d81c00b03000d450800840c50010300c0b5640401803d110074400343d490041d14100f4841c951144030740c01101c010204049 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 755104721 1250 755103471 755103473
    0x1401080303010512010e070e150a0e0c0904020408060c2533091202070e010b0906130308040f03060b01030207200a05060c01140c0315040902011b1407080a 68
    0xd903815038101315606943c04203150942801050b484200d40c0850041d01c100256805c043c41c1c810744102c00c00c94002550ba100e0b002001076484443c0102801c10342c090010640c07800003034002e4016000043d000510345134890403040c1c0b4201007107890038180e01d0700240c1c0c1c107102d21032050610692400d04d03c10000c4c822040ea15003804103440c618480410401c401d1420740d17034140306c1c20f2030f8283d003500c40104075609240c1800301c5025180f41068001d0b202e818000142001e07840e9000d030498030328a046e5030400da161020410350b40d001c40c02203c00008040ca0100c0418034210050008115501e4483c4038a8a14a040802d03a8240d141c1c00703061601c14001c00000c1411116002203202da507480c40d0090410303402c0019a0115240c110640004000c5104000d441055000c081c1d83c840c9080b2a14069031103111100301880b00b00d4008081210132210128141001e80003d200c69205041c03c2c0010081424003140728000484141d0f10708251800000d8003103018000c0501170701c1050f015180b00411 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 755105971 1250 755104721 755104723
    0x20a0224061509060a11160305070308161e050c0103020705031e19030b090109150b2802010212091902060c0c03060c070c0b04030b07081504021c140108 67
    0x30040c0311034099010030011841c560400c0044682c2240700500c4542c5804410000030071103160560014024418103001e00010000d003480d12003100d501800a01b95903085942c0d900544d0000c0419010341c014060755000010864000303170b80030003003400c6200800b0042c1d0234601c0c5008010042c69050510400c8000003142000c811103040709072200949110100058007400e16102ea07075100083c0481d115901d00d025030b415044403560040031600e09003242d0302d03031101404890507948207840104824408004680f220ba02401c4030126844880e842001d075541d407110001c1e03440300c213a00140d5001550800d0140c0102102d600700424000410031400d10300034400f002a50700c00042d11882003c0b554031422a010131452480c0c00307000c1c1c152a09030400307001c010523640040b03508a50f41403140002184140196003600c0480c2c1e008101d1800759281c81000f42c860400c003501c550240c8a540c281040d0584440c0003c03e9601498102100c4442103141301c0d10403a141407020300702000c1c6a4004100d407840c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 755107221 1250 755105971 755106043
    0x206191e0f05041403070503062a0f070209070513030804180b01090b0c0f0d090513020c0a0209070c050d080a0605030106031211030d0501030b060109150804200d06020a02 75
    0x1055003c60040d13032013100081e1600109900c2180d262042804016449003848058010f03c01d00e00c02c042059070180d00f070310415004020050803041b800b400200098a055001690001064180704e40b81c600c1442100c000d081c2c10f50829541c200300028100300d01d402d1960391811a0506100412220800384002003110300c02d48203c440b40800841c940446d01d1003440b00c00b00da0400c00c021904543d85040018080b403580f4890b45201d2180c18910761814140da0080360b15000082000e042106202e03402c10002907005080c00c02040291101907001420400c42c135021602680c0303680001e80340594014040d00c1c45500198000c0c0d0610004100045556032400949841401c2440ca4030030005c8040f4694042c15002001c100e04100c000403d01100c010241c0c02500c00382d03210f001480d00c40448001002e983d98240c0700060300308000401003400f80c1c0d481002400b908041803c13a08050000a1003131030340d10009e66166500050391800f650b01003004c82300d650400c48042104e203800310070018040c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 755108471 1250 755107221 755107229
    0x316031503030e040609020c1c172202040203040609260f0304030e0603070309170922020405060703020f190f1101030f06230a0b04120206191e0f0504 66
    0x100f2982034000140ea183c0c0c100340c020b880103070001c64035041074000307080d941c1d01c0c003c01d0001810801c400a00029201d9184e2a42a4280d0038004821703440700821200041c0248030b640540303141c0c0548201c0103035540d0009501a5020300004034046d68241401d00101660304010058103803281e101c2c0c4080900c49041d82d070ba02c008410b5041d10781da941d090640d02d100d5031035401c66110200100304075006416601c940602c0c0d000d4003008a010684402c0200c2c6449440600780d8000711f02c00444c000c00c07039403400c0032040221102c4094205036480c40801e84c2500304413000c90150b08646400c02000004001c00c03010f1030850f02a20317082c03242d44c8e140d071084c1661000d000340c070b050641d0421321100c0c0d0081e04014400b14800f14104085a5260030320600040d040c0c0a100002c26001c8040d00c00389420010303001070390620500795103010300d00310691420742031840c0100d800c402e0a0000c1c5c0c0000d222019001c2c10204d044e15000882002c0c4422000c1e0f01214004d04804d0060441200b00e1040d0f000c4c0980d0262 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 755109721 1250 755108471 755108477
    0x40b1e0703180e060f21070807090f0b0616020f03070b0c24040f0c0312051207030606091e09060306140c0c060a2c0c010e0f06031b04170102031603150303 68
    0x400070031a02c4800c0c40c41c0c24421b550003407203000c40c0080d81d03800000e48001101c06a490400c815844c1c828a0300548148100b074a522a1061040514200c103100740100348500c0204913a0300070110301c0200b400c0140c0d50340400352040c80030035202060300043c407024014106c10200c04d03245032090031000784050b40140000c0c00c03180707e5070150420400c607a11000f0181d904460075090110940701c004000c1d80c411000b004292102c0e401003003182d402030043c14260b44180d280d5041d11418a024800d840340401c124800c0304100000000f03c4031308520411000d5405000c0105805054441c11a04140003410400305102c081103070040c96040442d807160001c00e402c1021a03038071403420303001c100c0d600c2e01c0c84600c003003d08828440c070000c0000104445091400c2c4ca07015031415800003000b284100030280d054100341c2c1000091000042190159000c50000c0102d900b0940c83c0c1c2e1021035503082080d0f9262007694000284420144030102041c00000207140c2401848080c280390b050100030b1f44401014 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 755110971 1250 755109721 755109739
    0x15010f1a0f0f040e0c130501030e1e07090f020a09050303180f0a0315060314031e03060d14010b040b0409151d0d03090c1a040b1e0703180e060f 63
    0x1070b044841d01114020804420a4213050403c000c00d21125400300442404140c802140011107500a000c3c400c0000340c0312000c2e104080482a007041018024480e0041e140143d030380124449500b0700c580b0075080c0c6038400050320b031580041d000e050014960440ca01c258020301c4500e4041281b101c400342ca02c4c2068503140c460301c008101084941e07200b604000c0c8100941100809042156842201200c7c00f41c18501a402a1380312803c3c2c491050316241d1450540b440c101c0102e285410303000b182c001101808000d007444881e03d956030f1031041089a26a240d440740e610354803034030f4540140501924119402c200c2c1d070750245c1c0e60782021400504254004c64a800050120840b082c3d001e0303c100306200c2c284c0e1192050200010000c0c42a03240072102e0185d0f031680401c10700d0b1080c11210b460310b0b100519602d001d0134480c404019411040c034070b032010300092100c09030b62501040a0000076102e03484d0b2090383e060301c0f045083c0504841e080109100050000c21030035550710039500118401c141c502c102 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 755112221 1250 755110971 755110987
    0x3070609030909051801110a0c020d0203070302060301032102030301050d120207091d010e191e0c06080a0b0d02030d030c05040306110304032a0209090f15010f1a0f 72
    0x240d044a60fa2244905918100c00c00c200c1d0b188058010620b14003c0d40204403a40542c00503100501403074842c013000940403a10000182030440d400d003440c9000400f00c1d98015900d40c0045d9990340300f60002c8034480c0f04400d010030070700d0102c480e052a6140b030307002031030541d03040a002c160011409800900501120b4807100b5415000388919405450314030b00910034030001c10309041c69641c01d02c02c5090550b01c0e011100d80002c0e40803a90010340410103000d0030000019031201040c14461407600030103181c00680e6000012079240c00800200899110740000e850322a40302c034101c60194015501130040700103060700507a0041141780941c0c0d017600300086c0c3c1d446482c83c01ca075540115000200564038002e0b0880f005210400a144514420790702c624500c00f01d880c20300f10040d00e01c1c800307148603100824803000628010b003203c1d500503116004c03180c1080c00110f0061034004810f510528156030100103101c02520310406901500312003c090510035202a450800f03803140720440c00501001240d0a5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 755113471 1250 755112221 755112227
    0x90409031b140c0108010e0c0c120a081e040c030b15030a080904061208040608150301050f0403140a171b07030201141b120601091703031f05030307060903 68
    0x129181140d19880340800107601d40307601d03000781100140b00c0d02d1051101810307140d88204505410384a2000484446499440c81080260007000d104442030082030102d141500c00c18000d05030101480d40c4070140750070203441000420580c4500d13046080307620130401011498441d40042100d900c00a50021599441e51303500302d00e01c101c4500742c1d00d4042e0700321060030700c00c2000c05800609000c43c1c0411105544041c25800b800c03c46d036004008140a21040010074020b08141d54090040401d01d100301414000003802c44204403032001410706940140418142e00c040313152030501031104080e20f00120103c02401001503101c03000c01c101d5522002540000662101281000060300c0b01134907002240390283c06480c804a40701492040100020003a8a4407112300c189800d020315458a0442c0f0007600084801004200505000e40101c00282015031003002c0c9040005000140da01e900b4820f40c0e114400b10308a0302c80b8600b0030001030920a95502000720b50165521080c0041e050186203415 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 755114721 1250 755113471 755113487
    0x601020a20270c0a120b031f090b060312040e15031f05090304031101030209040e100b030105090c0117100b0a110d0206040302070501030b2e020601150509040903 71
    0xa604000c02c86070507021030411004030b200244040e80780310303116515a07030544500d008030441c400029441c04400155401c1983c00242e55280103800e0b900c00350b60040d054903402d40500e170101c0c682c41d0359180324414064a05140c64000c18100d0141090303260750100d00e9254003031405000700140021000c15920000c0040c60082c40c800a000d0300c10000c40c5624000501d600d01c501c40d06000c1c02c0c078002506d00680801282c0c00d980e80552144002180e10740110001c0d04040209500aa43d900c02c0390742d01101040201c0d10b420304800089000c4006030300381401e4500142c2480d013264000d402d4071400d0b03a04080122a648100c2c101c009c1c0660390054607213244813580e44446101d003400180ca02d0181d91010000d04070f2003107201100c410300011441240d4555003204d001d00103070004001404070750311039001000c1d000d070004c11040c0030210f1700441200694441420020314803460300f43c00401901407186a004240c01d01c0c4001e9102c0010707801500780d1050400042c481c80d82c40c101001014040e03204 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 755115971 1250 755114721 755114783
    0x1c0b300f1203040c08060606040e130606090605130e0a060b1305040b010f120b0705090a0b0319060b130905040c0815040302120c0309060d020c1f060e0601020a 70
    0x1140e440c0750311841c0494469000362401d4618280700302c0041502c1310700040715401282c0c00307000350303203054a4489000d9207040040c00a8001502c00e080100100b543e50246c2000b07450716280004425107818104070034607040f21420070140781441416250b8890104e842c0c5400ca81052000c1000c0b1081400100e0060b02e08102d0700e074241c5080c06000a0010042d4000d040e00c1c180e000700380195407500740000b6501603091004080d100c0040000f049280707d00301400c41c40d18041c08400c200f0381c403100590420703001150803138582c2002300d0008480c40550b0107201d00500800c1446860b0100c01c0c1e4050412104034003030040e8040c4c407840070504020b41164960010b15148082e04c104040401d441e080e5654140ea0550041c800d40c0107418919060324210b6044207131a90003149003880d120144a11600208071280c4c1240c0d080c840c008202c04103010744190000e42c5054810600e0340c1349110000c5404035004100340705094010083c4a9800007480440241c000d03c3c200c1d0392060119020740300f40d171420342d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 755117221 1250 755115971 755115973
    0x20f041401090b0702030a17040b0418060f0501020709050601051306021b0f0f1507080c0616021209010302070f060606020a02010e030f031606060b1c0b300f 69
    0x240020645403021042114400903a6814003096031041440664043c00d9400380d4190000e64514002070b0007042444044501c807824541050790303a0510025503009580526260b20107545554891000380c810361002d0402c1e070300104805030400d00001d6858055000c0e090449a8a1001c01c409a01440035110354283d9295a0144141c541c1002500c49501c5445803001d590010880b9400e494242000400e141000e080072000c50104001c101d801121440704500c0034408001c0380001c0f804480040c0f682d0b07200310340200940d0500c40d00e242c10030442034a51000b15041031b0a10401c000688045421071602440d015803100c5050605034900e4001c203000030402c614010000403400d4003c0340c0011500c0c001d807142131034003080c00c0c20b041e01d5003840c00d1042c006410801100e00100c0d0b4410303200c51064018507000a03c02e4640000010b55440100081d12200c503e12404071940070a0165003c2c011043e104c501c4884c100d06980e02080c200700c680300411546003400e010034010f0800c9458222f02240c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 755118471 1250 755117221 755117227
    0x1103040b0a050c150921120906510405070201050709080606031c120c090905070219080d02160c0f05120d03051503060906090606010c110d030201020f 66
    0x1801401c00c0e40140d000780f00c02e0050a40303e86140c2c16980d501842070007040003074003055081da050000740802a00420078112030600c035030103c01c000325a079184201280030040000e81000035480c40c00e010151140d5985040080e011221803944c80300a90b40b15a044041031000b000c01c4821910002d90640659041454071080203031003a230541155004410a8072481141501c592542e911514101ca841da01503110501c02254800c6240c2403062401217440c110154904100042069030050080c08000907440d1500313102d07403100e9220b00c0390070240a000511505264280034216a800007401a2501101154a076184041d03a0102c41250040c2c0e841e01c02c00800328940700c2c20b4901180184c0800d04a4000081000d00f071030410808039001c610001c100302240c800040700500030092482c841150220003501d210b84007000200d024030b1960024007080d207040701c3c000303140110041c41e050401040f204200c000c14005100300b031119509407800000144c880c00c059000e03124102d81c41c2d1440e0400 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 755119721 1250 755118471 755118487
    0x30b06150c0105011e050d02131d07140109080a1103010204081504060f0e1207020d060c0e011215050d1a070f08090109032f01020c030d060e0103121103040b 69
    0x1988030f181641e40f8644107503034041180007540003410042c018039411036200100080945005180c0080e40050440302243c0c18a0442c80248508507000c00d0422a50016a040c07052840208030151210801c2c0b86c00c1c020f40d45400c920079614071001a000e0641c1144458441040d2020340440f000350440d00c049404401240d43d04801c1400d00300c034140c448a2616181e007803a04260300a8020074100040105002030b41810b101c4a00c0d441003a080346c1c44410900c204c00021740501411030440c51940f0b6010b030030b4010f24009080000c130300c01102c845c07900d40201c0720340164030b032a1610180e410a443c0444034203100e10f80780c484078642e840d07115000e00d105020001d8080c0c2c050132543c01c0b490700b955105a5601c42e8201142a206aa100200490b1880c280480e8181242100d10100d1141006a04c854a80d928210f803ca80c04061124426000025590708210460045500420795a10020070075031543d150940c602034001303895001c00000e88020020541c042040d580507045241e0380942e81c1c00c070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 755120971 1250 755119721 755119723
    0x403021203190e06250206220b0315010f120c0914120304180212090c03070e150105070305092116050d030c17120403031b0915120e030306030606100207030b06150c 72
    0x102c00310800c203100036001150681424080c2c80c05a07603400c12f80114042107000540d200c6200d90041410015002d040101100c05401940100310300f94807040c0103103052502400b65861000c18003400b542e442e00c03540b08039030000801c4030100c6400c440b8103016000204079401c0648101046000c9030040d500500440540101c0c110000c1d48049003200c0603541d45084240410b03104690080b040382e40418411102e50090000380482d0303129240051600152000051030007801c0e052504000c00304002d24030114904002a00218601008102d07031f6600c0d204c0040c3c18405803600040421125481160401041030101002c144900300c80f15111030b91854103029400080324250002400c081d150629a0140014034030151490764070783d00001d0910a0b245034640e01022100100310700d0405a82068880384640341080981c0400f03143c2e0307420030004140c82c08002600c058421820070391090300c100e1b000141c0e07d0072030364010308410403555a0070018261601440e1241d05880c00082c0c4001002c074 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 755122221 1250 755120971 755121007
    0x203060f06030a230f070c061b3b040207140a0b0403080114030a1407180e240a0902030a1403030403090608010b0a050f0403021203190e06250206 64
    0x240861440094540c00c458804101010360b00c6400c400700701710203d00000e100b40c072444030700d0380180c0c004105105949561000303003e01c00d052100003a030300200070b20216030109000f490722500c110700c0045211001c20105d0030700b1001d940c90740304a500060355403c011a000c000f0075006980401c0c2c49502115043c100c2070104202d500b140000e040d2000440c030700d14104110810780e0009001400100b8250341d40e6141d020700440a109140f1903414000f40c51250303010301039200e000c048404100b440d1200b4140d450300c1e5a00040070400c0900840c2c00b082c08916500319035001c0804c40021480c1c109500209082120300a0003514411322030403107941d08440040194041d5100e07a83d000c10b92030750780000710b038406401c0c02030b000854030820018482d5481003010706488217000510a1900340d0325070000c1e4801c01041c00120454102141c00102d082c90300c08101085c1c1541d04100310350714850000160984614046c40078a0b82c411400508840103c03150341c0b43c4107a02038800e13039650b880c90384401e01200c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 755123471 1250 755122221 755122241
    0x100503070b071407030b04080d060906061110142d040f02130c02030912150108071802041409040f14100c050c0c090402030a0c0603020a09080a150203060f06030a 71
    0x1040c81c04000c003c0c0030002600d50031a50400107a4500d9265a96400700c1d079030000340c2c07038000f4540702c1c28041002001c611600005182513111203100d10344864409080080d00c80700240780d5450302040141c241c54005030a580180b0094407008404010301d040c0b0071848102860031a031565080800c01040344060140c52604e000311940900c4041d49c1c4041010740c0d84003401d81005800500c00d503403007410140c3c007030544141881c054920404118001c141c4038007099000f180d55a11810003007241c0c41c1c002084406900103290198901401d20000303940001d060302165020300b05810014040c800800b80c04a48151300005509290400f4000a6a41d01c0c030700d11035110140c986441c1c2d00c0454010800c40302124404809048480c2c0500f04101408200620913601401803840701c00000389407041120140031952401603c0300040c1d10001d1610308640c01400b40e95102d114080d0201e50340c4000c1040c2c02d0070300e00c005607a035541d210229a81c0c404000300c070350b080500401841204c45240d04a04000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 755124721 1250 755123471 755123483
    0xc0106060f09050303090d080c07081b04060608040503030105370312090518060102070509040606030b1303081801021b0102030a0b06040b07060c03020f0403110f0306070203090108100503070b07 85
    0x480e103c2d4101903c070322680c11495070100484000d0800550314401522030010800b0907621786644d40ca514034140808211000d2060100000c140c00626180c41004050142031400c68001d02e0a0350b0350582da40f10602030240306074a03408449400d200b40c0800680c04860b681407522101c034050408801e100420b0108030750f4005101d580b6250144600c10403c1104c5000706a5543e900c00c0d03114a00c0b0000016011a04600641e900400e980d220218100e020301c0c803803080040c0386440c60034074041010b40030308510080004240c03014003283c0d1100b580b5404c01c02000955005181d00e10031140203201d0020348581030852151600045001035016521400c0c20303803402d01c1000240170800c0740038030540c001c0a4005401344400e00120f0b0440e40700c0a804a11420010325098000384103941a8100b58400c54140341c0c810880c00141c02c0858101455900030740c01005a410f01e03040183d01c9001b8449000d0400c1981d000140e00d14408440050043c00c01070150b42000351200a000c000d03904c4250180c40c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 755125971 1250 755124721 755124737
    0x516180509030a0905041d15010906060e06192304030b09120a0804081201091a0d080a0c08090a0801060e0106050a05160f021005090f0a0f0303080c0c0106060f 70
    0x20001d0301008803100d0000c15600e01e0503242c180030400c03006019800c1130030540740b1401690001c1104c10024048000e144580d8100c240d850441d0040507280540c20100c200204140c404103240c0b50202a200021040c3c2c440130750f99030140300211074480d4a9081007464180551403080324100000050045d20f0294042083c40d6680c40d802507690440c40030001520b910401140480f142b0920113980c00034850307503145280010384a04101c2d0240d0a8000c0720009555109c00d90f00c40b20503020380c615142d000d0b00c0600c01500c0310f072111203c50040c40c4100060000303d4614100304403e0342d040310064480188071502c49911141d025000384240d01030710410525080010035032034000d8080c0c817021261550341c0c41c42d01a80c03254503211072444440440e50010164a510016614900380b1516810a6a01c0e01c2d03d0390f003c0d60400c2620540c0d01ba0043c0681d0035071400340502d030054655001500d40508003000c5986450140b00640d109070400e2404c95480c10703a000c243c041d4440c5000b84030702525510005 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 755127221 1250 755125971 755125981
    0x1e0e01060b040b0310091e1413020906040f140619080615010c051b0907030603110405040201140310050910180e100c0e120a0f0f05161805 61
    0x400c850290003080d0410307200380402c008140d1040001c41e40102ea002c00048415914039040d020380d180c000c101c2c43c00580c40010584001700902c601410135040841020241c100404e0015a0003d03ca40103405000e140c4001085622640c00800c2100d690034410407402c951180751401210301034030304512900e100e0b50440d00545038403040c9002c1d41e0710103024128940f24890110450b000303002c0c926040c041d40c01c0c042004910280481072000d4000303401c4991b440c5900b02001480d11f801400721061500c0d1041c288003040003205131031107000050b28000780c151951f00040e2100141801d1281404400200300035001036642a0141190310654800b41e00c2e845180b2281d1203d0840d0185c44885d0b41d07806003501d48410307182c01c4100d100403000243d610031070721a00f11800340c41005481c0400f05d042d81d54580b0090504e00840b0014010000c060030904a041e55410f40922185d040508400000100f40d03051000074051800c0c40a107400098180d26580c006078a444071000301400c1c0d0540c50840021 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 755128471 1250 755127221 755127223
    0xb061c06060221070507150302121b070f020414100305010c031103071808070b0c1903090506130504061d0f0702120a0309050d0c260301060e04020705011e0e 69
    0x200310021220f030034108442140d0061903040d0080042541e0500c00c0391800500200314840e02c0b003050900d0790b000b44e940d00885a02500801d801b51010b0100c040704002580300f94040e805a40136a50b10075203d850740109030001601910102160000011181c010301c01a0011750001d0340840b40300340c0c003d010034080580150204e600520541400f00303410400640200e1040140085030000d01c1d051144503612080e11503e440401e030800044024001241031900c03000700f1142159641452a580c2030070011743d00280f000100d44641c500602000c01d0f10f130b03d01020100184040e101c0a0f03c1089180d07030f2041c0300c5006441c00f99522100105009c0416403c0c10b01004c65803103075100e5002001003ca4a80c18902c0551000b4100c50030541e47d031120800180c01030100300711601c12560340e00c915040c28107007643c400f00c44e60034647c0700c0c0d0929529801017241900560f811568581411136880c1c07c0d10700810003922944000070400d502e001c039142150000581e407154031240c8136004002d18264002a9 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 755129721 1250 755128471 755128483
    0x51302070b0115020f1002090a0807050310051815071b021815030102030f0106020601080601080c06070206070501050405150603010204050604052806020307030810060c0609060b061c060602 83
    0x1030180081400140440300f120084190802400c0c4111100115090001c0c0d0520816050711905284c0000f0b100d000c6140600d900c0b00644280c3d0b003e485014030b0900001d542d1024484152591600d44000484030f1044030904004050b5000a0300d55200e00b044001c4503002d011904040030450140d80c95108408516000c1906a4040e007112110f003d0000360f0640d005c0010b044100c4d520030031030b203024141c4003800a10b00a070030505070b41e21203504084000c1e06001d0140c1240900e94070510042100d11000640b8030724808041d180d040d56840c0d03c0c0041204c511944001070002e60070720f014003041040000d0205600c1202d14403a501e980c6a25080500340d2080e4890964040414031060106280080c0c800d81d00b1505000c83c0e06100c9560a6080c05603402070b032091002da0008076084062641101079150710040042c00841c0040c10003102030089840d0050151119540d40b040208200361030748020040d1600a08880e02c92a4150481c0640903041d4100181e103428443d000581d0340c000100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 755130971 1250 755129721 755129723
    0x1403190f0f0b190209010e0d02240403052e0c0905040c080609070504230a030605181204060f0e0102150a0b011218080f13170d080f07050a0509040c0905130207 70
    0x11f100c00d9000c0f0352003040300b4a020311030203a80c000c4641d0380000c4002c9046031040596a240700c44a9169451410041c1c00d141c04d840040903240301d8014042a440e010031403282800314840c10019261142c6482102c100d0940c0d00500d80045c9400e10b039182e00c64000c0d01407481901c0407140c40c1c80c9951084e10466050056100d0302201c81e8a032031000d540c05024a520010b910006003521910a40e2502c401040d110190703101c00c5109910012240c06250030705c8940b2507072159034203a44ca1b0614103074004004d00441030601080000b41c40d20603403942c0c402d000306682c28030302071032080490500303000c60402000c4040b2440e020030140c00d07020190124034080c42d000403000801c400e40581c429101c82c0e0035036120b102800700600041201106140c110743c0740388040e0492094500100001510551800100391048070a11800e181040840305030b050f91607610205070714025032544c401e01015a2940100c0ba021548142007098480c07081d503002c00e20008503241125940180ea1549154030f08911603010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 755132221 1250 755130971 755130977
    0xa05040b06010e030d0f0c120305061306080606120109050703051c11070b0f0f070b1806090a02040b01020106030203190501111606020f0c0a0f020a1403190f0f0b19020901 75
    0xb45c0500c91405032500e0002400182044c8141c5071041d552039154103280188030000c00e80d600180281420b00c0d078101c41303441031240d000300495401d090311a03684d6100102950f11480505080808450007908809075851344035084130742441c4c4a207082d40d203c5502010112103083c0e120138000c8034610580b0714043d12020741c400b80406a00b4109041555482041804c80b490402c0111902030420304004080060140c0030f103040703d08251006100e0050510070302d4149920079004e00c100c40b0707404035401d11040c0d8100c400194400005006034050102c0d540080d5050080d810000f080f07807242459a2607440c8140d008004200d0412100801360203940448991a50700c0b401a4000a1440d8010080300902c0401e076800c08520350704d06440c000107100200c40c3e851002c504503045080ca33940003c00b03028075130131440c9204010400f103941ca071101d2840541c03030380e0034005c117000740030104c415800c2090700304c1c0780848a02500c0c10451040c8405549201401c040c0d1022407510983c2031003650b401d100140c2d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 755133471 1250 755132221 755132233
    0x6060409030518061204051f0603030f0e040b03030403051c03060305280602032701110a031d070b0310080607050f030a1d010c110102070803011e09050a05040b06010e03 74
    0x2c9244810025100f4003190495401c001c81158034001019052281c2c0c819001001d00060703504000c0804001030310b0708607140b801c11201b800040d0700294034000c020414030b0803100202e00390300010050500f150906805000000e001720034010041802c51200c04c079011030a424041b12b0b2030032801c49041c1d00c006466500819200390144c4070f0390600c8425950311803103410f0014925110765003242e00039030300b030600440c24202c03038503500c048400300c000400520b01c001c204140340c3c800740381d610744510340c112020180d80d40c41000301d8040a00481e0301159021040b110910740b9655241a43d074000d03245c2c1c9007065480711001030904800103500d4400e842941d10070b81850b0448904040035040030b40351103c070070307240e90070403100041c0c010702d104100348204000308010910a0011303200c0301510848149036401040b41501041401040382d046034130450114842c0928154030143e2010f95030041041c0504113001e1018040207500000d01903801401c0d4001c40362a040019031711801d102800700c0e0160040c6e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 755134721 1250 755133471 755133487
    0x904050c04030f080d0f0218030c09040b01090b031629070f0305031801050f010924051210051f05221808030a1b0804170f0d02030f0108060604090305 66
    0x4c0300c0902100321300713401e001c240101e000c2c3d965403d9801c5081d5002c5080360081448803507107002c001e010401442a1405010340c201600c507603810304030502034a12125100c2c2c045405070384040011604000740200c4560080d5201c0d00714080144503500502030340380054014001081429044034819a4880328074800100982d4040d541a080201a82e0030700c003074059900d102907400c1c054140706051302400803d4a604140c0000c04540d100d00c185080040f02240c042c2c0d5021800203c482a07500448a0200d4034000c80362a0b4604920520103100050401e8180321620390021070345000744003085601c800301c6441d9005c0c4000415135100711286000c40c000c0c504401078240e4080800c40349500c81c007600012840d105c0c0800d07640280d03040740140390b541214207034503044402c0b00b108140041c5006156420141c80d013144260100c0248500000002207810b1504184021620064180e100640d224640540c408606880034450002d550003040c0001c1d0305850030b482175905895042e1605410a204 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 755135971 1250 755134721 755134733
    0x10090e01090219111911041d0118050c130603150b040f110901080907210c0e07081605090a0909030f0e011b0c030b0c0703030b060301061202090112020f0904050c04030f 74
    0xe14401e50310401c100c12840d0391b50325980118a06403800350740794644214038100da2402c4510003100c5000c603e070321111140009601040d1540c20420880700e0080c19100390340c200c801020198801004201c0d81200105454016000010200c004503810094010100d010605854402d46003208003d41002880100e60261004580243c0410111081944c82d04001c401205500000f04c1054400ba0907420410200c4880c2c10090b04c1c0d480300307401003802c0c40c501c041d05980c00030302800c0c40c0c034030303800c11004540d48214141d0300820b0006020790380c03440d62484060020641c2d000c094000800c540000c3c013100c1c0c02207840302c08140040c0c1d55600c0e070304103442520f100d051710503c04892055045200101040c07130030f01c402c0e00a0100062085c0d03166050300d006401c484804410310700030042070004010498002031070300c414003041000566a001100010fd5100704400b085911451000c9a1244640e9841d13014285032070742920b080149440e030407251a200d01991000800ca90580c1c80e642c400640 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 755137221 1250 755135971 755136013
    0x1803020a1a0c1b0a05102004030c06081302030607050c010e060c0301140103320106020118380108010b010309020303040b1e0424030b010e10090e0109021911 69
    0x4070340c800f51541502c040e038482c6c2c1840986c10590300e1140d02c43c0351848940807042040e0941c00c1c0d000507210303c0e2620799584c5a00b9010184140d4040c410340e000040c00c0312109c500f40c20301841d0b000301a50054542290050b00701d4200c6c020f42c1d9090340c80d01085000f41440040c0c07681c000c500702c4901c141184c3c030b04503100148e02000b03c4a44d0405894050808460021031400511003064800f100084291451071a41c1a04140e00c91021a81011110310213041c410542c00d6a03144c02620701c901c3c0d80c44221858100c1f91400c85406c002d002d001c082600c2032503c3d80c034024142d0b502d0a0081c00480800d000440039507042600280d8550030403c0104818000c9038014080c20601c0300c03e2861000c1501522403064000d54445c400e50448004d20229111003080d00722032611181c2010040c000c0408002030a01e80b440b08400e00a041c614081c103500c5000700a464020040c0d0091081250313102c02454010750804106080b0f034200d003503520810b240c000c1495249001f0000014210f1f00041900092079030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 755138471 1250 755137221 755137267
    0x10902150309150f0a0b06030f04032a0501090b01140609060c0c030706020f2a043c050c0f0a03021303080c030712031a01050c011803020a1a0c 63
    0x84030301d0032210710b02110560382c0c0e40318060fa0142c405003850071001520551b240340742c6191080c0400c008000e203200e650302d4401d0b00540c040c507003400c4446040729450001c0a40381d400c2421500f8034010003080240540040d4025403084a00c001c81d43d0341c0752103020400f00b001c44c2040d4401c200348841c84050400c6006007200d10340340c000b1a004540b2480c0842d05043c11902708100503008804900d04040040000c0f40480552601b5240420026008511003052098040380b15985a05080c1d07501000111100d0120507800544400740c0742c4c041840c0441241030307021050305414030000a07050f01803c01502c05e0302101260440ca4518404001c0340203500c0825a445043e14131080840400d00b50009030044000c040000c41c0d039071001c0d0800c0000340300d4094544c0d0406003403010b00e07861180d5260365800341c280c0070708005442e01c50129400d03015103d02076420000c44442c014400074182d000803280b4809000d8080fa050120070400ca1204001088401d903402e10300800114080002400a83c0c001c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 755139721 1250 755138471 755138473
    0xa020906030c0a08061b1e1602090a15051e19180504050f060c09060903070b0c0a02091f060e030f1501080d1803020d0c12060507030e010902150309 65
    0x140c0c0164000800c05030b50703130304140312a5004508010024442400365200d044104000718108450308919600091031028102002039012a482c0c1d040c0d59961042410141e0091600c481c0d803500c500008010700d0749490000c14440090030015803030622200300449181040140340b00c6001500074416000103002001c540f10090030702c000340c128048040c51000303c81c014030120781030a01381801482e112464200301a10340184c0f06203e000da1000c001c84128040c26100c05841d0080000041c0c2407040c554000c0c0c1a9003400124010405008100700c102240300710396001c0341b912507884a402140010b500c0e12078183c808882800050b0282d0b080948a041c01000c84582d60241a2004d04045074444407214462815006010384001800303801c00900316807500a603d01c44011091800041c1803202074090003403500032109002c9240f40300c80141403201c06c001010b17040342c9840401400100d5090002034075100680c19042810f0245400c52a0000d20405101910100d1071850383d1000c0c10074089 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 755140971 1250 755139721 755139733
    0x617072105011202090609090c0111010f0f06090c090308071502040b0703020c090702030f0f0d0b12060a06050a05030309040b040f060303081e07021903032711040507020a02090603 79
    0x1030005005460180003080011000f6007020f1052028119025061a00c90500700781081811a80000c13101d844103809d00e403802600c04511062801081c0824000544e54100a50410785411b142c202d80304580010008025000440d0700c100c80c0716006000080c4850010042c40700412010880d00118480d5030744014035160b41c480e003200d0a40d0002104030003603000080c1a80c210f240c2004036a521403800e001851134148507407110181da100d40d0604440642010400e41500c102582c0804404907016202c030455902004140ba41c82000301c2e540c003400c5041070400704090900d56482c4049070030240086040c44003020401c006020f200c0c80341e07034019560310707402c0000b034075103001d1400154003e440301e4402d41004290320f2100014003030110018908038041c0016154000394240d200981c900001c20491110f00c2c04401501070301002850000360400b203120096900c1110100440c810b414214900c00d5410520040d03842c21039034034000d60049090f9030094148110401d40c4080000c083d605 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 755142221 1250 755140971 755141027
    0xc090412051306030518120904020c0c1909050123040c03290312090d0f030216030809010f0207060801090c051903050f2a0d1b0305060307061707 64
    0xb030340840e8807010000780c5950a1001000c48120044204840d02d0f0203040108944000503403a4402c4040e0b80d805160300003141d004003002480184141035000b402e404860b0090032055501c2a0b09004001c0100d1400e00001002c03d10200c00c03018044505100703480311a0000200402010607442030b40606480713180000790b900340b20700940306000750385200ca0010344001007410f160243c000c0744115244403c00c02c0d00207a9544812005101d0780c0013113800070708244c03880c00320304200000c0014108800c0c503910200811100c0c20103426a031000782e071903044103040c802c2c040303a66039110300c103071804655020f00501ca103081503040a40c4601060408501e0103031070001001c00791400c0a080000280d41e503080c4580000c04d22503aa82141465156a07004040095618001c01001d91340300c45003040000c45001c6046250403903651502c103a900300303600c80800240038010300b1044500130312a00440f207012600318000e105016210204043e90350755644e6620094031045d22618010703501d100403240083d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 755143471 1250 755142221 755142247
    0x6160807111c170613020313060513061109090423030c07031b0e010905180303040b09190b0f0411030a03030b1806011205041e0c050a080c09041205 65
    0x30000d80c1c1080303500d500c980c405050050401c00d0b43d078000303180c0007043c4040c001e055440d00302c0c014024016090041e0703242c0303d562050551313140d6000c0c020a2903086c01d08005140d00204503070710300c0034050b80061042d61504450f40a040c46100003003503104000c00003040204601e841078004107861008500841038141e844039107141c01c81e152602e0240c2c440c03030081c4200200c0d013a181e01034015001e020000035003400094254820305008000515580d00000b940c0c005810485104170f070805000e5a070750342858203010300803280894840c0d101340718101c8640b00f810304442c240b04a8a4012031401c40d943c50f020070540181c03602070320070f4032303001d201101141c0a60740c140044481544643c9001601c00c0203007060046650b0860300c042c440090450800000e0390f04002c000340305001c4480c6c002107980d00e601e00041072101540015140041000130107041008055a050039a0411184100304981c1d912542d581e4407415601303242c1224028020600040103035440962040c06801e01c5801e008260a2035 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 755144721 1250 755143471 755143483
    0xb04080606062109241006030e030a050d02040b0c0303040b070831120528050a050a0c060c0e04110315010507030323041115220e011202120616080711 66
    0x107151044030005c1030140c0000040504c01c001c00090605000302e0346842c1e2040d40300d000e42180e0134240301001407a43d503540b070a50304440141a01054007a01c0e200c443d07140d1a035a0300100c0303003100d070820380a011920250150305264032402d00c14490012918181a007000c104490311105054440c0520b00a80000c0012640360000d06680e92180c0d00c03010079030361036000e045150b840b032401d02070030ac4034170b00000f94010100e820fa2222401d00c15560a51450102c440e0380900320050401850410301da07515591058074040880d6044406002c3c103130980c422801c40d03203c00e4499144200720380b6407244080d402100500340150090400007442c0d03110303003981245214290202c0e00c1808551042004204032814590320000084c0d4140c0c1d110b05030b80784007020318070130716044007000345a0704102c1030f0041058100c00c025010b00d41d0702c15119695604150045660940200e114004c01c10501641120014201d4070408401d0740c503460751b003061901a214910081c1880c0c0411090492405e00c1e64410441 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 755145971 1250 755144721 755144773
    0xa030209030a0609020102060106050a020a0b130f110102013b030c0303090105011505072409020d0f0c0815060108040309081606020f030c071406040e010b04080606062109 75
    0x800c4c44140b40c8002810b00d98160400030500c4000d108103602e040c0d0010b01084051b511144101c0151600d00c2c1650707001c88500001004202030881620803c020ba0b10031413009603082e00203014004400d0b13070904415061140301c80d40064000d251700040c8070001070083c50b40a4070740640380340c0110b2501d80d070b055900807200001260f44a400420142c448810040c40d80012840c205003006c1c0180d440990b28181180104402c1310f030881c0005407074116034040c80140da030090401c84005c4103880c00c1080c0702d8501a040e100c0f12035102c400108036a0201c0c1007030203103282c0e0710000f4841c0e0751800155010680a0825803c000341b01d980451940e60030001850800340700250391402c64078010703000b480c254a1140003500303500103000c81c035044080012043c06603480c0b014148201010704000c50620b005961104161076841300c0002180b416510091040d58450400d030360882d507581092021a20a0074209009149005d40c1412007003080007015070841c2e12581610481c038040b0159580b10181444d03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 755147221 1250 755145971 755145983
    0x5041d041a1312080c0901080702070521010b04021615110c100507232218060506030402010903020f0406030204110c011a09070f090f0f09051b0f0a030209030a 70
    0xb0b410020300c11005000110303a0354904d030041440c58404a80003480c040c0600c2241400f00184c041182d00e8020301a1601500300542404107030304001e4400a101e0040c0d140000041d4070741640f240031400c15000304d41d002d04001c0713021041843c9a56412a0b039449000c55415030030340d0f0b0b00c6100c5100600d80028000b400700e5400404c0c074020350034600b030304032503014100d1014442100c403040389007070701d55110943c400c001600e0107481d04181103031103000c0511015400c800d00c40d00400420011410180d8016a9034008030401c0016191b4050003d1440180c601a01207a0b829504200518200e6840c6400d03140251012032116681d5000c10141c440300c008156154001168501210720244501e00d80c00c4c1740d00c1440d40000c04540c01040c0d00c0d010180407502045407a920102095005184500c000c00e034141080d00b40564607000b0b10020700060062003116410400171410801c0e107224140c0110b444260020314080310306070a00c1241d8040b1440c8424503409002422082d9400d1104040c114041c407 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 755148471 1250 755147221 755147251
    0x2060412050c070f061d09060d020d0206040e040c061706270702030a260c07020102030408120324130f0f061403060702030301081504020d240c05041d041a 68
    0x8080071b0003ea20060030580d1019500340101c01d59900da6000d2034021009a8865202c001180085282c890b50000065081000002c0000da4001001d5003240700320300903100b00440d59120380b000c44240d0b040526011000c102c880208900e80341c559102e04005000d503140101c140700c0f08180c9071985408842d00c8000d0b80010a00716100d940182c01c89942460311140510648508001900c0c4030030302500040c0003000102c2e0100459008004441c0a00a00390032150411b102d488405075552044401014142410310b0700d521020340d0406040d0003a2004040c001c251105c2c5000600500d01240100a0709454900240700302507688034840180100c0c0900440905549007410b16011010b00801c00319070081004000c07112001c282d0980c500c49448011456455174000140c000400950140007425102981840409540e01914203100100c40c1800b640e42d14001c240c600c1c1c0178622900e8980c0103134a84aa900c010180031107903000b8414865403421100840389884401003c4031060560100b007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 755149721 1250 755148471 755148479
    0x70b150406090c020303040b0720070305100903020615031c0e0a0608010b0706020f0d0c020a03090e10030b0414120d1b0c06090302010b060c07050f03060702060412050c070f 76
    0x290207408058051041d007840b41140e2080021360340d2100400c09890304440c1c1e40400c02c11445101480940c0002c0d512141000b00039074200e42e1240711a02c8210340c0381c03040d82d0761451302c40100d004a8510f2600350300038080aa482824123225814880001541800744e5812618030000e0341c1e01032007004a40740c0e00e082d501e006030401c1c0400e0950b13a801c400244216440100400c0002208456803030358800400350712002284841c144500031802100101c2c4d051881d50704050350700089d14801c81e4000d584030189142c0d40c10171090320031002d56802c0361240001d1070a1003c90101007000740c0151080e600000c0000060000301c1c00d110312140c6810340c41d04002031070b400c642c2e02400341c2d0344c51a00500e1545030100d814103014140520013600108542d07140c41c1000c040c91300039481010f03e200050402c0d03a60b00282c07081580c55600d03a01649110f40113280e80b40c031003410001403840c8142004e030010482500c507504c03411030115030100080100201089400c0080d0002e0041e800180190403c3e80012410 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 755150971 1250 755149721 755149729
    0x31b23070b040e1911070b2401050f07140a03020c0109090c0206190b0d1b0801060b0a05090d0c0e100806040302071806120b06030d02120406030b06070b15 68
    0x90390055103a8038050005000c040d09031440e050b00110385240c210403000c0b21880c40e8002d410f021020a0701c2c0070021840c082880b8140c0d00d4140f08c0c2510400303000e0301a4006c50000c2c0000011031200d030000b0828024100c00060500083c001d00f4047ca04605c01c0c0c1c14084070440c9080180ca030100c1c0180c10826010025507049050030b0b01401000b8003d22010f03007040002907071880002c1409100c28440b451740d0020b43c40c10303800187c00c200054420003000030181400c4400c0881070b004030445115009000888000601c103804c21354000501040ca4a0000841200c80741c020b11442e5500c00710400c81c1c1000250202c02802c01098551b100c0346030781c9072140404800b10066404149140c2100007000002503001c00d2000039501525034400038040300305600c000410003500080c0c400c43d45004400c003401070288086100d07038400c034101d400e0301c050600102c0e01d9021194042d480010f050200f40102c9000340c10541ca02c0c00c01500f0a402c103a200d0321180030000c020b0b500302c40040120398102403d414 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 755152221 1250 755150971 755150983
    0x1503080d0209120607023a0903030e01110c0d05011104060e0f0f0d03030e01060b160b07140d1e02030a020315090108150a090206121f12031b23 63
    0x21980034010340d2a20325001b80d2544121a020f00301a1005410110101ca4400840490065080c0500b4501400a10152103a00d05010541c085185128104125841240b000a0340c0c0c0c8050050200030008400b400641400c00b50202c5180d507ea04540000394146005400141000c0d5079841c0c030a2201d0040c0502500408485800f680c604103210009849401203611043d034149400140b040c0c40d0038201d40100300980014004160000305102c1061500e8040b40441c0e00a1291102d11b4503842000e445025071074010244c104010710059000b80000c0d0f001c020620380c411114038800d408141018105d83c001c5a070f51058130b5011003030142c03904003005000c009203800e4506504950400c2c81e6140d488100101c2d44604400d190000b070103402e2150000079805a002e407009441e102d480707120807150101112141c0c01303101e0030183c03082081c1c2440415012078110708145002e444090300c046420049800c6050070070080c040700c40d400140e03000c042030842038a8002e0014908070400c0360500303041c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 755153471 1250 755152221 755152249
    0x101109010c140a1223040506070c03060c050a03050a200d060b0a0c110f011202090a0503030a0921020d0b0c1e0301050a23010c0f080703030b0909150a1503080d0209 72
    0x40c52581c0218418503066046030b05441e8100d03248c94840006240c0701d40e0020441d00014001c038244400000c0658001d005426a5038040d1400d01c425605e0302c000740200c5180c1c1417001c10031758281d0050750b0340e2102d520080c00c1140c600100410a03503110600c0200b154001418180050382080d40c110510030400c40c0228071074021a145035002d200782c2c0000b0015408060030607082036000800403041e940c3c0406000040c1400b4007074a0319820030385c0000e400c9178040c1c4100440001c40450448004151706c00d840b102c1d6034000c00808181c603040d22184e8504400401480d02040204403100c0c00f84503c0c200c00c0c8104c02c4e80c44240356030751304140c140700884c18079500c60021100300940c4401c0d40018414800040b000a1900841c4101c090421002d039240c5040d01a1060200254090a0662640002d1401035064525210780d031298480203603600880c1d00386003180580b03540415080b40340c680010080c12014036051040984a0b100d4643c01c0e0320035a02c0d00c0340319600041283d05410b043c0a07214100d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 755154721 1250 755153471 755153507
    0x70e0c130b0306011d030c130c0f0c05061603020d0207140708070f120302070b0304030905040b060f0d0e03040810090228030f02060d050117101109010c140a12 70
    0x35043c0500044c10304035124040144001e00d81d200148252070400c400b103007942d00141a190015010034180008041300804e800008089000ea180e05602984042c81e640358042e0081c0410340e20321008400d00005031008004042d02000f40d4588240640042e01030103000d20b444440110060461030300d408110307070000d5410740011008000c111800d200e080d003210002c8007211a05d220b80e00d0201c2c14404203405c40f00000b0004014081415404520b82d015030324103880c104a40800e240402a441c01411201c0b01c2903141044204001d80050300540703c0794205c50110303410180c40740b16881c1070060480c1a00e048603940c00c001401e620348001341d51055460440310b02105080d0507110140543d09001c06400c40b0f038400d40f05411507d032081129207400d81508100115619010000308a681991002416109241000c2c18400c401d100700d440880c4485107179460032041500541e00b0707410703500040c3e0305d000740e500388596819070078009100443d00c20103607503445411110300540424019040d120700 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 755155971 1250 755154721 755154727
    0xe010606050403030c0f0206120901050a050103110616150906050a0509070302010c0c1809110f0f010f0504080601090b01120c0203030408160f03020708120c0a1103070e0c130b 77
    0xc900d4204003210181e03905443c0c05050b1500304c1c2041c0074200035400d4000c5d0012800141000d0b0864540401400790030404e00a0240342ca41849c2d400c190b600a003c086c081c9107140708031001034a0240010448804500c400a103100c6d40b94444504401d03101c9100b4030096140ca602c402086024842e4179405404070404118a05001c5d8900c1c0e61200c50b0f000007414850710403400c4003400706030300e99030000349450450b2031140300b8180003050182c41c0d0007508a61031b5103140e2102e021458000c108a81081e805409001c0c00d00d520801142c080104000c08400c0c081c04020116220600f400200d003e00b02c11980428840010000100748035600a1182c40152401a1410300142c1c044100c0ea00590080b150315200c84680103c0040d40300c0a4100514008080821404041c0c01007000000c9030742c1442034170070b020501e00c0301c909240310324115540d440e0030140895000400e20350204041e0315000d8115810f69488600b51581101e06a030740b11152540410004441e145840b410806000d0316070949003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 755157221 1250 755155971 755155979
    0x10602030d0f060e0103020d1721010608040b0c09040f05041a0906091c2607030c0e150a180905040b0c180d150c051213020102190201020313060203030a0e0106 70
    0x10135200b0601000340b1072440d02c01c0a40500c0807030810a505002d48040e0b03160348500031000c419070600e840d000142c107000f48100003d41c4a0007404514030403038014000c0310140c0d42e10010000c8988c000c10586500c2540d0702d5284161501d0752045d140300b5442040b2110103c890081d9800c0101c4000308240880d0340103a041251050000c6140d11000c9901026050741a0752400142c80704400c0c102c01e0300810403014000803022183c11021405103659031401c0042d040310b184101d81401035164819080f034071141c0c9005484413240700911519000345031040b88001c0d85814101100110750190429913101e109101c107006201c03d2494000881c40401c3d403504101035038805c000c10303c605d016071040060f950020148681030002c41810424a4401c101c20b00501700007501c65080306421842410010b000504140142d442000070039405800074244100a0f00b440090601540d808a0441c04184903a140c423024290301c0c40c010340401d80107984c6070b10304440e0810803142c2088031394119a0620030104 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 755158471 1250 755157221 755157239
    0xa050609010f030e0106150f120b101b021807030b040504020f0f0a09050903041404020903070e0709051c0b0906010e150102070b030c03073e15010602030d0f06 70
    0xb0a8011281000301c0d40b6071003080107038014a070540c4400d0300f0304407010600b004958400b20700c1c55256084d80700c00310b00c22030380245c0800f100c1c0f203610b00d01e0300a41c0b1a8002d8001c0d6008003810b102842444040b441c9501c400d50104442a6080b0600c1a071428140c040c49000c83e0980148460510155400c004030310740764000400740110300609078010540d207482200281c495401d0f000c040c00b107242d030500450400028492340c030383c0309105a641c5a4610400c01200e031900740229221000002c0c01003107400e041a003c1c4580380d001400700700074040c00410018842e250f552a4641f91141c000039074803080001c0c180510b444100510780c00e4075420080050000c0280d0001d02d54100d0345903442e4a110041e4600180c0c504000341d000b5004508020080050000c1d016009522441690381d80c603c280e400202c0015000f04988100250704810b21004484450807100300e03a4020207800441d18140301c2c007002414440130070303040080140c00000340060848102c0c05141c2c0d40140d202000c01c2154a000185 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 755159721 1250 755158471 755158487
    0x9040c1e0c150e251e050d080a2006100618171905011b0206010605090906130c021015050a031103071d040308011a07020d060e0102180a05060901 64
    0xc4a606903498401079112001041041d02c808001340590f100d411410203400b1810380d0f1031003400d918214442c2e425168040b0b4070304480481d600030b0200751036580b10b0740d51070280d600720500e07410400503040d407603c544907090000112812440c40c040d00c9142000c5e14484070000e865044840be000c240131000b15036030007142d00d290860f600800510340100c201f0580904142c41286800c5966407041201e60901c1010350100c0086c4002da07040ea48021810270f403c0c4c2c2caa8000740b04204c0443c00a000130b03001c40c01c12844242c1c0c0410020100c1050242e031044800c1226041c0c06041f00684c824592260003803024452a4007000001c0d29015407207103400002800b0788001d0100030314102c1107401103d0680c07800c12101d005041c90483c64403c000c0500e00c0380c030414000300c90960014401c03000025005d0049181c03a82046644140c6c50b15040c12902030040705140248100c0310070750384425550b0340d55000e00c040c00e404d0b9a44020310820110420400c5040e034140d4000320f01c03c1c20b08002c2c03100ea0342e81200c10 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 755160971 1250 755159721 755159753
    0x9050103060b1e1c1b02010902030a061a06070317010503030c120706020910020d030b01030b090412300f0c0206180709020315040c03092609040c1e0c 66
    0x4403000e00c400303201511030b42d130040b0112100030a00210307000030b241d130f1503801c1015204440501002c1c64070019208a017a00c00c402d40c06505600426014004510a43c010442d0006054099042100c00d04040780c80b59006035020340c0018510001d5040c01002d07018a6801424110700950070102d12011990b111140c0078160300301150f000a10b90308000c1c040c0c040d0b03140100020710004076240c0003400a5252240d00f0124000240b42c85100040c0790300074480c401c101080580b00c00f90540c1d596032201c1c9503240c07684a10051215041c0381801c210303800c26401000c26056401070f401c16079071420050a80e0415500c071601c06007040c3c080360f801c9500003003081d4080f0b09102180c44030f041c01060fa074145050f40d00001c031024000001c110800c0b17000350b0440d1482c00c0907502008845c0380780004500700c1b1200c0384024007555a00b0406554144c4101c1020465045480c001d40780070356180c006400c40742603290300008903005142400c8034404c0c00c9103e191018540c101604500000c0d0b0750303e200b010804c04 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 755162221 1250 755160971 755160997
    0x3020603150a03060c090f090e0a0f06020d0e011b050f090904030c08070807150e0a080a12050405060a060b0406050409020f12340503180a0507030b0709050103060b 72
    0x4080d690303402c400401980c200004200c01444007000500b4204070703001d050951030800d5000952414103100300d00b00900240d010b4010030030196641c100700741c2c000100344d6045409000e082130040e01803080580c52448200005071440301c50001203010503580094030305001c420b200d41c00300642001c04480c0704200803207000c40151b5440c80c0c181e0b020694448050b001800214200003044400001084014040c0c901c041d00f006196284800351080840822880d82106203030800062003680030700f1809001d401c2800c0000d0760070707103420101c0d54200c070240d48640c460310500a003403103c0c3c41100040d2038901c161500c0e01d4103081c0060450300c1280300b164100345e800a5114003400c8903100b50b40a40602e00c1e90908541080e55801e800d101425130180d94003c0030b0070600c100004080c840e20b41074040d81c1ca402e401d540d110403090344100c1030b010815803a4018000703030303e00140b0140990130185200f410640741c0390804001c0140200b04d645c00c0b4605041c6005010310020401c9403c4c3e40320407070411 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 755163471 1250 755162221 755162251
    0xb1606050a2304031107060908120403260c0d030203012c0403080a093008071d06280e031f0905250806060d020d15060803130305061003020603 63
    0x454125100c072014117a40005006051000ca101035100b41118200e074098022140d0320361009080aa0302e1290f0b2000a01400d10b8804495800c50740390b06048490341252041c0381000e0f24024190300304040d03000004002a400801444041e100c2121200c003031a1041d801c241040c10340c904d02030304010251026041c041d41e64001038082503a5044440200d500110f01032842c5840840985090041015007071004400e801c001385581c840d0340b0341403050009941e019084001003000c03005000b0038150503a00607904100b8484402c103808070002070b101304540701c413001d403000c5240241909414482940310f0342211b0740070021500000e034501494076903c1000284820bc900c2c1c80e030b151116040040380805001c41c1050002c2e8182c0000c14100c0d4002c1040d103407213a5031001001020072203000001e40c0044180b0550000c204922000110300000490014540e501c4114541c81c6803c2125141142e001e00c5805008101c01401100e800025620003041c075181142d00050070741c0402810881c2c2c1d18400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 755164721 1250 755163471 755163473
    0x30105240903100c0f11071e0509010602060f0903030f0a1109040e0d02010e0609060406180b0c04030204060e1b0c0a020604080a06180507090c090b1606050a2304 71
    0x92000c450320200000c04aa40420071401c0fa98050464510280c0100345650300b010302d81030041c20328002400a0f00060801a824050440c4112402e52440c40e00c4200e400804546600d882c26010b0180446400070800d52400d4490741c001c1c410000c21144071900300b4070038004840036181850390411760761000483c40c0006001c00c80a5401514092035202d400c28a4501c1d00d01c1012441e825106940c0c2d000380000d01802144aa5444003a568620036900078000100070410b071742d03c012072282c0d80c8800481045119151030707080030310564040c2c1c1095000902081113242500c15103004001c0b140c01c50030a0701d0311105c00d144031041811100c555140c00a07149032005828056200000e9006000544403501c400c5040d994172282a8200e82407480c084400c806040c00b840381d20704003640f15000b400030074203102c1d02c007024103140717201c58051210002d0003081144c4010017500441c0c10f000d2042e038281c4200e04218003a10405003925015074904007000039000100d4110540a81c0035241a041d00c2e00c032 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 755165971 1250 755164721 755164789
    0xc07030e01210c170703230c04031208090106060309021c15060e090634120c05190806011202030c09040923070f0608100503160317030105 61
    0x50310b4500340000d403a2690003091960804007041c0a0420005100c141d41e9886509608892207500c90403c2c1e1962811601c06203003842000e5580100e2014041c0d04056482c0c0e61a00c50900e00045071012034581800c200da076110034071840000b00004c1c602803154100940124800c0d49400c007094225000b9149290203005440c1c2d0201c85045c01c1c03110420100742d6070612501c402d5429643c100c15400f902022541400041d80300003981039540e9610700103022598031000b103614041004005106e03001785005040800342c402c2546840c2d51743ca602e5900c0d0b045180d000b9403003441c2c0302ca05050100013014481c542c2d903c035140c10510fa84507039006950740c5545100c12800e00424100d00d41c0b142c20000e00f13400300811038072000c00c03441e6840e20885554070700b180400c1c0c90b0b52140c05655009080b40b2020031100c2c1c420a102904041c80c500d4440b000c83c1c5502c0801c5c1003c4c250f842c085920b4104143c20802c200c10020011150100e818805007194141f01c00192041c0003030100611038191300c03013800400c1c40c0e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 755167221 1250 755165971 755166017
    0x60f07050a03090c050a06052101080d120b1503010303021c0f05070201030f180213111603030b0a031209092a021005040c031a09062215020903060c07030e01 69
    0x2001e00d41ca040d1f885400174031b1a030212117240004c856104400e0703030b481514000d15068601c001c026141c89901644104d03185d075000101074611503281c2900102d280c42d90445c1d803e000180043c0d10390b40c0d604500340a40f404059811001c40011081801591036511a0300300a1400151034820381d66425800120040c19004c043c2040e600d1400c1100c141712240012020305062082d100b845003031620122090445003440d500c2005000100b2550680d00441c250000390180300782400103110b0040e4010a40c0e03609150030450f544c4004110000c2d9568120208400070b000c110790500400126140c5916118039400162442a15080c0e014110b540280403100c582240400100f0141c9024100f41c0d0b08610700d440180c42c0459841900100c02280113030040c4508601030041c00701d80c0303481c003100c1e840d0b08400d128041407131100040000014415106911054000700c400342c0c0350f0030f55200301820f019000c0c0003680032560800c02040080d0f004450303490204024201805403090103107030706001c1a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 755168471 1250 755167221 755167229
    0x21060f07020f1209011701030b0a0f020c0303150909010612140304050603130b0f130f0303020f070c0e010b031303050a030b040615030f02040803040308070f0b0906010602060f07050a03090c 83
    0x202664034030343e0410100c0300240400c020309984894803840903842e0103030350f400207010140c821401c4500140401105030401840811601d400524001d50451002d06640081c4d0382c1c0b00f45900f000010045500c0c06c0c0c0304468010314028000c101a030314041201c14908400f1a0040441060405001164400348155801008043d04550342c038501904c1c0aa42100c0558040b00e0404054012969001240500c544030390703a84500400000c00c01e8880280c20082e4400443c2015000c00c00441c102403d03070301074030000b4454140c0c0403440703080c000d41d03112010b0140c1105110940c1841000a40c07030103240e21411054240c20701340d940c0c401100045011f01440046650000d00340500011561583c0d0708030030002509580c00c0084041c0c01d04c0000580c46a4441e4010b0780e4000d0006001141e1160000c0451382e100c1d65002205100a40d1015400182200c0d9081d03280c200e400100001d540600c0070580c0b00d031203142c8491aa16050f280641240601c00440b403c140c2c0daa607100003080300b0401c05101034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 755169721 1250 755168471 755168473
    0x12100906060f0906020d0807030f1512050c030c210705030613120e060406270b12010b090603070c021914030d0c080403020d02060d0e03030621060f07020f 68
    0x14039103840001d410540108082c100083c2e01000001300c1c5480880c090f441412203940e00f8902d0388900b2800c0b0060000c035442c000d28980d4030409000c031003a011710000001c0c02d5492414006000d40e09101c0e0920202d0385000b40241c20000c83d5050b10754a80840720240180003001c50f030f032441c1c041a00ca103401c069400080d0144158428818600c21040682e0300a030310036410520790304140302e001c544101d5a481501c0d0800410301080c40240d00070311401e41501074482d81ca0803c9608406810b1000b40c09a01890140d44c0015060145080c42108180542040b86095103000d0280000c90034503c0028403140800c1203103090f000071076880740c0f0310051780e20059091101190300d84259070085d1920380c811074070920890111080450050000205880d00017900c0c17400d0520316001d00110a40c2901c0480c0c1c4084200802d00d070540407486000550b1035541c4c025522454240280000c1c07041e01c9010b030740c80c44101420091000800116194401c0401203441120b0302c0d0b020049c0c1c5881c0c442ca41070030a03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 755170971 1250 755169721 755169731
    0x140f030a0e040f090b07050c030c0a110102010501050d08040b1e120105120f071403030f1303020f0d0b180f01230a050103081603051606020d0b03060c121009 69
    0x10803036100c201d01c00d0152044a003042003501d0001c40c00b0460340d40442c01441d01c02082c0003d140300d4000c1014140d0154200c007074070f161a0030300302030768140740207890101d49103100382c003c1c8400d5590910480c1d014180a44290034203c501d40c6802d440c41c01544100c1d00d4111001820901074060705019214681051500c1600c6562111a907045c05100340a480d004d040c4400e130b040242d14000542c500c00b84003010140c48954103041c4108565400c1201d4176400d03200412134a07400c01850002044018020031100c00d240b0b0031407041007600c2c500e2003041e13031140e903c140d43d05002c605098a0079030000d518080484050310068901ca051003281c400d4018194a0031524103c1c80020500c80c054540d10240b02c0b9805035201085581114000c2c080540101c0d000c2c030040300440720340c1c0c44001100b80203090045c18803c0008220801c400e80001c200ca00c0d6801081c0c00c01e00005902481044050072406005035240c02c0c5091815401104040c0c08201d00c40404502d03a5884111030b400036000c420420f1103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 755172221 1250 755170971 755170987
    0x50415050705010b2205040516060203040e0105010336060203011e0b0307020304032603190f0614040902010c150903020607020303060d0210050d0f2906030103140f03 73
    0x1003141c21260003603903194200f070740000840ca043d80301c100c04454000640b491040d00868100000c110050003103440d4882d0b140070744848105000c075080140087e60045a94a00f0030001107964401030380b015052504240710704030040742601d5011120791742d03020251000085007466407440c84240c900940390f50320010010400c46081e29842118001c10300d00005003031341d68000c4410300e1108480340700060f00140003d2000440e0101da500c072030280f49005000c0c007000302008c20440c0d44180e9090b1522180c00e02c81e50324541c0703140110b10b0400322030359041000c0346c5411a4801e4180c84415081d1003180d5a402c0d042c216030003003094030b1041350001040e180400c80445400014021403000b03601500c103400c00207030070910000c110f0b44104809080030502c000686d0034040e022082c3c505030002d0007418041808a800140715105d407100c1e0041002c580d400c01d48004d48017020410a0071030420380403900f69842c5c0d4407020308070f0703046070390019080005140f090f10280c2842980101500c03540000103c6030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 755173471 1250 755172221 755172227
    0x516150509010606030b0609060f07020303071a06040509191506030f0804360f09050d170a020c03040510050f030103030503100e0f0402010c060b0a0803030f011413090201050415 78
    0x70090312001d072020000d20703030806c08008441c091550041d07480750b0704021200005280d0030191007240e00c0503007100d0501151f641d070080034030342943d481a22049818200a82850107024042d0400031940c06021105207004194501005040010340b0a4280f10001c1d4113550f001c2d4052402140c00030000340f07520b078a910304181e065010b8801c016034802480c01032111200c0305d081d1202c0740d810a00382026000e06626016028101a2800d858211354550641c00818424000a145640340c2ea403181c0a506601c020100703078003409040440e80301e2060000240030a0004100c0b0f0641c1d0b01144c04031462490384800312a0b61081c04845402000044000010150000059070140c0d04c0300c24503545607512146802c003908400c46014030590341d982c021a01550003140e0400301e060141c0c801040701140c0c14040343e000c002175401400c103940700108211140f8070020940e4003406c85034110a020a06580000b1031500c0580007160300070f40d443c6001d100f168064400c58005003d0382000c07181c19005160f000d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 755174721 1250 755173471 755173481
    0x3030504170412051c0c1209030f050f15090a030c05030f1201330e0a0b04060c1403090a05210115030203100b06040b09060c010624030606051615050901 67
    0x803100344c46000c000200c4070031500880140503196994502102c6e1450304c404522105004803030b03042c881804400320208551210420000e07008100500300844010389281c540400030b40b02800d02500001400b40440d000b040c3d00000b145c040c070b40842c0301303400c9080981c114403e84034102c1540707000088400407900d401600d98101d82e10955240b04408284c43c0c50106400350b880c2a4038100201d1101160040c000e05995091203409426980c00c0c070b4a5008030ba1455101d50403075000316200a02180030025003507403d003000145500034604007500708011a0f80c0e0415030240910850b1b8168070025040300e00c2003101e00030f2030381c10f00074441260000c141c1c40c0b01189034041a8024040d0503160300c40f0b82051301800a5164028001d42e1400d440d2155640913500190315142e4007410400000012203424061400503000d01c001101030700032074a03403000c4410595450b010038103062107401c000741078002055840d0a4586100300c00e81d040036161060b200e800302141100410304e40300600802da2415409 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 755175971 1250 755174721 755174723
    0x30118120212070c150e0411031b0c030a03111315110303161d0916090e0412180302030f0706020f01060506090f010e09040f170306060703030504170412 67
    0x2990820082e680c004181480744500c050903d4a640c0e408200311141d803038610b18000010b03d010103a030440303e03001a09440103405400d9001c5808420b201c090349084100c0340245401000781c52800941a4405440303004000002d01415234462310081c0d101c41460444071928559140110510346131041017a0700707a80c160303a8030000b8a00040d2940240030000459000b010007882d03001290442510898101c80310064a41c0c3c940200080701d03243c1c0e2a1015810f014000d0300d80300c4c160100516500503c01281c65020049821200f818000440c051001403402004140b4001c249240514100a84044140d10082d058494680c107080480c0021541c54162070490b404c2d03841043c1c00d59846c0f803c0c0c0c1d072207029699000c1001c2102c0c83e10391a040102e03800d0170406060008072015800001800010200c03800c0d10030041008000d0100901c1c2c242e142d0000c00411411801c50401d10080f606070300034200000d00b8036a645000c142445121241d48800925290083e603885441c0c1c0007a50300c40c0e0764404 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 755177221 1250 755175971 755175973
    0x50316050318042a09080d08160906090605030a090b0a0902040f0c1d04090b0115170c04090207050f07120501050105091e040c09020f091c03050313020301181202 71
    0x7071440280e1034903000f541000700c4401404c1c103030b90501e407642642c1c00007a203610109100038000000b035842e909020440c5a0059500c2d8085d8501e0280b20f501c3c001c481151540080018541c02488000d0704102c0120a983d80c6140441e12030b40c134220690000e201d01c03440a024505928100203002410750001358a0394800c0e1000c1c0040b0b6065042e50301503601c50003100002c0f9004c00307d4054000542d0f000d890040030700400206a40740c00c8d8a0345100b084082c2c010402d140110380310205510f400c600425000541e4000c0200d10303281001c3c042c41507000780c4c000d41030920f8000030b01400380a001c00008489d0700248065405e1540d88100300c0e00c50b4481140200e90550030400001054070300b40c0b100d02d200301d0003440d40d400c90040d03a40802c03181020003001281e01412054000c40e05411500c06400c0c8400c1034100985c1e43d0107940708010380d51500e0418011000c102c00803000000b6071110a490b0800c40030881007184000510009015012014600d4450405446c0f040184101c40c24428940340d2290 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 755178471 1250 755177221 755177257
    0x1533040f090c090c0e06070303090210022b020f070603061409040203060a02071523010905060a03122303041703010e0c1e0309060a0e1b0d0503160503 66
    0x361000c0549688040c09485034518100c1000015a07030b80000000d00d502c1c1c03401c25800c013180b400080058204031307020707030019580c1c0c7c2c010008c50a01d110322081c615845d000500c019142103500080000340380c80c0d07120707542e41819918064180204000ca80500700c05060314400390300c448008008051600c5400406600011551090309100394139500958014020701501d40d81c10204c0806980402d5003241c0807201e0024610581800e482884065102c0002104940c140141c54003000752068000c444254904414802039a94a8001c0c02c102d03070340414071408075814220140c1e05111007003080740d240d110a040c103842c5444101e0003140b256100749030480a00007945140300084c0000d01030b10b5807482419022030560170110019009501c44040c00d12115440414000f210750000e40c0c151011b984001c0074031803621000c0c0205100701c1588002003035440d000c0500058800040c0031094010010f14400c5424804180100c600d000403841010ba03800c00c55150250346d81d4801d2070f85c0c0624003800 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 755179721 1250 755178471 755178491
    0x1a04030305060307120804140a0e190b2718030a02070f08070605041e03060e03070c06020f030a03020304110402031f090b0f100903060e0d08010512153304 68
    0x5400151305060f00400341e05c1c149420318050310700f00944506c09035841101c509d8006502654034540d00e02c60b80080e5004180c4100325050b0800740c2c0c80820505116a0042d600019500d90614004041078881c42e00200b0545a0703266041004c13204110224890000185601103540c0000d0024100c50079207445544c060f0f56050801d0705c50105000390000503030100300400030000c41004501584c100052141034095980c1d945c0c40884110300e0702c241080c0c10104928007408042e1303a5982c0106100d002030040c910007141e840e80c491085a081401745a4080086410310035229040c80e00f010016008641d1b81c00c20313140c2d0000a400001032130420000442c80070498000d680201c201d9000e02800c24294900c034841040200c080308012a010040390791000000300d94180181c000282d6902d01800c03c038904284000e000440503000315005140810b06e50320aca005c00a2001010b07402e1a16013803040e00c0d0400c0c4810000018101d200c0c81d024072031424200c100914954040000c41102c0c10480702a20b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 755180971 1250 755179721 755179739
    0x9151906080108121b01020904091217010e0601270609030b0c0c0303070302070519110a0902120403030525020607092403020309010b040603051005011a070f1a04030305060307 77
    0x8595116558120144003131710b1209407006440750540c0714a0000341c10a0f00107008907003203500015064450212800c43c80405a800c0030151007114880224140290b0601e400400784c4400908000d04000030445c0c0070b442e0081900d032030721003401810301d9101d00c1565180000d00c1c1c1c1d8040e02007505c41d64001000314204440b5002103450f4041e100c0042c500756507a040c01036000b500704010580e01e80c081ea403240c001d4001c80c454000b0340207103c3d0030045001c05401c410b108110b00c5a0304400f11403403040080b0840000807811044e4885c5d4145008282d03a034a003801c58bc0c26a40c50b14010360f40e03111a500268460303070041403880c030641d016a07884000d00c0c0e68410042d81c5c04581c11403016000c2c10030140c0007615110350000e56200c1d06100c00843c0b40380d400c0002c641101d140790b10a03500354100d0804540c2170169400703243d0062100c6030b15500c070410750310495503803445882c0c0d0092041d00c50141c440e0030444003480e21903402d26408115500f61400341006000752408980c49446401241404264886 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 755182221 1250 755180971 755180983
    0xe061b0c101706151204060e010e0307150e07030f0b070e010f03110408030a20010504031707030f05040b04021014120a02041703070606061d09151906080108 69
    0x4070903561a00c0038244002800d441c00c001420590304140b0407001480061311500050584031000600e1450390714040c1000800c503a01c2c4407a1603016414488500c60b10100002944d4101d40c00c4080e1203211040c2d42508801041d48540e49405800b40c11000814080090003c0c240c10340100501100740e42e0741d600460f8460107001490740415002c0519407103403403182c0c0c8510000d0000c841140d1500e42ca5104813440e40e00705d41e84120014010030700138505a000800c01c1d04a0510100c020f01581c01c0c10364000c1c064007031802c56040e0300c00d40080000d0711184079410011035400e14032401c201341d041078148068004003c841c140d00500c000000d158107284243c90303601c80c03600c2130503070581080d0040348914140500035142c40d482e6a004c3c000801d9690a030b040d03144203400031000850344e803103043c5000d00a90700942e00410502c04442c45552107107003800310f904044a001c0b0b81030041ca40d2001d04108a105801d034241e600241880b500400c200d01112558054810b60f45416110780e984501d5a0b940355 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 755183471 1250 755182221 755182249
    0x70b09150f010312030b0f03060c0a021b0f01110106050a03110f03070b1602040603080c0d12060b0405010f020a0b011509050603190903020a0f12030506030307020f010f0e061b0c 78
    0x107480c0401140302107120782c0c00211b00e503070b005000e59a803080040001c0d10b170a0b010b8410540f10140058001801e540405c94480c5410305904509219410000001c8180250728071141c1401f03030031500d02207658420352111018080080c1400e425944070706164080c1041c6601081c0200c080300f0060f0240e2400040720803c540140003118603101106040c602e0040c0c4c03800040b6081504c4407230202c0083ca5020107042c4548070f5100404602d909414020030003040600c0c9020030614000c000d011b042002ca00b200e040d50001e007060603540c20844c004910b4444d0b21003019005c51541800031806051240795107030b40b410741d0703980c070b00d259601d80042149034030065840c05045400688654460020740c1c2044072614000c0c015104a80119203541d80c511107418001c0315034141c0001030030700c03403505440b4168010000750001c506010f28ee50124418194482c1410305006103c41c10003e21485544100f1941c100640f102d620703a401040750f00c15614900e40842200d005840c00c400c01824001c44091040c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 755184721 1250 755183471 755183483
    0x2304050c04180204050406020a030b0a061403040c08030a48030905130606030c0f0c0303150b070b0609010501050f0304141501080a02090108060106091802070b09150f0103 75
    0x494403090811004155036200044070b20b8203020b07100056910740c402c05110714020b0304003581d11000240000c040348c2450f00c1c214898001d56906000c2d80da400308803d02e180102d5040340796a601d0700c0c103240d802c80485a00641c0b503480002a00d92503184d2020f00c100b1601703080b4500080d4549103180900e60344030340034892500c0c2108040f1544480c45d2912030400b800b400303828400e002030340750340216200881d035410004a50f5144c0c2c404021655040c45964042221480d00303266078000c0b008003e0a42001d400f000d01003607280c080032900009407800c110014458290324956903c45c030300d86116070510032204180b00e02d0212000144950207103084440c0104c00c1e801c81481c550342c0c4e50307030f200c2c20031384000840106200d41d140d035a00e407035080c810850180500000400100003240b0411500c280c0581026026400c09401001b626070070481d508140c0b200300305d8803680d00700381100c404003d002d10300010700810800e1707081c0300001c80042045058440000c2c4040c907240e40c1d0281d0300101c00004e100041131 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 755185971 1250 755184721 755184733
    0x81e2a0a020114040812040e060402070f0b0402121e0601080f0a03050f0f0f0d1d1e031c05090d0203070804050405060105210601020d02060402030c270a230405 70
    0x10b43c80342c4040014000411049070400f511950801e20302100e052a408101d02c002406000c483c11400c0c2c03c1c0d40c40f21007240d040d860100e0740ea40e4060a41d54400c0010704414045010408550711030341c1d0403411482d828211902c9622180003441d44054012841c0310b0350081c0780010030000000b00d14100c0d0180d0490040c40300d90340d250750403602640305182600c014042030001c0004000d801c0d00402890400d42074040d1500e40c900c1e04502101c0c480c0a2141d5180b0010b1034201400901103003084126010180b1103103501005048a41103126011034007245e030b8030b03403101d0001102c61340e48a24010601d4004441c007400301014140c0c2d41e071040c420081d060100c00c1c002006107180c103800c9580e212006240c210304007194068800030072020344480072884400302c01080169641041040901c0d05588014103040c2402e401186d145c1c0444003a0f035006026160000940f84812521725055000321000a4820725107190804000e200b0751850300d0780c442d503070700c582e2040c20402003405010301d8000c005011 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 755187221 1250 755185971 755185973
    0x30f02120a1b11300708040515093a050102031e010609031101090b271801030803060402130608160504030b060d030e04140f060406030519081e2a0a 65
    0x500f41c4d00d1514844801040007038056580e103c440680001445030390f44a4580342482e00f0407039200d0900c408036026003402d0000784559035851180b1041d1044526002006a044100584000400780f442c4001035004180d02c5040200541c0114410400b01e410707101c880d0420480540144000c0c4a100000390b00e6490504c04a11000000000c44105040401c28203546901282c02034010301c444400341d50500040c5d1440c1107080d00304034100c8804032203101c40107003c2071a19103034800c10f010181c5044030120020701591940e5044898803040c2011030540244e0b07410000340b42c1e1070110303040c00700c41a030742c0355004c00a40181c0c261410b0b01e40c01540c03c00c81e651504180200e18010f181c040d410001c00c06c0112140c2d40315807143d0000c081d1055081c008610300050141551080a0704c018055841e200c010400314201048101c1036611806a02944e507510342043d42c0c403030007400040140030840038034180662100c03000130010300b840d060428902c130414007240405044041800001504108407000c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 755188471 1250 755187221 755187253
    0x212060907020a030f05280c0b15100815060f0a12050c0304110d08180316031218030512040302090601080105031e03120906011e050f01030f02120a1b11 67
    0x380b452105030600030105000f01c4010440b6007c503607108040f6141c1c40c1c08206000b4020725156008903411000908031000d10080341c0f604441e03200800c10001d04c840400d5008122038400c800c0060000c0c201170321002800c80312060f40c0c1c07084240802059030040d10944c000240d008035032084118400c1c440c2903588230307106c1540000300d103030001c3d90044445807100b000030310560103024505015034404c4203041401c2c060502d07284500c08104000800071500b0400680711003c1c1c03214540242c504405524403003600450855001c0e00010194041c0d0b00007400f214200c54041e1007121f0085a0441e50383d2955001540c0206080c0203a41c0c240d001050340c24120003400e1019500380c500c05044a140407043d81003611490300a684000d1903070081d0004111483c0310081c0e9101d061901ca5103909482c1c07808000030160708640441d54141500d80c580c1c1c0100c01c41d19410b80da22080c5030780c00e2000710315100c511003004060004448034414081500c103a906803042d040d225400690b14003c080d481c01c249118 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 755189721 1250 755188471 755188477
    0x90309010207080d080a1109031615020c0307170304031415061207062604060903080108030f030a1e090302010b13061a0904020403050703050c0108070305070c12020f010212060907020a030f05 84
    0x50101d043c0c104482e0440b900c041185140096281d8542b402c41801d000f00d00f541c890190400004641c080707840c1607007075600416002d0407980340314405d803501103400c0d81490840c025a403025100e4020070444007100500492000002d9940228010817513455908104803400c0700c0c40ca10b040f60344101024001c040c000d041ea1200814404101c6a9004080c017240107010303422101159015146c0c41400209500709100c0c502520456002d18201217003060400518080144508007440d03c45107040d018500d018a24440300c1a0420280445045410040d0203000450780c0300d4040d9503252100a446000361140e001942d0300018000700d0000e40700c16264203074000c1107200c2c2e4030550070000000000c2c400c2001c840154800d00c00340507e0143e4030000340080000401100906040c0020041e4140d8050203200c035030307a40001501031151160b0000ca28080c100390641a00303620000710150440c100021030352140100b125013100b1035441003000c03a240ca41445000300403500140450310054098405 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 755190971 1250 755189721 755189741
    0x9020414040c1e14190b07061a0103050405030d09150c0206151203070615050a1d0c040e01050904050a0b0c07110303070b010b070807050d0804050c0a06090527090309010207080d080a 80
    0x405c400c02c6032545200c4519a0102c0b0f0b04562040d554a1814034402980702140c4400300242810407a03480c15881e01341d2203110301204121221f55906440c0200031490030b07042d40b105507129040040c0c0a5003a0003a60701e403015034805198400030b147d00e0310107240181d140c40503000484095418544150788203006450750b036003554040b20b00820046a2902c034100000024031014920440c007980f075403140e000580c0d014240c2c072208035042200f8000b0070074589240b070454009a80d80a5665201d040c00f0b81008404200245045060001c1c400b0500d903e10107400c0440c0a04800e50000460400705941c900ca800302c0200003132100b4004204070300d0b051001d4030a041c000e420311440e20210350b07103050500a03404400c0001c15801c40511040c4030040262024410050b2510710310309041c803034080e03d0200384d4800d0500c80d5000c00544804c6d0f500130080800c00d000c040741104200c0c240031040c40d40320b4119543c018010310802200003807800d40000e810a5030b16080e110107d06880c0c80742000d0203000c6041c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 755192221 1250 755190971 755191009
    0x1240b0d0f0f06050a0603111912060806010602070506030f15060c1609050108010213180b0a031a0c0a05040603020a0c02030a03080405010e030901020c0409020414040c1e14 76
    0x30072800c0e400c58501a5500200c1039150006000c1d003070078104140805242c000d041090310740004032881c2803400c0c0494180b240c0101594100e0381d0160400c64101c02015500c0f0107450900034001b945040014000d4161041c94003a540426161424420103020403610940501d030201c01213070640813040784400003100080c3c0030514080f51082c0c054038159815090f0003031a015200c08022a807024441c02d40036003500e400030b510344101c41c1805c0f185000b46000c1c401c1120107042c803e0f0180851980503806600c1e0107821010401c0e070380c0c248860001c0c01c030800071140d821240c1c0003d001c084290110390a010440c0c44040c1000d00303181d011802508070709003200603c02100426809a5400c1003120701c02c0d442030340c45213030f5850a80380141c251021a01401c0c83c0b80c1c414084000140c0e0089200d800da40020742780003485009a000107800b4003090703085d40c004800d140050206120b45600c0e4032003503a201490002c1504010810074043c03103480d10134020101d0813a080c006d0030307180c51358084c4425132070301c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 755193471 1250 755192221 755192231
    0xc120e031b0d0f0c02100e010908010908031602030310060c06110f0c0c040204051e210f190f150b040f090b0c0f030c0d02040806070801060201240b0d 66
    0x10032003201c40900081048440c0e80628100740300d640d0b000410034600d290344d160459410080e60301046a010f850600102400321038002c41c3d0a0703910482d030003001040c07100000e10400300d160800011707560041d249224400b4a900080e142d00d8000011240620300d01d05800354010300c0d08034121410704403c0002c980d80358440780e025040c2c0005002400c1c64148c0203084554803914400305d030b850407500c141118040e50041c0010444c40e900d075a0b100c21741c00d14401585c107884660b5400920b0a41c50710070b050145a0703011011700e02001d400695040d050500d01c0072510000c03007007079905440e80c40d820380c01454640000400740004070401030411380040b80074804201541150700250586440c942c00c03113692591520014140503402c190b147d00a0b401017400340c540191a58801e80a110040c20f440d1041c00c001003107000345e09568105c4d0b0050044c6819500b207428502c00c020b00340300c000c4c070910005608120f0514203201d003c406040c0302c0200301c86900a081d160540765480c0390014030002c5913150342e41c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 755194721 1250 755193471 755193487
    0x41b05070812070e030f0d02100c090f06081f1802090d050105010308130e010f1a22090e0d020a030e030705060409051e04050a0f11041a0109090c120e03 67
    0x48009240505a284c55800424404106141ca0300301e0b09105500640d03c4005200542500401c506600885100010940b0500b401040e038640e00643d010420300c0c1c2045000045842c1d100c0301e99030260600310503030752140d5120072036180f03240760a004d03600300c030464401042c0038540582e005150095000d801e6100d001c4c40380d02d40350f003150401d0384240c5420304005070801464000710150f1002d44880445135610f035040c0607521840301090b015000d40c408041680d508070500c90720541d4200082501c8010100040c3c00e400c07038608401e80f05104c11241081c450603820702e00410082400c46c103940c001c0410404a032801c98071483d125007403503050b0154510100d0540c58820050000d0324613114080780324113049520000c2200c81c08101503080c3c3d644c01c20b201c0000c40200b00103883e81d8105011200d04105070519101101d801030349076030710a107886099040c0c5071180d035050b0f0f5450b500f40c036101d640d41d64542c500002e441c000303a50200020f00c804001c0b1801030f0580d200440e4060703c1d400302c1e8149818 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 755195971 1250 755194721 755194747
    0x506101205061f03050f0a150b07050a0507090204051c0f020f0a0801062408070c0303050403050f03092a062a0d120606021f050712110c0606041b050708 67
    0x1c07031005480001c5d00d9000300801e010045004c0d40d0060030046003080003868541100c0c6841543d40103001a6020002d190303428018104040b000340e54110050344c0410f030b40c5036182c000030b60091060b80c0c0203503091031400422907a1901040c540c0c5400c03105403444c60f282e0381d003049400c106e4400c5060b80201c0403100400d103144240728540150510801c440d01d00d00d00f03c029201910f030003801b0f4004000c03441c810080402d0380020030006d280c1d813505020880391503524065900d03010b0942d00da16040d0b808400c11440c50f1002602c607070558590150b4480b140075030070b441d8142c1e621196480e0b402800810192504c0012400c50101a4803041a103011040040d000b85007041a180751030b1f80041c140c0c031607440030a0900d200301c100a01c01400149001c90103084030811009103108a00d1400399200300207902e2074064191542e5110790f01c00c0400c0204100801032815400550944c42d20344100350001d40c580c240344c400d0bc040440d11000010141c030350030701c0844803039003c5101116190300a0100041c0202 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 755197221 1250 755195971 755196019
    0xe04060f0b030601032d1515051303060507090608090105010806061311040f170c01020c121c02030a0f091410090b160b060d1109070203120a020a0201050610120506 72
    0x81050170300482c40000b000e050300c0000c1f884450350709402200300409155422441c00d0441c2508111381c0300c511b1a40309000c841d0003644050809400d050801842d280e2100310042590203c1c0c448403a81d4031030340c4000c0c3c200d42d024003803041c0c41c1d80040b000c21010b00c2c0140d0120a880080304010509012890aa0855400952100c80c140000071000d000c1b204440d04110801c40c107141c01080d80c050041c000039500c9241f685a10b00030000c410600314420f2013031041e0700d2803595281501704003091580000755694070940c0c07104006944507106040d164401c02c011011100300d15003005d0110010320401111f1060300000000b44195148002142c0d02c0b030078090100090841005102d01490307003024440319000400141c40b4940c515941e80014160740381c0c0089490041d10308910760740d0743d1081030340b66203d111020b00550000104100c0852100c0c0c0040074102d0300d40d40284050384409051100902000079a04086004542c5c2c031498607102340c4c0101d070300c15030003040c1000d074403024084035107042 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 755198471 1250 755197221 755197271
    0x4060e1003152d3b0a050406020d0504030f1b050307082206170a06061d21070305190206030a050c070c090b041505061204060b0418030e04060f0b03060103 68
    0x80e00150034200d500301c0400c0c4e16aa18108107035031101d03812510b45000384500000740788010880d910300100702480165070540d000501c4040341002035044c00e05001e0124801c900c60300000510410441405072228650388503801c1e84540218107204e0382d551030300030741d401c40c1c030402021150314051805c848811042c0f0070005d10f5682c1b1689182c80600340c0700ca45101008000721800da003841002c00245600c801c001c211101c18078400480c0607a03450029420703041d0070850200032404209100c00668011a00c2001c4034828012581201404000b40f094082010130181d8444000c0c8009000d142458001d1030b800131483e210305182c140d42d40e56454040304180c010f1061079903105500c8105084c070b4400c2000e48601c4626506078075282c040010310f14882c2c40c00c5540200c0c41c09006c10100301840c0c07c8840400b800500034450902040346040360b162440c0c00c2600001c006055280c6d4a0805101d14030a5030100c07071002c41481e0070142840d1041d8406411241095a40c00c03011020316003030fc940003039503 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 755199721 1250 755198471 755198489
    0x501150308041805070f2007090623090402010503091603080d0507021f020c01180609020a0b0903190212010e0f010b0618010f0908010204060e1003152d 67
    0x30380d080009907a03d408500d41d118050300d04d80414401c0c0d031500180b084441d0541071400001980340c80c140519000c114214984640c0300340341000c500c00c1c1e001e810410070b9640060103410702080381d032007000209600040d82c0da04014540081805944904015507000b515a42140d03a080c0f0121440004014503500c25a06030350f0204203002d142c0700c0c6014091b08200030b48010301c2c607001e034418005c241c90420701e03541880c10750000e81e403c04544290007145501184000080000216040107005018002000c80c8142901d10000c40c41c2120f01d000e44400d0340303024000340020040c2031108003081280810580e4026001000034005140c00d020303400b00744022030003506070f2114a44000c0e007580c00202c20140f080106002c00b12003000c1c62503541030213400174600720b140c0c0d4031002000e4581c0304072038000c0741c21540005004550380f82c01a1300b8000319001502c0d440640e6824920403000ca07030703a01c0541c603412082d2040800c9a160b0702241b05e0b80000030f0010134074581d5854821a80e58071a50751010001c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 755200971 1250 755199721 755199727
    0x7020a110306092d01020c0313050901140d154d13050a080d0905060301080d110c04180c0609151103070b0405030304060b030115050d0501150308 64
    0x40009000403801040c50039001088941041080d00341c44075202411800071041100403c40c000000030b00c3d840f00040030500843d500c008849400d40c480d805021003c840b541e06490000d1503003031045416040300d00031296103001400d400d0070400c1d940544102600c0c0b081103519110b5409602d4481c1740c145501c1e1884151940500c026540d0800c00070048403100d0140a0440c420006d02a2100140100c0c4c80000d8a544950002e070001d0b10701c0081e00031a030054800c00c8007040f54080003924282108294403100104c40d901d008001c43d500c401d005a804580088524841e0107028450340c1d84590004030684420740603410200d07007125544c020401015a4901c0c801c0140111651500b01820ba9850008801c5017016281c6e140d8001d84880c4c40108181e196111100d10800e00540340e00c2507201d104c65803a03003403609045550b0f400643e001d4410900c0c00b14040642d01d01403007140118440b04808c0e462076458178042003c2411602c40aa440d0b5485913070f6010344d805452200380255100d1001d10b45c07 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 755202221 1250 755200971 755200973
    0xd020a0806120624030708070308040602100516180509190f0e07052205070905092a0d090c0b071e020f093402010f0b0603060f120607020a 61
    0x80c0d1008908101030301c1d0040d2052200d008002c4d4020f02c6154581500d4103a61801c00020900d4a102640040700901900d013000c400c0220100003482140e820360b088401c0c1c0170013000a04120f59054810048028141c11a6440c950181d10b01034001c09407008804842d03655100424200c45040341c80a1005041d0154040c0340c00703640c0314131003201d18119000c001e004445800a03603911254000c1c144510702011070000905c0105d250080c421070160380a000300d04085401070b10808550107001d20804243c0300182e84494a00b1603041107a00513448052081c0d0351104c10001a4000e0110303c1507586c031140d0010108401e40a504020708511580301c0e9110042e0501004044c440220f14281480c0015001c002d0781d19001c20039000b50307007240c4503a616251101c4101070f450000d295407005070344038484110003640a9240c80016805034000340180500c07100b00340200e170f0000b016035a1005c3c05001050782e030300b044000301d030301903001414141c42085103500301490030300221001e80043c0d0110301114 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 755203471 1250 755202221 755202229
    0x1e0b01020d031505040513051603030801060e010c0b070201020918100e0f041e020301150305160b040e070216080a1b050108062803140f030909070e03030d020a0806 72
    0xc041c49100d8a8100003003200040860b84807059446024400c035190b101103071000c1e12142603a4502da500104407480d0000100c859680010a80300940c042103e9000026040d80192100702880005a5882d860700c481d554070031102d0013020b00600c0440d942403054640544415510728042c01c0c99110f003140914203101ca41020f800c40e40c02110900c0c1032141440150f100b450b20580d002640082d8101c000b00090b08105045403000b003001e076166090496418030440c20440080903a4000c2d41910b004003da0350b103992124500d442040c00c0c0c0c4400b044104007003151481490b40216051050f260044504002a00d0f6440140c122100d540c20400b40801040740716894440d006581c0c2e100c84901070f00d8000060404c10000b407046001d903690410a0240c001960b0000e00b008101101c140c21207610707400c0170341030100701c034501c0161403099003842d0036150000002d44146c107400402070f2201c0d41c0c500c801242e042a0301011036800d488140000d2041c403001d400500341c078024a651300a45884c181d4100 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 755204721 1250 755203471 755203483
    0x60e031c050106020723010c080f13050613050922080a0201061413050a09020301051003060b180c0a03020d020315040f1401060c0c0302040c26010b040e0a1e0b0102 72
    0x1040071355024036010400c9400607500d041402c20100e0000d101600210010b880c1d4040c9601c008102000010302d452140002401800000c03c3d89824500307407a4a480501c00f0621079440e0b10350400c98450f108020707516180d000d01c0c0c0c0c0081c40d1070070400075451540240454911420702118804408a0444081607091150724010440010700d541c030a0840d1010030410458000e92030311240c0c6510004820340341d5a00030038146a4050002c00441c0340c038908042d1800514002100c1050600c849200300345055408041c0042d51050002c009440d0060b03e10f0403075001040e003a0a1540a02c9080038001d010710207184280b4480c820f040e4051071107020001100d040c90740195010703107001c030f1a07075031145400412815250281003800e0f108100c2c4c1800d111070340185e44020b5115080c40c8030181c00c59808011442c078260780882800c2074039448007180391100402d0103040c0307444100340403c002410400360800e4101c0710200c80040c4000b18184200084240d1b5a52580c0c2c298a540c005e0455580c10009 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 755205971 1250 755204721 755204729
    0x3803120a0302030912090a03110f0a06080105011205040b070f11010905070620151e04060906111e03070507050d0e0901060f0504120204060807030b040b13020d020904060e031c0501 79
    0x646d281c07019085c001102c4c000b0b1400090314000d841e40007504241c071070851342801c031003005001c0529550355100081142d0003d00031940098200e1124006604603030040b03034022648078030a502d05680b1400111010b000b14591541001504400108404000c0c400c0b000014041e1015110751400c214003c1c00c01444e41540e0120307448002c8805009040104014400004041c5016880e4554288000c07110189520314500e90407043c080c08100076007a480801c00a1080b001400342006588031060503015000e090840d031400b05840d0329100007070000031035000c03809042450030300f901c42d182c1501e4003a096040001296060b9200c44881c07900010041c010141850b0030348281e03910143c010300d503000c2c0344106900901810f000400b1951180c10590241904404a400c215603e06005821140554044e640c1404d101c5c08510b10041b81da9207100120b802424140c2200c0040c1d003440061a001041951103030b03034403600c50241c0c0030705100500940140901415006120f91222400c465060784 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 755207221 1250 755205971 755206003
    0x612010f03061d150702071706091e0d0c031713020117071d03120c100c050f030c130510030c02010501050d0309030326010306020c013803120a03020309 67
    0x840b211550400160903819403041c3c040500c455200c1c29011b0b0b1400ca07641c0c02810b0702040c40c000320700c041d010002c0c00320b11401c0d601d003c89030214183c040c201034211100d000443d403a000803480d494a14000e59900c00594841c0c98031034165400341c08a110400015209103000f46c03103a507040415036a000318200265000050b0010070707800d00903c094143c040e51004200540e01500d030390842550140300c203160781c00c103030700344160b640d1080d0024907110342c4e100c8010340001d46031003500c45100d440354040d20398a0b2010070400e0700d15111208842415002a10000c6d8130301e942003c0130969480d217900b6840340340c04070b03103022920307205503440039007550030503008035005000c041c0c800c401103580f0502c5201100c1c2c243c00c042c51517824000c0449004103054002c401101c8220000000700112580105071480c01d19008211006601283c000d6021031583c44400d11032204481c00c03541101900102c40281000702154901403d582500000380c0041c290358002c40e9011040101d5000103200f05020040504 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 755208471 1250 755207221 755207261
    0x21504050907081017120406080f0a02070c0b0309100c030b0a09050606071b090515010f02011b11030c0a08070501060e071d0f060705010f0b010903020114090612010f0306 75
    0x140c130108180b000344106140d110340c1c0c540800300007006002500012140721419071382c84d52a15800346c50724800b82c5001050300c080c900060301344103c52080c3ca00e9140e0229030314079064038104203c481c6400241010400740210b01c5000100001d611400414507201d84002c2003006041d02008004215603010001c290700b071408001c0b0b55501e803005c035220b10780c1c04100280160002c01d440e50b00c030310040e0032040c1030601d06030601414a040031000b80c0c0011090323076014101c01344044202c2c20303188082005110703000075280b21084c3c00e0288500041c00346c0510101e90800c5007003211a40f070405605030551301c0000018561052120138042c4a014043c0e0301225810360401300d60041ca40505503070b6142024102c60b00a403104d9030781c81c4041c0c0c45060020083c54603003506003001030080980703101540a40b0b1034601c0091443d40a60194021681c058440234004044407014103000e84c400005294000002c101c22403903030000040d01ca001e08000802c035035030b0300d00714030f002c8089420880800e0901c1980f0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 755209721 1250 755208471 755208481
    0xa05060a060f0c08030414060c0c100212150102012c010b01020703030801060503130b0c0a081b09011d0904050f10150506161502180a0302010801061b02150405090708 73
    0x40110110043d03440f130b5080c1e079a40e03075a0a003045020001540b40905004400904c002d030610100544002c494007015125440142e000a00032442003c0801005103060000151100301d01e82582c0400300c810700012403010322425620442151402000742d8054002d42503400c2e402c024499891034000030b00042c840c0c3c40c155100500441014410b4078200100040015200c100c41502285601e90107104011541881c0c0c1c3d0061113504000d440c900010155400103000b003640c000040a21642c941059207005000001103400142d0411180620041e500701481691965500c1c6841540128080c0c20000010001d05007441c00001810440078103000c4841801c0c8503038140141240e000300d441d03565400001b105400d010080d445e02800c9081b0410b40c500500100b43c0090208d54040e0050b10481b18040d0100706000709180006030002e0080c0c001844110b01a059940034009040318503055503049a0000d0074910034031084207030500c004102000a82095296a90007121500744201540340c1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 755210971 1250 755209721 755209727
    0x911100206180708010212041b03030504051002211e03010503100905010e2a040608060708100305101a12120f0d0f0209030606100903030f050d050a05060a060f 70
    0x800b81c0070000b140c00c1c0e0540380700103100c10040c4200a1518000a54903036004400300300001c2011101581d44010406020010002924400c01502d60503101c85061a040505001380c6c8508018600c05620680c85892402101c0342c03400e101035008140425900c4180d4006081d0240e1251004a12070405100511051350041100780d00348031900000210b00825050481c09018050b0000b4244d0099291403580003501d0f801000fa00d50310300b403203003d442c2021414401258075500c61100c06801407004a5601c611851034240c21030000d4a411790019100e45406041440503540c0036007040e6299100100c0c140341414901e00c11100711a88500c880340e49080356110f6a5003035201c0340110002851410281d4200191514208140410498100c04043c510000d520440e0301038842e1003040000340492070075541303010719503001d5615248098915901550401004080b031703400e01c030b004d000b000c0c0c40c0c0c2400d1040c6807140f0408000030409040c113030b0a00010746503542042c1d0070400540a4031030f03c130360 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 755212221 1250 755210971 755210983
    0xb0304081b06041113022a010c0c0b061215010806060901060f0503040210030609020714100203070909051e070c03030e0607090e0901150605180603060d08070201020c04060909111002 80
    0x15594801c1c40c80c1e117144140002c0c4102c1096824130b6a02611240034040600c03041c04030981114004c001d810030280c001d99640381484030080100100c0740002e210340c00d00415180d40d0384c1e00308044540c2012482484100180260000c0710282d10500800c5402d14081e0b641c00d004100d141425514071004d410b006203d0b1100500107030041c0141c42d8007444580c4258401c1c8000c01140c80d0454443c900c51a00101c00321000e0b2983e02984102c07001880401142c0c42228021800341c0c1f10b0240c050310340f454203806041c0040c4200800884000c000d20200900c020952042c6096904e0410814107484e014049880c100d00700b01d440d9121004001249400105100c141d8800010a096590342da08040303014126904201c0104a40f80c907000424627040341c041c1440749401c42c480003801600d0800c1c440c45000c101c030030b01c0d40300d14008002c8021a81180040020b14010300c1070341c0ca03001d500c90120f016039415a01015456a4604140c01405000580c8401c8002c0c115a1005000000300c0001d6841d0303 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 755213471 1250 755212221 755212253
    0xf071a2401050705250501022418010b03070605030f0f0601120905010603150c12020a090302040207150e1c05030408030105040e030d0609020307090b07050604030503100b0304081b0604 81
    0x80c00080071404d01c682046100420864001e8070820700c2103e15050301c401c056881903902500c9540c404140d60203403003900e5214403124407403007416a5145810b0140360b0401c3c85000c0703a0b6540c0e4030050016a1014409180a425a0b86074695a820f22142500f03801c140105840110400541880580e0780d101d480e5101d00000200003166100c1907041c01d500514140e8002000410a130381003503000c1006404c00310082000d034566200c4603c80e01004c500380d211740124000042c2c60748809100503d000d0340036019540c02a0f0029174007070104081d0300c0885170300f011103480542c4820165010458032003100310f46028a40340ca641982042d41c3c1da8985400103003d541e118548603584e0211005041041e03e0b288003008000341700c140e50b14041310000350b200351100c10014802240c0400d404d6200000c0710300c1540d20600418040e940c40d2400c896641019142d6803170455007480c0090600754110180d8040c901502c16180c0d1184000f0071a004580c21104280254101c40308020101d5034409550b8208 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 755214721 1250 755213471 755213477
    0x30c060403120c0f050c0123040606051c1209050324010b04060905040c1704030f020615030604030e0a0f090641012c0108010e09030f0f0f071a2401 65
    0x2480c43c06c003031540908403100c00380d0340440c2454040920040800991402203000d40350412105448006005101010003055003c10030302c95028000991a4034030100b00c3c40341460501c03503042d00d620002c0e01f410300c2070b800081b8034600402a548001c08510143e0300400a0408682c60649080302c083c00c00091842118865550b030317217110458a0080348a803080940e42e010144561810303140107804028881d2003c001442034030001444448003600707014103468014000c21740c50b035860783c00f252146c421000303982d00055283d100040f003204460b03000c1d000c4d000020740861a0b6042a07107400042d6004a0540c08155085042c81f1401140140c2800d64411454041080319180801628170101c45041c0c8029103035510a0740e4022942c40400704d508e00320990754280340e81d90300c0c0c007000030041080d01c005d5101c1d08100543c010141c2a04018200a000480c40c83d08000b0300d41c03020542c035041440180c40b0201c4075064480c3c6c02e18012000c1ea0f0140c1c80122460145074801d805080c9058144078440c14 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 755215827 1106 755214721 755214727
    0x4030b150d0b040f0c0503161e1a0309011410090f090b13170a0513080f0c04020a05120a022101050306060108070908030c060403120c0f05 61
    0x81150840519076041e207454031100102c450f0b010003164003d43c405e40000f1982c03414801c280c22001891280070302d0515200b0300032400c5851004104810b038546a042c4041c0205901c0910006104004152655900e105c0b00d801004040d1210740c120384070100700000140c0010350303e000d03101c14040a0100041c101d0321101a120b1940000f0500b10b40380d0300203001aa02c01794003076203040c090700c110400a0f0300860040d015520941c03036400018070010b040000822110103a00062029400510002d44842c400f039440b9004c80b6822842030f81c0000e00880074511480945154003c42090302d241814407251040003540000810050b860b45102060682c0c034441c105c0d64100d41c000f5002d0702035580c500d00111140b4100428483c00d000d1800c40c00318000504001502c8103101010080545003407a04000e04a41540480e4900181c14514500342d0303554800c1c10894103a043d4104a80c03 = true := by decide +kernel

theorem cover : BRFrame.Cov 755035971 755215827 := by
  have h0 := BRFrame.cov_init 755035971
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755035971 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 755035971 ≤ n) (h2 : n < 755215827) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
