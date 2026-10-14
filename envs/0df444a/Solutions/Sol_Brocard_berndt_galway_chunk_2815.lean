-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2815
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:49:25.731588+00:00
-- url     : https://prove2.me/submissions/69e3b9e4-1d6f-408f-ac57-409c73fa928f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 506115107 ≤ n < 506294964 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 506116357 1250 506115107 506115139
    0xd0306180603120305060103020d0c0e03010b190b0a0c0c18110c1510050409050604050616050427020705010e0f19020d060207050f01151706070f09120b06 68
    0x51008030b0740c100010104103003510070203c015041c02490241410707000c000311041c03071f40c05128900c01000d01ea514154981e20000c10542540c20b0740f10741c58400c81c20200c1c040c03074590005c1100740032140301c5000591303202e2003500283ca00709581d440c0a01000c40b01000001d01050008107000c01c1240b60000300082c0402c020440407500403038842c1c240660241c120a0f4240c811408a103403c0300039000d07031011340f48d607810018082d600700359002c0301c16070010010b1108011040011940004408980c901010720000e0300910a0040c2d04c1225000c5a83c80b601d0800f640c130303001003111420599401550f585055040040c0680b0b6420a900100e03c102d0b04007500d17a4001082c0705039041d4854116014443c2c01e50200034085041745000c1d5800c560800801d80080c200304020341c820312084001080640201c10382941c40c0520350701c00100c0c95040141c0740d6580c4404103c03140c1c03001d6181020070382854107800846203600560071500c0005140d24010f420f0100c40c1118038071881c022540040c03442c0b803084c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 506117607 1250 506116357 506116361
    0x316030b011a0307080c19020a0c05091b070323090306090106080d031a0a03150b030109031b060908130e0105040905300d0e01050708040c090b030f0d030618 69
    0x202c0402d070140050000c126128403400c040d03604607282d401c01c0c5007011001c000d816488155140c0c4000964840741248040010098130301008020485801d2060314040c01400c1441c2c9a01c1842e222060f40050b0705810580100c40c07582c400440c0c1388220008402d00782030000d85501c0701c2c00d00380c0310b8426000010108207050003210203a42408021b03200c4161440800d501400040521800300003c110108a681d120020a14001d60184507101a07000c41420340c01c4c11103103400c00303007402030341003408240200350080c1658014111b10b0220b8903808940b07041020052044c020018500080026092680d100a075040e80690380300002d02d0780242d0740d030310030041121140d920040154100c020101013070400e212803103044080440700142d22015180b0ba0704400ea0005016080c816603074084000d03810024801e80b0781c0704995080c402a2030409032500018004140f00d602c6400d40c40d4086441a900e007031101118025040048603400061050054003a141e1801032445070340d240000042c28101038 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 506118857 1250 506117607 506117639
    0x50106121503052503140607110604020d2307030803070f0206060310020a050d060909110409111905180a0c0c0f080901111609060609050604170c0316030b01 69
    0x44004c00e4010030501819500b1140c042c205041c00ca1100c10020100b40e0114005a24826090181070680740c171980190601c801900c02241302c1e0301c25030402c801a00e400700001d0b44aa000101e00c051070724209606900f406041c00a21818007030940c0000400c8103800145000321802e03180c1d5058990a84012690390008543e102d0381940003070407480c1013501c96030041c04502c1240c80d1880c03400c034003800c1c80c10540d4a0b0303a0111040340e50340c010384010b1001106001403000340403103090008142c00c1e00c480c60801401780310107200c0d0480118042c409608900c40000070400a00440c81e05417090f07124242d034110443e5400000360410844501c0b440c030881c01105000d0740424030040c00603803501c40d0790840d0001081c840c11b008004c0b01404504808204040090001004d50005c0d94100b800074015075400380d000406100100c3c3e41400181d076100280c800f40e502950b040e080c40004003114610306201850015094003401170300b4503950310700303d51010641e4000da45400c616640d03902210004005 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 506120107 1250 506118857 506118863
    0x20111030a0912060207020a06020304081203060d1104180c031704060807030506012006041209050604051905060f03010807060512070e01020f101e06080d0f12050106121503 76
    0x4406003d0044030026948003205501664006042a01603130100d50201c4254216402603030010800b008201d4041000381c107403107200084c443c19400c1c0070020805920714810000c0031034400404840090b140c2e58070190403000c1078030040d20b07034010303a003400005082940015100005000008650404c044027101c0c00c481d2960b44856440d82d030640218020000500f0f414108919880f54200070307150010540c12811180d00600981d061038a0201e50f01c480c0418810140300c0e041000700015030762441035804541d41a28492500325580d01d03441c902f118607400c103d900100c007013003200303c1014103001395044c0e40c0c0c150126100e00d500c4003070655240c001c90500384c2c1042c50090010350074503c581c0c2d90f0a040366060040320120642c24200c5803c0110050150890310360780e2034484c00306e00506070a040c0000c0c05000070403400c0c2c103003801c00762600070341000d1009202181007451000d034414000c2e000c041c010700108000359610760750009c0000365440540000d40e4103002c00c3d03240726004000718074200e0364 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 506121357 1250 506120107 506120117
    0x1503070504030f080d050f0f0610200f030a02010209090a0525200c0411090a0306050c0c0304060914040e151308030f0105090f070f05030604060b070609020111030a 72
    0x21840d03503483c3d01180c1500040303429030024004007840c003126008545c0180c1c40440e000300c080c90300c83c43e140c603141002400584104400000c1c1e80302d162300000100050313044209409100c4c00d440069500e00b01881c046074240d84800207048401c90782c198090200b203030044884030450340f85c007201001500c3d0b090b11200c0e8491644111881da02000049101c1240d585013022200b00110715110107160420b0051040d098014400c440391618280c41008114a14004114145002003000c41c0d64288a400020116540c0300e0115030304024440c2501c8501344d5004c100c0799503070380701e00c0010680e0700b0a10403911151004c09660501d858203018441c48004060f0050a00d011100109505108043c09000003141001005400305568200540c4035009001d010001c951410050001700b40c40204444011f00440d414000c080b035003c13001041810682c5015500c0362a100c0000e401481c4e030b0f5100103131540001844000300600c60704078115580c002d0722202d00e1103a001c0700ca01d0726440760b19a064005a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 506122607 1250 506121357 506121359
    0x1f0e01030207110301050a150603180b0402030a211218030e0a050604031b09050910050705040510031b02120901050d020403060e0303090c030706080c071518021503070504 75
    0x9442a80a008000c0c0111441007929210101003821100c0c15500800c0c0e04c2c0d1655100803079824200e0011008080b02c0c070701041080c1c81d801c07142d20460100701008000084c904d01040c1075541c10440c00c02101d40010205450b10103c402d0550041150721407000403500d09100060320b802c41c4c0c0705d1401046182c80ea44104a54641e0302152107042d80360561794002404080411262545c5021b000514841d540c1c0c6042c42ea003992814102030116801441c46a0410301006683d05010801c103810001426000c9081c3d15880020b0701c00340100d82003207412405410420207525403541201c4405102e2660400300c0c150241e42c00c9840340c82c0d444076690261010000c52001e5480f0710f00070440c210007400014201a100e0755850240c8074904080c4005900100c10301c5402c446c240080003220600320001c00100d4a00745028180344001805004d50003804508441402900c0a155040c1103061000b0080c52201d0350048211076504882a0700484450030396501b0801410704680c0221120380701c8608103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 506123857 1250 506122607 506122609
    0x60103020f01030c14040807050f06071e080904052e030201051b011e060f0f080606061602041407170f0a02090a0e0106050423090f060103021e091f0e 66
    0xe840794684810802045c3c030502d03001540c00e9009072002c0c05c40c41000e01161032a0104104581d90404c4046100f400d0401003080000c03103240591011904d003119513021a0111700b0805001d0040b16003d5802c1410801005240c2e8094104d41440194500442034500100c2e400d10482001a00000f4045102007100207103072401070030502c0c01901210b0020a49000801200a000306280d02d06032b141c41d10b0f00307002d100e80344000003240040c0c070440419020180c1f60104140d51580e020308914013550740081e540185a0860405800382c40d000307801800004502e44019440c10811a6490001401507400d00002071200340c016004a910341c01a4451b5101e2045a01c003c7d8409100e20303901ca414072800090352003508007002c0c02410b403903d4894840d032401c1861111018980c1c006144801c400c490120150745004e8540e40110742120f001c0126543d04005800903c103581c880b44889800c440100da9900c0036400805006d0015240200c00090105441040720504202c507800700316010100012 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 506125107 1250 506123857 506123861
    0xe07020606041808070c030c080d120b04020d2306030d08060405070c05100c020d09032105040504020f040503010b010906020d050d1119091e180905061e0108060103020f0103 76
    0x8000010207401d20102c0c3c95035203401d02da500c680c000b111008810801042406401c0fa0a0b41c01042000d001c2e00e4046d80b041002000c986c5889035118840395070300340d030100c1c54840c3d5050ba28801189242081a04400c0000c210380050a0040943d400600341c0050520304011a50318140304468940403601e4075a44100009060010300b5942040342d40d006040c04910200b28026868030640d00008407044000c0001b400e004401c4081d005028034464100b0000d10641500480c05014001c036082511400000711403520030340d0f1061307501c07034000f1944414100c0f42030018000c4910032002044414070b84c1c00191105001482881c0c0583c0180840d903e0840c02a40104491003c040c2c3c0040e54600e03501d00070200c0d0700700f00c2002e5402c0d105540c000a000d80c0001000014048604c040050803100e40c0e0708401000050180d5410b00114003111002c400250300200c2d007280d800010f444841c40c1c0300c0300315000540407192007413104011100010358024081240c81c10303241c016002c0100d005000c0c00540c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 506126357 1250 506125107 506125121
    0x90603030901120b0325060e030a0305030c0a030f1109090609060603010b0a03020906210f040c180b1f08010b0403020114091807050a031104050a060f0c0f03050301030209010e0702060604 82
    0x45c01d40501850070705000396034481d100000c0c085a441d2071000d803c001c001094076010216050190344000e40c41c1010076008416030350300040e520140ca54640d2080400c0300a042c003121402e0f481800c1403000d40149410303502504040506489509895440304200218540c0543d19150822020401805500c00040003800c00000a0a015140c051010041103140e400b9031142800000100b001ca02c20840b0010306503003246054800b4400c90401d0b441d045440300082c0700780340800e02c0310f00310340307403000840d400030403000800030241d012440e1940c004081a01403441042e0004441c40d0010555180d10800d4a0a480e01030396006450801c0c5107210b04d0641c02034403200d81c030944070303818606502602000e280c820703440b903a01d807925030001c107030082c00b610690074034199201c41c2400240081e494001d828030444000307103440c1032804a0a00300751035070f0380c900304054001128191600103040d04403000f54101c0f88203980c2c0c261103aa03103490115851606075001c0005070480b40108450f0b03c0c00340c000c58 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 506127607 1250 506126357 506126359
    0x130b07020d08040e0403090b03070f0e01110102070b070e0102070608010509040201030e0d17331f0c05190812090304080a06051501030605090f091f0209090603030901120b 75
    0x409600000e490b009401d420542c40001524168010401090f5000180500030300050780c04500b075040c4008007420684490080300c042140b43c021001c900e80c41004000300e403128500085543c2c411a0800f0118604110b4482c40401c10a009480f80c075480081d90a08842e600c0d52141003690070b0030300f046102100900164105600c48001d102c200c08207005248042045444082e540c9440c40c91840036072100402040101600e010784200d5100340d51401c1e099012100d101079503040300d000007da5510250700307160b2a03065592500c0190a0f4001c880c4500040c095001c403031341082894546562060200e9005040e0071007800540e003404004e4010301e800c0006c80c8241c034182502c03003400c24503110302001d080d607919132500c041c41003040a8645401020800386400d2007514202008a0f8007407601412201ea02c0d000c0d02c0010f0790485040c86071100c100030589034003c48142d00c0140c98080c2d002080d00902c1115258045425840d0010448410030410307118207001c21400b2514400410510a0071 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 506128857 1250 506127607 506127619
    0x60f12080d1e021206100306050612130f050d2706030903020a060c0207060e04050106020d08070e10080109050901060e0c0c010905030a03021c0e0a11031c020f0c0105130b0702 77
    0x1007002d00300a0b002510340118000c0c0604c000303207040340400c5000c501d0030718503000b03061038450184015140ca2045a64803050f6145150003925214660b405141281801400c10750105d030700c00301003200108408031b64888507500c10114500d280d00080c404614001c820459a04a4004000085c001e40007441e10500900560300342c41a140caa030410740340350f804d50b840181c00480b07051180315080042c079014a03c046c0c808010307660504001130340e20100d03080c100c03060203021030024030381501c43c007083e10711100017030558202c42107241c0015040d90400e0003811000c0d401c0500080002038148a580111031060020f0003d58882c102049075a5100810040a079501c0c0c1d04a1004220200018240b642055400503551003c5004920402d00b00d15001e5095a00b08450b810081c08000782a0600300c1d00300c0e2a00c0c8180182d07000180ca0001290341c0700380c0c8070020400c041000e41c0c02007003c01d1505550425101c0038104000111058032501d09100501ea04030300081c450b103110340c0007801e54144040e00c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 506130107 1250 506128857 506128901
    0xf03041415100807061103040501081f03050a1a0906010e31170403030503151225140a1206060807080309010f05120615040513060f12080d 61
    0x1071401a101214810206000301c541000188020881000140103a01e40011310043d1b0043c0f141d1203100c0c03881080c1c10031680c40c022545140e201610104600901d0081404042d41d03031a040f921007044070750642d0100050307901c40d607000041700116407080c1203030300141c1417980c24028000b8a43c1c0c1702a150054000d000c648860004034094906546000071006150b4040c4c00391610b01c3d20b02080659220714000107000410011360888103981c0c204100d01a1611580c00c460040b8912000480c148006813085c0c0e640d000c070a40035200050f401c0c1e5200e85c1c03480301490b203a4207ea0011a8408441a08030f40c00315803c012510f5504108000f261041c040402c07070b1507071007040a107041c0e29a00410180d400c0055055003c4d80c02004000c0c150100d801c14904049a00c0d000c00e0340c40c0001040c0794020a45140c9188040340d41ca000c46002d0400140080882e00103140c40c2d50003010340e8019070902c58141034010428240078000c0c4000d19901c690102d1828200b80e500c030014084201e10760501000c855a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 506131357 1250 506130107 506130133
    0xf0a021f140f09030d24030b010f150203181c031d04020307020a060f021608040806010806010f031e061104050306220210110712050c0d17090a050a08060f0a020f030414 74
    0x52114007c1d400303003202c1c0c2811b50601d090081e141c0c0c0703a40e2181d1007118040c05642d81098012041c1d908070020540b51450916001000c550a0b59180300c800103124641b00e51841090707000f5a03440d20100f090140c595004d404842071204034802600d43d480541d100003c214002240350304140c208040a40000d802c141c2c80341524540e01803061011161220b0200301401a6001046040c1c01030043d1402002c0725458031144160081d0140000b0b03251110301ea0b102e04041161a0006040907803040307040040a07018480c00700581c02c5801010b104e40500f03c0810000c042c0d01c2c10044080301c10422508a454003903007040903800300d42100005001c0c4a2060a030019400c1c0140c41c0140b80c0700c0700c101030320496403400354100a2842d081a200391798540ba400040b420180c0303a0106e01e008140003c0d80c0380900d00005411500d07580c00664898600380c07000c01d049030b000c21a01c1c040c48142801c0c0c0a5a1507481303624003a40070b0160002c00d480c01c1480018041041c84618102447c0328070261400ca41c1850 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 506132607 1250 506131357 506131421
    0xf060e0103060b12150c0f130e090705040e1b150d140601020a050703031d121b0604031a130602071103210f0a021f140f09030d 56
    0x1038800d4405981d200f11110301c60034003101800400c4507032406004003c84a102152914101409003010242d001c6882c00b00507066501722440d50342c500c5c0c0c0c0183d885981e000401040b00040b61004864052103c0001d02810103000d4500e00d940a08007a2000c0051408012000164180d41d03e41c0054a10526070f8400c004400400340e41e138a2100109860a030341902a41e90307400641440e04661207000d00c800842d034041007483c01e0300c2d030501e803260550391040000c000c500c0c00c40c10b209600806902c1d00394030035000042d200e41003030000c802c1000646410020000c09014a1002500180350714035100d00d0840c9502045509c0308601100c40070140c0c1c00e0b00e030f9600b01d821038901200d51012000061080707203020001c4c0c1c54005490318518405d614091101c44c902d010b41030b170340c141c510004288615a40d0007441000303138444500610540c0c0048801851000d00303100c9030b020324888440d80100b60a06001e00c0803d04c140c16040c004c61038041c020840c0001014405000130b801501c5c2d010019000880b0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 506133857 1250 506132607 506132609
    0xd0207051519030212180312060609280603021207111603140601050a060e06031b2701050405010507140a080409020c01110703020c10020a0204020f120603150105040f060e01 76
    0x143d9801030301c07a03039040c40b03040c110000a04490469050f008408924980c0001103455400100070302079400d448100100d50f01d80140d10b089075000c40c01c1119000d1b814079100402c0211114200c01000007070b92114164220311461000d04508030510b400038290342e0041e030720b0320380b0000404221088100d801e01400480c00c260780040f90b540c000149102d000c8041080f003a40540b00c2180c03201c100e24600240904010758000d440c1d0301a0602200282d0300d1088081007a03240421a03034a15070b12050003001752480080139261403613508481154003525481003040c1e4042d9031060312a586006001e44032800e9846280644481d40e11910310740d000050503c0c40904002c0c800700501507161201011014250307119046410044a8284070b1740c0c0200e40c0c00644261060f00c01d40f203c0080d503ea00310201c1c00c0c00704400e07010b034110303000150114000c880400180101c0b501001c19006035240c110406440f1180c0c1050b5a03400c0fa0020b006020519040d485491031058444001681c0c954406100c1c00600007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 506135107 1250 506133857 506133907
    0x1e1008100902010e10080a0b0d0b1f0806090a08030405190606050102071e0302090c1207120501170a17070f0605040b0c120106120f090b0103140d02070515 68
    0x60703503000021943c00c8080c0741c1951038203c403402044500e040d001460721000500c180c4241d526240524502d40301c040315802c429030003500034001c1e8500080340c00801204002c82e82c5071245038141c001043c8101088850164a100e0042c04c0800c5164540c0c151642010700190743c0f50007071400c629421000c45210401d46480b40750003284151030302001904103511036109081c508050090a076665250410403810740398101c03541030160b00d030007044842c28064403209024450746c8109100038a6003101e0240c2c00300a40b410f042c0b12030380c2ca4071b211083c1da080303c04001a0542c0311015000004901c080c000d1000d151010f0035505000c0d5980324405402070905c02520742c55650b80500051001c071303080c01980010034003205407800c08207035507401b01c14005125020400058070714811000d030384c0381c024423140c5102079030a02400c00385050800035042c00384001c1342c409103107207000000c01c840812900f92161081c2c010f490646c0c5030400748007241101171100c1031034030313010090b5031680b13441d00c4000d00c08422 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 506136357 1250 506135107 506135111
    0x406091d3c160e0906060d14150a0501050a020d08090118150f0e0d180f260d0c030c080c010c02070602060108070b0301031b03140a020112051e100810 66
    0xe2207000d102500c1c50001c0060100140740240f00d0207901c52080d0030b90056403d40e55295200b081100d048010110051480070842c041428003810300342c140140181d020040301c0d044011681e950040d1018401c6061200141c0c101311404030140b800b40828a50100d4503000128000c3d00e00404c141c00001409011034088090344001c9902d05460312072141090441442006402e5084c400c5507600c1400041460400c1640c0c42e500301d203d1040c542c54070003014981121500703d519605680c80760b41941e261301d00c40041181d0328807a4030130700103000b58190032162144291001d1a850441d501c00c02c03403809940321081004580840d5909204401d5035200540c05822014140325000313050000c1a8461400d6501c080404d124600020040700d0460b40c0c4101c1c000200240c0c801001d528407682d40c0060041040180d070304000c5400403c020f42c1c00c92003680c540080d021039120b544116101030318401110b00311100300c02d41c1403210b58101c5801044a84840c0c0c8a01d660320010351500d0072481c0f40e0f600043d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 506137607 1250 506136357 506136361
    0x60904060b031e010e0a030801170f060c0909060a0303140d061a0702031b0109170a14010606022a0103090f0c080106051c03121a0303030108030406091d3c 68
    0x43c0080c441d031141081754201505d40070740309840050050006000b410402482000c0c6104246000c2102d580b1803022001611018905464000c4050300448031080c021601d0304001030141c60300c90782c810166685600c4082c0a1740d121500540580c10113100040c1990f03a481021860400c0311917400ea118090104240da2000e6a205143c10b201030b40b01c2000c09401e006010341a02c0e80c00c010000c3c2502c40440303440c0e215a01c4c800d502071412842c1c44000c1d285440c040c1000d4a404c5042d00b00400b0749290360211001508030801080f0002e0010321802a00340c81c0035a003588a600c6900031082c4e043c0102d00b01d20320b000150f1250b40820307a00340e20009403a03540300c40402150410040c41488420404c80c07a80500e0159180980400e4000d0341c84140726a44036003031007000380c20031800741c4400000750860b503c0b9138440d002c05a680e80180191000728002850000743d801c4a4900b10003150703031075500c1c81c82d1500d5251500000c6035011704101c580f07902d65511508008100c1d440d80284200606040c00720f8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 506138857 1250 506137607 506137663
    0x609080306040b090f0604090201030b060a02071a04050102073c05150307020d0e120106060314011203140a031e0c0e01110c01080c0c010e072c060904060b03 69
    0x60f030114040b03a00a4800d4810451410141801603034421010788001c503e02c1c42d980300407401020030800301d55020070082903801140768002050000e45803480203084001011184000080c000d40c418280181e0010a0034080741c110050400503030140d41c40301f0329070b0340203c200713103001c0b200460a80c05110071008000c0007235207004a0000c0080b031060100a01d90300b00407000940740e60035500b01c9802c0c0110042e110700c2d03544440419600408050f0000c110745030b15190018060241c0c400d03038040c0c054101c000410b880c6031000c04000c0e807070345c0764644030001d01825602220680100000d1010305a0750080a00541080d08818103100020f007c00a0700c81854030000d00001d8040d40103504000210b910640b140310006000b82c1e1000c0d0900386003a1956410384d44d02c5083c82000380d000b80ca5406c284640d640003000054000640304000640c20000031031800c180d00f030a10100950b01250710b90004960710b8282090b00b65045030140704082512007810010900e40b00040c40803058600312a4000400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 506140107 1250 506138857 506138861
    0xd0c020d080c040e0c0c0c0603090109020301150506070b0a0608100506030d0903051216050a030c03020609030a050d0c0522141903140f12040306050c1306030b0d060908030604 77
    0x301402c0350815a092a0828018500313404d0001c03c0c00c0d002007400501034100c5102040b01c100000c400402c40d581d01d10344646003d01910a44004031300960070032401c0710b03903841382c0300300003050f00c00144c1080d0030944aa10f0b05075402501810907a6034a941d22400b0820100c144000c03c19a000c030b90307006c210780c14441c05152910070700d90302c01c40400c01d002c0f000b440062404500742100306031210800d83c4504900a0807808a060a08000e04600c1030040c00c00815801c03000c9604400d0080e000d44115907500414140c49205040c51940068810030040c241c0110715440754181c0f408a00d82141840c522007290102e910150a010726050f08c2c4210403c4010603500d02000030300c0f81594860712504842c80d0b04011900b650000400d11040e10240c0c0100e01010001e10f4045c840d00421103404070559481c22110f54458001911468240000120001b800c40202d42480c0706c500341403215585400340450080084502c07003a88a032600c040708020503480d01450188034003d440320740e80c9042030700401c41 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 506141357 1250 506140107 506140111
    0x102070c12020d030302030c21040b091216240e010b18060f041103070e1003020702030c132c07060c0203210f120a060501090b0f0f0d0c020d08 63
    0x603400d5107501e103401c0182c94104429485550509000d41c99898182c15000c41e4014200b1b03000310f003817888078095403440c941c0d42140d00031b6009408030841520350002c0280c640841d50441d03507124800b044007a82891942c1001d004480c09070078520702d050341c1803109214043c0644003003101142c441c02c09840001d401e101c0c58240f198200e070348502794400021001400f440c002c10701d9100c3c002a840200c6591a01d410000016201030080380c1d403440e00100c00b0740724030b2500c802ea80c0900d0740d4509228a541c000c0c4210340c441038000b4010004d48107003c08000d00d00130b00c540b55684680c0c0302c01f034031204107503488040200740100111100702d0070446d000340c40c44c00d0340e690b0141c4104582c40310740c000941c0b00490138a4a5400c5900c400321001800039107c4030070710859000090700c1d84002082d48001520a24150148902c41c1007801182d0303580004507182a82402074841103401082102018410072004241800110602034108840844076004031425001c6000c0560004002241819402800c050b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 506142607 1250 506141357 506141369
    0x30b10120501061107030b06060d140415020310030803060f0301050112051c0912110a062d0206220b10030201080c0f040303141204060209040c1e03090201110a03020102070c 76
    0x102c2030a120b1040702d80e40300385d1440701410845407040850016210350303040b1907000c0440300081c401d49914500400310000700721406e640001c1c801c291000c08916034022a405240c03c0715507400c0b103600350f0700e440d001c690024052550241c1034450006542d1001e000c0c050003802484000307858116941003150074503802030a10055222010380321120340f030700503020800307440980341d00d81500490740c41c00d400740c54842d2044c2079212243c1000003460590181c0c8070380e41805036001036000710b000004403c40a070b103001e0300301000da004200090900448051480184180c0c040c0000004e056901c0d544040c0360151581d900c804a001018001d5503000f4486a800c0a80103618600c0c1c040c1102229611340200c2c0401005c102c0035100005c24521900300792075480c0c000ca6110449400c080c0b030480c000750b2182490038015401c10041d03007041030040020401103041e10310600e942c081080c1c0c3c11001802400d402301d06010a100c0c180c80140e0382004040a00b070300c2900016900d5101d0b040004034918540d01c60 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 506143857 1250 506142607 506142617
    0xb0f0603070b070c1a0c030301090615111203060109030f080a0807050a1d01030f020309101b050d051e0903180406060e01080711031c060801180f03030b1012050106 72
    0x4a000840c52030840084840c2400b86050545d65400100c55921030f0042c1c41d5024800400003181e142856402802280e0143c4001d0304010b6861074140c4819402028410143d0860400600000301c00e00055500c0750051400b105082d0b100c2e0b03100c410034842d800068480810114980c1441a08042400d408c003566081060074010b1f0310b6801818a08100f040001205906004180d10b0f406501300c0d80041015907000e5440e0714008110302e80e84e000900c1c56203001410b080900c801062500000c0c0d40c007140d80d0703503818545110004800c000d01805040c10300380c8480c0c100004a10600d064005000f5803800018581e180c01d884140d00641450456072413080740f8280c4100440e0b43c1062500703680342c01c282070046456942c20010f0703400d08095051400306020003d078122101940c904d4040141101d164104402910b4942050881704020044118820302c941c000001c22040c0c0101c6240502c21301e800701e01c26042101054072108541454000f281700c40702d9914500d0f05070b001d60340c0944005d280c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 506145107 1250 506143857 506143867
    0x100c0209060109150e030a14010921050d0b0d0c0b031f0b0301051c05120d050a0510050111010f02120103050105071716091203020303010312020613080d090b0f0603070b 74
    0x20412580145002c800c05d201c1c0301800d0701450f440c02d010440d0ba40d50007050800d070007049080403501a0080c00720845916010400c2c40503903244100d0410703202c554a60b07803e410841c3d60481e2800429444001320780c13000c0802074090000d8450000c02c0003030840826410b07140e003800048080c000d0804012a00010b203058006c1c0f00c0d074403c01c0c1c00c0e0703411a14112032802c0c4141d10081c2d43d00b442445503030050042d01490510039025804a8001c2c03031465050b200c00c020721f07034514103103000b00d0b00140e03444540b0560f100b07010442984035590744071072800d081c0300010b440072100c81c014040b640600c4202c42d000b003da43c0100305110080c8903c1d80c4c018040d0030000300c003081813014006d0102000340003805d0b41406a600903a10703445510014050445080c1c00c007220f605070300b0f0195580c0c1003440b007214480001401000d0580c0b01056141c00385800701e45a004501040e81e541c4c0403034010030b10280203036581e8200a80131a81a0140502030704004d0750314141401c0141c281407c0001d0b03504000e81030b4200304030b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 506146357 1250 506145107 506145119
    0x40b190905060f0f0702090f01062007050d1401021615021306081b03010308090301150e31060b090a0b010e0d02010504121103060f060105071202010b100c0209060109 73
    0x4031100324100c503c2d00342c0c0c0d0313561140016089000c0d450b8040e400c021003074100100340d820300c8072143c1039a00c541c840094800070305034081d04d103c2030080f04034070035000000b0811050805100d00a600d030710070a44040c1d00049440b9841c220f801c001d4621084504003d100801d0015142c101d283e02c2c155120305518007000f8602d040c1900400b41700715000c22000340d000915035102c007250758000c2c071910307101103603a5692030804000c0b0342c014614441c469480c0000c1c45821a1518510074119441222460225911201d41c0308140980c0700c4800745110901c07a005d540d6a40c00403442040500c0741000280e002000c8091090201000b000000310524041c0d9070451680c10090107a9810b00488000c1150602c51004944900542d403201b00000c1c0c1004821041104118410b0314044040c2c044417503e41c0c9030011051194025251540426810810200410452801544a50780c540008150000131354042074110060142d041c0000c0e0b60b03560440c04501c1c0080806402c11001d107007258100d41080 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 506147607 1250 506146357 506146369
    0xe09070e09070216230901030321020403020d051609050123180f090105060d0305030613111605150103020a0b0c0106090218040507020f1b15040b190905 67
    0x510914407421000c000200e206208120109110810207404014180d4507942c4910725110b40400441800c0c0c0c02c4400301090904249560403a60955103130021885d48009031003145c03202d150444800c0f5002c03c40440075807140346000007550301ca4401411705032801d02d0711005804030f0350804028036051500410540080a600700340f048803030b10200200390840b1000441040f8084c1c1a8404044143c041081071000303d0340d000d225101810082c4525a54070f070030005041d0410350300901246050020510354140031080c8070f4000c041c2c0000151840075440d00c12119048000312404802280c4001810042c090000c81401c0000018203900355065500080c2502c001d8007400c50108400310341c840260a09403c11401000c2881046541e8010042000d2154140e040464015400e110214850394400104402e511444001400800c0f00c142503055107000ba050075aa03202080f111050910024074004100402956041035510311303410703010400300c44009140109104c1c101d5010001c03901d400e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 506148857 1250 506147607 506147627
    0x314010603020f10031d032503080403121d03030603011401050901092f04030308060d03121107060509030403050610030506070819020d0e0c0a05030c0405060102030c06100302010e0907 81
    0x104c0300c146900341281c9045000301100c0310700c20110101c55a4030a00400040014610502e0b0941c4041c5c03880ca40545100510034000300060000e82d00400240101c1e20883c441c0c520001d1414000c00d0714000c800701000c000090310302800c195040042802014a001d11840c01c6400c02c0d0382c0c5584d103e624203030005001c440c0504c5600e8203240c444560048103480e5003042402100f0704541c0e40c40304d0400e14080e0f00d55030041e010490210344034001081c3d2624241c20782842c115410764030500301003074160310038000c0c150451030043c510500b40102000100540122481800e40000468a43e807460500034a0719070058013622640c0c0c0560000e001156000c07a86603801301e10b50402ea04107482e40500b203800010340401c0c80c2c405030320106900c1842521604201076814541044815401c40003040044d524028491160300d9449514210340030700301501302ca0703486141401075a04201c8582505410510100c81002d007000c00210103104540c1c102ca010700b10070792300b0754080c405840d00040140a180c04 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 506150107 1250 506148857 506148859
    0xb180a020312090307051203040515120703090305040b0d050406050c040501050324130903030609020f1806250506010602010b060307110c030d110f0d0c02060706020702090408040314010603020f 85
    0x42e601ea0076102040b1039001400e01414a403245c0b07468034501f5840f034005004141c841e505850201041e041c50750240c07000082000e0040809448800c802c0c0c00600c0100d404505001c01804005614480d1102038510915003002c08903243c0340a1502c0e0003141c10040807414181002d00c0184240c0c0da0120540b9480280401403d0042c0710492140407041c407182246540139401450400c0c4041790343c1c0140411500ca920103000c0300740c465805400707038010500104c4151005001010102505c10300e10a0840000780405241c68032000103a851010352030503110546140143c00700401c00100f25031801000544001c02003613044400141d42172102801c40ea041009081202851130030512065483c400010101c4080c0215008040c240e244440751161045c0504145010651030200311400d1010141d80d680318000300c130342c1c00c00c00039401181007070301c0e116401c4c00018010303103030b6040d400d0280340034158040e103561841c644884884002504e019050341844010401a00d07442058100440 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 506151357 1250 506150107 506150143
    0x603230106051c0504030f0f0809032b0e010204030210030b011704082701030e21032205010219030e330a1d121909030f0b180a0203 58
    0x380c000e070143d500e00c1c1039030508401031610041c00109070b04480c500028018a807180d00f1380c0400782c0c1050703401e510125040022504100103540705e0880c0f09140c8580702501c04541b07810302c03289200220072104c0020b480810350f0341c005000e000750315141101c040c4414580c501803000c9407110740000c00580800b03007010b082c10104400b09040200d004140d0344100c050003840251007440110490580084460080c0401c0c035182c1a480890400b0031541c1e00209020603004000c0d40c2c0a4803030013182d20045c0209000701422154000456041d07000c0c800c010301900c0096151461009500c0d01300041c40c00b00002e040c540341802605510219a0500808036101602c0100208400f145000019074840413100b44015040041c601e41c47d0384070400c02c4903000d4a160701d02d540050744907074030291419120314000060015601c4400c0310303003281d5100d40300751030040c2da40c50340c0381d555050000b1410002c07100b64506038204131944500c1c1c62079140d194417680091921155907008203480d40308079038002240103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 506152607 1250 506151357 506151367
    0x6240b0a0e0907091a07021513080613030228060c1b05011505100903260f09120d0c17091009090b010f0e120a0b070504060323010605 59
    0x381c0070305a01c589006001d400e000140c9412a00113001d0f0f0784a0240b000280c501819503444070821406a80e08030750f010305001944241e002c02ca8000e9005007030408505480c81001160309901403041a0088014451108461916107000f07400e004181d1a00c0e02c0355801010b01a400c030b05c0440b5200707022a0082c1c2c1c0041c440070035550881c0e511203502812031003000d00c400e40070200b001c1540f08102c40004101c0000420b0b40b02c10400c41c08030468140440050f0f5184400e00115080c44280d0340c013094a80d00301b68680da000081c0c1315050304405820000740001040045003030404440b0600d0795416200540030000c84000064514080d2010151501d150604a001002076400440741ca50500070001e110703101d0055801007080007103001e01c032003040c2054003220155000e26241a409001603c4412110a401c0d0911621110140b40d601c10352154022170b00200d100591201d008050301d44d103242d035072428400040c0030b864008002d07102521a81d2491070203d03c042c15042d041d9038062034500e50310 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 506153857 1250 506152607 506152627
    0x5030610120c020304060216050108061c0605101509050a14040204051f1416200405070305091608120715020d09030311030f041101110f0a06240b 64
    0x8180302040000c0721450549240c040b0358000002d401140c000303908455424400c4200d102c02031070300c1e110380c60108a0303207004141d991a0a001610291802c040d0fa441c0c41c0760151900c5041d100241d0315445e0003012580c050110b690700c0400952404454103056000c00d19260110701c0427031246c8204482e0a803041410305240e40e86404540044c04007c10600d00c1f00306040c83c082c1c0301104000e01c1800300d219000418080e989500c00c0d103115140c906402c104040154440780310111172b5040030141182d030000030045641c0c0e1803103000e0107011641d80003d02441d2444d0050b00c0d00314100c03014130030300c5104e90040103244400901e20f014110300c040015110911413514a5102d081428940461400401d4000310b07001d5a0340101806030003507806200c2c40183d8800305132544020b413107010b18160104009400b04900a40314080050107160180ea04000171203100d040043c90344859034140c000d11100360510280303014030440542910860681c10b444806400505001442510035a5901107912100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 506155107 1250 506153857 506153867
    0x13121401020a0c060b040605130c020d140d2003091e0a0c031707021002011406010318020f01140d020c150f042a060201090c0e07020712020a052119020105030610 71
    0x200005482c2003608003274041c144010b48071240e00b500061190001c0c41d02200c2c8561030b42c00d0303181c02c0c042101d4600400003100c40c000d00110301c401c080411301c45503085150310300000114805c1c40c40700007509580901d07280106a4a0104510100503030020303400d0400b00f0162440182201c3c2c2c05444032503039843c00360821190340680c043c040e50094040c4500c810b61a0117400c84104c0142e1043c40f040203940703d800540840e800b071030003243c02c3c0006140031001401c294081a001c030805040c01c4105120401c40107040341d000b2444440c1d0303140c02013102e80c0428410025031101d442c0d507038250021403034068000b00034080020000740140c20300844c5070103602124401030108044001403654401d89680c2e010340a010014411161900318080c0010001a04020380d4080d4142e47c0c042c015061600c03880c2490411942403ea901c040642c0d000212680c0d4454103442c01002400100f1083c0e000341262400c04a0052480307002c2c0c001010704100503031f4442c04480d40030404a628080321840c018003103038 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 506156357 1250 506155107 506155109
    0xa1202030109082101051c08030603010b04180b01050d17031801020a030501151d040b18161103030613020721020313080312160513121401020a0c060b0406 68
    0x40090b00082c02c00e03200e141c2c15035007005031144404d400c1569030380f50b042c8424aa58085201900081469400f0000e0050340c000e50f000a4010004546001c1c85000034089440c86405420048030440d42201001030042c03505004040446102a240e1006d0725680d5114007607001099051100000141c01000d10825895540034180f0085446d4807003100702500424080c0542411030b110705c0740c3e4680d40b0b031040e014601c04244140a40c148122a003040c880901014040d00b039001d0301142c4800b00800040416a20504101903001441c0f501808003508030540400718a00e10380080081003850b444822032191810802a00142da41d41c4c0c0741804006038040104503500390344150950240761740d002000d80a07054030810f1035084c10765180c40c002d5903807103511041c8200005620010b60b0340710b001001c1c036000040d641480c034a041c1c46040004461610385e0840c031028071340c005165050000d80c005850650b500d00d402146802d5441d54003030034080320101d00608403912840200900c0d220f42d0002c01c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 506157607 1250 506156357 506156363
    0x80601080a02240c03030106140901020c120307022d2b06060305010e010c080a0b030718020f0309010614060703020a0b151203190804080a080703110c01020901020d020105060a1202030109 82
    0x150700c5506013420181c5135882889030600281164112601c461420070486807258016001001143c10304000e100c08800d80303210000c6240402d100840158550100e0f82d4126520801041052980b000a5041000171118103a0080e010480c5281c1703845041c000c1044003590805840050b1005480c294016142942000f00107508040000d490464150014515120709481d4102307a41d80310411281103803410b180980d03143d070100804020198914010702c107640c854030400740c6410604180c10203117034010f403810500c680d502c45041060340100302a001d540c030b4040710f4152500d002624001c0d41c411400d580540508408000320340c0615164010681054024013508601c4200805c0c403900d9400181c0d001148001c000d00c0919824840d1411520030ba03400342e40f203030501d0340c400c00855140301c00421036000e0694540150054902203009401d602507200009a62840d0b00c1d0002401c01c61511524015681414107019940da94000744000395800c1d1030b144c0c2d4041d040381c00040d024160900001d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 506158857 1250 506157607 506157679
    0x50a0b0c0403140f100203060d0f060f061d0702070e070302030a0e06012c010302030d0c0312051503100c020c0f0301020f0a110d0c0b0705370306080601080a02 70
    0x1074101403c0802c0e40320081c4014815941e1003905816810301341e22007105c1c2681d00a510b02c4180000031080781c001c0300c143d4050100000d40c9480068440200c942641180c6400c1d4450707211500030890f00a03030300d9405a00740c07024001ca18944003041c5a044405001c110a240e004400102c1d072003c07507804210345e150304034111005569940c02eaa0403015207201480e10f103407451140404086103456240d8126907000d8010f00150016407800c03241203100e0384084040000100c42e4a100b41114083c250082c5c401c4000c3c50020344001c000c040c9040131904c8100d14072410061815940d98000ca03400701e5600090702c5040c0301c6c4000000003070081c0b084181404030043d011036030408882d800b001007003c0729200b00c202d800648008030140c42942d200800140303411004800100403500c80e03005846140c40840c0c00c54900002031111300c8085042c0308540c080c09070568009540c0c59454081e12000b411940301409055040003800342d180c2c035050b07001a0007481c240142406031010840740b4060a0740054072 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 506160107 1250 506158857 506158883
    0xf011b0e0310110901030617030a0f1b05100f0c0f0f11100902040b0a030809010e1f0c0309050d0c0b0c0f10020903010b060f03150f0415080d0507050a0b0c0403 70
    0x703108041c1c01804e507540c00030f4030f89100400c040751a07001c4000304070070385c9000f5810031900c20383c03c842009031a1100403c100d1000303c5800000c0c54042c070362143d6403058000d40039003410106010111011522420b060500f40740d01c0d0086280c00103c40b644a040e50301d480d05034014518019141115403030701184031403050441a505203000c980c04070f00000e100701c82c1484051560300c01c1140111032400003130300b010010071441600358050500b1402260000d484000740c641169107a820042002c0c2d95400170606007a8504100340c1d019941c0c4000c0d200c1225507010801d07440e203801a0415490254600c3c1a80000301511a40710800a00c8041d0115a0840318400d241c2c440b003101039003192540501a6090241c2e000300c1d458407600b9100ba401610080900315924950381c4002e034024481e01d1500010007851840082d2181c0c0280104240a049100c03412490195480c0c07500404444e0380702004001d2001c80000f1b240402e262210300c0c6c00036551041503d400014502a214640c401082d4085042c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 506161357 1250 506160107 506160131
    0xc01020a0201110405102f0105100b030c040e100e011e08120a0809070e010f031502030c071e05070b070b090102030f04020d0623221e03020304170f0f011b0e0310 71
    0x18070910308810756031380b40d0340d4034081c0c0e2000d40815100d80300c80dc04240710911030b0044007056280d1101d6841d6056802c00e03500c02d00810703001000e07000013546465003070b0134034040041000d1040c001c1c60038800400b101e0881c610b4100f814001d0307044401c01c10002c440032903651101001444040c0020580200065a4a0303502c16804010352100702c0700c013803000412810910a80c400c0e81d00c581d5582d10214a088265615001c040d0080c0c5010200200f0200000002c60010800b0b5400703030000c90040c5544046604000f04009401402003005a004008000c0350481040c16590441d50548402c1d09025051420101400e056640a20004c42c1c0d00b0b40c1809401968182a0282c44c0160300e21400b4409074407100d000343c94402d0050708003080301000f2590354569945144020340288140c90070b054440c0c4005990880038400d403070890b84000010440620140589509818514020403404040005411169025454000500424211040560f00c007485912610140880b0402240b11556 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 506162607 1250 506161357 506161361
    0x1418150a080906040507120305070c0b0c010b030319080402130207120e1c1209090609060806010e040308010b130b0705280215130b0c01020a0201110405102f01 70
    0xc0011000a8064404903207084400710f0342a01664000c0040e1000c5c03810001a00100c1600080450400c641080320318049240010035601074a48030f1019036803803014012942c01d41e442d211400b882900100b10300d03c0d504000100c103400e01c1e02e40d0709046d2a5591a400020074000d05440b001104a00006100d81045102590702034200d1498580d03010712000c00080c4001845004240500541c203400b03010003040d07800401c451807143c50701c0c04103101c50315002d0352000e030794980d80301103100f030b031600402d110168052001314050400009406003030328240c4c070000c05554040c0306040900b100005d01c4105083c0c00017000c40581140d07803030556034078050300c1d10b0340c0d64880541d17080c80f00b00040d0042d2500601740004030b01a29070020300c01009102c1c000024401680840b80d541200003600800140d0f4060100c06065034a5003500010f0303d1306014070001e801c0d43c41c0c900c0382c1e004403c010041480302d641e4003162103c550b0700394030b400180c40440100784001d10000b035a44070f001822403e018005a0815 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 506163857 1250 506162607 506162617
    0xf050d020114070b1f05310e0705040c020607020a11061207120c020c01020a03030f0b0306040b0405010e160603050403020106180218120601060804080d0207030e010816141815 77
    0x3c030103078040c0301714148004c41003103504d8003901d030344840c02d008041c0401007030783c2030707941c0b070518040329110002c414030302070011552040407030040d41c0c02c01202040585010300c640b00e81201d03a400508200c3c5840d0200a440c0c40c00544010a206941154403104d511540d00f9544038043c0550f51294038200240c01070034200880d480078000600300510001040c2c408105095407043c10b0700206904012036030194040c0c0a0010501040c5540b845107403a01d0350100302285c0640d00a10100c9a0b03030505040090942d41540c000d1310041c9e01145000341d8040564070700500b2075030396250015407900d5071700d0b00702e024281942c480000350306580c1c41049522015801840007250100b032a5001740c0300103048c0b004165031004045001c0e04040010040702c1d000c0c0d01803e602c00d00c14900780d441c1c01c1c0c02449070780c100c0c1c010000c29800262884000300305941c2240c4501d1300048030b450303000c15003d4645801000c03480c2e210340700d00c089140070520381807044240d00310070440c8900420119800781c0541c1d200170f10303800c1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 506165107 1250 506163857 506163871
    0xa0e0102180319020a050d0f060504030c02010908060105090402090c090907180509010f090507140309060402180405060c09010c060f091217040210120507030501031b0f050d020114070b 81
    0x50010070a030a03039010115099440d801742c103c042d410304d042d04000e445003103036070265400381c510141100051210b00c030780741c4100e01c60303200d20b80444518000142004140d801562603640205c00501042d030314046200c1d44641d044844207102c1d6039000418500340210307135100350010081d0091160540d00482c002c0781c1541031001c0c00b150035503145d0401a00d19400e1050b48021505080c0600c00000c040e08071543c4042d06040403100000e412411100ca40c0c0304403421003154110100f0701c0210701d04684c406007002020300d0a041d89050a45072251550000381100150035000900c071101c603409042c4d0002c1282d040030080220f9405400c40802800c0900001c545081c0c0200054100c0c1d40190320b40400c002e60241c0c145660368480d401e209500c40741c030900c10700b480051721414010300c2440c01014800e0f141c941e00403640d9451441c103030060040741040c0411082c000d210034084404240004403c440045501c50320030013031400140c55403c61088004010034002650300c0c2808a5618658083c01d5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 506166357 1250 506165107 506165113
    0x2120114180304061d12070b030604050109020a023a031b050c070e061309050f07060e01050901031512050304061b021f210e01151208030a0e01021803 66
    0x7051010075a120310a6009003c086103000b41881100d52510304480c0b0006805000580610480c21250f40b0349011035004014402c000800c01280c2d0030030b80580e5004282940c0150f040040750540a525031240070000d07411401c2c181d10440b02c0384804501c0544600d10b05c01115800380c1b41c044000c0103064850245000d900c295207400c40c5036031085007114a94081c96002c0c203100713820032b413448400c2d170b2004c0c0c1156400006030008030b60401507480b60f074124910a200800f60358000500300d60402c410340e4800014800c0001d0320400992b040310071902c0c40e03102444d00280c0110290520711204506402036103004040c02040c40412070004024429901691500303c00d240e00c01740130100700b18603c00000d42203401c02c0b13181c542e400e25144130f00400c09181d00b480c2c3ca140c171f03100c0303012184c0341e0803011400d10060b04e0721120038142c0f1f000c2c03003203150b010411580d200e43c1d2801c24401890401c0500b40041c404a000400951079180d9507002d08200c004140c0295600c01c1184980551441d0194245102e80 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 506167607 1250 506166357 506166391
    0xb0f090a0302061b16030b01061d0306240d02210f06100501110c0a060332010906050d050303011a161208010e10090c02071d0109050112030206040f02120114 69
    0x5c6a1402503204982e80700c0c508038141e03070030202d0443e0b900070a69181101030440103c4041c441d0343c10f00c001480707503500031350044840c0d10f40d02c160b41a1141034170f1424000e5900300c003420056112140c2002513007040c103e5503200c0340040311005151859040c50341066000340c3c0c041c00381c24420b20700c1c0b45003142c009036910103c8141d070808241e21900c120305800d5002039040340c00c002090091704103181d214403c0700c80040c0c038684003901c5505805103c0040c5c0c034540100740140452103e034440c010150606403807070b0070040744a03070b1441d03540d21041c0280304504034103d401040340754081d4212201015126035400d082d0a0034a00942c00388801d45050300403c10420000c151424000725451040301c100c0c40c02c8407841e2510b0303111001480f600c2501011401601c80204402e005001c00c4150300c03185520044141d0b15141070082203d5068000c59440181c290403600440d500042c81a00250041260f6140030f0040c800582a003212115006d00ca50a200c0703d2000c064000160500c10041000ca0014078 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 506168857 1250 506167607 506167633
    0x20417060c0f091c0f030f030e03090303090d0606050d120806010305090a0b0421050306040f06050105121317070b160c0b060d2f04060b0f090a0302061b 67
    0x50702400ba40c00000b108140800b40ea985005544d05a141180120303c00b0700800b552220018107103800410f0300803828216105081a616100e07662484643c58051801c22502c1c200007a124415012014803a0240d1410402800003a034012002000c00170a01036088685280100940c0c0000c06d00a011903c8000068915402409074522804405000d48640d90326541c85801c41000500107485442c000340e981064200d80b14000480440c2c161180d07626450103201300000c1e1211194540c204a0400c1e03005c0059036003140580d0780e00203060b81740203140e641d6418004c0b100200600041d001d240300704a0010708800c1c10307005140d218011290034540b60f440c0f800f9070b45003081103600e03000010020b040c038201181140c0550340d08804010500429901c4944514511402e8400c06407191501180701d2a440c0411480d4050419002d403000d00c802c6141118011440c000d036802100d01103000a880d60032a0703244800c0d03034080c5a005200c95280c00407441003412071004c41c0344c01d407214130909585c0185 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 506170107 1250 506168857 506168881
    0x7090b0303040e060d05120d0e0705060702090c030c0f0409020903100522030c02130c0f031e050a1e0507030e071503110c0a03050703120507020c06160602041706 71
    0x30b65101015000c00b0740c8840e13062140a41d60f000050758a07008040d0703659003014040d0010440140c2100b804521f049420f204a4109026988080d104001c00c121420050b2074041096621894642149403250f50703100409d103440c17040420301041e400c00010701040d0041603501500000d54103400b19a10007200030340e0383d411141c054800b00c01350080341840011044091462241c0c0038401d15007046e501126034040b40c41303e209805007803601c0362a01080d0714029400301c00c0400703c02c090325007030180d403482951440c50382440482e800d030000c0d1907e0000710800c25640040581c2c82d490405e1040d81201c03142190020300042e10518002401c0201071070405100144000a48890400b1340d03a541c10312003801e800900044405280081051081e148210014052901c146002c0c2d113501d1f6666146150082029101c084502002c138a00818051030039400205a03030301400c284c492682d10740210b21306100501d450300000f004140005400301c1c200a10800060081c1c2810f003c8480984078001d440d11 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 506171357 1250 506170107 506170109
    0x3080307031d100b0402040306050901020301320d032f0c0a0e0c03070915020304030302010c03230703060b0a030f0c0e01230405060d0e0f0106081203100f060207090b030304 76
    0x40a903c20740d0f00b0050b4080c0c541c0b0051007250010001464a552a5038400541e01c00b2076114011365800306c0100a00b8404480036502d408420726640b52456580308098608180500140e001d10321202213842014090103400c1c0c0300340c4080118070081408140c44051452006c0b82426150042c00c00485040c1862403400060b1030701c01c07200c1505135980740852140b0341c01c010805020072003d2800082e000100452400b0b041000e44c0c0a10798890035414064207440f0f8440713610081519104240030403003001150030302807001901d8201c4c856280c910084015201a0304158078034000003508040c116015402481040c5500c181804141103009081c0c4128240301903031400302d5214080700742e511611282c011220800b42c4242802c2036110b0001c84c100303402031008405d406039034540201509404000c0b00a00700e400c48001e000389070506418540729503a141c81e0910305e00b40800032810a00b4a0301c0c411020b45050b440c841d003469036500c4000d644400502c80d1700c02947c50100312010a09010003220 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 506172607 1250 506171357 506171411
    0x13020109050a08030a050f1605030d05060d080901050313060e2d060612010915020a030e060c160201030e0a0c0321210e0105010f0512010207050a0308040f0803010308030703 76
    0x141003142e0b0b100141d42071f41c4113900c1200320400401643c1c200c00c42061038061180d0240c40150307211072050178a01b049801c0a0322251154107c2452040005d80d89412544541c00a2a14035180d49400c0300c03c540016400d14020b16940c109000004072100004982c5030300000001d05071182d08100400d1402c50f01100403910702c03a00104001110313420905c480c41707080b0080740d00010351031845480702e000c6000c2c061f01003107070303943c000805002641c0d1500071302070341e0007160002c0c0c00e05090401c40ea148911910302180c20340c800300c011903c05d680c00380c0d003c8124140940d0503503032495030900d01602e194005010440f0200282850030b10060b40c0c8151280e0700b4144c50700c0304040760303d40114488001200d0f090701002c107512020001414503080c01807030b0091000c5035000e03640328106401c1281c0d100018107003001381e130320510800005caa00050128000c03905170034440c141c0e46031803c020641c40c80c46407024100302c0001000108010441005600c103240a507000c0202410600d80a500000000004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 506173857 1250 506172607 506172613
    0x406090b18160f050d050c0405120d09090f0906140906090312011202042310060216090203060a12050d0e0a0302061c0615030605030d02030a080a050601021513020109050a08 76
    0x1070007864054640803c101c0100c1c1441070401c00c600703483e002501e00880e0f0002411742d01040070800c606080034241c0f006130b0b144015008200c00c2001c0144000058490300d89050380310040d88040a401d54001e99035160016030034007800d400c0300110b0200c90802d0360340360728070300c19200080e0010342e000c01907810760811080e8a403003d900e04510300e250319140c400709a038403e40e40d0002c0305000b40328001107801044400000d0905241403200c1c2010034100c1d0b40600290b40180380841e0180d98001158800d66000201c0140c070b0380c4900c07000c5004411070790424407000d4500722350b90703060100008113070500796048c0e9507800c1403181c41000d1000300700359840000d401034018483c42c22408a0ba070030061101c0e248440c00200141d0300c448140e08140c1807111840405e50306c040502c80c034103050108280101c440d000440c0f402c0c6940d00000d188120041950580c50355400104000303038801d02243e9940031034203040300140d0428a0201040c0b22a4110490102e98810300002e90341c02c1c000c1c110000c5607109005 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 506175107 1250 506173857 506173891
    0xc0d090f06052a1e0d0f0906020309010c150e060f0108030a0c0f0201270519050306042003010606050405031c0f0f1b0302070608012102010302090f0406090b18 70
    0xd5840d203084100c006500d00e000d0650181004041c03220a001000300c13000040455684481d805010101291207100400c40076000030301641c0d400200f140c280002c28a403c02c41c642c2c0c141080c20203040c002c0d81c4403c002e070610042c900c070528001343c1e1501400301004156856640d6580095980c4260084440030070b00300301c1d1041c04910f01001c04820180103042c11132500340019071500201d152041511749050a2100c144002d0914030f40314408000c81d45e401001c9541042c0c00682d0300d201c020402402c811006821a6262440f0810344042c008060000c1c41060303190b040c090a10b030498050384c0d0180c85411459081e1400301d00415501040b00d48651074072049894044035515480311296003803200d4038450801d6600703012522000107000b5409440e00605015008105c5a01039024964040031000b0f405001429034550309041039090800503514800d2030085011a5110101641c0c02840c101001070071072a290403401030904121111100806542c131075440458058441106100240c04 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 506176357 1250 506175107 506175157
    0x20102032212081906081e0f0c280603020d11121801090b15030f0f030a050310050402070302010902090703091502030c0913022203051c050c0d090f0605 67
    0xe126600005111940148084c1060041064800d16131002d4196404415600c1e03d8040d07038a001c00f01850f0900240c00317130342d29000005656010b550880341c442d611250344904a1041a8225416440402020010f80d83d41e900c000d002904210359036408103007083c4403144400602c000b2076440303181202100540da00c4001300c0d003c40d80d0b4010261485503688840160119840c0041a80300f040f4421181055103000410325080881307000d400042e603401144001000c1c203001c0300f60781e140d84140c503240b03440ba601d880080e0b6900000c2d601050b00315100062841c24160706402c80301d0014000c1d141140c19403a940821000c82d06002c1001c0c0604065160700d84e00800a84c00840d044202820b0007410305107848001010b41800110400c20154001034050a4400d807614180c84450714010603a0f035640785413240740e141d00d4030085070b0124100030304410b046580540c0941e6102e036440c07000c913001c0314400e0314041c003110614014061410028140010014842c00498529807020102c406035406100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 506177607 1250 506176357 506176367
    0xe04080a0c080d0204140a091b21050403050a02011a13090f020a2615041104110a110c0a030503040509070c1a0f06010e030601170a0210020102032212 66
    0x940d040b10403070000c201900e2444458000741c0041c2c05505c104405018001c0704002d282000c96001c228540d050031480102c08080c01e80c88805801030b41030180200002d1990105803154410140101a01c1d14003440f051560110141c401c1c400c140c1c00802c800550f841b0070611001c503840c10903034003440c25a0009a811943e81000c0c10a078407401040c20701e20070540c0021404500c58000050040102c1c2c219912070091480f903c51200740d40014242c00c200c440845121060024805002007170007460710121910340d40d00c0320103041205030200f034590300b042500070040c2e184ca80301e00449108d1684541141d203442941c4504490f031003802945018902020f11152480041810702481107554940c40803c02413840c000034012121603000651901d00b03050201c40340b028100d10704001c50740e454900c0c0d5890004000741901c065000041980e82904820741c60b01208000007504114101600085682c0540241d40604001568000c070705485030b1169498520081010f400079001c0c901200c0351034090 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 506178857 1250 506177607 506177627
    0xb130b031c12050c070c1202010e0d020303090a030818040e06041202100f09060f0207020904170c0f010b03120f041509051f0801051206011503180317010e04080a 71
    0x604001d0603801d0300040190843c0d00490340004144400038914007085130710000b8201030b215626401c20703110701a0300000c08111441c140d550041c48082400015541c00304291000003800611800e00e1645a103400c00c201e402030580d0086110f401c1280740094a841c0c0900004180d00c2c0008109030766440d26901c585c0b4410000340e00550180201259085405d4003460010605508010840307000614011044850a62180400130b10501c407401c0180e031502ca40c103130441e401040d040c0d402c0c40170b0f0b070a11800d4801c10b0320340c50342ca10030f081c141d03003010006411807000000110b065030300808a049400700a40b01c0c0e41001012520100424490b64141d203182d900200000d01c0d0032130009446401003210b000901c070062103100b500c84041139140c0d52010b000d40c05054151280141036000b000c2140e51813006016a80406071070750740e00c402d014404d0744001210034001c6409007245806080142c4441c412404a085044540f0000f080b0b110814000c4c50280fa4450a07072031a041240808a03192010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 506180107 1250 506178857 506178913
    0x31710140312070b1f0e0708010914070e0103060f06080103020307060c051c02070302090f09101503080f0f03160206130b040f0c051005090a1a04030807060b03030d0b130b03 76
    0x95804901e00e0912100c5c02040500b013203031b80c5120981010203004d481040140d0009146d1801d00c140b10301c0d0f503007080701120f81103144c60510300b507040114401640a048550442004081c40100c00501c1c281d1059505040764001c3d01566200340e11703048101d070480391600015001d584520101d21046804030751703000700c182e09441a225005d40700d038009801c650050f01c80040b0041c480d800c0c4108484141319100004920100c01c2000d07001c3e200714401e807040c080c40301815001e00481c103c03500010450440c0c41c240705040a080c0d40f4680300704000c40850365040b0f0030005200365000119442a204202c110341c64005031199040e6489503101c40e0b0000060404482c140c1103080005425180c60320615a40074840c0c640d00c0d00e50f51084203000110140b40c4c4040c1c90b21682c05140ca09402e0040222401d4942003001995a409181400303800303801c7e81503600d070b014440090b01080c12210b5502c00f003801c6204848007074140400d18007401c1650113442e11107616400154160018030305036116503039000170b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 506181357 1250 506180107 506180131
    0xe0105280c08070c1a0f072c04020f1c1d0106050a0e0402120a050106050411071211031c060609091a0103020307021204080a03021225031710140312070b 67
    0x15110170f112101100b500d81c4980074103168207000d2815000703001143c50300c4076600b0107069400340e0b118900004807180d0714140281d5000a1060070b82c8214800c8400505143c41c2020b64070050b0441000100080c4012400b0b1180704680b015a4040602440b07048440040c911443d150401031003900c00a0b02a0040b41d1200c04005450103082041c44035101c11402000001030765882c0209100560b01c016991490300b60017000030400040d6084140c08400d13030640b511800c0c00c1500d8207003034034511030606804000c0910b03a4821803141b045411017010384202356180403215646403244020f440c000120007030ba40c14868102039183d4480c0d40074540c4a029841107981c8440000d400300d103c0e46c02034221100b2908040400b105140c3c040203010303400262940f0541c544184070602d45042c4000c2412001d0503142905000180351140c20f003a24031a40141d0640403900b070520642c240b980552003900921031860200c8050b624010030024156822642903518089a640d00e00e04d00c2c000086c8503204046e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 506182607 1250 506181357 506181383
    0x81302100309121d01050a140c010905070b0403050d031112090309180105040605031513080f030705120a02160b06061e0d05090a0f02090402040e0105280c08070c 71
    0x1500300566003d810006483d0780400d07021030a10540080c540f46950b505118042242034480344c4c0c1f1000540404c500c15008544565814990324050201454041d00a100d070382c00200f540080fa800400c101c0b4814801c403620181c001d1819400da42d1600d0030490003083c00c0c4810903003003890104555200d20030301c041d2441d201d1040000742c206005100070245000c1c40318018885800e0038030500d4040c1108500600038036802c1600e61990500052130b242c5811801c000d15003c00191005880c10454071601b0705440703250040700140305401242c080524440c0311070214030300022038822181c5121405859420a1103680c4034201c143c080908002c1e00700b9070410103041002c0c040524162a107602082c003603501c00307440504909540020f0703d4072160350040341109000407032108543c0c051a505031442c140341da0f1a80001801402c902c2c2e005003065080904012451500c01c07040020b6410f1036907008005c1510b0341d80c6808039200b0302c0c44a004074440101003903505002d8004203071341c2d51249241074400 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 506183857 1250 506182607 506182613
    0x50a062f07060e0310021e130b1206040c0f140a141605070608010806060f030c030d110d0908060718031406010e0f1501080a0e0a14060106081302100309 67
    0x3144603580100000b4022a103c2442d92130284031603005152511400d5060611191541d90107120b1022081242040080c104a4801000c0342e000300400c500349180307449e00701450003001115411a0300c40d11036032400000c7c61100d4040d540d41c0325007682c65940e021800c2260483e0040c1a84095188014030010344070b0030901c1000b140060105e010703102c1c01c442024103a450102e18011180e0061000e0000e408018000c00c0c00000305241d0000d000c0b03455880400c0c204c40070a007029450031085805019180000000300c1d00440c0040d40d4020000440f055070704000300c125005011030044500781d400420101e01410701c1413661809c5c04149401109144e80eaa0703072042e04946500107030210703580002d001081205411101240d0220140c1c442141c01c4c82e00108a04100d600c0d0403145041c01010b078007149031502c45512482c40c1c0f40a1401f207422034400c07403d0044040c00120340c1031805110301c00000c50b060740318a4089000300d4401c1d440e078045c4070450b800c014800c0d41d003038251420107030b8440c420004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 506185107 1250 506183857 506183863
    0x140a0218010813020a0f0e061c080d060b0d06050909030a050d0e241603020403050d0336063e1903020a03060f0605160602070c03080a09050a062f 64
    0x50202014501039036182541d01c040f8004002e123400e20030314040c01e80c3c2c0d620000484086444a6006002c15681e505c45144003004103c0c50b0000d0100c0c400216048a1808140c1c0c40b52381a60421980e11600b680c40741d87c6d166582c07041c04d000c000010810300203080e0423115600022241200c41094030820380c03d2407000d0b40300c00808190f40200f541020140940000f8a40051500098900d005d51815042d900d80c19a2401e103030007508101507131090f110f50340304801e00f000307015810315445609141046402010301540100001d4904601c1c000200181c000920072035100c4e40d0043c44a44406118000300c450142c0070040b140b010143d00f000074007103000c901c5400400c03c0c609904c0040c0c07a260302c0d80c07000302140e90700e400c005203035600710b24140034440c0c00000707031282013060f6182c440f82c061180c50701002070b024074040203000313116202000c000c00000310050502ca10345562011b22180e500c104100404845103d1b100105070b40c500a82c4070080d1038030300410303001c008084544080d111000702901e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 506186357 1250 506185107 506185109
    0x111c0f05270c1507030906020601050a030b1008030a02010221011401050a1215030b0610120f0f0912121401030201030906090c0e0a2016020a0e0406140a0218010813020a 74
    0x5080f0b070300007070391508140d044050324010b815a44020020380d070510000c5400e1141c540800b80c01c40c00f040740044c850b00601d6510034050220901501c6d01c8000d2004017a010703402c041440e140c02c504c0610452040c10240c480241241c03565180400941d040b18015129584078000150401041c3c030711b0300030404250b0042c5204224500c031b40f03c21841c03540c02c00c09650000030707002da40320383c1e02113030f0491240d68407200403e0300d05d03045d800004561030f400c64480001d001c0d1104900c11a4180300300002440729a0300710507440740c050744568054202c401d0468007216401325210b013010300b58034010320165101c0e50200e40e02c244a6540010017040988a175001c144080d44240c3c003040d510000c010180d040c030700402e125054080c2c0c06001c0c08001300850401e9000f000b0104a14a541c0840c0005551710590f90500500041081240c1802c141c10070102a1201c541880c02051034540841c5171412244221800d002001c2000b4000c28440030044540420140007116000042494030f8007683d5410a144 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 506187607 1250 506186357 506186389
    0x60a0501081902120a0b0102011b08070e0d050319050a09062114040201020c040b151303080d150509070507020d06020d0204080f01051612020a03111c0f05270c 70
    0x10714205c0008425100c58280f214111f9061581c1e006042400f10038110b9401c80c0d6040c00c014603079545004841401e0b200604607845010140050309110011000342524101c10900e00541c4011007425a16071107015400000540412001c008c840d1040c09010031003d0705910002d1030120305c2c0c03580700603200c8242c138108180e04c03203506000c1103680401c0a984045025102441812041000581c103202000c0c0c0442104c1c1000070002014080c150308000507640c021551910340303a400300c10100601d921040e4401601204002240c07615199806a00c1078865980711442c01801d64248003102c03804840459465030244050300800c982c5001400140c0320000060041c20a070080351030941c1e078040e21800440b03c1220a1503161076001c00f210007501e48020001d680d0300c201041c114001e050110525414410101d0449921070b5003142c400b502c800c0c405001e00042e90a65100c070f04565003a0380f800e181e0725403081040055480c1075500100c410490007a59828003030107022a020480c41d244003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 506188857 1250 506187607 506187637
    0x12020a0b0714070f150c1805040506030a12233103050304090c030501051504030b07090f141e0f0423070801030c0602030315010c02030a02030d081905060a0501081902 73
    0x1d1740c29210a84a03000c6025400d107072a2851500c0815030065010a42c0561809207858100240c00760303d041101c00d5050f82e1044141c43d610f4036100d0020715240a6461141c1c00c4408812003800d4400598240c9091035500071081c141146981407286080c02c1e11041c012800d0403490001001c240184007900080200303c1003c40c101000b0280201110416007001c4e21902043d0145407042c8a03003c00e41e000d50307901c0b4407141e00b66140c0b90025076004001c0d0380186200c1c0c6407600c0100b110a007054485900318015615102256034072100f0303940b86403404c1a42a04054000b400d000c1c00c3c9440d804c10303c500c0c00140080c40410440c1c4440150085c401c4401d1800300c0c06800040081082040031200204100e00c065030841c02e06406403000f510720818100d0401605801c000c055517001e20040001d01ea0003400ca4440e28102540649071040032900301c40341000c0d001c0d205400e11601e020b071500c075801c01440ca4040341c1c2803000556501402030600d5002005404465601300400d10017864802200440 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 506190107 1250 506188857 506188883
    0x111010e070612090503180112020408010b0114121501090308040806071103040e0705030a06091d16081c09050306091f09020607020d020103022512020a0b0714070f 72
    0x2400700340041212038030b400e10742000c00d404200e0110547c1c1c0c2ca440d011112000e55600c1c000100e46020000301e07150b009520000b4009100d8005502c84000842c00381c840301c2d08003010900c918654003d6598008003043c81000180b5100c130301c1d400c0c1621424050410700440d944035254a000f50700700c0d400441141d4000b205110445810020718200c8090840096180504000a503108040c000d0b000c441407010100108901030019000704001e025005401c105445806207001300401184000014a00507101d00310134100c0405110750a84413003000501804041002843d951150041c540b0304010b4941d0010906580900100b80900ba10000410042d01c001c43c603400f204220300d0494003078600d045000401038452609a5081036012501c1c101c0c41d41c1c250005030007910031100514140740c00a1b511110b6145010445116a40075182e03401e510506040e0070f0f40d0350b160030036002d4849808e000000d43d030303d0301c50307841181c003400c4000b081c5003054076940d6444200300c0e9000703044800c0340d10030b85 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 506191357 1250 506190107 506190119
    0x10c0801030b09072301030f0905030d0b15070209130203060709090c08070e12070306020301180e370c300c090c030209150903070b0705100b0111010e07 67
    0xc20b45030040700000c05042c80030f2600100307010707900c00c2000c01c480054006090140b241c2c0070b940100400280500f05003d0780790030345400341d16a40812101240d00c1e01d010300c42c000c9818542c004240049080b01b04500e09010758080100a1000501c005203a00d020804500141c809000c4c00d8082c007201e0311b60654542c20f0268030010b40d55202c03020000c11003a1001c01c00120307403114591a0200055031600040d100c90000b0710b040c05000c0e000500418000000080c40543c4d0708015640000c00300f5040000c0b8000210440d1513040c0702184103500c604030f02500c8100d4810784040003203c921f117003116480d0481d40d941c10341906004c0c0c7c07043c0700c41d0103c803891041d9814030005a810035400484401c0c0c11141c40c0d510400e04202c10300480000540d540d907414211400780d8116032210742c0040c28409042305030803100794664002007403030703001e40203600d00050036081400030703500c0e2207501001400901100f000302c03c00601a11030001d0401c102260f0804803075a0a1103100070a001c00350182416030b0500e8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 506192607 1250 506191357 506191373
    0x10c0f1b061709060103021201090b090708010b010302040509010614040f0602010c0905040e0d12020906070f0c1d060f010903020405040c030c06050a120b01030b1f1412060918010c080103 82
    0x740030072616016075010043c0290300071880c00c0c15641e0484035482c4d241c61032080d95004001c1c2500080484c0145420b11510348000600d060031203201c00020710180c0d10100044080c1d015502c02c0d44e030056491801400340d18021a20718201184102005040564852184140301026401400585d544070315000c80680e11103405c0c0050034051b2014440c1040040040d81d03610a940100020400c2114030760306450541e070103c801140b002000144c441d10309007862064a02c2590040b6113070506404d0010355110800280114030b144040800f10301da5910040c4030303202182c4120782e81000142100480144d685100741c50040340a00c254020300c508502d84038400ea10250002810b1020621501c02d071164042c0900d03480c5204032902040d000e2901c80140c000c1c2c0544500e4540c0502c1d04500030020340b10b2213101c0313000741c007150b9542c1040701c1125075070301c5252140740c0c2c1d515a105141c400095003804d00401458006481507005848002407011171360845603401d40d0640010f0084004000703001d020 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 506193857 1250 506192607 506192627
    0x30c06040305120c030c0a03090201050d11030a0507080106020601231c20130f0e070602100f0c050d0903021005100602070518070c05070302060f0406180f05010c0f1b06 74
    0x9061240c51424151801b2113a40280b08000040640300d007034030380c1164411410f45140306042201880020b983c40207416450300102c645078943d509c0c000000c1e503002e00c6003091504980040c3c01034003040c2d00b00706000f00310303d551089032040c0e00d0310824410001d0325103100c5902d6446510074103030310724a414900210032440d8082c2c1c41404940c00788605110b0703500e1144040f40059506000500b01c810b00ca071340d101400102c481c002d2640524480040d40700d4001c982c00c0000c0304022003c1240d0310110110310304803404100035000250091100031181c0300715600c00ea00483c024011101c06c0c00e94621410b0035201b0803207003070441003140d880400a05404220a00c050242120881c4094403145110440305d4130041401d000c0041d5101144148070341030240d2005960060101c80e40c0d841d500344900d42c107900a1141030001191107280c0c400d250003c00310b0790140e17454089001000c0e441c2100441e110b5810200640d030000412410400080e09080100e85a6841c003041481807071610304058000c1c110 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 506195107 1250 506193857 506193871
    0x150f17010503100e0a02060706020309070f031a0a0e01060611010b0319020603060109150905090f130b10050d060507020106290f07050d0c14070803041502030c0604030512 75
    0x604001400700d03a4000c0382c0e50030702d0210300c0f00025004400d02001880c000103a50041c1d0040710002c4c2c01002d0096a400031803041195a04980c0c440781d8505d000081043c882c403001c2d00c4074210100c2c4c988140b200c240b0f036903000691480d000c10320b00306507001a421601c80e41c0c0b1200100b00100e0b01134801d49420b0242580d820821009811100c1d04180703a1100e8004008000b881844000b0003d2102d0380141e5400004d014000c2c0002995040c0c03000103080d03001d0b280036a03440340340e940002655082810300120702c24a4140c0401d0600c046c650f41d0504054005031a10300f00000da80804501d03a1140d502506420780103410215a0b0b081010002c3e0131030300e45402191a00d601d420102d0301d0249648076132001e40844407001743d69900c000014200c40d0150880041640c0501c0c402c03007014503800204002e609018900d005c41d10080e02200a1b6104c91600c80c5502a40051004208040d9000c0040e0300ca8001401580e14102c00c44103580d04009048a0440120b17001203092100b200e03c1d40d101a9100c80 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 506196357 1250 506195107 506195147
    0x1b06160f1d0f0d0510020706050609071b061d100e0a051c0509060403050f0106050102010b0315180604030914040b0f060702010e04020301060c03031802150c07150f 72
    0x250101040c241c080201e14081c0210204051101c1c55110046828031507600941520742d4280c8064820b0081d512044050b00c00f80e00702401300e031240c41c0c031540d21030281000361102c1340345a040380c4210004400529058400316a5448108003c241144004080310405800742130305021500025044a040505011050313008414840008000007120200410811904040782c0d007810002c03034803031041d049072030b410140106000040040002e88000b0382c0e00c1801c002d22072188c17a50300480c200ca2071010100e0385a40034241d51101c00e421005a290480b42c465a00d9140040640b25245403541c20340e822000502e01c18010000006c4101c0c1c44e0b0030300f50b41100c0501458072002c0024802c0016018100e12039800042c0840031680210f0750180e01c2403014000759101d603507510b0040c000c0d07403c001c8150086070510203070302c10f00c0d11145c42c1d602c182c6500030140518141008c1043c01540c1002c10441c3c801d01c91107034082031842d4100d41c15081d58405075a9a0580720900d04001c1c0354560b540f072081c0d611a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 506197607 1250 506196357 506196377
    0x501050a06080c0c07121110050306041a03010c0527100e0d0609080903070515180d06020301080c120109030e121005010e0703050117060a021b06160f 66
    0x9a6819a4941101c4003490440015114403503a101544212540c00540d8403e000340014540403149951200c0d034010310003d05458812000d201c0d24030003c1a481d000248100001907c40c60b06130b0004c3d16000340880001481000480400d003140e0f03034910303224003185c03004c540102003484807606001c030801d1806041c0d61020403800850304400d5409203010a1115038172800380d50b81c481daa428114150448010b0141040038205a05560700040d0514007900500d50041843c3c105240050300707031f010343c02145280c044014031050b81c00b142801030b140e1105101a1038008150640013450190404801401003240c1d040d041101005030701d456010541d042c00c0c0010b01203600412240b2424000f039401080c1901c58455142c200410320352042d14452600c40003245040d520020705100f840152420805a6250988441000b603c2c0c0b950000591017080000c9540045402034416107024811901940d0800d040c0982400800c983d424442d0800003400751a895001e200e00c0d1195086003040a955 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 506198857 1250 506197607 506197609
    0x4090c090303171b130801060b0c0a0204020304050a15050a0b0f0f090c0903011a04051012030507020d060e0f0114091908040e070906021b010905090a06030602030109020913050105 79
    0x184100c02e44100b6600074020006411a0204615504d00e94111116980e2801034001400c07a001c40c80c000c0c0034440d80b814001140b024046c034119001600920005c18aa060f1a0b003004040c0d0b1000b40105c505010f2450908000345003101400481d40c10f40d48003040c10316003030020000701c4881c210401d00c98410792034a0140f035254900700035070800b0240c814427029a40c80315540380d9840b0705403060342c043d860081c1403903010110351402035409100721001d001c16100c7c01400c55503100b4500035900302000c03c2c1030000009003e080108807032032020701b21000d00c3c155500c40004890050408031060380014101007070280081c41100230750741c4401130715034480c1042c8414980d580c8115540c0c804140c5003240c900c0500452100399801880010441031803840c0c595030080080290344109005889080c1a810302510160500d07184050306940c0c00101c185484100404154080e0030502085d503207400c0130010480318001140a0031480c000035a58485c1d01040c0084105d1003102c6541040c40c1000502031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 506200107 1250 506198857 506198867
    0xc110a120f020409080d0c11031e0c0a02130203160306082a032d03030103120c0204020d050c04140303040b040b0309070807080610060201020307140a2304090c090303 73
    0x1840d0380118490610400e6880400c00a00b80381101400f01500480d402120144035007003100300302c1290362102002031507207034140c1e681e000740c0d084040071107020541001680c02d4280500010041e06003118400313100740d000b0400005019a296810325000070400c0a01140103102140c10062482c0400a03189440036081e00c680000b11074042613400311482401e60f020202001500400050913103000d906005644030454070034180c1080d0314003048880c0c1702160004030a07a41269001002c8009850701c0d100c0484000005890480c0e10950034040441022102d108052140300c002c01c5159880c0e04010b0307040010410754409a1007540100414800d03105890b00350b400321f41d10008070641320b4460001c0d8504041d02900000c14174400c20b00005181c1c4400a42c2e140541c2c0200c05c1030340c0007a2142c500324240e00c0b044035608040340f01801c610a9050303030440202000b81c07092414140710219a141d9121404c080e4030b6600c01d1000104050100102d0344c401c3c40c00a02090a022410b146140e9001d44 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 506201357 1250 506200107 506200139
    0x60e010c050c12010204180b01080f1519030f3210020702060c03030703020a0f031a012f0307170301050307030605041e060c090e0105180c04080303070c110a 69
    0x80034103201803c01d28030b078600350141c0d00646501895021110304c0ba00700580103110515080b40022001c1000c54a04d082c050240da0041c16455a201d06800b1450706009140003075001040d51190701c0c05000001c580685081d0b100c0b00e00c9151011030710241a8602d0a00d4441d00b03015030001900074000d10421100040d80a2400c40b03000750168130341e41c0c5800001c00c14011012402018000001042281c99150340100011892910341c0c01280d41c252a044040f12401b526500004101d0282c1c4295980a030101c100310b08040004800c45440700320203810f03442402403034185194001318000c420000140d4070a240d0075031000c1c1141c255850900060354400040c480a003030b01c0d9451000c1803c0c40149103820300382402e407010900d00800740d40340c89030003011800d4000002440c1d040700400c10080041d5614101e030b000500046a003e903000d207840000b00c3c0030303084024060041000195008040c0080e500c1100141c032411603010072400d00c0ca085281300c07058a0b20809582c1000c2c0802454041420 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 506202607 1250 506201357 506201359
    0x10b10051c022803060b03010f0302120f160501080108030a02060f070e0306010608180106150f02070f060e1002010e071203230405030d0503042d1506060e010c050c 72
    0x240380e48030150706000380300e41d40c02da03280b030415005000c0e01180c1c2c8000e50601040356940402c140760b691402908240020b0140901000c50075000f000940f42c80c80144122511040a0310240340e40d80f0310833441c001c510780c84400103041940c1e00300055170300700e0346990042034030310069031600303825500081d01d0743d50062504001900d0a0b0105408512801410002d508041d088816950315410060140c440454500d0f14060494580c401019810b004030b608545000302100d04445203860160340162000c5600411845100c10001d00400c2c1030070000c0080c2029120307000c0b0382c2c0302c1703006012258006034003030400e580c1055205a08950001030580c1103407984c10000d81c4c0c00c0c1e8a4070702100c1d80400841242c040c52405603940102615980003001181d40490840b02c440d0116282914940000c0364040c00240014211111b0802000101a040510704400540c4001c3c59901d9074445c450210403090090b9651100b4040d5540021140182c10b2003400c006501d020341d950780303580d18400c4d66032f11 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 506203857 1250 506202607 506202637
    0x806040c05010804080d02040b040e0903070213050a2307112109010903080a2c01090905040c120503030601031a0306040212010b0607060b03070f0b040b070203030f120702010b1005 79
    0x1424040f10b04141c0b21500f402c03071015540c0340d603030b90327002d61194000c2d02910f143d040e5410003003003d1050020403608001c1e805002030b500036100502200080c00002e003225040e503124108955001c104103d18240080e410750761003a00e04040744014050000d85511000c42d078080480e0048401500c0140c00d9414049103405035900a183e004aa190400760b04c000d08501c40459110505600700c04031002101d07103415400c11000035001c00841c3c54448204d06404903a40140602c04250390b40c00080d0b215000d800340c4070080f070f0344505112906821042c01c0e5015080402400302c0ca682c1800342e6050120078080c00d03500017a000700000e8807104043c0000340b2900e00c1182c050901402900400708044000740b0407926280d042c1040700150547e011414440d0050040204929200030807040684514036102070070f06003001c00081702c039030088c1003c0e030b41031100340000c25031580c6e8035000b03040032a4120420542c030305011a0283c00e507942d09900d94491b006119910390040e40c01410756120110300002 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 506205107 1250 506203857 506203861
    0x112061d010e100204060e120102070b040821040b0f06040f0e070f09050c0a1d1005040e07030504080f090406080f0303091c1d0f280806040c050108 65
    0x12010081111011030300455000150240140c0c4041d84a403214116030010745400c2c02c4040f800c0c0c4100d2069010f410b011400201d000041418400c0c120501900350300d00062400704541c440190b034402c11202161003a600090040c0c86074148203c0c080200322540c440112410701d030365101100c0318000e14020b480344401c03000683c29643c03034101066040c09a80100018410094510344904081c010f0016645c850000003034001075505c030f2079100d5250781441500703044482030112a100d078084007044800c9420314150005585240d40002941040d4039080d07036813441d095081c8480700000b44410705151400e030812000ca50107404540542c02110155642c55017040c0005004061581080816104091211521650001c001c41c000c1242e036013190000d01c0c000741170b8246540d8072829840054046400c1c1104884902046401100c0040100000701c55500c0030490740380d6449841c114940480c403001c00c0e00c07030355882e01e8006440d001010307281c40d10300768507140c0d00700c034252140034100110300e40 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 506206357 1250 506205107 506205113
    0x7032f01080c21040303050901140f0106110312010b03010501030b0d0c03030e0402040e040f02090f160815060307020705090c04060516020604081501090c0507050d21090302330112 79
    0x9504000071001c03150503d010708113800c0c0100289406c0328296019840d02e80c1d40c2c441c0c001c54008007880350700c500561311112307820a401256103111101c00c04025100c1031106003030501203440c0e558013070304240a8440e12585000300040c180c0344150910f41c020090603001d040490111070034402038a8141c00c1202807001c07a0000308000348a298402e4441d240050203200800c201e0004e0303020141c3c002c98141c840e41c1c0340c285104802039015203903003010302410b501461609018010740b55100b4038000076140342131003000c0400e0441e88210307a00b000603040601c05002e0351410b00d0f52240c2107000e00c011641840d081100241c0b451044007401004560362a5180d003c55950350116070152403103401351242c0e8006c03428403c40d441002c0c0241d007049814a03c1c0c058480303104205842d0103a801600410704960324440c01d80d01c0e185015400c80328a80405000045c03811203024800e0402d201398002c0c0800c0e00c0715180380200705408144981c10070303030001911101d182c0e1404001d05559504c1d080c80c8614074549 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 506207607 1250 506206357 506206387
    0xf0c0f1d060109120c1e05060301060c050a140a120e130f0608160906080309090a0c09080f03070302250608191107020310151505090307032f01080c 65
    0x1134002510412000c900000308400070302008111100281030b00100303c030b01056102204c001e8001c80342c002c002800100312140c400c002c401c0c400360140003038407441c22540d00d5071060303007100741c031000107503031081c0d45000401500c24640d1540e01000e2910751744e0042c8a0380000c1d802072280b409401c003a501c0c0d4070721002c21615075010600418811b42220702c90b1025080b2061101e516105200b20a49462000212038030b000c07088034070b40c80001b82803c0356569500d4604000f881000d0019080068242c3c010802c8001000b080c10380d160080021500d0321950b15000f40341040100001e120751814014040139a40c0f050450015136203182810151a03480c0c02d010f40466004d1040040014103100038410b1020a0100911220340284c060340d40c0700ca04000b142c42a11080719401e042c21109080070480c4403840c500d10814008203140081c0303001d00210000e40b40082e190410369401d10415031491504d29080419080c49598441d0921400c0c000000608001001890010603a00015040070004061 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 506208857 1250 506207607 506207609
    0x305010c030b190f0b22090b0111030304050604331a0109080a0b0702150406021207020c0901211401020409050105090405060a1e020a08010e0a02040b040b090411070f0c0f1d060109 79
    0x200901b041c110754500054001d002c1c100310b0b25011846154440d001000c02004592103250041c00416082d00d96075602d9920465001d600491034004000180588407080318084e803d500030325000c100744071042c00d201100c88400c0e000c0c3c1c0c103110b0b01400030840f00102103510390345503070451030506842d0350741e2034146c0c280482041d01c0700c2800600c0702008200030343c5602401d150b045454500489603a1614181da854ac080150300d47d111360550b00400c00c04040d000800d4211404907298000d100072981d41200049050800c2d0205035008101070180d0200c80c4601d1340108411980340c00f407403c2640b917450312014040c10500c1140c0c0c4039048076142d4140000d46040d6030784e0071031045548424140c00103254034401c1c0034403070f00c032400701021444048840c020745003690828450301303241070f04e00311220746d49603c8480201e8000c3d0722900201048000f03440548010341c06045000b10b242594602610704803055080802c02c01480e0105000605141d0381c00b03010300c40544024a120340381d18005132000003503 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 506210107 1250 506208857 506208907
    0xa0b091504030c030215060d11060f1201091a0d060c090b120f0106110c01030f0b060c060405010b030d0801061d040e0c0411070308040b040305040305010c030b190f0b 73
    0x5001c00c056200000c002018040c0d1300380c40480c10804890a191581590b510390700025445d11500819011450b1858070740e00288140d140581c100500091030700200d0340c1d0f0f29020300e5800108800b0341ca41c0917010b500f9101d00803110400342402c00041d811280544040c00207566410804203440c0a19079440c0a088503200302c6440ea129101c10290114040f2030203030006a01701e000141d0540101c1c142448803041c3e10142055881720001140109028003c451055131140008802d6407a15030041103070b620510042c001e2450300341800c501351a840d0b4940c0d40203901c81014000c02e60340c07044185054622918003100e0300c030500781c5554962080005071580c4689842c400c0b054110001a0700a8540000c2d00e060105c00c034403040018242c0151100a00421003401c00200002c80401d84940d010340f2034142170742880e0302c0f51a41d60844100a000902290342c40002090718038200011652036068440c0c0ca031059801c00c0c018205024903032051003481a00401d00310801030a0640d82040861 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 506211357 1250 506210107 506210143
    0x40c0e040c0e04080703020d020d02030405060f0906071b08030a080105040c020a050f03030105040c05030603120a050d230604020c0c0f06370f021504020f030316110a080a0b09 77
    0x70f2608090700943c2c1328110807005840b030038600002ea980040b580288000d0160003030760a1a141030180644d0364802c2d20202120071082121010950712000a410007502409200309002d600b203000034036000050700704130f84543c0184000e40c28a90b1103c40302e4190740045c0c40204643c00d0707041b0264605003101130014064008e0045101c10100008003860494030200d50500040d90000d1307043e20316110a8174143e4164000c0c010b0842c110480e03000510300030705540f900a00e0410001d4220088428081300b044281c084501c03c203407401101c616035031f089107048404616040c0011448e503560410459a41c2c0140c2d0207450108550341c440d0161190360b800000345001001d03480b405108920074060340e40c60409918550484034074421117680d40c100c0c00c20303002003081d03a001c0e9440459004004104903800070740111410a1074805001070b11107158645007a150304070039840c08211441203e41c1c040e01615001320704100483c0002692051680c12542c1001e80303407140802c6d1800d000b080b009025440d5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 506212607 1250 506211357 506211361
    0x6140c07121101140411180406021614010204030b0705160b1515070b07030e0d031104120506090c100203040e0c041d0103111e120a0b09010c030f0203040c0e040c0e 72
    0x130a40c62480303129500c82c042c03d1384400390540130041c402d000c90040b6075038031405400080c0002c0c4241d0003490380f1420503420303440b800e0b45035540900e036959000658601c2e07500071070704200304420501280c0d000440c2d400e0142c1441076400c0110806414003001501e0710071090049070b42c075500388440000320b100145c41d041c6d56075040880000f10781c0c0441d1003200c40841c1000003a20701403117031041140081f80003000d8120941c0c0795800328050304c004010301c1d030a12004c0200141035a040f44134404028810800b5211a18007601003a00700942062001d018103e2600c1c0e0046041d4003104840c16100402558011900c0d29040214180256045820350800d66848440100c0680f2040d90499104d001500a41c4800105000498100c1d80f41c0d410740d00703084c0c190080d0728982113005140c130394005004c8901c0f03846151107000381031600b035802c02c92513507445241072802c1d03626010700e8000b8103665405500e9402c0c50780c0c032034256030303118804c201502d004940030504000301416102e00030481c0490b1800a8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 506213857 1250 506212607 506212631
    0x40c1101051807050f0f0d0c0b130302010201150608160c080417060705070c1a0d0515181015090807033f120b0a03080706140c07121101 60
    0x119a42c0c1180c00541d114298002480c0c2c600580070000c1c03210003805280c40c03205441e0600c040071403482011219a0342c411404104100d46170007820300110700000c1c82602d18031354000a408c407000c801d485c090300c044014040c05440d070041b041980060000c2c103074070f152101e0508100c030507504086000b0600700c0001000640300041c0343ca0402c4402002c400d031007840d141d8002c107862601c119030000700b000c014220208040c0c49080380c06075100f903080401d140350903001d02c600c0c0200d41c412640c0350140e8000740c08422081c05d15000c040c951000c8025603011f681000300c17a0314880d039190709c15500b0905281c054a24101d2148680d8401851000100c4030103507202d01c0c21034618a2105d1901c0d00c042c4c18403100c00110011900311804107541429140d020300f0452400300c40581044003108181600e0380802116a1900d09010006500680c0030359101c9906180007019503460300c4207026040d104d80c0c14404426880c204031401d643d40001407000c030642c10328090711440d58850301c408055203080c03246010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 506215107 1250 506213857 506213881
    0xc0703020901080313170c06070201030f020c0a0507050f0604031e0507060207050112090b0f0403030b0d03080108010b01110607120f140403030e06012603040306051f05030c0609040c110105 83
    0x504425108170f05103548462001a070300c1804600c08404d9440340f0201843c0c0c0c01d10b0401414094010701d008220401c94046500603607020710210302c0d07644d001c1c460f144240310050000d0703405001e04641c51000f101c1010b001500d0fa010300e010103031131407860005104003686c4020507611029030100650300c0752513903818080c1d01d130302e0b140c0300389408504050b120b11601c9219204007200258080c0d0440e1554440304007040c90300000410031021306503222030100c540c0d582e25420001c09442552503541560400308180e00b551261810541449041d9501070303046440440d010798810028a000003041c450a43d0a40140c205080c0b5120040d143c5460161140c41d0418802d1246001c1e031002e0040c6042c00700c1c2e45541d00300c03d1003520554402c00c3c02d0740020083d0100d4110031074400d14100c0b414240c494803504111202956484e00701c0c00f04889103203140680701160401018210007030070206600c00081401c52140078442c512803a6641c9032880030314014030441881804900081200c0e140109100750 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 506216357 1250 506215107 506215117
    0x60d060f1b05030f400204060807050f04090b0402092e03140a0b010501050c0c040609140a021309020a031b0206071106060d0602070c03051203010e010501051206060c07030209010803 80
    0x2084151050005501c101d000d00824422817280900021094400d500500d01c1250940107648420304d00080c003015a41c1d90050001408000000d8400b542c80e0204208080f050040c24501450800e001e900c0800d014910702139005405444c2c010785075590760800660800b00080300d0b01282150184000c0201601d264002504d1041308103140c10030302043c2031907440c1c0b84168024040680c00c4014440c0e5445400070b0b0080c450360314100d135155100500042d055480300d800c1540c0480d510305030780d0207440752207655035008252a5000c62400403048251600e180389800b816002d29000140310f24454880e074490058440f089640c082c0402e04000001c1d2202c04c00d0750402c0000c0c04c1680ca4011050300428080d01401e0b0041900800c1c08603941d8403006500326007000e54091400100000c0030035014045841400349440d40981d40e0740c14800c02d804802810307000030741004424815442c5044070041e000da000802261031544410004480d54500800398100940010f03180c400051003100000241c4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 506217607 1250 506216357 506216371
    0xc2402070c140a090c26070806011110110c010504060e0606030102091e0103090b010806160c0201021f0605130f050105040b0a18110c0c040c0503060d060f1b0503 71
    0xd44001e5a410403542e21007081c0642c1075001c0d050000410680c1032035402000c2203030040c204000c807000740310075240900c2c20b09503400200c00c1c00c607010080503603800010b00c4d912a8003400d011203207494103010380742c1d500042d08040f60641d80e620140c400d4500402e0580f12402001e030024802da00c0c091030a807020301551600340440b84192408205149810b0003a10b1420001804400014104481e80d1228401c00301d00300307052690744c001d11004250100182e034041c011800042090b824031101c503d405101440c00d00c0c3c1040998894030780180e9001c150640c06030305288007031641d05180d0812300e008204030352169070312130b4a0151a28404150760040d51000043d400308000f00d81e44e03501404142c540c22080316a02005001d01402940307941c00840d002032080302030011310b540100ca5074411540c84031070340d4034035a4860075086100303180c24002c1c540c43c204540b802d02c0c15800c1c0000883c03c0e030b501c0160000c00c415250300c0c0d10241c4580640c485104940d070b10030104001c03021800e001c1c090354000c0d100707a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 506218857 1250 506217607 506217623
    0x50d03020f07051e0603040f051e06070201020f090d0302100c1701051206040b1905040c081e07290307050403020a12080733051905040f030c240207 65
    0x10f060310b880800300c00790700c030140103c1003101c0070705040200c580d05c0100112018181c016013800414020801c060a01010f4220340d01c3c0305a43d60192480d08070014144000c5a00400c030200712441034400356000c02109079403150051246141c10b03818590103000800840f80341008401301294003240000000c2c1000f0761a08250343c8440901c0311060240e90031210076407000004c100080da510354a50340c4590b42c0c1060308140c14010080d8000d8450a903419030300d02c400f0354010f2100d40c0007444580c00c00840d40c0c016010004480f42c149440d581c4510400026481009101c560701c5000d0611554040c001e038400c50b0780340791030b68003c4c145800c18001039014119070f03407010843c882e00c2e1429003251604080342da802c085540d640d031022101844a020004191034030a01082a80e42d0844d0050130100d040108072403820b214904400603c803000d101d5500e05200c00c4c000441c4400c034880b08070039014602008003403ca4145032010364100d44800010350024200720a003075015501505103a4480c0b010 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 506220107 1250 506218857 506218859
    0xd050405031e04140f030a030c022b1e1a090a08041205010c0246031e020a0b040f060605060a11010c05040e15130c05031f06020703080a09050d03020f07 67
    0x2403005c036010032111a074141c1e0145101c01c001ca40252203050401e8401018041800540d0f0310b82620504d0314501303010600042402e54040059108800f07441110341c0707042d40003c0c500d5032100e28094a8040414000f0040600442d581013424004020b04a81000b00259903561342e60301034041090602007a54030b03510340075421714014030200d8842548000007000c07500f40ba841e440d41e904180c0c209180004ca03100c25041c0d4040004070542000310740c42c00785e120069040e80e010545207012007482d80400840d0003a4642c00005510f82d1310361508580c2001140d00060424500b060080c84a134009652012000c03e803980c00d198840e454906040002c0000e001c001c030442c005444c10300403070048001480642e0006240075000603071705084520010880c544403000004c40074216440e42070480001038001040141c0d40c42408040c01c016007845030861001ca1030540700941312501404010641200058080b14207445910f03071202800008098005848030b503e13001c0e540c1c204503001d4040c6401000d42c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 506221357 1250 506220107 506220109
    0xa0e010e06160f09140307030c08150a1104061409030105160f0306050a0b07020d061503020a0509013005060109050a0b04050603030f130f09051909080d050405031e0414 74
    0x119040700c070f0141c0f2040042400c1c200c0030310242e10440b07419905445070baa40000400c442002ca140186800c02c080c0c5181c008030444964a03040003441c00d0002410104841119080842142c0484d101c6241c400300c1c0b0101d021450b40306120316983c455042d807c00c070034400020b00f10500b004040c07070300c1d440d4580343d5080d049054099600c03903c41c455108101d44002c00411101400031305407944004c00e504102c0c019680c1e20740803903118080d141c4800d600c1d0b40041c421400d200d01d0840c00382004035403002c2ea66150221101d038070840801321122003504481c8100302c068801d6a014001503202003524215a101d0144900034402190000741c810309040d444203090030244500c900403200a006180b410098601034045d40c1d12012240d00c8002e800c1d580001c40400c21903031007014041c503240c041401d0030941c0c444401c1c058004505c035070041c03030600440001403038070044070341c0c41440e0a40421103030b6031820a1410350262801c8042c1c4c280d01340641c0e107198011140108183e136030030924440b504400d20 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 506222607 1250 506221357 506221367
    0x204030807210c031d0d062d0219030905030706020406080f15090414100618061e1e050402030a0e010c21020f0702030f06040201080a020702030a02090a0e010e0616 72
    0xb940030380400c40e11700124160b0901c0c01084048450040c1c955503041d010381c0d1f590800c8031416804000003800680380c00386034040c5208044038500c14131030f0941c1403980302b134042181010100c140c04c0501d030303980b00e003001001001d0080da0446138003c6801c644545e6214009081c040c07003290f024450b0119503000544001d00910801a41311002d003540740340e0703941c96032000c442c004285010941031240500d100c1032050540518005010080031a1035103490b00940c1409a448580184202503120814038080030350b405114003c581103400400c8a0b96a08650494a203a049d04846c1e04280000200090800c15402000c50040100000c000c20111450304565200403840d200d0b186032801803140c4410865034002e0888a0541d1700c0389464124181d00281c6880c403600f0942085400440c2084103642e0407640c1141e010a24503025490300003141d0000e5221004100002e104101d00341c0400d284002c04c0d800820b41c081d140000b0414141c009010680c5c2e0502161a0120092003802c400d880314851 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 506223857 1250 506222607 506222627
    0x3061d0a030c0c120f06050903031b09040b04051512010b06091e0303040e0403110303010609090504031215091a09012102060304121209051c03020403080721 69
    0x824040c0c010609255011070751148245026120925071003c00305940921440841e011803260f10001d44032110b51406200b0380301c006240459581090080016040e023020401164002c120f40c9559240350210001d0000c000688005800521b808200304c01410809150302264a003120607884040c00f12180d04c0c02e80c1c41c114040c0703810240030301042c3c00c14202071038034110741100d52114007482d11040020924607041580181c010303851400c2031000303043e0000c120741038800e041c07000b071841e5604102001c1c1400c101c81c0b085400042d9910b000406141c850480060304514118062203101c901144403004158a800750380032492800c0c0000701d92548450300340882d404098081040d6a10303084d50303074480c00000e161100c000945401c1080040c0e803080e00462103170740300e0b104408800a061400800c0d07608521002c4543c60300d001407050100b070000504012003400400181030207480844214040c5c02181d00080070f00300003081a04c20031480c10049454183c400c1210700c01d1580b507a40c02c0b1554504 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 506225107 1250 506223857 506223911
    0xf0903050906090a030b0c03040b100608040201140909010b0d06050d0f0b09031603020d090b0309120307090f090605030105060a150e040207140d0e150d0b15040603060306 75
    0x410000c0301c0c0541000405055404002007560384991307a2500d8061030040c1c12510401e101d4070000402080001c0b400c1100e400900301c0d040c0240d254100030026010400217440a418451360542c40044e00602400321518983c1c00707080c1454650755111009041d070000e056044010342041404151801c110080c1c087c0107800554601d00d0185980326081d03010000752040c0994041003001200103601c050320000d000e4400d40c02000540d4403108014070122140d00503207141c00c010800c0c0151400b0001d881004842d5040c000380d42e03074452000540b851910340d4413408011152000008a80100394082402c0f100203400034409559204100400b43c2100d0207140001030000c500014014407500200b458501c01903c010301d0646a5104c810004840047c400342036489490f4400311585d00c9200113490200c01e664400c590503c20b84200600d003c1c1d0040c01035510351300d40c450740322640e90401c00c405007022000300e5907803248c1351407008014080030b000030b07100c09040805a846244c107a05101040000d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 506226357 1250 506225107 506225117
    0x6030f0d08010b090a03050601030309080d080103031706010912060905100606120902060906030114010f08070219110d080d2702060310050909030403110d02032d06150102010f0903 79
    0xb0800142a055402540b03210b03802a00100000c40065410230010b40a18041d0322038518003840c1c80c071000d2403c0304154092003000604401040001d80003001052800032b000800c0740b45644880c01258143c0340303980a41c03d0182c819a0b041c0510600b9401222046d018000340d40c0354442c0000302c1001e07501c1d1441503000103001060343c0f03402e1038101d40c8201d420603c02019545000030031070000b100c40c0c00c01e0300000c40d0302c1180440c1d0f240560b0403192800610455080a408601e880b9074084d48074808041c460000264132484d03401045112412104218801028403c0804982c249154281c002d003503101c40440c5807101c0da540a03240c4004071140c40441810f050100c0e1001d60912080c0d8001525003601003000341c00208403541c4402c0041d22a4620f0002161610b1840c1091040c440c445100903010307201c01c49a280250714042a00034040b444401d0b030310500a424005501412003112303611f401c6010700002d0083d0803081400c51691680c1c240c3c000d0204000b100c80744421605000702c0200824 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 506227607 1250 506226357 506226359
    0x120309141b091f030c0617010b1902030d150f080a0b2202040638030f130503070f170c0d031508070e071704030504090203040f1a06030f0d0801 63
    0x40740c182c0900d80c0c40b1469080c0d410030b0106060381d0b50704400c15604212891185c1e030a0500460b5804081210404260b071003c4100b540740001c000701c0b46c46140c080312000d98203070034680304840c020011608038220b840f50801c41c030310010301c1001d5051a1400707081d11003617000c04001980600010024001c503007000000600d6100c04c0402c2901c0c07001300c01da685416244020f800056035071485054014112006c541104c0c441080110502c00742c0202c00d070364007140039030b8200006c5e4850741c2503940c8000ca144400c481038542c0d104c005448000100c0080241c800040e9400400c03800103c0304a40f43c0c410100c5070014101c0e00c00041c501e010b4282c0813071040c0e118200400c0c1c0750f1300c070741c021520417090ba0403500c1d1000c1d1100242e40c00d05c0c1c01034000b500404401003d210b80309511005000b00d556241402c22f5050810343d03001800c40c0b1807881100c2e5850303008404942400543c4982c4904c4960010402d0400362040d0303c0c880310002c048078071502c40d0040040b9200ca200020444803e00800c59079036405c0d42e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 506228857 1250 506227607 506227609
    0x180c10050d0f0e0f0a03020c01020a20011b1a070809060a200f1305010918110f0319050f090c0108040510050c0414010302121302030109120309141b 65
    0x42c0102d00c0030080883c0c560a0f400b2140105001c0618512100c001611140c1c0340b80c24068540394810704068110340c003503003a00000c200071030307020f444004564002200c503024050040b03a02e12038002e540101414003c01d0b40e010802d00c80b202c00340b01003901700814490364420b00c0540d00f4a00403181401c9941105c2e00088100d4225403102c4100f0034803d0014451072200342a07840c680c0c000090109055800081c0b90000e8a268503042c1d0003401c0910f041d420460071300c0c4150300c90a400c000d241e103d85881e07607010561101c19009070fa003505038074140d0350388900d00050100300c0c3d4484200011042442c0101240303002c20300c003030411300c566580c1000748104151a0300451700c0b141c008209803402d000b04008414a0f00b002d0045900840007654010b4846003000e2010000703030304580300f0905251040065242a15100840c1039001c188800d2140110300640040303400f501c1160001041e81e0101d64010803078917003652022520034000d001d4545e498007011408c41d40c03040309012040810007002501142 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 506230107 1250 506228857 506228861
    0xc0129062110031e020d0b450c0d03110106090c03020304120e1005210103050a0c1d0114010c02040e06100f050f10110714010f081923180c10050d 64
    0x1320041041c10f1400d6200a12080340015010381c0c442d0b0451b004001000c02d21b0400d18059510001201406950881c0ba000ac0c1c801541c00703034010180700b24410080690140bc2d44801d00805814005109100a0b00c0c0020000d40c4100c40444981c015060110710482c80b0b051036031000342020340300d005040100c010a60701c1d60000c407001c0c03c0c8502c071190f1203107410200d4400140210b2041c0018002c03507005140c4082e4030340756508107002813629202e2404480c0405110a4111050b400c0303051a60100c50004994004001c0b4000e504581003d00b03400380c5103000101c1c0c0344110a80491000d15a442d001e80451000151041d0b43d030089024500741d00b503142c240e045542c80340003400e10070000c05843c80c1d054100126a031000ba5103543c400600da40b103503006400d512032101c8a01d0078696620f840324040e00c60700010503865402940d0745401541d01d40b012000c05600d404020103000451512031440001c070078541b40740403014081c100705d403030f1030342008038407103108070700039151780c0d051003548056440 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 506231357 1250 506230107 506230111
    0xa0605090102040b040e070809030c0c010e06090306040b090714030304140f03060403030902040b0108060319081b100b03060613020c0115030501020c0129062110031e020d0b 76
    0x3109540c20003002800c4a03240004000803c130040c02a0090b15209070060005900188681811303081040b00c031114030004101030840703c1d03090030303c1c0c511084c010010600c1d0307015604075290980b11700003d200a10007807482d0309200b41021000c50b8100ca8546600040088449080e5a05940305100030f01c10803144081030201901c018180c0381c0343c1d04d0b02c600004d10382101550300f40c000c642c0c3c90482c0c006508242c0188500c403c000c9c00e1000e80307400c100001c80c0d5100d0305002a2000c01096600150402c003c6000701c0e02c0714407002000b1000c4001c032040c040c5d00c46900c0d00801c94210300c1c0c00e104107032604021510758401e913001881215070040100603640650b20200e4004003175543c0b102280f54008610f205e0f0b1001c0c6000b10001615074001e00e003480c2c00c41d00301d161502c400310064a032031820789403001604107001001365040e40e124504082c10181002c0000d0b101158801c10340708200f400d81c041880031044030301412606031140b80f40b011100c88402d4401000c0d40100255410002080010348096 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 506232607 1250 506231357 506231371
    0x40606180323120403110603010b1603020a020910060210060b1b07030204020f03190506090a0902010306030b0915220201110a0213050a0c140a035601020a0605 70
    0x41e4000c2440000c9a0030f24200d1103548403415004501030040c0504010b4600100c20142d800c0c81c6594100042e01455004a1a00829088100c05500101031003440340d881100c5d40079004403450f061245030b03001c44400a000383c10040c441e20803001a0506540120011135208441c1c4501c0c00c0114101c0310b4070030768151408001403041c5280080143c95178401010410b644140b0300703441e0b0502e182c0036030260800b0449009c0240c100000e0200740c0c1e5030305030711b10b401100844000406d4141803005034003501040c0c0c005030581a107a8104501401e0218030180c18000c0f13240480c4540c0c0d651444022441000b0440075000d1034081003102c015400384280d8841c101100303040790303451a5603900003513241c0f084545030403a00e500ca00900c00007141500401211910f07500700021440b4003028070203000e0141245141c10151980380500c0d44a00d0480c071500d0038090303c41c03608090b03400c6011900016080c0c014882d144580d0710b501050106040b00c0701000540140d004d000e00c001c0d10b48685c0040c2c88060151 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 506233857 1250 506232607 506232653
    0x5010c1202120103112412090d2109020a080705010f0207030f02150706181104090b0a15050307060e03060703050708040f0303110a0207150905090c0c1c02010b0406061803 75
    0x12110880d00742d5039001006c07008030110743e2a444074025200d44c80313020303003450915440300d401001c0c3c082c1c0201c0902c0240010ba100c0040101459000002402c01c0001c00794205285050107d00c40c0408544201900c0c0d00b0380359102820340303540d001c80c1c2d110740d41e03c0b0246c04900070405200062408039891407250456400b114145822500d0f044119a80c408020320440c1d82280b114041000d0032000780c0c02e240c0201c1d400c10030722000d03444190320248001c061107440b5a5408016074100080781c56000646005001c454401761510000380030003045070201d80c440d22405000454551280c05018801c50b155602c07082c00341c0340c036941d681088520b00000c50605443c2d603100b0021511100c003400140019500600000785854152103501a038541c144c81000100c11040c0981c1d11055089a0040a01060660344000d84038500b400c206a2219034100c023903003060071ba110540e05400101c0208800c0350204011a43c5000950f4401c0840c000d2030702c0e21101d03080c10008555001d500003560716071513603c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 506235107 1250 506233857 506233879
    0x50903090a240234030506041a0c0708120907030b1e010f06020715050f040b030603060601020a02010e0f010e09040b0405060a05010501140a050d0905010c120212010311 74
    0xd07599078400c0d00180c0c0340360590707418020b031581061460800d40c08180040d10034501307841c520003000b1044454450105290300c003110b85000a0880f510004c6803c8810341d983c1c0d06103450460b0000d5007803410300d0b4104c803296010507800718000048400c4a580a0b54503031404000c031a00c2c00c001880103000c00c040d809030035000404101c1c25a02c0600c00e8018019404c220000f07400b03015400d02041e04554295406078900344521a000509901950000d04100142c4048460112a01d100e00c1703402c00741c444404240007608803801409503004145c01c40a44140f9590320004a0342e4101c0041e02030700081b0f40c02e2440405040c5107140f46100501031400d88030309070800d00407039402c0f14252011036040d2080e01c100030a220050142e9500300001250a00107945440300090050490768940d6000f29400690300307c00501a008a81503407184400a010b40b86060134554000c0c282001590003150b0324003404d000b146558421200302142100c4c8900d51039080d0340351402080040d5032819044178010f0b172 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 506236357 1250 506235107 506235109
    0x3071e020a0b0903010c0801030203072117130806040b06130b041119170c0d023702010b0a090b0604051306080d05040501081603111204051e06010905090309 69
    0x14070201505008104039039400e50072003030608560444404804006200d00144016038003ca51241100c0c042c85480154240140e4082446580c0d214002d00c6088000110f4100100c1c02020f840203920000c000d0719460355a00000f61200021107009012030554400201e5a15005400748030a90410000040c1980e036140400c040700c008064100d1070200104a1841d2132a00500d1041050101e00e0000a0f4842180240e6134410029003111100c80004c145080c88003500d03815208000121900a044011600b114200000c0078141c03644001440130070720302c601401402249860711010b400b5180d103919101800380104100200c0940c403960801000a01d03039200b40c04103501070112040007401d640307000c00d400d1030500e01d03e208000b842014002004140e0b00603004903800552007a07490310300c000495046008101d00d545c2c078411007102003048001b182c0007101851140b440741007201e24000d007000e0f6116040d070740c0400305442944a200144694242d036042690440d10a004803810302d00920 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 506237607 1250 506236357 506236369
    0x3060f0c0d1a031009020a09090803130201120615080a200c03070c061d040b0612090f06070302130e04020d140115030807021e0109090c0c060203101509060203071e02 73
    0x204c9801d0310f654540c110041580b501031242030080c0141081001100101c2e5900600d40c00000e150020700320340300481c030042d640601076594440a100307200700040c0c1c0d02d49031a412140c0c20440c840e00000c000d100056400302c4688a0103080308100c0740d1a51525074080301c56840c40e4460441b641d2300b80014401e01d4002086585d00102501c00b0307403191102908568000c0280084410f2461310850a1542858294881c5000c84103c02840c110200450340c0701070b500e80c5854005203c1482a11403c1c2c00c02c608640e0640c0500542c0400c82040b001c0a03035526155003040d10190340103544480710050700400200c01000420240c4423000002c145520203481003040700c115070344195a00180091410110b04d41a101c804652030844980300c02c182c16000002c2031540c0e00e015480d45c1540e5032950103007143c0901003c50240f0fa1003d0295038914041c115910b44000f98401c1410204089034039103400c0d405800c100007a202c1640c015810046a501c500d409418912104801d03450401c8403080035844071 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 506238857 1250 506237607 506237623
    0xe181f0c0210021201030f020d0507180605040b090c072a05010e310905011104140603010305100c05190206060306150306040206070816050c03060f0c0d1a03 69
    0x24100004102400d400081e06100307210b403485218910400c03418842021140a16066030f0300121801c901c4c680c5403001c50540c001903a07006d0701c50310a5800010b940001050f042e5524000750b1018000b1982d80c030144402ea507094110245e0003d03d800006a9201d240800b501c00c01740290000c010a018510119403022090024150040f0401c83d0a000c6075820070171075644802c0c181e030a852074248071808400300900d041c0040300003840c105101c0000c9003a5410410006400500821200004110526183c1d00c80d210f032a002200380d10720318486180050a4038120b07500300c0c3c01360804089a8110340000c1030950b5001c000c4c0801400490303a200b82c1113588a0f00c1450356001410b06003805410980fa110b80109903c00d940c03105611445180c0300402e08035082a4191826038803510549000445e43c00380c21941d45040030f9828081c0c09101d0002903d1b100c0a0007501036a0b807503140d4a0709000e48400444d00c401c1d14800400c0000341010340b075840fa8904000000e05002135403948000a0304001032 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 506240107 1250 506238857 506238913
    0x91a01060509031507051602031618060501020102031b16080a0309140705010212180405100e0c070b040b040c0506040b181804030c080d02130617010e18 67
    0x8089042c0c10701d401e04000041c0c00058062015505241c211402800e600c01d61403400c0c0981c0143c1100030071034a040008020113108100e20b0303081592990807030494406400240407944d030500200041550041c401c40307010b4250303050510a407d40e0141d16010b00d92001d2285860350301400c0482020601001c041d2a40c400155030110304052141000b100c400380e41c82003036140750001d210802c0320380e03000074813100c0014240500d9900d07000d080b00481140c0758449000c81d00303d070615080087c2c0403413421010054481c200084d04068540800d00786050080c06401000e5402141c04100403854100360242d2081c411002e42d5182900ea2000c80d11035000359010a08408001c15401d043c2d800086202200030400e0301c075600303035204a8089844000f0080c10103414001d0343d24410040c0603a82c1e081703500e090154102503540b80e80e40740c6850b6021905104d00c0740001c1a040c40400000f0b000510203040321499010054a61184200c1c05004035182480b10607510034400120461010311681000c8110 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 506241357 1250 506240107 506240117
    0x28050a08070b0a0c080109091b15090b070b06060327060615090607060b030307080a0e010905010309020a051002030c100c2d0c03090518010302190803030a091a0106 72
    0x24442c5004180d1003400341c01000f200f070a01951203409907100c220603044460840000c11720441c40d0078280c03a1580701025482d00c44152440c0858013441c030000413400340100390785090030541d40e4003041800d8090301000509820801022902e10f16200c0040c1d034000714580381c8421303050a404104840a050b00616800c1c54010b4010056a131400b0054440f030501c004000358940546500011001e1080d810001c1429641b8034a183c2152002c1054600e802d6010018650315405240050300004801f016640019011000401c0e69440307401400e0701c4650241403104281e04000800440b020f0408942086100c2841402c40309202000b0108044000410008a945500000800359500c1150905101075680c24522240700740c1446140c284185241c000385a1603280350031100410ba607884a03610180c000f6403441c00d20388031150913048038400c0b6040001007000c1001c80c0c0321803085200b244d03201d400174030004201c4e01e69a00b041140b02d00c500c90310110f040790040301c4112000281c004200081d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 506242607 1250 506241357 506241367
    0x9041b120b0a14040c0e100203040806072c011814040501050118060305090c06031503010e0c1c0602040f060801060201050a02160201050a210f1a0328050a08 69
    0x1018612940076404030955810034100d0400407181c01c01c0008282250199986484402ca2a40301c1c8140c0c950700d0f01d0040550300461050a030003135403500f183c00760030500c2c014070f0f010403043c074000d109850401c404444607000c0c0c1d4224000721a03010031021201818800170488008100c034640302000701038062001070051a181840a003c21248140c21a9042c003040c4c003c0c166030035000382d40c410f0171200240f402044940c0e4030000c55082c6002d2644403a006071010052140304902c2c081002180313881640204080c1e000621003a544d5070280300d00c160025001c0083d00c1d0410210b50380c10805d07d0140c4005454981d9900c0c1200e260500f590205001031303048401404415828040c180d04082620829402c1c9501c40195000b2a8035004009050010000307120480724011100b8141030050014040166104078103102d014103a446020b1074128604070044401c400001541000c84c00c0180040140051844120391100c12010701c1d11040b40301d0001460003e07000700079245003103104e0b000c03580d114 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 506243857 1250 506242607 506242637
    0x90e07180506070c03120c0503071a1501270b18240d050a1508160e090601210503030c040504110c0c100c0605040c0f0b0313020609041b 60
    0xc0d00d69504400c1c410070b410410400411144210314013a0780d0000641c030a10090070005441c040c00e504001401da01000c038462081c054a101d18459800a1060012032551110300480c030030918007107800e012945d520022007251189085520a0a5040c055160740584604111000f60060701c42c0218142000c44001c00c01d08200d48035007801c0358ac40b200140003c1c10f444105010340540c10311068070f26071b280001494000d5a412159a404451800010f1a40c848101d50340719880d50041c40381c001c1010500241403101c5200c0319104184a201070309041e4240507002440554011141c00f00100281324903001c114144002c5002e003681804141d507462629040c44152103170165100b800340424800c180041c03c0201c0c2000c910542120110000d4016800c29503495402843c0941181d140a00b00020407642964200650303041140c1c00c0380c5560344180c000c8043c441160f250f0031820740c910012005061400250421030030050000c10b001207001c2d55000700313615420402c0c0005600169038000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 506245107 1250 506243857 506243897
    0xe0310020a03270b0601030212100509011208090409021207061d060c030d09081909091103010302011b210309120504291207020610061716090e07 64
    0x34140300b81c01c0d4a00310243d042c1e04503641c000c441c0b0004d001c40030310300d00050303d0743e110358100d600c6500030150b811441d0411201e41c03603a14005000c1c640c05444008000700d8405001c85100c000158446065440c210b940414003010b000c99840880c1c00c06006007040d6903072982800b100000e400517035100799160005920314030800300c1c0c03c0d01c0175000308003c206802e5045408404c40705c40d048041c43c0481c502441c0e00e0421010702c50301c08200c6036400303000e000c0d544c45948a1a001c084805868041c0500301d5102001090741c0320038031009000c40c0301200b003600c00840500001d54440e010b01d111440d498518400300000c40071354688480000d5407001485c003085882086042d001040d8030384682000d08090040602d00076620802d0b003403d080740e0000003888000000c50300f110250b02d010f2642e40c181410040c5d03980806a90701d924a40300c440010840c40d102d42c040124481c88401e891500b0386844134041c03001ca00044c0200c041054070310011550000540d040c0c1e00641d05070391034100800d0002c0c18106 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 506246357 1250 506245107 506245121
    0x9020621010b03190b030f01020a0513050a08031e07080d2403080d020c100912080f060901030602030406020702090711010c1b060c0203070b0a1e1b0f0e0310020a03 72
    0xc0b01a024403d002c000950fa1240201c2d20020800008444940c0d20000e4075041d8008580c01c860741c00058401162680700c0050115035199205031039046445030200710b10b1a01034001c40809074000d10a07950002038082c405081000708a1103141380903440d4444000daa40000451440d00d900c8400798041e4000c0708115190151844034210401402d41d035031580184030b019082d014551300442c2030300c6406018030600da141090040104a2149540f0b02030f003815004802c0080414030381800241c0020299032118444d50008040d0310180e030a40d03548800a4001030000d44406500b401280c0060301c0c1c2d0450640100b42030f0300d0b40044c80d51039503000c50035980c842400740304106808040311401c6000c0d4000803d001e81c00440420b62282c2e61504030301e140a2144090302e4012030340c0c00d00040c002c441c0c0c040c04485040c0140c040c2c00104696170b040c1555442c1d400b00d03074002110f1b640314500a1003020048072191445c94074070101e03550180000c0c9000c8400310301102440d80020315000c803503094800c4034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 506247607 1250 506246357 506246369
    0x130317030f01151d03030c01020c0705030c0a0b04061d10090e0c0403030816030e070e07090504110738060f090108030d0c030f23090c130f0902062101 66
    0x1000b40ba00c09070014100c03038102d00981e07480680c50302e00c00c08035517090098584518603080215200d07000c0da1245030380c4a040b0b1040078068010707000f01e00e14900b040d0030783c5030940d007204110074981440d00308102c1d048401d812900039001c446220f84901507a422500800d83c25241e680c180c941c504244085000000141005e560198104010130010742c000c03c243c0d5200c802000d550440b0130100e94141c001c0c02d099070a40c60305000d0080080707a0380302d01c040d001d40528a1581c41201c040d8a038002c1c0022140071140c0b039942c0410900000c0f0001d0401d60501c8411000340201210f0750b0403c10819902d5111084424482c080c1c80c0300300110380c2000190745803e2041100d041c101c6515004180343c41e0301c0341200c001003260f221350080d0a507501135000a0a401000c10080094410079001d01c0382c6040310000c0c81e80c68000300710108191040005203c1c6141400500440064202c0d4210400a00d002020b5417003140d121840c81026940b044060700d001951a0841d00da025460718080d035a04105030000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 506248857 1250 506247607 506247629
    0xc0e03160f051201020c0607091505031e09010902061908220f210c061409120c0c031002040503061003030210050a1503080d060b1905130317030f01 65
    0x4018030750648030700d9800c40c1e6083e1001d251401c100c5400790301a11482086403440d00c81c00040c0725401e6444800e580480c0c1d001c40c200c110301d100400040303a945c131054030802182e58542c00d0f881582ca07116400c40c1c6d04542d20000010321103889034041030141d00100e0302c41c021040043c1c0c0f001e500c5500f0484050b1320000601c0742c0342003104400d1411950120f0f44e42c000e011203580c0c103142400c0111030742050303024000030a840304e50041c1d40b0200410001d50f0788000c032101d80c01d10500c154200c80c8441c6090080c11080081d002d8a072190200600607001101c400c40780380305584551900752014080901e01c04440030b0007580d514103100900d864028050405c002181d0030180401c04217501140764a2144500b80700451142c0340c00e00c540700a04801d558010159281c440008208401903001701500c4000031024445541d50f86201c4000340036181108941000c140000f44040c0d114200030210700d000501203074601c5459031030b4415074000c01c444000c01c07020300105100350b440c40b02d0003090041c0026030031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 506250107 1250 506248857 506248859
    0x9150b030f190c03080c0c0f0409020f01050c03041703040305010c020d020a021e0306151e0603130515090a0204200d090503190305151c1209090c0e0316 67
    0x40d240d034031031100703040c90700b80c21442d8403460421001c1160a4001c54221815030b448414001c2d0180e21014188006c0d4440c428a4004400f41d040902807200c1aa800800e80401d81000000664135548400c1c20342c4685e010030400800c5080e110300c21003602c0303c4214000c40c0c8039070540ca00282141d003448100750555010803208510b030b0368002040810316a041e28040701c4451f152141c240c411121300440e80e4180075000410403400244030200256000441d005055400d82c82903800f01c0314a90210355030803070382c1000000e01c06120b401d02d903d03a207881401100e03840c121102c07003481020003c1c0d500060a40103111184151324003805a00f01480c0e103800e075880d0001d640081583e4034452007426140702030315140d0700c00a02c00c0c00e0060b140e40120041c0040f021292081c0000c00901c012184281005c0588050384042d0400d01010000544104610221900551900e15406038001441c0c0c080150030080424881128002d5900304021350300d8580c0c96016006c00c15003000041c0040c0401d186142030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 506251357 1250 506250107 506250133
    0x102040803030109021c0606020d09050907020d03090c0302030f07030606091103070f12020f2a060f09070f060519030c0212070809040207110a0602030304020a0501030c1209150b03 79
    0x1c1100e045903149040141e0300c0003100b108030b402c140c200551000451500500148864010800c0c0050060540d100700300f1640f13410401c01111307801c0d600000103034080c00c40200118044c1d400313481441e0069501d805039079540c2e0b002a00e0000e544032003072069000208200208003040c0030b2840070306000c1c94140010f03001600009040d020042242c0e0410022002e0300b05860b024500252a403004004195601c1c0071000b09400d55034883e100b420a15401e201d00c0034180881e03002c40321213041210f0f000e003200d0380381c0819134420010090030000507400389100001d0074000c1419503400402098842e02d0b100d0000c00d90030b00341c00a044411000f070600303140300c1e500e9480c1d010420a1307000c1c03054601c0300e40702e88050400306c600b402260452038029100181c03000034881c2c407205a481d600743c02ca648264003521054220784a0005403002504040441c0050040350f00039041601e01c0f40fa246050510098018003420640740c003044207484c00101c4c0c074078400e0303805501e02405082c0c5006600a0650f0500c0c08 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 506252607 1250 506251357 506251363
    0x902121608060702240414151b07020d0807080408060906150d0c0501030509032502121504080a0c0807030905040506060c1b06070c08010203151e010e0613080105040b060301020408 79
    0x450304010b2150504000350400c45007c55800c0340702c80246c2154010480f070106102480e401343c0701c0d81744100d00024501540c800300748c220303022154041e041002010082e0380c2c000864020800403075100106010104182d0410001c1078031807002c081c0286601d040101c01c60740030090035a0018002e441c0c0c80149070120f035401d80d049044650030b01c0c1c00242ca030340d0344518a0660007003030784255a040b01004448611030245e014400180d0085038038461210300c0f0b030412640c40e011100c902259118040c005004a22070002600d02418035040c12686404c8036504c2150a512030001100070407601d1070140001c0c281481410b9000100b6110986800d48880d080c80d60342c500c035030360010800300c48070031011140c58500c1030301c0b0400d91103040c201c41c80d030f25040940e001c0c2d0000c0701e0b00c0da00002e0a0880203442d2804030402c103001d140c1d200107400500a0180116030810300a200190080c408100e0203051884414041004007888000000e16080500d070002010f40d0150120784683c0c018007003845105004 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 506253857 1250 506252607 506252653
    0x60303090510082403120d06151d010e04092919231608091606081302120309030c030109021809120f0c160b0d0902121608060702 57
    0x710b00d0903030305241e610030000100054042410703010301a90b14007a4106d050600038103111400d0744000d00c11141c603070340d031404042d07202c442e81c000080861000c10800000b5554481b4900d00615101d404001c02e00041000c1c0d40561b1400c59524441070041030004012040c0c5038203a030b480148642c0b003424030714984a40702d19224400c0c1c021030354805a0901182503040c100c001016500c61115540c682041c40310800c80100314a90041422440000c2e00c1c8007004c13070a03098107159015051b54917410300c0d0b412600010001e015030442c00b0703040000070150766280780c1030480c4520035000310341e1806810207043c03c0200804c040350190b81407840001c01645c0e0030b00d005480c1090ba0b00748440f250340f88401540303803030398443e009007002c403001400b00440302d101c000a1400d03c0101c0115000c2040c0b02d16900480c1b1200c1c0709440412500384450311890945400c10340c60715000800011200c582c2c0b03c0b28905101000140704085901c1c102c5c00c01c0340079814000c0540c04002400139000f49098030142c40d210300e1031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 506255107 1250 506253857 506253871
    0x103050304090e0102280f0906090b030711011a0f0a0f030b0606040b12012d0312020717010506010f050c06040f140303070c0201081003170a05090603090106030309051008 75
    0xc403643c480d041c0800354140e8072104004032000c4440c060120001444c040d516044000150031562960707142400381e0004c1c3c0c00c50b101661107200302c918050f4030680c41c0e00003800040800240d040c2c46d034a4440c090003003e828001203054100c00c03941e418104040c0509502045015118800d820424404000640c40813a508051401c11075603407200054418869600012034a11022800d00081d8030701105040c10b0f10000d1042c0c041140c48000e1002204c0c9801e00720000c0005400e0041c0002440e80700840c1115042c0d00403520807a40341c17401202000e4034460728100036903403103041014669020004510030710503410401d1921021190b41030302c2c0d880060029140400c0717040c4007401c01c402a04003040c5010240c058075142d05192030000e1007042c0c14101a4000780710300340455200c400742030000c012640d2100e1101c850008900c038140071600542994828414144448005611400020343c401d0454100001d07540d803e500d4054069022a013040380607125076000344000b5500400c000d03800c43e0b2 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 506256357 1250 506255107 506255111
    0xf06040f02190e101b080c03070804030303050a0b0904050307020f270a150302061b19050a0203010c0f09050d17030c1b0a0206040302090615390703080c0709050708041a010305030409 80
    0x180241f141d03071441c8a0210014801c2c000003500006040d17041d803009018850b00308091040e940b40d43c0800c10701003001e0780d018000350020031092005103031000d0100c484080161080f18444040e9171411a0150b458070280d00b0041035804201e11890144908030000440395289580b85080d6004270b44c4600500c82c610043c104800c0342141080300400001200d02000075109040b60307c40e1030610345955948070201d00075820b1101c0313032003424010034009010b099266900302c0010700d420100100c15580800559801d080c50700180da80c941070100031441109541c0c0a10358601a008000307100000c101d009a10b03c1d04230f4001c160040e91141c00320f03800c8940450318074025488120004840418000068421a0001031800341c8403286040c9003005000050341c4044024503120b0310f041060208000c10040e40100b00c1c02d0000603250b2000d000403c11440031240c88036100d400e98012104195041030100308800304010821034030a54001c180b000c110440000e551540da2050760b2400350b8044c110f81c2036 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 506257607 1250 506256357 506256367
    0x11206020903030a030905010c0e01140a050c030711030607050708030c0c031c0c262212021605120d120b03061e0606030f06040f02190e101b08 63
    0x641901501d000e95002002d403503030b8003e0020094000c2c00b8085044034603500340001e44d070b4004c0c09511549000c0f041038441606603245821480c000768800e524003820b0003410710208104500800c003900c40648540c01c102c1c14910710034205468404014403080400000b0480000001c4d8002c060f60f4208504117003203a1117640e80f941c0d640c11030240c050480d040b0b07845070861a6500741c143d0000c00311141661600f100400400090040700c028a580c0c81c44585403000204502d0101104c60816803069544201041003e03a603910002503540e08030a001680b0400c18107460100d001203140003040102c0710700030404ca030680342c0c4c0d440d04086504801442054081d81c0c1d607984d50794003d02908200201958014500100010019007010540003101e10540000440b5418502c1c11a4011058100218419038912003040082c0100803c001905074080c0501c0c5118024402c07060b04010494a8111080d0100310a000141014100d11810404036003041000e20403155080c45a041c0c000760b881ea950 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 506258857 1250 506257607 506257613
    0x5100519090302120d12061d100f0f150c02030a0b09030c0106060305010e01080c090c0703051606020c01050a050112030507020312040b04081b060301121a01060c02030f060f0112 78
    0x250506a0010b504083da013001415003440100e02c003180142540c6840d4108020341c00001c0c01c65215004500705501c5804002c5e20000b0592400341d480301404181c0c40142d030b04c0785501c240300c00d0f490b48604007034a9400e43c18060028903e04400f0a6103c5280c400307244c40c9142c00203961001203203170107401d102c10540415070920040c011a15200c0c103039402480307006c0ea159030080041c0024466954902040000802e803080c0109818140a4000b02002c4550715014442440e99215442c12400d1100422102d00000e0520051380125400303000010303103c0800c16003030b0b070a60383c006100303144980c40c240c01840500c03120f0110b14103858040c40c220f620340d0780a102107480c041500320804007201001c600010303804030a500520030390b07420354141c904a0701e504640d9040a80e441480c154480018070052100840141d050321500b070103003550b86005e0300e030200e00d40a030003003e0304610000743d010030a10381941820010003804003001c00040c48240751840300c031b52003040180100c50780a40540c0841082c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 506260107 1250 506258857 506258867
    0x10501030b280503010e0304030b010e0c0304030f0c150c081e070e2d03120403050c040209010509180a1514041112130c140d030e031002040902030a0605100519 70
    0x40c0a01078000c06c0034000c45000310b582c9800610044405072011000031903030724036a45040c4e000720540000941141c40302e030380030303641c2141320781c51141007041025405000c14244d078401c0041400c0000001003281d84000020070941c1e0050030450881030b10f03400051214070300924103521922504d001111664402c0001c1c1550310301c80c541e514000f2551101d01100d18103440c04204240049003101c6000400c2c000c000094050740c40041c2250300003808100d02c505181d001010080014905146440b5001c000074502a01c40103824154041d0354080140411441c0300b521003d90424601980707452a0824851103510201c1d14240102d0720340c590b6105510307034001600c03d95112200c80041c1880c08188170b1103e0b54502c43e042c0c0da0260412800905003400c902c403c95050005084541c00c1c03e210344007030345c81c626401d00302c54151250b8080f099060b03078644082e1000d0170014802590302e0070004006c0c4281d59464001da403080c110310302c001e100b103500b00c0d01300c6280601841394451400758070402551 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 506261357 1250 506260107 506260109
    0x403171617060a2904260f06130305270a06020c090109020a0507020303030f07020607030c2718090212010c120f090b0c07120f050a0810120c0608010501030b28 70
    0x300a0004100031981600c0c02c48111044400403001d00710030594686c6440d620510030240700110380010004ca201c002082a200103240c2c002e0a055150400c2d1601420300700340340045240c1c031000350f003415840e0391812000c014001c0c0000e00c010600811120300240c5441c206124401a8039030010f10404482d000e24283e402c1150020b003a246c0301c0c90510351602e058003044071007a005005100000304000c0c064400c12034504256640c10b2003803001524502c000c044004800c084c81019200009501d4910700c10300300744000442c101284c3c00e60781e84144402c5000b00a02c04100380d05042000100c213a200c428040200000314002c03c840540c1503400005080d500b4001d400c4901c24070401c10b61a100000410b8868411101140400313090203013128064079402c0e00300e0004004011f5500150312441c40e80c2e8200803103801800d40d031039860f030484085020340c40f0116072508801134104031550700320094038010042801d080c03004821314000181022402d140742d1002c9541d03c0921541802a581c03100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 506262607 1250 506261357 506261429
    0x10605181f020601060311030f010e061906030e06161b0f020406031a092d03040e040c030201020708060c1b0102090306010e060a0501050c03030606030403171617060a 73
    0x2061080c0c41d4009448040c00d000d0a00400e0500340c14040d07413440c1c41d00710b17889501c42c9002007c003079090250362283c41c1c00103440c1070341c4112403102202d0840b441d0000c40300106200d071400145050302c2900f442c141180103060904100b81c5503d18100c494224017100760042c1c00405118854460f0301c6c2880c3e640d9803a00e40070b9041841c2082c00b004101c10328030003407000c014620034500c90303903614140c0c0c0b030761140f40f0324546001500f138107045840c0b903c501840a040301d2901058030704143d20f030340b861507140d90300b190180c41c01c4240c0c3d0b00800070755805204103009072013290080c0171940b40c03e01071101140b00780410f040c0400c14bc003250084208013981520f06203440182035451950307642c0646641900140e41682c492a0b01c130b54000340c2c41d80510101c9194211203009941180d40e101e0802034190002003040d030502652004401840c0e00303d1840d18450b101480c2010a902460f0034020408041500f950000310800000e0140b16038800158004039030400502105140c558880c0003d03524400c8202 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 506263857 1250 506262607 506262649
    0x4090b010e063708151207031112030f0405210a1e080d0902031212130c180f06121509080d020406050414101d011e0305060301050f01060518 62
    0x200303841c0e13500500b018019204184421030031921101000000f10781c2c2d210000882c2c0c0260360170000141d0310540d486004400810070244c01c801080860305503417100d002c11008490004040c00039241c2414040c10405640c140c05480116140c10035540b1704066401412035403805c00951100b056695269015580c450701c1251036615252111000c0d005600040b40b0030301807108c41e0211003084c070041e684510544080b0706c1558442c80400a076016402c0801d071000e554000000c205030046d10040407104000500010301c0c0c10b01181031030301300e80075034005400c0f8501c0440e05038085050700c00705000303100c252100043c4c00d07001c9241004452003051100d011403400864001412a00704000d0700803214201100c441000e403c1c0100018903460340f00c05c10109a04003002c00c0e0509200c121400316002c10b0402d0305080207045401e100705510a0382480000362500c042000360b05081c06195040308108814070055418004094040d01076044840000c88240b05002c2d00c035601c00070b1112801482c0002 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 506265107 1250 506263857 506263957
    0x904090b0702101b0e0a090501030b150a052b050615040e06010819060b0405040b270d05180d0503040e0108030f0d09060914010204090b010e06 63
    0x803110800c0c2150010054040c0340d40400c41001580600c0034000015000c070050034422103003d4807030195141d1019008031b580c00c1301183c204c1342407240034084e5000b18070140301351070b1558111034815654400c0c0e40c058000b94004009a440d10103072201c2c4000c41c11410055080d10f40d0013800075842c446805003c61150341d050016100e401c02d040b50313070f2840c00e80301401845160821103036612420310440269500030912520842c0100b807100c103446108030000f145c05068000044c0c2075480503141030314030101b80014407510034031509002c400b282c2c074200d11203169000660103d8466040702503600600c00c00051841c14100129091460b80c90010104480424241002070340c9402c42e0250070818060000042031010b400000d030f5084d4050800b80510b001940700c0c0b0b05018002c0000f08560701d079254101300c00010704c0203147c4c201c102220000145c842e4074003010402070b00d030750003041030500690310030003490798840c102281c00c0c031000c2d56038102826190a02c1c82d01641003601c83d070101440321041e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 506266357 1250 506265107 506265113
    0x605040602010e07030c120f060f0b041b020d0e0d0c0305011a031605060d020d020a0f0306090207080d0b0117130b010e24060f040905060301050a060e1b090409 70
    0x60410340302294020800f200001d00216954a102d00021305103001c520810003031403404450107072000d0b228201c81e140f01e0b011690766405031001c203450610b03038545454107142e050400744184000c2d500509008580d00710842c801a4071103400c04090402c00100c1411010b96807140051091866071100d801a807855480c10024004c000280d00c0c080c0d1420100400c0c1c2c1c203440e0000e5200c100b170b120a103520071564a42000c20030b940c0e10550703072103813801d070284043d1000060b0b070f2016040c1382c201d5803200000030750b0301d4a000f01200c4194001c034007a58814010302d40071400f40f4007611407400104800090803030841d40180c403c0301d212440b000756180c0b200200540940e01c42003003104544140c06240642c0d88a000030840ca060071101d41804030440000d0540c1303022282c040e481d0010003e45464580098003280041c20b034000c2d00400d030141c0e2100d003441045c0c1024450594809506901040501d040a0003200802d002514284220044143d44103280389180700700c40c1c52280c010002c210065180c0f0b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 506267607 1250 506266357 506266367
    0xc03050c0708010f06120c06211b020f06090c040207020402040f1d010b16110a0e010f180209030304050d06060e0f070f03091e141516020304030f020f0402070c06 71
    0x40d441c04204d600b810b0001506225101d0503051007903020785500c0603541046804c8404411220006402801400b103421075a40d244c03268014500800da4040440107490304060b00d031200007006045264000002c10011010225003048039003421a00541c4c0c0b5107035400098048d010355000b130154528243e40008942005864110f1680c2100b41c400b4426a070701c40c0b0003151801402c01c04d04403050b00300f40c8140001c40c034006410a0210081860381c240c0d841e101c2202009038260450f0400060444062041140c02c0025250361034200c6c105603e410350000102e5268045e500c982d5000c0c0021980d80c3c400c01a6540041d07000d02031417003d503441032404100c5900d0306c078010b8074000c001c26991405044294402c1c0192000d01e1780160040f0110b500c646045c510541c491042503942c00c407000e824aa01042c1880119091190f20505440700d00345180300d00860020265641c05551040008000044000340f03407003030071074040791415000c10600c0d0101c0e0280c4588000206015180903001c12021780103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 506268857 1250 506267607 506267621
    0x20105060307060305010b0d1e0e0f010e06010305070314120712030c170f0c12040602040906050316090c0c02031c08060411030c0a02032701080601140a0c03050c070801 74
    0x101c040b03544856a8400c01c0d01207820a000d0b1501441e010405421003001c1c0b904100c030b80569490000f820180340c03a46441c2110f100000b04500394101e022503503000f48d800d000c3e03800008000e030042c012551444c0d0b2070b180d4441d40c07440014011804140c851071020700c240320034480341c0710f400909641e40d80305213000d0110051800000000c245841c8880d250244a1a0381060580d8240c003c02c50300d44540f424601c1500d0000e04c180700c0c07000100403a1112181078070f402c601403842008090b8031a41401c00500c02c1d034880b80c22079402584032025041c21400088504801c41d81d49000024100b55100e404035a01c105025000c0d4162207044c401c41000b00d25014001d102c001103507500707070031170711011301300b105035401c1c2d03101c807000303a24103101091070160600001c0035401c0c0b040c0100c91804944841d06260782090070200d42800800302592405035030081318080d4402e1003403810080c010300071100c084046c05070714219010030200340380320340c20940690700f201d009024a07000c036a078056880c0c0030140a000c003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 506270107 1250 506268857 506268859
    0x305030403080c0405032a03160801050c1e09010207170f070905130b1e010803041a030408071407030b012601020a021f1b050306012d0c02060f0a02010506 68
    0x42e400083c0b004100711040e5070a0300e074001d02400320103007101c4024551001c0388503a0b0f840d2581000030241c560350b04008148807416800d113400c4034113141c40702903401c44400520084c51410204071021590303a000001c0d099407a05042e48548945010f00106e01d090125000000b000c0543c0d0401c3c110a000068008a018a50422600841e4841d1032480944c0e006440c51241e551a80c2c0d080400500d03004078480d0b000c44944400c40d000003101000e4071988500313900c08565030304005014003050032449800107108404c035a1702d5280d030408d40e41c1c1c0345817841002000350104107104810082c04106001000003141c2100d04502c03d961a01c042090701a2180c07070798a454050307280750740c91101040c029100200401e401914401424002e603480f642d1810580c4808103903107510b290f102c40600091040c1203151a40e41c2174603883c00600140100c080d0080a201c249509100040705604820301c0407203100c01382c50490541c60051000c180039008080348041104008980c890b1384590551241d481100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 506271357 1250 506270107 506270117
    0xf060f0b010201200a050c03040902070506100308070f0201030f05090303010501260c0319020d090c060302090a140427110114090618180a060f0617220305030403 71
    0x10300e0314010390803943c43d150b20000d428040285002030003000e01c007030304414800b404c0c4945440440705500e0705582c06500024045a40450300c0420b00c44100903e41c1d0040f01c450345c52040c3c1c1e0454a9120490040c440c0044c0324000c0c09048001f164420340081c403003000d860500340140c0c140003500540780e4109019460002b00c209145540005540300c40d0088170903000c1164401e0380b00c1c1c1010744415400200010712203142140300014140540c0700500c415a007d0303500183c0418130b0b1a045c5090040b036440314041600520180b06141d564400c60412600749041d04415400101d0104025159400003000384006c0703069045251002c044200c07455502c6200403c6202c07809030019260320300d942c0f600868904050214401074203006000300805008160700f81e1084d444c501c0040c4405c4482d10014038aa08403005010107a1050f00848019140101030712521034200fa000900e00d201042c1c942e1201240c175008650301c182c4400c0755541d9140d221040282c0045241800b0304190b01c20b1b03404500140c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 506272607 1250 506271357 506271371
    0xc010624200601050f06041809020f040c080604050a090b090a060c09080d03050702070f0902040e0109020313030e1f0f1d011d061209060403020d03061412101503110d050a1704030f060f 81
    0x4581403003030141d6442c46853b03200d1162100000d00c001400010050b00c0b030a0390f0b038000d200105031454440351040c0d580348001c0081c0c01283c50044280d50701100d800081c441c0680080c84480700204040289600c0380c50700103803690720108124503100c100e80c4036428120100c000494014145d8004106880d0385d140c2810040c0d0343e0305c070b0b020101c0c8030032680c0124020b12891440002403244080a10002c80100700301008091161482100460240403501155010b45034100494014082c558001100d00b0720b4000300040a001074040f000008040340a0200d440100304c07030755240706c01d031500100401c070211128503000402c2955201c06603020f401603c1080015100e9511038028a0306595a05083e0444400b113441070003500040200c001360f81f800347c42c4500186140b24850850b200300340c021100001c51a60402859542c49945aa4019185924403001050b00000e00c1540590b0103003170240c8400e40601350300b5290007242c100910b038004000343d0030305224041d00880c2d2702084007803041100c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 506273857 1250 506272607 506272609
    0x201020105011a0418020c1f1d0d0e01050f0f030103150b151c0e0c1201022d0c010c050a270b0c010624200601050f06041809020f 57
    0x225116542e9040c1d140c404001c02d0252901e001105c4103005c00d40c0030003605207000425210b041c803c9a0105002a400070f503c115080c8100380100c5020020380c480869024011407417003610b41c0340040da9142480701042101100d03920035012641240751071701c0003680726003100468581d580d000388000d9034401044e90004001044078810100c180000802e09113000301898524055a00075110f021556002c00030158481074080c06943c0360204000042e02d8400700407802c0010342c90300c00c0721400300c1368410712032140d612005182d00c0b40048043c0300542001d03000440305103814426001d40c0b88a95003440e602a141c3c81d000006000c07200d82c0f545031044407032010713122070903281c502da102c0d101d0010000d501000298066402400d403400a1400414002e480300800444085041084198035031240c3c03d100106070710400350310001074480301c240420161507040c41d23076a09043c001d0600c21481045405041d6440008540040c4204a82080c4600408109000074440c0f00c605034003c4002c40e40551705 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 506275107 1250 506273857 506273879
    0x20106050307060c031b0204020d051b16201503160509060711010504081e06060307030c030b091606110d03020c0d0c0f020603042118030f0c0e0c07020102010501 71
    0xa45489582e044c8031014643ca044804040030090240b0300c0748030350090000344e2035038001408158075064010400e401c128400c0317a146c0d042804424081c0d00305000641ca189001e01d5130343d0300e00c5d410007441500317406000212100c0000c1003604c958068015848202c910b0300d0305015504c180c2d01c0c02d514008855006405448600c80c40c0c141c20f034072a03400c00040000554180804041c000d0616206040c9622641c01074030341010b85542090b091103503200c10402500402c00e01e940071005a0261500a1561340d4030345c2a80120300000b08480c01900016a43da5002c0110032042141381d0180c0402e0f5696401c06081c44201100120b00790044014006260b4024000c030391600300700c03c0003071010040da00d104640007800020100c03100d0110710360410150707841c0d030082c600560043c900b00030303001050710700c00c0c0010a1056414050100000004222101c0072101c1c80c00c0303079000040380301841541c0c5000c0445000c150400d01000a006080c0000580c0c410064845540300b238008000036602d032406500 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 506276357 1250 506275107 506275109
    0x14010303080c0a0f0f091e0305060112080f0c0a0204050a050105030c040603080a1413080312100b04032003010c050d0c0206190b06040e010e0a0c0c170a17010b0406020106050307 78
    0x100315400840e01e5044c3c400c40030722040320310300e10f400700e45035448205818004c0c82582c03100b12147e001203403d00c24408240601801401240c445c0c1941e181e1644d9403131a075004140d071100d04201c012a030000d0411060194407d40d0f640100200f28a250510b401c10007801c00780240b5000b4800c20741003c001e401e0a200d11003c0d66040000305082009003901264880c1521030103000a11041c0050322110060300140c102070500342c806544c95042d08040040d091100400300c1c006050b400c2e004004403070f0b06804650580350030840c441019030300038640f20858007040e080b60b500766103454014612507901401401040c202c0344402d01c42c580c1719440484c0d030b588040e2126080c25960f0290082e184100380d10000050304040c5c40c89050658500e128000784800741d220040c419400b50030081c0d011b41e00d10030603103000354600f480e01e20301d42c81d902c81200311481107900751296040040c0e0203002d24051172802d03070001c01580d078020842da12203080b142aa0880c0c0b289038003660030202c0124142c5000300d6120 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 506277607 1250 506276357 506276377
    0x309032a0c140a090b0a030206040b0c0609031c050621061803040303020c10020109051002090f0603130f020a17010b0306090a05060417090901060e090a0c3014010303080c 75
    0x1a4200303050a80c800001c00c88030a05c40d60029003640300000689640016000a02e1b50f012090745489012002c1418400000c10281d090740007045001c02d025051040c43c00b841820180020fa9603451102040c800541411085510051800b42c070030080c01c0003c03258495440503015482000042d900707203075280904d01009005da00714018203d01402c050510380240d11182c400454030864680300c1d2810701541d426070000b44d03a000241c001241c20701a01071081c001d010f80c1ca8602d14a0212484442c0740c040c1c8200400022224510105558035502c2c0d65015220780c40745404c1c5021400300f5280200204c00080e03000c1d01610000500a500200b2a04400e54000300500740e80e0b52159160788140c80010f4024a8401d0180440e46980c1ca60a148a02a00d00780d01c1d40c01c92501180c040244560001380b091018600708000805420b40c04000b682d8602c00c490701684400c0f00052a2030308202e2040911807400d85030691034904070102002c50350403a4069140c0b54115210030b8000d1034940315291641c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 506278857 1250 506277607 506277619
    0x3603010b120c06030a0b1002160501050a080708040f200a141f02071d01080f1c0f02070504110319060305060f1e0702161e03030309032a0c14 62
    0x182d016418040001c40d800100340100240500c0a000029201c2d04072909940060b41300343c1c204085040100c0490300a082c090902d2400c04004c90001094014001d11072010400001e010500b0009542040c2c241140e0050b148075002b180c6050341781e40c08450b802124491442c1003400264400d4071401c2c1e18084001402c0d81e16a03101081b06078002c0501e51065400b18400c1140004840c181c0c0311265601d950302d103046030603030751504540c0ea10700820f801003030700305401401100c940b003d074100c040300301541e03d8144030250b402a1034050b4200401c5a002507002800e142030342c124500c0d000010340c81018001c803040c144000c01400201121403d000050041c0c2c400b80101d1400c8000e400b440307a200030044001c0b020312001000700405810155004005030f88a83c8010040c000c81c0140100684a06140c00700103048c81e241001018086100140505984007000c5041c544101c0026144c5000d040440c0c41143c2d031038000e1640900f0000d425102038421781e44c0412106411591032807100b100802c4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 506280107 1250 506278857 506278873
    0xd1d01111504081201060509041a01020c10020111040e04020102150702030f09060708160506060d021f1b03090e07080f04110310091a0f060310023603010b12 69
    0x411503200301800507902400300384141d44c088011980401d000e084141d440c1c507112081e003828442902c52611611b44141d00d808080001640d000414080c029011101c01240d0210404241c1c0140001048400458400280405c00d1030301c001c007541c0a40d100780d0842c1c00c0c0400581060750741c00c0052b00d0400050b00200121206800208040e04a00b04002c1c4510f103840120741d60542c480c0c0c04100c801500710390000c015000c0c09003d00c0140e034000303420b80311507460402a500003401c00103800c40f0303298007844201b041c2400b02d01c902d280e90440252000c2d41003004209040103004d030000c52041e502d81100050000311410300c185c80d064091414100f811419480e6596000d01c016910198640c0501c1244c200140400107409005481e071b02400c1c944004408408c000814041c005010400280326842030003a80d88000543c50000300e4908001611443c0e186000004514490301c50345440300c240c1c00203000e90501d0160902103010031002013215084000c140030614807090750700e1580b5005490 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 506281357 1250 506280107 506280133
    0x10f0902090105040b03130312150608090a0b2806060905040207020f150c1e0c010c051c03060602011a100c050c040204090507140c0309041d0d1d0111 66
    0x1034450880d05040607820261540c0180384030f074004490003141c544461f21810203058115840c041e114040150502c1000722400c3d07540c003145610321600e81001704440005d0aa65814801c80001c0381d8005c644960609242440900130000b0003001181020408417003012075400d88034203400c0f6400c1d601c540c1051442c1c401000029040726406a0300074207802c00c3d104451380d40c80e4026004600014075191030381c95490f010b134600111a003a0103001030300060b52a00f850000120000741101c246000c0d040c00d942842e21506100000c02d21003890400e1041244a41c1d0f05500140107568071540200300c54404200d2040050900500c42904138028503070704420136100303240c003045a5000e44116502c0d00d01c80c00220b0102c3c1d2060b0b02801586560f142440006030b8004d803a8041da50071200707841c0c01e04040300402da40300e1240c0000e1901c00c83d0344007070700001303680801220342c44a0303120002d80d6120352402c10003030452412665500703940210f46100020701e40c0910302c04105004048002c0c00710300320240d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 506282607 1250 506281357 506281361
    0x1091205161e050f030408070e010806060409050f1f05060d02010c06020d0e0a150e030a120c0e060309070e011a1902030903031801020706080f190e191703010f09 71
    0x1030842d00c1480b0b0803800c8800403800030400c0c0c40111072404004c550301d84c6000e10160600c1541d4000c048000340d090010440721800241054128004417400a40c0d11f5840c5091031800d180303140b138458540925808048107041d505101d900510240900b0304c095644c03d0204140f1100840c0c009011681e103039103400c0800c0a5078082c1101c3c1c42016000500c0c0d01c40c0c190350b145844841d403c11100c10024801c6888520018010704507040700e80f0008500f404140c0307c000d4100040c42e002c08200554414911150522607040341c4000180580042d5503070420010590710344c80b4a020749840d0003080700000400d030303218142c0d641710120703107030941804c04114000d9401030100d030023802400c51005120801990345c3c2840108a0000c080055200e0130980b00c0019040400c103a2228003842182400c0010030008002e880d940103003440d0107180c1e14680030300c0107801070080c0c2048503000e110390b12102409a0a040c001c05409000e400740380f01d8009a070092200610090141c000c00c00098502000606815 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 506283857 1250 506282607 506282633
    0xa11030a0c0e040905030d0e0d050f13051305040209161706120d020f0c090c04050111010603080c030705060105190e040c080a080a12060b0910090905090109120516 72
    0x2d02c0c141039000320b1140000c058840383c400c04d81d025000001c541c0f40c001861301c074050f980c12420015203d04000ca038405441801403141da030009140000710196800c0c58201d65101628000300b141e04030b2108081c20600510b07040307504a00401c0f211001c1010b101800c0c4804283c0d00c5940d072409014100e081285003031403806005590801c0c2070782914516200d0900015859100503801048500c038504030300c07407030841c82044203400f0f214008103000c040b40f40f4030f00320f806846017800c1003201503280040090050040d644081c1c0804804650a084008040b0040682d607024008442090b6280d00420214549440c0040b03850300c8000010032000900c006d009500c01d0044010100668be1400190308000d181c0d103003120f180600150b1ba60382203410458440c210721910b0402c108403800c0c200580c49074441c150070640300703100141000c00c80901c00d400e03c501511f41d40340d06200504107410840e020b0542c4050440d0a0384415030010003480c401c5003a03440804c2060300e50000380340f00f6190300c40d80c1c54503 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 506285107 1250 506283857 506283881
    0x19020102011805190c0509040303020702010f170a0207032c0f01030b061615020703050a1704020112050912041206061d19112205031506041503020a1d0a11030a 70
    0x45d240051555540540c0a101c0c40c025200940d4400c0e11344001050652024841800d00207a040c4141001200f040713a154003641d11030740140d841c025420b05903114120700512544113842005400b4440c0115200207141d81d10580300750805141c0308005409807110f03406901d412510a000348048115400400c207003942c020707002c032109409000380b004181d82c810030301640031510001c4c0d21074000e07a000c4101400b028510b42c2c01c142078100b0354002840ba42d440b0401403040b649a5012887c80d8400b4407418110010514000741e07201d40d90190610300c06e50b0a902034405600d02400010f038088524522821000b070200701012542c1c80b207a51004106c0781c1d02d107240c400ca80d42c2000b5030017002928024043c00020300054102480354483d040003009080c2c001500941008141203081411150025000f10040300d000c18a42190801031030190582c0c1d001960100ba0008001401c1801070100d64940087c0c00d88190103a903042c18038011354500c181c07612a5440100001045001c05500c41c41c0354100d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 506286357 1250 506285107 506285123
    0x18170d0801060302430b06030c100e0f0109180e010c03061802070804091109091503030d0b0303090a1e0b07020919060b0a02014107111902010201180519 67
    0xca000e14217048120035442101c1c0008080c080c810289001c000804d00c440c81118402a00c801007040104160007014940d070041181c00b40310650343e800b45404c0c9018080f00c0d103041003c002050103410141001d41588800b5501e00700800400c1403203801a04143c032243c044507410a11450007900095100010603540d824003030102080d00d20b0103002d180342c2c1e190380c50030380e07501c40c00c840c0200b00030310802500001b0240d0002a541880d03072804401d5901c4900e15101c0040c61303240002c0031070f082d840751603049680701c1c041142c0801e034074201000101c01100c060340e2405039141c4481169016216460000e9030051501d400034142000324840e24858003200c2c0004140b29a40d80b9800d00e031600241c0440700035035111140501c02c41ca4088000d80c0b40000c6a01906250002604103070300505d10041504880c0f5201000402e894064ae000039000c2100c4411101215081c1603070300d02112600380100d005500301070b49001a20301d4501803240058000028241d82ca241c00704000c22441403640c1190160 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 506287607 1250 506286357 506286457
    0x1b0d0308070804031218050606090103030915090510020a140c0108040605060301020d0c0206090c061201053007031112150a06051206101d01030318170d0801060302 72
    0x58074003440c41000c02c80e2921b0301c110340540c5002807e021009100c1401514a60010008260704c00412811503001844400c1d0b0707071615800480320308078250020340c1c001d0503015015681aa0000e1b043da603090142e0350f0030000b13014a04806840d11004000c60303001605071070124001c07030025888981c11800041c0010715041800307441d40700303039602c0040310400f603000001040321240051011005440c41212106d2074001c3c2003d44400c1d50b01d06001c0c0303d000d000194450f0705203600c3c002000c0c540c000d01c20340d4045441d000c0401e181d41d03041c1a01041f03c81d06040318440c8640e0908040c410716021103513026004445811002c9600170100034240c2220980b11a800902904c80e11b2817000342e2120f050203061240f0300404504000b0003180d01007102c1c0d088218102c50f204181c0c40c45c460542e0350620300314140c09100d0035132030810a1560404544031500c100003a55135003000a08468400490b110242e80d80e9171401c05070120300074403007640b038050304415040e042000f00e040c60200a00000e204c0c04114 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 506288857 1250 506287607 506287637
    0x60806090106170a080d0f1812120b0603040f051603030923060715150608091029060f0a02030c0f0714060c0a02040e1b0d030807080403 60
    0x800640e025040c40e59581810310000e206002c1c00c3c20704040b010000c000801065603240528421106480d100c0c0d580c602c0824108040da801ca801e40044000141110304142c0c28441d11002510741c03c0c00c0030610424041c4507078a82800348601c44000104245d081d0f507129181d16042c103811901c111518000c598203c600c00b04920340303c40185002e03503100d103441d50900e85040718003a000e0314000c600e880c00c4203400303401e0394a81d000c541599600210040032984041914009042000741d031400034031a240c8040f9000e98001d00c180e00c12240702c01220340999461000c2d01c200d1300d030040c01004008841c00c03014828180c110403624810304c05840380b40303000194a0021203a42000440ba80180c0000603581014a410880300380380319582405050610f25040b2528804024a20154000c0c1030101c1c8000344444140164000203030040c0042c0030709100c01e00020f450703d03843d0844001000e100d1006041c01c3c1003c508242d5090340c1034890401e591036021080d91407580040084003005500d0380301c03001c1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 506290107 1250 506288857 506288863
    0xe1513031712010e01050607030f020c03010f020a0e09010b04051509030a0501060510080c19030e070b030a06091a0904050f0109051501140f100203090307120c0f030b07080a0608 78
    0x7424105101c054071010003125003445804103a202e03598440a42c40140b240341c0c1c8a00841c0c51031a410b041402200205090990030808481d401590551030200e110746d6010854006007501840c0d96980d1456408150410451000c03c2c01500200e03c0d0502c814000303424000790302c148171a01a44210b040c03240410005e484c11481d248202d40c141d465060401c21030815141c8034231804c45a0400b2425860080c40f41201e502034003030688200ca4026071030071b240c24001d0340880400340300070098515551b00c980103410f15601c259074200e04207140010000d0050380384d214004d400c032850400c480c0310800681c20000001400f42064801d409401103021844d8400d2055100e070030f1003040901141c4a04803042c0b2002c1805a1040d46c41581d908174400310381e038840241d215641007c8070700400c00146281c1c120f145009049080f90103204d954000b151300424001c94600152190000001c0700b51107640b6070060035407510005004643e001c011448540c0103000041e80012402e100049075130341e502040349 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 506291357 1250 506290107 506290133
    0x509030a060e0d0e100c06050705070525050a06050d0507090e09061b090f01080921030901110a21020f04030b060a06031a1201060506040b1206010e151303 68
    0xc0c2d164400c400c4200c0440c1c003c15040c811800488540c41d074020031a40151407402a204018070041d82c5500142c1c0040c040c1c02907481982d001070407941244140c10102c1d1311002038845089000d944010f0000703031841d000400506655441c1cac0d8a5043c15002c0b000c140c05801c01606110078001081008038031780d81c0f402d942c3c0d0b10480350040185914180402c64886020240703000c44414202040513404030744943d0314540c214203080c40c0200480d41d60803032035820011014000ea41c280c103480c61079002c01c41d043d8041e50048034504020003c414040000000324807c007510080032504440403101e12860035502e00d03e103400108405450011009000ba0940d80a508205c940074160380c01d2000c20705015103008041d0140303003800c003c240664824201350040040074a482842100700c0203580100030342210380145070240a10b6207880c2c580545151030f400c841d4094241c1d06000000900661043c04002c0020780083c055080382d02c9400d21011080e48034103417158048900d001700100040710071020031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 506292607 1250 506291357 506291381
    0xa200a080f0a090b0304021807020a02030d0e1801030c0e1003020a18051e01151713020102060f060f0f03160603021c02030c0f0a021203100f06050a0f0509030a06 71
    0x1c1e5102c040345406004512a42c01c600402d0800740200700060302c450b03c0103010390450101c030094942d51300408070314102105100942501034012141030142d0841001d0344024812114014424135810030026240c00900c0044c01d80c400720642000303c0081008015000890030300c02c6011140c4980100700950502c0e072101d1400321400c4080801c0032514401d29400140304032011400341c02210750105000c03418029045040b441402007100e80c8e01070018040042950702a4010925100c800c2d03480302c001e20f50341030b405805944005811000e1214600d446041d0040481540207d2003003030004075900c4208440c0c0510a0882218407888524a200300a00d00d0747c3c0c01590307488041342e1001950120500000d065801030003070150205001c07003600c20740101c0c5580c807901c403071503100100e20f030038181680c0b140604c10010a20494080c0743c141401912060f40b0440090f070341ea40c20441f014425407852800049140342c415456038801c2004040c2ca103002000c89401d40d0305a15408111980c4031158 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 506293857 1250 506292607 506292637
    0x3030301030f030c140709050c0703020601051011100507140310060f030e1e010e030705030d020706061706100609150f02010b040c050702030708010c080c071a0906060909030a200a08 80
    0x400100015000351a809270006140038184520ba0f900a960303180103005441c402c1d80d042d0307803000c5503500c02c04c401d2031083d0303280c0b08803000000700c41b03030400050500303440301000a10010043d0506d03031104c100300c9014000c841c910002e420301e000401c54005400c18624020140c9400070b000b0f0b6840304010001c4486c4152000030311010626640d6800c680d001d4540360040e8005021040129401200392244008604005a9036030300324a0428008d050f1fa40008015440440e00c108000718002840c9100e03244c0c03015654030b903a031144401d80340d84490f4400d40e41640c0c030614058a61510030348203483c036540e150002081d08030b2075000080958100000b01c2c400507074046142e81c10352608110100040860000820020003150b000401440004101c03e403890340006008003000100402c070841c0091110380c03d0458184980580d84900054420b2441440c880e404210f008401004841c10b0b801c00e9101c0b0760b0000040b1846189410540070450068010005408041030307603c0c009140c845924181 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 506294964 1107 506293857 506293859
    0xe060403231c2619200a0302092d01120e0303041b0806150306070801061215050d1b0602030412030e0409060f0605030c01030b03030301030f030c1407 66
    0x442d03c502d111403040106800da21402900c014044a505000301c9100c030641011300d0940941d41c8005c801c00b0440c06e03140e28000d6008007650040034090340e55441c409045014610070f039029421120030040f0140d1400d40c0c0c03003401d040f941e4581000400085080b612441c2ea00e010092004202505800e000c212400079841c400000f419a042101d1440c86e0080301c1c0455010400c0c4074901034459034020482180c00745660718145c88407503490000d10102c001c403980c09801d04401080361400c400e880807640c0d49601e040000b05900a010103000c000c01e03942080f00110065220a003150000e10082c4035030a2200005240340e41c051405258096402000400500d2905c4008003010301d09a5160356548080d004403040b00c208905850354000c3c1803006605aa5480f40304507416042000180006840141c0303036450a80a0318042c0310701c070b10070340e5462702c41e2105550307100c1d40d0307408200 = true := by decide +kernel

theorem cover : BRFrame.Cov 506115107 506294964 := by
  have h0 := BRFrame.cov_init 506115107
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506115107 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 506115107 ≤ n) (h2 : n < 506294964) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
