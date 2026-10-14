-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0994
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:42:41.238064+00:00
-- url     : https://prove2.me/submissions/ae94d626-c256-47f5-a50b-a9014c16e623

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 178597122 ≤ n < 178776978 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 178598372 1250 178597122 178597129
    0xf210b030a0b01080f0d020c13050709080304140909060601020606151c06090c0305270c0303030112030f0f0c120e03070b0c010f090b0408030c0403050313030c050d0b15 74
    0x110008000c02c1c1c400600c2c0041008080801c01e40b500207011400c0740c0000d40346003800ea0311100c00401103a040003000c0381c00110291550800c0f500488a8101441e40c80d8507807519034250740c841d800c0b40da440621100e200ca00c1c1e080c81028141e00c054000060616800c103030300000d481d90b01c060b00c028450580e2007204081010880f04440b510501e4003540c0840c60714400398000900520300c1030401d120714048a103912070f80280100307449004a4240040c110705d00c10b00d4035001254038000c600d6144200d4020300c0081e10108003c41c00303001000f0034140400d5070f0703280c010311068160000324108141202e0403014103401415000c40664440421125404d001d00110741c0c00c00d061072820780c540308040000410b040c10030002c0c21042c181da80240020410701d81c6e8041513030b884000c0101403108030000100032510507000307141c010001c111074502c0c2655949031039203160007180c0040981c1e05c072488200100180b0546c001c00400003540c221b040c034140d98030f0b590740c4041e000b044040d04000041c100102580e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 178599622 1250 178598372 178598383
    0x41a03060f2202041d060303181e0d0b040204230c071a10030302060108010209060306040c0e0a0b0301051003110306041d030c16060201060f0303030b01030603081206010f210b03 78
    0x610b40c140840d25643d81e204040350604c114442c0c400ca000c1810081401c2c1c0c2070110485d807041005501c1c80c2c100c0720084003882880c2c80350184424210110b1000308074140d4403243c1c502030f02d5000380003003449824075004100032151060ba030142d0003403440b00d070400890310b01c02c1c40700d41c001c202070151500e07030100b400d01401401c07114224804508401e4104403011032007080b00f100380c034026801c841e116a01e4441150807442807400603580b044041c40098507a140c6508001550102454008410480880031800d0a007054012012904010006010390b0926940e444180300c81031405004e4221a00c00b8001c0700e100c050314460249072070b0400c0203070f9079480712000150062003904a076035910200d803a00f625a1030f0f6849000181004c008006052031050041c0d806036280d011008000915555080d802051000e503918141900c0d00701c00804101c400000d403118000319200120307e031070151f000411001481c5070190600501e0120315281100d4405c0010328404c4881d00001e14100d240300117480c00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 178600872 1250 178599622 178599679
    0x90c190e0c1b010911121b0307031a090d020c0d02060325050d051003030f050c01060b0d0902100212040b0d0618240302091605130b041a03060f 63
    0x102034280c0e601d91035260551164038498040c410b01984a91803604000780e11102040c0b0034070540c00814048181f10350001c4540c0045002402c8404841d5242d40380c90300c0d14450007410180340b2035030b404c1089015080c00960103950003440a072481c1c903080000240000c179200c0010340201c1004c0009000180c11315480c2540c640190300560b000c8103910001400c9501900310826190f04001c04039094990190743c550661740d2688800031a0b82e5014001c444c56000310710703208407540d00d83c03900241c841001e000400f81c08002050211310a81a80180804511904000e104640c4003000c0003d225200205032000d8801c0c840f803403541c5800b151012000742c0480d030014140c081100f84c18180459503540b001e510000b16201c0b141848a01c6103000b843c420072440003070741110720200001c940800c20b0f152201a11070340d08226042888000f01e0b00c01486d0b1641140100100001d02403007003480007418550001440c0d400246145807507804181070511002525010302200889200d9031000d001c58036211 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 178602122 1250 178600872 178600897
    0x150303070f0c060e04060312050f07170d0c05090307062025051516060905060a051902041d04020f122b02150601020c0d030503090c190e0c 61
    0x11003103030502410302c091500c0f40b03201052400d1000d80c0682010f0040300212900008000703c003900c10301040e03d66038801d40c42d02440380d03010082c000010341410900070f81d050015421a0b00d072000c02c6240f6080313076060a80c400030301105101c00320055034001100c0d010f80d2814034110001110394841144542c0340041c40a5550090400315010702035103125581c80d0800f2aa01410410303a13900c240a00c00220300390300000d603001003120740c0344003244400710400c481c0b040c1000a481c4001c2d8941f641440b03400c0e242600d8258856040c003820070250511108101f41c50341d01140380034a0614219610410303981c010301d00c034080400040c00c0d59261030750b6a0074050007030071090360100c113408025160f00f02d40e0b4906d84440c0c610351581303035801c460310007498442c01550000c12048950000d20104000700401141c11841903200ca90440c0d1290081d201c0818480e072506901d074103201c0c010300e0419010f04e0040e0b002c0d0901c460720081c03000c1c420390300070201e9019020300c5201c1d4444a83c013540c14825080c00d01e41 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 178603372 1250 178602122 178602143
    0x6070c0203030f121e0106020303011415040b090a09050105030712060e1c020d030236120304050306010e1312090803040b12070c05101805011d10050403050315030307 73
    0x1942c0d0002d0350081c0f0914000321010f01241e1750390600b0315444400c0c000c500041c1c2c010320050001c1820000078110481c40200b4812541d00300e00c2140c200c039440354000000d004400306040407a400d1844900e030281c540700e0b00034800340d0306040c082643c0e014103101c3c0caa03080c1d800c00413170401d214890b80b09448081d410030a40c0c1d01301030b1400d82c801840204000002c014400e0741c0350601490312901c203450025a1905050400d1102c200b4480a400a082c4986811700403403170384003042d40d580405e60f8140c44c1a0801454132070340341030101030500b0302c143c1c014400446200b042280c140007941d072111996078404a1544480f50400080340c00c0c000f282c10618152200007804108206200c01a1101410043c60200c01e0b560b0b04808803141520f80314002d196900284d400d0655200079005804610751850084043d40d0179070b01c47c0ca0a481c10356100c0d800100d0011005581038605200e842c1c0d101c50b20800c1480941895a8010070921000700135504104444003083d5490307500b80b080320720842c1c00506045 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 178604622 1250 178603372 178603387
    0x1112010e06030f03040b030610020c04320103211e020106090b0f10030b150f0304060518070603051008061005010e240d02070203070803040905070302040806070c0203030f 75
    0x6045140c1a20000d1080c031620018007500c080000403102601c05e5115140d040d52103c3c801d000e00c20f00409900130a60103040d418058a450701d01c00c41c1c0610f03013440c01c5400e0809201c0c2c0b480c4150303082e4003180c880081d648030041c80440c60540d2140070410b072044543c089040c14200403141084040e010a86a03130b4041c04c41d0721003540c150021000d8892401e000c000707002c504820080c21403603896096401c440200c0b06002c0d0580264450520350324003800c411419a14544003004075030114030b1813508494040140018054644145a4000c040595500042c3e40e4402c6241c0c1e98407084c403c0e001003540310303800506904418200e941c010300700072084a40b40d04000b51107010403800d038020380d8002070491001d00c000e0b14080030814950360b4a0030419054003c40070300c20f122688020241802d02d9002c2140100580f0100001c1008007151006103858508200d45401520805000441090b0040c80103200d0f880f000f10f010b42e003008bc0d5081c4a80444110310210382140246030141d044803101240d0345 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 178605872 1250 178604622 178604639
    0x4030803130606091802040c020c190e01090204050a1514070f060c2c2809050a09020915030a02100e19030512070c05090106090306050f090c04111201 66
    0x2101c510348240001c0c05883d0301e800501c0100c852560786035915482018814004d070400703500000c14500f0910590340c100c0c00380c1000c1003103150a1322034502d10040200007084202000c610b00c4e40588030000c3c0552030680740c000019206515406011400412030f044202028007402d10780340341c07140c980b10703868507800c1e582049100984034120641d0f0302810b00c40d0201010f80308103080740c00125002084032101101844c1d80d004140340041c8550009840300c240c45c4819000952418020503040f101280c990900041c417040d0785000d08460240e81c00c0045000c0169244110164040d4205140d610f40b901d01100007450000812030103074122420440540440398000b92510a841c02980e0f010600000c2206401d00d46045110241454010b10002e01410b9a444010320005010302200c071446500e42c00080c5400a080e0320403400310b01e06800c10000c00901d8041d803a40310541c5400e6825034035250b02455201d1005d82ca6040c441d541c0c03036070321108054400c2c00740e80c842e40020482040310b40e12803555 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 178607122 1250 178605872 178605901
    0xf160303020c300a031103010305010203011a0a0903150b0901080c120f0c150c01060b04060e03010c0906050d060e010b0a0810060e010804081c060f0b040303050301170304030803 78
    0x2081054000d2001c10019080c03c042c43d01c8815400403411050516a1100c007800303a008400000d0030540ca450145038448032503805140a180101c00040c7c0e42d5151a01116000c00f07010301d6103104840c14044848019000540c2c0d008a83e000f11300005000008910070008010350094168855101400402c204400181d403c00242007030747c008a2140d0310707203e6665540134511030f0124640c0000901007803803c00c0315080320003400a500d02d234144404441c2c100d081d00d115801114103480081401c000b0307150301c908003a415800960081003514040e013030040031000e003405100c05000c000110a410201107520110080a20321160b1400d035844801441c01a40603071031940008148002003a1001c28110100c000c0704d00545490051aa0b0040103650302c600042068841401c01e001c0003003e0700c03041c400300040190942c0300090b40740c00c0402064501130550800003c01e01d0620080c400640c00000701c2e419034403a021140c4040401c820103524620490304000c00f02a8040b0610200f400ca6014 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 178608372 1250 178607122 178607137
    0x20d1a1305010c1d0d0512070605071403060915031002070507030501051803030106081e010e0702060a05090309040b03120408160b0a0f03050718170f06010b0406050f16030302 77
    0x34404035490324000c0b01c0191499075007062405429022131300d140303403594110b10400d1241c4d041d150044403070760445910341c0148205460041c0c5410810610365400280300e030b90818090686800d50403d100464192a0700600d00040991503005101e1160341c20010380020044150303056594018030301c2c1113500c6982070b05c0110b505600f400e02189500c0310b02c070141700000b8001001113017941e00e000801c071150703800a404e11005000b04224400c5a2035034500c0f25020380b00d0020124000d0510903070092a021004250568107803604081c40144070f004800c0718503e64080300c003c9a64110303000041d08044041d074900c1e681000001d40003c40d200080703005000119019190404160f4a445407844d17032180228500c0040d10142800401074025441540c12400d117107000010840f210360200c1c111030441d00980c4800741e08000711503051108001001010100901070b041039490600c44403001e014034010201401400b1810107040d0903144c0c00d60302c03001041001e2809014890030060000c2d44400c1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 178609622 1250 178608372 178608383
    0xc0204180b1e0f040807020118032102060603010905030d0c020f0d0e0108070306030807030f050d0e0106080c0307120807080f03132003120903070e01031505090712020d1a13 76
    0x800043c0002c007011600c604c61038000c142c40340b03410040d50046039410780404440c0c0c010940c800021020400f0300310a214805001c80305001502c0450a01a00c2c041004103820301c03c0c2e0405d80c8040024101209541070300712043c0010072141800d0b14181e08040c1d14032071916051007042e1040041036485844546514401c0c0c13140c41450300c440300c00314140d4445000c0684a0781042001400092195450080200321460003030709007622107402c43e05898030182d1082d01e50303441701b00500a030716042c4480c1c107201d5001c40003009040d242424540c0e00104802c009040c501d800308404043c44510011a0200304640d4803881e034a15000145000c00d6829050584403440c00e420b1042c44030b80c03100070724100a03800a006290446200034144d00c164803000b08141c05000da5000050100c1e69000c84601941c8100382940c501201c1003400412184010844040d03640080c0303080055122800c6010b03012901690014032000c0d450800c0070003544010791507a920701c000f100f00220310550240405081d840340 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 178610872 1250 178609622 178609681
    0x150c060a02030f061801030b1306020a03050405102f09030f070e10061b0507350a0b222010090605040603021303020415140a03030c0204180b 62
    0x34401d20440d689401002d00d083c418920050000c1880048c1092340103c00c25900d040c85642c541d07400c07050743c2000c01010702081d00c03601400100b02c400d1000c41c502c060a51002c10503520a170311500c0403100c1c0e00044400e100e40d148000d9100c0262001181c600a6019003111340c00301003082544c1e0b58543e130b880b44101c41400800801d1604112002c1c0c1001c407011070740c503200b25801c1c2203550480450801400c80e42c921852100049064640b90592100f20381d940000e03040061320f20314100b2160300c1c0000340c00180c001401540000344c41d03031180e98020201030841603000029080290000c20610b4000d8081e002d40c81d03d013410101003881c80322600784255184a604050f148041c4c3d4405076a01544010070710170702c420710842d0b201b030740036211904400c2a0091459604d8000c9000c440440285041c0205103500600c000d001e0384226140002e4281d4840481c00d1664034024601c000d06080240300f552900f802803142080a0118081650824064032050505d41501c43c0742404400381e852800c1c851 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 178612122 1250 178610872 178610881
    0x7030e03010c170601090515040801060506070209070c14060c0d15030b180a170c0d05040807050d020d061b02010c03090c062109030e011103090d02150c060a02030f 72
    0x40c0a901c041c0c9046444031030ba0381c1e0404203d00c40307a2400901650400101701d40000721584c0d0200148070808481c4001036a840c103000d03007d820b42e88990010350003100304214460058864400e6294000c11920b808408098075207020701105211804529091241c24280100c10351980300404480c9131b500f208000050452080070b852140303900c405007610b5010000102c80d8000b101070315052601e00003e903500c601d0b403503449101000c06400f1540c541c500214041c1c003010001c00810700c4070303412400d01c240bc0500c0c14551550720b880c0c600505020f400910941d0045441d120750b0700030b220b0f43c4140103103e28281d0802e58003254a075900c0d401c00641c00d14109101d450301902c03861350701c42c0d0001500c5502c182002c4c000c0e1201d04101c1d04180f0f91302c00c000d08410b4500c80034420242d40764403a542c1c0007181080d01e8001481429a1000c140031904200600b5000d40d64081002d0302c2d090303064031000388062801c00c0401d200c3c0187e44442d5030f1405240c00700200c1451030b90080d4814201c030704801145496 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 178613372 1250 178612122 178612129
    0xc2d1a0f06040509060601050307020a050304120c17120a031b12050a14010509070905030d020304182a02030f04030c08060711060a0b0a0b0a030903090e0709090504020402070b0c07030e 81
    0x4095079406450717007141c4085a03643d44108002c65000e00240122154000c407540c44501c0c0d58401c0d4000000c80404254076810444040c17011002002c480e481074071803000c9550100e0b210307504008100c050f02c5001403c000558000d80110410820415141002d81118000034185185012a926000d0725050005003281d10360f10803d100c0d018202040c5074640c0c202018402100300244c189010310812031400282d554080080100da45540c0d400f66131154034211000300c10101004c1084034140c1002072070070080150710002d04c0303002c0861500e0744c01d52912402c107030b05511604454540809000401106111103500c024084449000803100d15544807002250488405440c00146401c45404034109003011f401200f1088001850610101d990b00c1900f13140340e21102010b000320b0f864107030b100c00745074020007180028500481c0b5241640362641c0003d10784401401894000ba540b0400305040d912554103540000707500c02101ca045040c420032000660700143d02c01c0300010310400e6070300f01504 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 178614622 1250 178613372 178613381
    0x20f06040e0603010e01181707060e0a1b140d0c030b070c1a01050d020114090a06030c02061b040b1c0606031b050702061c0905120a09060c2d1a0f0604 66
    0x24147d40c4010140040d1307030f803400700785904e03010524543c03903040c0b00d590049000c038480d5030791801010000303144107292031030f01e41210036404003450f04204d492403041014200d011030303004a040d800c5964203005c200034500071b10050029000a408200e03900100700744240c001c1140718415000ea5607035807003d41e60300b01802c074103517090040ba5044002940d4003001940642101c10018402d03000c414141445900400c880d40a20340c01000041c2c2c4808524200580603c01b658200c840a01078850b00c26080300005110300ca248030321503090800142e0f484030740454250046040d00c0b040e6003404029501d88004015003690b03e00c20400f1030380354480b000f510b1301510450301c0031030307001c1c00044c1401c0d01c1c01021080495030740d140303101c0f42c1c0c0c44a0f41000001c0041c85550610000554640d48034a02da10700180303011201e402c04014004200380540108100f1600700c60394140d4000c80b02407c44600715400700301d030450704006040010010884002541107440688901d5034204a140c03da9a018100b2080e40c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 178615872 1250 178614622 178614641
    0x1e061d090706030b0303041d0f0115020a1101030b0333011202010c080712090305010b04140412021e07060212030103150b06092101050603030702060313020f06040e0603010e01 77
    0x9a00604003000450700a8000460131074008050ba803d00e550380c0b4880c454224803e2003071003018002d208109500d051040c1c000d01404072980b0142c1f040c8910103000c0c0d0740e050300e80005407120b030009004410b1a0300c41c4d040300c1003a104c054107072160704031003480490314842804140300d100d032360070380d4140340240e081c446c814101c42d5881d0391207100d01442c1d00150340701950000b094030101c104002801c04a0490840c80e4840690342e0b40c0c0c540a9443c500f07065084801060340c00b442981883c0f50b003840c208100d029242c22680103000e40071b1710486203106a00e0f218070312010404501100d4001001390f1030204005044415540039038050303184908206450744400d001c020103078002c50000d2609120030f940b05060004014001501e007502000004c1c1c1e0309070350034181d044500c0b02098802049d00f020701426406ca0415001903060122650002d120390000030685c3d4049003c92548006540d41c8461000090501806043c0c3d62600c8000780000748170100c2d501d9000c0c1d0309009850001c25014400c40d420b1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 178617122 1250 178615872 178615891
    0x40e01021b0a1205030408070b0c0306040b0109080c0909013b0d0c080a090905190f050601090e0a020909070309060b0909100c0e0613030c0e0615030402041e061d 71
    0xc43c244510305403a2030700040d0041c0c1d0a604107105040000c4c900c800e07070a004110351a0000c0d140d161200400007a5030890002c5410446400410000c0038070001711a40103403c100d404543c182c2e074890b0035a006040350103541d21300540c2d40161526400c01d0000e840c5940700e01001410100001441d0729646003922a65007000039942c4800c40040780b180400b80400640340c0c6080e160700c1d542d41081c01c0941e4416a100c0c440007449042d034040000d0a03200b01f10001011420511036898220000b038148401441043c40c490216070028580c0d814650440720300100050000d480c0d804c1010009000742640c0108565141c50903032031101500e032540d00584189151001002c03000824800791000d0f040c45540d80e801c0c00f6000700c07412503a50342da1020f0803162707403d40d030328003140c61039420a0f0f03540f000703964000e038110701000040c0411900c0700030200248902a1200640d00c0d12188003060040034000310048200e80700c44042031360b013030942e04104120742c07489000d04030b440e02c005145d5013010001c0c3c41070b640 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 178618372 1250 178617122 178617143
    0x90a05030d0902030109140d020d091a0f07050d050918061012060317120115020d030b0105070f1208011401051605070b030f0703180f06050c0405040e01021b0a 70
    0x2480303803290014202c0501c040c001084c44d601c1035039100e01c10694030503d600140c200126940015a04114a4056602c01d01d040c0c0511490000b00c0d0705241886548055500c500003824041240e0f00781c1240d25866001c030440345600c40040c1e004005800600e01036104507010300c07000f03d2102307100403014020b045c020300203541154140b2090391017030503524000d43c0c03d0f604c0f1000000460340c03e90750f140f0300c542080003065803814201114526074605070401814031030100c0b0143c5181394001048100c1c07024500b00003e102c9651401620786000300c1f030000b071880c0c134a407407020b0070044001c0d14200c6081050b11000800e9032183e114902d00d8a44001d240d002035001d015200d58215802d200075030070740c000c030141c0320040e4035180000110b510864061500c003804c00140301d0599030620803441d85600301782010b90600c40750f43d03982e400c500401c44080c00280e00c44010509110b10742d0110380083c540100200302058168213030038080d40100114480c2601034003c203680d2110b01041445030207070300080068 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 178619622 1250 178618372 178618387
    0x103020c0316060e030a020c030c0102010903020a0b09120d0b010210111204140a05030a1d01080114150c0f010b04150303050d09020d42020c03091302090108090a0503 73
    0x2c1075880c40010a5900c0354850807020419502800140303c2882e040d40500f44841c440000e2620b865802c0787c2480c11607252810350404640e005c20880402e03503001e42007a02548030410403610385031044c4880800d205001510000d8075040da800824030010a800792030722001c1c179152039412910300d0040b52004680400c0b00884e401c03400001d5680c4140304000c8808100d007421b603030b146803e908950489076640001181101150800a107400e440c8107203a0f046040848200001e2012070188180604070906842000b4030341c0d50400c40380c1e64244202610b507244e400740384100741c0d540759128543d1005d502c0c100700085181031501588100118081842c9045842c1d60f17000c032180d920004d841d10031b09507141d10600044c1c0c2d5100d0440b0181d8012018545640100c0c00e0b0302c2080f00d8142d400940410a031000d01075038814071106840d01d101218001604d440c03544c004681944281c1100603401003001c200085514003960140081002c01ea071a008195a41e03a40309648104401c40a00703190310038030401 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 178620872 1250 178619622 178619647
    0x616081303030212040305031e0c0a08070e0306190b0102030304020303070212030d0501120b060906090610140318010e0f060105041802040f0b0f060403200619020a050c0103020c03 79
    0x11038510311910b0014a06042d8003540da0009200303441c12000900c0c00802d005603508220365040180d80c2100f2840d4090600c0180440380c1d201e105000c03414000c0e00400a941d2502071403141604c90000380a80380c0703070b1624054200820310135140408446103000089036582d480041503030320565014008515080c120303020402001c69107043d00318544410007041c1c66050860060f1802080d1100815102002905d80381c501030380d005007424000e4100390304000381d47ea207800280380c121200742d565050042c1c001c6021103900d0341a12010b40b520b00008180040c0c0d640400c0c03413100303007104403000700b165240c00d034182e07a202c406010b4403681580c0302000500c120302c0c5c540e00c036280d6400c42c02c0c0c0c1594021495030210b4181e0b92440d42c10750220341e07070b00700340c103200d040004000c0e54020302110441d103880d00319a60440c05a184d1500c0c0705104900d542d00f0750242d2204000c0b101c0451940641213080b60146400a54070501315030201c4543c001c18031200c86550003802610800349018000e1418850b041023070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 178622122 1250 178620872 178620901
    0xf03030c06151203020307050d1b0b0624071b0806190f140f06040b100507050316052103190e07030605090115080601081203040303090611070203061608 67
    0x42111082c0d810a000404202004501d0340c1c4511a402a6072102c54900b0280e007000c00d41600076003401a6004801030b0860704190040400303500c05031141d1240c50390404a1003025002e6511545000039100500503980128042c3c1070b110300c03031000111403034408080642240060b10401d100e940c001d41c01f0804000c04400c0f10401c2d1005440c0004a864030065144142d481e26102c28506d1101d24003403224080c1c40c804400e600c040266418006040982c004c54001d40c2074444140810001040503c20040300707004079800b031000380c002030000c0328181c1041c2c2e031075081c22400021109102606120780740d0700350f810340384118100c1300c0082c0e1140104600388081c141c0c0290894150050200c0480011114400e0f540154002c0b8000a890036100502c003420128540158542d0303800b10004110041001480c00031000e00700080d6601c82d01e680c42c0a4015003203481c0000d00b81e074100564180c0e03691f070042c0502401c0b4000c90840706540c44100c00d984106400510840c0042c4603140080ca902c640c103040e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 178623372 1250 178622122 178622141
    0x5130608010b0414190e03040303110c0301060501050d0c0212041707090c0804060b220b130207080403020607020a091821020a2405150a1d010501030b1f080906010f03030c06 76
    0x45039400d854034006d41540d015030411004503a0013045111003210401c0350010391203041e0000c002050800740040c0203070050039170300b201864454800d01030f45442481054a00921003005d1601c690b2a0b40d2405d071181604070500c0003601c00c200000500e021140070f99a9014500d4a62182c9501c90780c03940005405002c03042a000018000050b01c20395141066980384402c070200010801d21000c104030140046075900345603940140040000324266004880482c0d504170780e15907494000c0d1010803400398607684007682080c40c14500b04680076608221540a62094031190b000071100e08901e002e944041d40c0f0540140d03c0b11114100280d0181c090340c2203110740b400040040220801c014060710342c01c5480c4440042d00c40c00c2030845040c031600c0c080182c201c19400304000005204070004618051113118101519900c010160b5100d5803824218206406080c402c80100410003a043c10401e840d055828403a0100024000c0441c4590f0002c2da90f1641d100c00410420351540c401174440b40c007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 178624622 1250 178623372 178623421
    0x150a080f0f16031104060b07060f0b0f0303031915060f02070b0301030503030a0e030c01020403110a06112509020f1804020427020d0c080708011a0405120705130608010b0414 76
    0x2000f0940c5c1140d000231780503041c4106404100b1a070111889800e0311415840c140c02806106800c0b071711540c0c04401d0b40d41c46122040c0121880710f074000524054100724682da904010180400308602d076100540030000c000079000ca80301542d480c2e2800030280300c08d11024016030010b0000c00d901e04600d030812504140740c14101ca0400700c461440b142203a1160303008503101c6000c1e10106810b810300c50107000080c442814940010081c4454191702c031408404101001c02840c0941200003a1901180c809480401411926000c0822105138164000c4424004140705204004514a40382c001c5600342c0b82c1c028a1b65680d111000c4c40c00c08030700480040310700c1503502406801c5190302d0500c916601e034541641d442050f07007049200034003c07030010b0b00f0002c0c0c02c0c0184017504002c04004012101140c13000c0e54025681250800400c0c140905504600e80c010aa4404280304507401c0e00800141c1d04100700030821440081d040104032102c90040e1170820714090001600511900070a1083c1034880 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 178625872 1250 178624622 178624631
    0x309070b0d150510020303070f0c0f060609150506040b0f0f030a0203160516080313060e0102040620060406090c030c080a06050604150509150a080f0f16031104 70
    0x3048194419000032200200007a903504003010754880c51080c400003804103031040c2c1c05052009800a440e440002d1042040c42403000b451012148076009030000603800820460340006a89044800742c0050b02c540c03031050307081230342e07400c400d00200301e400045501c0140203514003843c1120320762298001403000c400781d0748148000400c4607244002184144d41d20309005a50b49080c0c840300318030344400c0e0540c101b008018090220aa046042c0044410342c002503600d80342d644044c2c072211031000040740204000e00b880c0001100c0740054002d0003d41703081c0e449600d085c03694006842480d45089045503842c0d4001c40c0450040b0301d15600108405026100b02072403d5200c1e00c4e42c41ba602c480c0d40c44414980e120344110410700405d407251540103a402c803028056641503045101c0e86001d80d014a9120b0310f90721000c60001c051308035150710442c00240800102c0c5543c2e04d81d00d0385400c85200341c800e45010f44042901f0340d640c0810008014001110307480d030302c0390454880c145441d4200c01e1154109030384 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 178627122 1250 178625872 178625879
    0x120f0f0105190306151a0c1e2109130c02120c070e1e040302060124020c040b0301060503150402040c180b07020103020d090f050c01020334021507170406050708030907 73
    0x11a140c4c0d05000024100d196900c58a8079222172400030400401380c9020090700450b842d0780000700e01e829100c030009c00305c230700d04040301e10707041c4400e10500345000c0c0c0c89141f008140d86501c205400c0f030700c6450019025100303c8580c801a00d8014407885021001a40143c10305000d003890501000c0e0300041c0010840500a002004d50a800c1d6401c2d1020340c00b61348402c00410180c040e860300c03000401d00c504c076040f0752842e0589020303507140c2c12200780c0c62185884182d080301d680c42c01d40c001d00c020600201101c0c15142c103540f0300d9026510640307040e80190f042c0010801c07400d004109c018900281c1c004454070f03151804210b6074490304140000c03030400d5020031403031070758040c2c2e8060b0125407800303013005000a03140d0b4508a840d02a1002405066420501455110501800006000e100e0385c0f41c00110541c00100480e030742404150009612000011002d002449120094188544101c41282000d000400103000d54080d40c400c50000800c00c000c24400940304001440d0046118411680c0540d01d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 178628372 1250 178627122 178627139
    0x507030c031a0112020f2e0f020c09070801030b04060f020d0b040b100503070507061407020c0108010602060609160318080d060603060509060f0105120f0f010519030615 74
    0x9a2080e07505103070710030940525140d403000041c014041c20f2201004d000055020408014000d58218032078066141a4081150764011300120300c01c00d282130f07500300042004003074004200920604018401c02e03e03074407807600f4283c0206010b0b5400c1d84564090ba8039658810703404d000010070403541551120080c088004690000c0d103511100107801003150f8040134207000460700c3c1d5a01d014403030300d2503c0c1000ea14541240880740c1111440c5031055981d2034606040c006803409000ca0440e0400c8070007080074095020400100710783c02641c880b095660399440c1280e8864051300c02c26031199100d404100515150100e00802e1001c605002ca2800030300d9030440c00508040c80c007910201c10014080072007800d1803040c003000e4505410100800c50402011807540e85000b011380d8041c420841c071f43c0c00d01d40c3c000c0003030300c03100311418060340510b103040c1c1d010311026802a9611039032107040500215031880c124104901110342050050700329803440e00d80c6400780c0091888200400710902000c10000e4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 178629622 1250 178628372 178628393
    0x50c0303010303081506030f0a11040b0d14010f031a04020112051e1006021e01090f031107061d19120501090c120c060e010e0d060902040b0915010309050703 69
    0x18000d07140c1c1003217072900121a0150049010055204440c1007040265000e00e05940b2600003c83d440001001c0f426013000c1c40c414400c50f080300b036801e0400b281e0004501a0758020b600408482c407146a4a88d986801c482a0b00d42075020061054510241400c00700000742c80a0364060700516150411008061070001224400d98078a03000d04130500c403c400400140000a0b00004d0207000c078030000340342120003915101e000c16034001c0d102e003a0300e22546095094102844280d00541c07440c010041b10b01d0003078980025103103912498080c1403000515203016203000b00f29056800d02d400e8101c425401000814071f03103a04c2e0100291100301c00440d08842c103501c01c49000b403060000040000180c1880340444202e0f40c007181029664102d07400004049450540450704176013451001d103509100161081c01180941e2a080206115040c0900c81180c00580089000b550204204100351080c81240f9074100d0344100e0015400610008a5103e58402040940984169058170740c0726592030741c100c0b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 178630872 1250 178629622 178629629
    0x51b0a0f080a0501290904140d0f11070b0702040213081c1107050604060c0515070c03030b090c090d0302070503030a0c021c020a06030f020904090309060f0e0916050c030301 76
    0x241c2c0304106080400509200c3c00c84050f012411055035180fa2601c04c801070390340300c05031a004003040c4c004907080000d241c610440b03924105c400d5401200d0304036002490000802e82150004280c0c1d0010011181c000c165081640d8030080c40340c2c036024a40e000c2c0310103980410101650840e05040c00540c000d418807000c65000c13119030100034070716103401d00100304510424060015402c20442009160b8406045038222001424001d010f002c00307041a50410f164007541d2002001e01d10100031000780d02030098000d2034401e450070000d0390b0507102403149106084a01c41409601002041c6031468585c503200e101d00d200c2e10448003241c0c1c485c0c0100781103030081d450020115214500b80c80441c94440c1c2030142040d50078114041c551500c2d00050300324074251048005240c0d445200100b00e000c3d130b030115215a50043c2041c4400f0400d450024014422841080e0015103030302030300d000040c4100e0500410180003825854283c942c2070b02d05050851428111080c40010807103080482000c2c0041c5008 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 178632122 1250 178630872 178630889
    0xc050903011514040203060a0603051312080a06060302090306061201060918020f03190206090a05031507141305100302130b04090605010e10031e02120a18051b0a0f 72
    0x8a03850322504030002c00740f41d0340c503510850041c81004155211030030104c0c100da18501c2c020030a0f44a04416820a06942601510b1402c003055540c0080b6000500c040c0110394519081080c1079031128110700320f000c2c8401c09070307150f0031110224000345401426080451942000014401e55466921040321000d41d03034004a211580c0075003055150110700d060301003070203074040e04466440700c1444002003103540d0b00a200703071004540c1c28956141e20703070b405014000c0a82103801d5002840d044203800745c0120382d4000028526103a01c02104078104c10740d0101240500c0321203890381001c0800038000e10505003c41016420b00c8109034418054241c0002040750102e49691103061003040015610150404d0f814013140c0700100c441a00c5200800e2500c4010b4070340013512412008051282920710300f00a00540d0001c980302640c0403a6a40b4039008880403030003040401803080340740c06102d1001d11701038103941000c06c0441050b11244050209258000c00189009440c3c803a070140915260704890318 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 178633372 1250 178632122 178632161
    0x2405010503070503070e010303080c27120106120f0501020904020a051801030203010f0b09130e010614191e0b040303030b0f0f090601050c01021b01050709060809030a030c05090301 79
    0x92400c05001180c06800f055020f1300c0803e040c00f0a130841c419040c4001400c1040600c00600f01c02c5404050758054001080d00b100e01c00410b12060f00707410311103491281315104014514441c03000c144039080c110303030355800990015107298a0f540000c03404a84103032030b2950200544266951144002c00c1c1074500e030b450f01a1507000c1484c1c00031281c90072080c254141841000107010844d1915184000ca4400704100359890b0408404645030005a9503c1d0740341c642041e255061955040d040740060742e1454034801c0103101805c3c108400108a800c504032402480d600a10400001d02c20303141d1400003040089282070340e50783c01414640d026500607000640c0c2c581464880303203000000c5c1361490400f2501e0003c00c40da83c0c400610b6090000d0580e5050110014000c000c0350f5082d01907800201d40ca210241300d090741448254060041148d0034000180260004603c0501818540d805071500c80700441c03c0034002d0714150010011241f01c0d000340441031001442c00e0790300340a587e03c50134400f0413550 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 178634622 1250 178633372 178633379
    0x6130308090304050916030b03072403020f19170403020307110303031603020d06030b130212031603030902060f031e09032506090203030a090501140403021c240501 72
    0x1401954050006000d42c1c0003004108401d590742c8454542010610b011000100100c107400d4000f8107850180c00d405000317500001075091207102c007011500f0840f01c0003841117001e48604402324407a144e00240c000b48240500c581c09541d500030f0700c0d451034050404486202c003480a0000801c8129000c80050740001114000c1144038201116122019030007181182030002c12214001c4090340003008041d40421240032045c215000314000f5600100300101c0c1c0d0034001c445005c8055403400981c050408030740040d60044000086815520301040102072402c103e80d012405010040001d0f07030f01400600030305001580880007117001c0c10300d6903502c0c40d03059200000c4664418000f09280920740041c450004005080000c0090030705207440408500c138240e10f00400108100701c006034142c4004500d0f01e04041d0403071240d40c25500d003600e80103004906007204641e14030803400029000b03440241d440403100305410040d0801c0380720f00b079000103400d00c005070110f98400c460008034010362600e0041 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 178635872 1250 178634622 178634627
    0x90b040e060f1f0311090a02040906030503040f1202011d0301110a1e050412110a080a0b040b010b03010b04120215031017070608010b07050c030102130302130e0d051803061303 77
    0x30343c221114880d80320305186071101e03610750200e00d645a00466558000030303151852681150041c100c0743c4001c022854407810256901d4009000700f112552065101264022004566500c156070581d83c4260500099200d640c3c0a42458023842c0c05640303c910500640c40f00c080904500140c60f80c07500e2443d01c110050308543c0c9145040c038014480d04110a0200d01055011800708036001303d841030b0110010f2022411980066200d904107000b000000010480d0a03002c45002d1800b450101c40d060340c90340c0c080c0406101c00c0c85840100041000100504015980c079042981d00080c03121401c00340d02e01d14180580c0c400c40f8501d02c001c400c80014070505000c0d01070106131008281c000c0060b903080040160190a060045549100003c82c2c10020400b04000411000002a00035520b4403c01d004454401406000c120320407095071000c4403520845108541a00202c070340181100d060610041c1c030300b5808100c01c0398200072890030040c126142002a54080e44406101d203040d0f030002d0400 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 178637122 1250 178635872 178635901
    0x10f05060907030b15090a0f0f03030f0816080717040b061302032a0408010608010c0e0d030206060402031503071211180613020d0e100b0316090b040e060f 68
    0x50014503281c041e000b0318507120000003603806040110300580c1c2d01140d01c001070380c00055501c1100c0102d800c23840850000c031851080ca040300d1007911003500030a10100300b910001411200c030300404800301c01c942152446105607a1300042c990421a0b05694096a0000000011070b000d880182e010800e100c03003404c2580d050381002c0c84100003141941071001d0b0b48da64050040b07e0259454062b2a0410076040080041b41c009024200c003c004c00e65481d81000d000e00084440480816500c800c842064201030041c6803003180d041d406851981c3c0c44808100007500042c0c00c51040042c1ca00207204103407030400a480c0584094460100c40d011a80b40c041c4000c100700b80818010140e041400c02d61044042c400c2c0c0d000901181d0950103141000000d000038002c0b50800310b2100e041c40c940c040814004511038a2340320706a132050002c41641c105040c0c5d25007a201050700707041071001c0c01300709142d032540c4003442c02000284046902120094594900b007410381c1d8000420031101d0520106451f00b481 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 178638372 1250 178637122 178637131
    0x10030302060106210504030e0d1505010506040b1e09031203100f230d02130c02061f060815030109030f090e100e070908071e14090106050714010f050609 67
    0x14420b403000500c0300340080d404441c4078421002902c810101b001c041c0a0b801e01c4903500030281c140003079a41c50b404c00d01a1030044100740104286042d00109032170410104880989541c010903e140c20440c500079800707040000700b40202aa0248020303112540c0610580b0300c0719181000c11910780c1481c9c2c4604002d64005d031f0295081d050307401810020424500801c503400010400d800c1071224804000c60070340056544000d5100900c03d02082d00c0e6502c135402203074007005990858a55603541c151114500024084405281ca8203a4081005a02c10703280e103030348500c44000c018000065080070a01355005054210042114003c04900c9a5404098100180710304c03000010103041564230030240701e04c0340c09041801d26448001075100c900548d80c6070002e03c2c5031001c5030401c980d1104003e01c0c842600039446d41402d40f00f00001088a185200c050f00f492004000300c026901e40703a0103550395888010211000260080e4000c40024284281640d005004001069610302001000340b815001403 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 178639622 1250 178638372 178638377
    0x282406030f091a0718090c0f030c0801270203070306180209010903080703050c100b040f0614062a1606020a0308040b100509150319031704031710030302060106 70
    0x120900c041071070042d480842c031001e00810002c5803504074003110450703040006049815003585c0f0004125116500c541044111651012210003800e1030803020303229107101440005070b60000602011504903107204990b2102419800d002c0d91070802401a03801c110b0340400842d944040400c81c4a0920440750304001c84c5650031868180401e0010384100c03e0b07800b02030301c1c103800031441004250080046420140b9644225074144d044851581c0242a0440381140268204500286140700c5070007400161854410b1500c0d5000c050750502045800c840c6858041c88500b503001c55840a04469480d10480e40f200601a6107030360310010302d044101a4040800c6601080302c00001c80d901000150b0007070f80c4050b1035150341e103a5102402d25900f40390460303507006170001c050184c486100c031408248902c0603805d8a8103000f015990300701c400071110002c0c0c045075040940e020213100d294074141d03100d8403e0504074450002105110001a411140b20034111401c0100b4800d01d501080300b03c6c01003041e072 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 178640872 1250 178639622 178639631
    0x90210020604080a120209040207200607050c0906010201151d0f0f1314010e03041a0703050a0309051606020606030f06131e0506070c0b0a0203282406030f 68
    0x60f92101c943c0d02c01c2c6801d400400c0340e2481c0d2222a010560112480b002004005644544586c1030031100b2007400341c02d01041180d020f4110441d810414281ea0031507400c0300c0034040c102c0c603a01c03c2c0880b01c040200298115540c68160108540035480c1c40ba010703000c0f84001a21001d0546581041d02d81c02070507482e02512a002004007130048144034981c0440382001e0f44114681e94a082c3c00344260b5400d0f10b001550a11810f842081c0000014004480c0c0c00d0480300c1031001048031015681c40342d680e0241c00107104120090095001ea00401406407041c1d04894042900c8001e0f0a03007413105400600050300500180065442e040021200c04611040900024244041c400036012000d0200070040700001f0110400081040c151500058002c1c0036514a4074050390000c0030f040034200308846519103130020582c0c1840f0780c402d691040300e11111520341440c41c9034034031100f485040700065500c2d031079070341c210030260003803411061500d11480c1c0301c60b0041c240341c0040d00703446034141340c00110f5140 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 178642122 1250 178640872 178640881
    0x7020f060402130917040621020702030d180302060304080711090601082e090203101a070605040f0f03030e0705090603030405010c14010204060f0e010206131b05090a0902100206 78
    0x3c005441c1c2c04004003010009000d00310389005402c0c00c6406458520080e0003241c006a0700e50000c66511071103448410f03002400b054141e4041c1240a00d21010350194829190401d400303001e55554280c440038020104a8503560342d000610540c01160120b030071035408240202040801c941680c0e4140041721014128501003000a01860004100714415030035440c1204201c1030301d640c001d540c0c000790441d02900301c4c0c5030780b4120042e61065a01540c000c4010078000341589283e03c019030024150300b0080d01c0d000c07503500d4541c09044050001d850004000d8843e8000904079840084664881d8401142c0e11003024400c6041440c075510041c0030785500020003100c0da4000c03040b5816900d09080c030150b48900b50801e080c000c00d1090a030241584006004100690080418602d5040c2544c415030034030000401242c9564040d41e00715181d4070006245070003e10640070010a500050048071045551800060741c0d60074240d0b65001b04070b42c0c0e000030314107504101680503040030445c002010682030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 178643372 1250 178642122 178642129
    0xc070b03090a300e15030604020909010f06180303050a050912010510030b060f010203031f0e04050a021509010c02010324060e0406060503071b06060506070501050f0610021f02040504050f07020f060402 88
    0x2146105c2e0801e62000000200580d8170360303054500e00000680701007095a164034283d9076420041c020031011540d902101d20611034401105825260b25a03106408d0034408030090b1840d801520b4101c2d070022a103180014140340c00d01c2820f00c119018505400b05a02d54104024071460140c00180111f20750444a01503903000002c8030780100e40b0103416040a000030083c800807585603040209a01c500000388818000000350500c1031600896a440d0314820f4005641054030441c00c416000c50480c0c144071001d1342c0260f10040b401300220a0034200d40020480800c1424029002003000c0b543c41c001c20a02800d003440384001803d2103007880ba1560500a20107414802515a6045500416101801002155008440184800352889484140501c0c0440c068482101d10b00c0703a10490f40006061440d00040c600502c0c1c0854001e02200c110701204c0484040030328045d491300079020000068a5100c03441500c3c4105003640c07030207969061106001b8148140f04071400e2569201c03009200c056136 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 178644622 1250 178643372 178643389
    0x40605040b060a08150904050d17061008090f19030306080c060403080c0102090d031223010603020a02190507050a090203040c090216052d030c070b03090a300e 70
    0x2c3c10b09043c3d1030b541d284015454450500c10300103411a407210709200800c14001081d000a40e041e481c0c41030740c040e03040d188000192044034456400126103803034080140c02041030351b4120aa02d825100e0b002d060342c0c0c076140b80400340c0d0399480d0070208600181c4140341d8103114078006411007402422804652000081c1240120301000c1c2c4050342c0003038201c2c08440709504951030b20101070300d418407005003410702a00324507100b1008100603003407042c600c03016050089111800706280040c41c3c0980d00b0400220000e401201176131042d4880e401041d100100101f25000010b4840c80041620302c2c200028041c0301d89050744601700b10390042c000d04c00000c0840e0300102c1501d0048500580b20b0141c481340202c1c6031713140e0748090064054042d22080300300c04a1a040c007a0180780040320030301e540a410301d90fa00c0c49661071082d1581c10018080c006118004003c541100761a02101e00340922034031240107012401c801480c0081d60010803254640380040c4010b05102103080c480000740b001b002095890 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 178645872 1250 178644622 178644637
    0xa1e060206040b010b03060d05010504050a030e040b01092106141b041217040302060715060b040302030307080a110f010c090e070e040c091a0d0608010203041208060310020d0b040605040b06 83
    0x1700c0100016905440386201120020f802800078042414503040094903003054000c03d500246080803010301d54285800340454a4006035101800d0602d00301c514085851031300108000b4a003501c00180c003280090082d510032500200d001d841c181070465500c126200300c080480c1d60a10140300c00c1014841480003000084d421880020006e10250a0307441140300301e4100a42c0302d01c000c6907817402e08c103d00c1003030b000440a208040215584401d10201e0070b004601c80258103510402c41c060000d41c140b8040d0120030082d04040c0580b181e880c888908002e406018000141e5641640c100141d500848030001000c0b061302200482c10040e200400704801001c845000d0743c3c9600c40c0f840c010741b0860510004101e030090184030b100742100c3d41c2510798000040348203014100304020402c64010310880e40695440703504500300404154040d00c2d10039004060541c036000d5104c003c843c84d18640000d01c4c40d0a01080000b43d0641800e0810044440c0c5070000c0d0f00443c940099483c80d0b848800440e04031 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 178647122 1250 178645872 178645889
    0xb01030b040312060b071505010b040504020d0b0901030b04030201050604140a0c090801110703080901050606091c02030610081605060f0c010b03010908031e100e13020a1e060206040b01 81
    0x150740ca608042e03d031204580c003205100c80c036001c40018056207400103002c0f100e10608411520980302c01d0101c0c00d6550a001c5e041e217001080204000320318143c0d00038080080e02e1078022400c0040000000c840d007100740c0c81a01d000c00440708100402d0381c2032080640c804070840702044010901041c5c1020b045000b032002d41500d41e900180d1020307a0040389188018000c0e0320003031000f455236402d512245e400c6143d040300171690300c0d404101490410702401c0c3c13040c0c0000e0f0855040c011007204106c80e01c014903207001c00045500f1090005610184400351042d0b0002682410161400c180b641c03070b280520b03400e01c1890803040000c0c0425502c800c2207a042035540c2e041161100b00c00c0304403900400030090095455868100c80c51308200400c005148962082d00508a460088129002e01140e04403030042d82c00340001e00522940c000d00c901d094018a030081414500145a400301e01040d0168011092044010300741400001342c5035880b030040e1103d4405010036040c00d41d6010503214060196611 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 178648372 1250 178647122 178647143
    0x4050705040207020d0212030417060105090a11040b04060e0a05010503070c061a0310060e0601050c07050112020f13080d020a03020a02040e16091e0b010f08040204110403200307030b0103 82
    0x70355582505210b5000d400030010008017442d52041d0ba500d912a20501e02b081d47d440c02003451042c00414030034100c0b0340161011400d541c0e6903507120000c041c03251814180c000188804107580407039038060300c098502c940b02c50038418000c004102c0c410080c4d50009041000800800c8035031907101e0381155001d40d01c520049400e400c05400c400c08400c0055210341c00d0300c2400341c5059600745581240b03080b5038440384540c40c691144c04c01145c052251104001c90765000c503030304011551060a554901241495006083c0104208802c040f5406001c0c10014401c60070000e000c006024003800041d03260700d00041ca44a0340380d0303602075240c2c240a400a4071072617a620000c00194014020303c49024003a000ca01d401135150791040c3c00030280850700d072000301c03184d124954204006106054400364140c407940d444221510045a03080750082049030499206e0750007124140400300580081c612813003881c5c0b01034103542d10169000014190881c400d0384122020000b1807070046c0c00303906403a0001c20713800 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 178649622 1250 178648372 178648387
    0x3080f04081507053705030402040501140306041506050603010b1c05150d08040503011107050105060f0904080307090b0c07061205040c03030c06090831080c01030c120c0201050f0a05040507050402 86
    0x36040101e0400ca0030440c1115030f04100e172107601400540c4a18421502001640d1700e0b008806002031500d448240c140d4884404a80401d04254502c1031021007a00017088041e107071008151150001e0b4000c0243d450007003190b840300b0400399035051540003000c404012500e48420b906040403145807141c0e00850b521389210741809501c03012a4040c0c08040e00034884001c1c4164028050351025405030741c00d503e07010101c1d1543c500074241d1003450b01c1c010034001d581e49070781e100e00d0001c0d40060700e0fa0052289003840040d80340c2404010f0005d003d5034001401e5118a0928054800106207038401d081618240070040001e03224003000d815241c151812490031001841c0c90001070215010103040c6103000b04060203480309415504903911143c1c0322181c0d0308501c440c13503038409000c58010440704d60413000181c20030303501c260b0000801103024030780110b41c1c0c2c544214a1007150901000080142d450782d00b0070485004540310305070444020241001070307140c1a01d485407a40f88078003e44d44900d0f000100c0780c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 178650872 1250 178649622 178649677
    0x21030601050702151201030b0f0c0a081e010605040812160f050a1406010906080d02060a0e07090905011b0f080c09060c1911010c0201020604110a03080f0408150705 72
    0x1a104c40305500402a07884100300c0501c05544e0091104803031804066000520002030302c06442d016400e45120203082c039500d00001d03500c80000401c048907424040e440f21404032902c640b064000c0500d40c0381d29640398141020385003400c94011101c5402c5108200102e0a41401c68441149039003203060314208800300d00d001400c1090985014040c03c494260812240389d0120701da41c121141c201c0100005030f56442c0403900d4100e00c1031b00358091b800c02e100085075142c070394101526040c1c03084151040d1503120a40c1d41b0888030384610507510f42c1e5480041d607040424800720039142c0b01c01400d1090200703d82d820001c0c21403400900b20061540c0100d910070080d101c080a860b180342c851800e44a482d006001e080c90800d4040800b500c030601d04040100c03695006040f600952601a03001d07101c40d9440c1c2d100c081d00d42003d4030095410002e45000040481c2c46040504001918114a1680c072841c01c14881d14002151184405103144881441500e0b6000070861b003001c0c10500748107580350b6030314014 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 178652122 1250 178650872 178650889
    0x1203040210030b15041e14040c02100c030b03073615140405010b03060d0809280e010b250501110a030605010305010b040608010b0c030702041a0321030601050702 71
    0x1083e40142196140000c0707a1380d03c0c00035106854043d05c103400c2142c0340d911281504800c0f84100030390460031250764100d9040540002400e2302584c012107400500001c0080c040700c03140518440060381d505109400340c5170a000d40401448400c1c4640b060340d801ea4540c840241c4905000d1400c4150111001c42155064014a68072070b00e01d0208013080d0f5850070b45a2580700c02710032241c49a85002e0000c6103d8680300c00b40d034007480024080110b4803038643d440303201c1603000200959000c0303621030020240000288030303540703074042c44420251290329048a50781c0815040c2c00401c0c09000600141c4850000c02c818043c141d0111038808003c0300843c2000760040c612003405000345000040e4550341180c054100c80126070081e07904009581c1d9944080030503000c0c5010b00c20001c0c0c500c6004000c001440340c05068500304080c10f480c41c020341d541c006412640f800c0c4002000183c00164080c0501d4288140783c4a40706400652040c4000391802c4ca001e4400246001c0c1488000300b03154041d5155250b4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 178653372 1250 178652122 178652141
    0x3071b0503190f0305010b0910090f08030a021c05090907051306080601020c06070506061011070f03140109050c09071103040806010312140403030302070f02130e0f120304021003 78
    0x2520759804a10030b110222036007401001c008640b1101020300814860b1007914100c4100b802c1a90030309a1401c1000302c584001025003040001c080700c04294010614401d0009101490080d5590b1280000c041d04000b010b4940941202d0641d0000a001da0170408943c1c2c41001180c0a6015641c1d115041c1c1d005d020301a014103481564007800700c3e00d03d820042941c001c1d60260212042c042075003081200c0c5101d0a9001880b6030040c40202d066401d0040004180d4141c2d418521100b0005406407460031210f44d101202060000100304207205c16040000100e201210007440305a01c15124581d45075000d802c090300581d40c08000901d5144507541e04451545190280c2c0c0c3c0d00c607602d40c079107640d401e17003070009490099100101c42a803c1c09607820340c0d10380801483c0700c1d06041c91030300d0a03030080d0001602030715145000a044401030317a40b00300d007462414128000184003582600a45c1c6003e0104503200c0055221142203001100c124081d607600a0341142c1c5c100d9030078445a0b00b00e029010544 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 178654622 1250 178653372 178653383
    0x130b1501120207050105070305221104020c0a051b04020415140c01060e041b030b24120307110312040b03090307050a0807210f0309050114100906050402040b03071b 72
    0x43c05010480c0640113a400342c001076400784240d855400b66104a0003000c400c18010440346403034200000c1990918403c8414014001802c0c40c0e01c0382c120904080303031090100c440d03800000701821501902c400012703031100156021424603040001c84d61005005004142c00d00c0800c030064041810070030101e41205907404001e0000999400180c11070001c02e03242214500900400b2101980e185c82005040b01c3d01704140c9251503c900300070000c07030100030b5807040c000210420308180360f440e04100b000a003190075008654489440c2002614015610800e5219411001c0c040000003440401e135001d80744c1d00004150b890300c1b101039071441e512540034000c046000c3c40956400313001c0640050400c003030050402d8010388030810000500315014400400110310312665030131103617110760b00c0300b05900d00c910000a152420408260021281141c1c4403105c0d845101050064600074020ba400405c0d043d1380c15400d06040884000150000078110410058403c03030240103242d52089144e002034124 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 178655872 1250 178654622 178654627
    0x1009180219050411070501140903090d050a0501020a0e0306070207050f040b0a0f06020d080a0501050d12020115150e030c1e0312030123100903060e030408060903040509130b15011202 80
    0x1004d03280380c00d400114003a1602d510b00b1500d14800954003850521400ca41d202444ca001da4039410041036500070907040c3c502c0d2082641d0304002036401d05c010301040c2a5501d48045070080c2100309460150010080e0085400801c0108260384805000855406048501140c005a100045009500d1070340c0b0076884401040d90000702590049480581c100d05030b5103030010b81c1c0d142c007480b101382d540a200c3c2d19045503440003008042080300a110440070311510000c030340c1d90003c00004101002d260046002d10324000c10851100b908950b0115080500350041c100b80715400300040d00c100e242e01c900028284c2540758081c4160341c02e103c0c603100345500c140600d80780c0d6149e60020705510004100c01d81504800c841400a500d8108030905d20013045541e4404900d00710750303609000e01041d5003043c240f80310500012800ca4006d000740d07807040500c10002d503101ca107000c04000000001074180c140740c42c0e5883c0e0000109081d000a00d500c20b583c00740c4140510103a40040724403158440c45400b000b03102 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 178657122 1250 178655872 178655891
    0xc02031504121110020d0914010507081f1809080403080904060906080c150c1b03120a05041707050a0620120d09020d1a10091802190504 60
    0x400500030302075400340030440402207a0300c806594070300c00e02c074441d07049510880c4060084c46140d00105003100482e42c0125155409940c1e0520340d003110703a03800000380d441d50108400a50300c01d44541d440829440d180341c2050941510100c011000d004110b02140e54040d052130707501460f08035010484c0d001c02c45a13035a69a074100683c04e5008080d81c02e1140c1e00f040c10001c3e00303815501400707086e20a110003500300c060500c0c1c10000001c078030005202c000b00b001c0c0001d0a000d00d041c820301c0c0c2c888042d800702140303542c4100101400d00c80c48a08110f00c0440c1884011502c1e50300c1801e40e03081d211415204190500050700c21403800441d41e000542c0929803d0002c00e61030307484000c81c16000b80e08111080e503180340c8915152a50320720401c0c5003045e03400340501c503254407064000e200340034006082c1000c034100549138a824040042c0116418005031018406840010300315140100545041007100002c505a8082010341c0b18201030301c10540c0f04068078002c3d000860884c01031a0040080044140 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 178658372 1250 178657122 178657153
    0x30f020a0e010b0d0b030d080a050a0f0e030901020c040203070c0201050a051903061404050403020c010c080c010c0528080613180c140d08030a0e07030b070810050d051c0c0203 77
    0x3201500813203041c10140360038010f050001e400400715459132560b170b50694a4502a20003070000402d42036080c1c2e2102d00c0003088110034403a01404502d0340002d190b843c1302030320029180854901e0914021032040040280455100341c1d10354a490382480d01556a50340b401048520380550060000411342d0207060821464166110504850030104424141660310f010881291002c44010f000740e088400c644001d507205d950361006044c4119241030400e804040000d08480b05041c044010a40020303076024104103c1008802c109006141200c8248015500074114400504010b000d5007000d07400348180d0326903410aa03100b850000c084000c031582c500309480d80e290503100b680d44000401000d1111406c04a00c03603030040b030b042054030386140c03a0703085000e00800400400601c0f80c0100361007c0001100036544a0184401d0354400700d041c20140ca454696428651286100d10b43c016010740000e040400d603000901c1006034500101c80c022041628840442d1a0003541030143c01e110104000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 178659622 1250 178658372 178658377
    0x30a0c0e0f16020c1311130609050319120905030a12030e0304080601120804080303010f030c090501051c060b0604081606020c0a0308030402040603080d02030403021b0a030f020a0e010b 81
    0x41080c04910707142c0b0345101c0ba01d8811590800c680050304200b03400070b024203102e071609007081810540014007411181e00341e55141c002c031400020030a803401e02048026444007030b80020707000490140103011403086003100c20003d0148020080d070010405549058061a1602c004120140c00d60f010400c40c1c0c50411201b0b1030f100d84145c00b180c50004e000103135100010541c1c0548061100500d4285d00f0011091240003a0701411a20440200004204041d050019500030403242120030b0100381145004131502400e0381210000a103461300400c46030341c0700380e601c00d9088025a4418008111030070030030301070001122000d400160008000489400014404802030b000d00103801d15140c0b5104101e0701d0b001400f501907441b803038542092001c242a040190380252005100042c042d40d282d4852105070004440300300d64590110400082c1501488010000040c54420000442050b00000c02c041e072903010103054090449420340440d190203603040080c1c508844840c10719a074484041019030b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 178660872 1250 178659622 178659631
    0x60409121707030c0f050706020c030a02160b0304020a0506130305010218040f0c090303052d190e010516060207060f0203011d07050a031a100906030b06040509060d02030a0c0e 77
    0x7094400000b64034520a00c60708101d0745690356445158900700100f1913180d0002c01090360200d0303082011a02c002010402041c03a4400707500030301003d400030388a420310440c1a80c0300000642081082000503550301d2006006d445084401c19100e1a070300d036002c0d034030707492030723000206590f100040c0e4210742e01054272100c020010458043c00402181000d000c1601e803001200300100360121402d1000078000c1d0040c00702e201420301c4c51110b041000038070b921108100d50200030401d82c00101036241b00c0b50138901c107400c28840c2c01e08031003409600000901a1080d441031910380c071065100c0c10b00300407140e0103c40030113400c41c006100e49102404d046c8000e41c028130a02c5c038890303950b4034805004144204018807500d80c0e1380b00c441c1060a240400d80140c4a1503042c83e003c407107401c10800280d078a5043c900c80c45000e95441009142c00c0040180071100c80b40e00240c4151401d000802c5269191440741d40c0c400e03001d80c1d00b01d0f02d40001e440482c1c9000b05090006040003000040030459400c4207507418420b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 178662122 1250 178660872 178660907
    0xa0e010614040b04020f040603020c030d23010e10090e01091b05031501060e04052205010501090e011116050304030f05060403030f0908030406050606040f060201050609072606040912 80
    0x20480c0b50f810401240701e050100c1c0c0e00e500062204003c003501a41c0036003900448bc4040e0f916054030300045000f156544000030340c10343c1c00c800244901540310f2110f540034160b00e8131a040941444401128040b40601c0750b200420307220810041200820742289441301d5002d05280c900741c034101c01c1400b1201250203104d02920590312214100001a07100d41c0c121a29030710b58140d084860014400a031600408080d01c2d00c0c10300071042d125103181440c4512840c002c0d0000a038a5050111440540707034600200c5001ea8104000000d80311402400c85440003207501d001100500c40c0d00e005030a50040794009800c0c041c08030551018000042081c0e8425403280d542005000c00882c2e025085070228140031700b43c00030a10002e4001201b0b6440907401c0080101711605103543c802903515150216004040103075103550a0009906140061a81114071343c11701e02e140300800090802c90581d9120800c00d800c2074800070032860384940d80840004c0d50001000068104403160151080743c241502e08074 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 178663372 1250 178662122 178662131
    0x70f080606040f061211060405090a0506010f020c031024060f030b040504081605120c01020d0605030a0206030f13020301091a070801050907110c030604050604140a05030a05030a0e01061404 83
    0x220100f24460141070704d00034402d0000380c07500e50312081035048219440681004080002103520796441ca06688690070b006000f060070300e0004001030160f070000001c00150742c042c02a00340750303541c04203441124684d01d000016000102607180180680841c0403024001a00d007000308003682e110210645121603510284229081241400112001220090a00b131014480c5d22000c0108005580c0d6180c002c0d01102c01b11280c1140c1c003941c83d0b008603103e4030035030b50000c0c8005148680e8018840244000c40281021240c143c000c100d00b44402032071020220444400241080584000241915001780c000c10000055240c120004842d4543e01c030120016080015009486074900c541070303e8000c1d0204500b51244241600c0ca184842d440f500c10340201b8010b680c0703645041003054440c900500060151741171a00300400d1950600342e4680c4203800410a0002013a0700204032400c007175492829070703507e544aa03440401003c0c034186001c0320f9424044c0000310310440c0034104800c860200d50402 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 178664622 1250 178663372 178663391
    0x105072303280c021c050607090816080c092d0f1501090501030507050702040504080d0e16050d021309060e19020f040209060f0a1d060304030818070f08060604 70
    0x9882c0c48103800c00500264541480d00014140081c084540d0311222401c1103c240e0195255400c28504490b0364000845010040044490070006000384903400065043c0c02818801c60710744548000c034400340184c0d070140202c1c200d0311200d911011646c0d1030003482c80600c0c013900079407000e8003002d0f51891032051400340840c0c0c1800441c0c0204541c150141c4070003028520707020041d009000000c29a0042c0201408100090703103881c0034052080744a01c9030310365244400d070544000c0b110380c000180001e9210b400e8a001c3d40900705040c006841040300e112580182c01c1c07000414244d0701409016200d800c1002d0700381003200d00d030801958400030106440000c0c00d102144040139a00c0e05002e540102d0101000103181003d50007004c4889000d00468a030510800c5113034110380c48034114000150260002c2c411b4906080142a0483c00c101e58403031450400752001884018040d05850f200d0942001c004a00c0c5020048000104815620102190350326410640c4a0008503035190140d41400c18a4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 178665872 1250 178664622 178664677
    0x9090d021c020607140408010c0c021309030c0605062d090601020d14161b030c120b01060509130c02010c0e040903270f0e0106110105010b090105072303 67
    0x74032842455004010310341d954001201c0c0ca41e100b0320301c0c14106504200200341740341c1c20b000e03201700004281c40324141041144103000060302d5100c42429203c0c60951100300003a44500c41041c1c05030040030104d4180c40305c00004c2c40b40c040088040c1c014000b10a0304850000468100c4a0400400c5905011326940c20b001640c590000034500070001e600e20340e030120510b6440001d8040e0612078100c10310060029501c4c07100b6412100c2e50183d610710403081c2001080807454080700585108550900000059540d0069240060255405002c4042111141915550010410403103101010311402da403416001e80284488002100011900041e620040c00d040c003900b03011541c10303540e4100305d0000041d02500c2c00a848913040c2119543c03030001a01c6c031701c0d5a0010014148103104a00154540840a02205945c6040d45402e0b41050300410550b075441d030659041e082c0c2800d00541d43c2c2150700d041c030000e80020107891700f0f4031001c555140310046d001018005803010340b0700f00071590014a205c03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 178667122 1250 178665872 178665913
    0x2100306031205070c0b0301062f030f07080d05010e06010306080102070c05040b0a0b2802010b100e01050d02070503030a1104031110090305010525052a030909090d02 73
    0x900620381c10b841c0380ca0030911a070010801103014290707401106490384843e42c2e0691003a8011400500c1e04078902c042ca250300020918807440c101414000c0e5202002c00301c0d100d02039055282c0d56054040380010520800b0b00448007510498001080190b84900440c1118002a6541c0780000d191800100d00644140f0840b04115003010130721902c035251800300405085d08044082d003200c90100000b0f01090500041c18140c40e0000311840d89086a030460400e070000e585445085a060460184a035211054188922081882e100741602c00c280700603215480347d490b182d030b0a04d01c0000d6803c00d00002001850141001200501040d26a06555203e074000c41c0805450008000446100c61901c1c5400d00198001c0c0c0c10b01390601035403a29001d0071524125594070241c50899012007500d034440c0842121150342c2d05206050042404a0001c24407296400510a10030a50090f21145080090f00c21100d0028002c582901d08014010749138442420080054840c0d0121270040c081d08081 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 178668372 1250 178667122 178667129
    0x6030201050405060708090907020a0516050904030e1215190e0601090b041d01091101180e0405070902030c1209070b0f07060f0c050c1b1c03170403030902100306 71
    0x4400b401c160400c000c116803940240d40450744461304000c885859159001c2407803082c200d603006004c50b98080e040c91400c150200c0d0a485449030700810a01043d524025060782068040c03809007903075801240420f41050116848100303e00c148005100064000c15100e80300f0480e01e40c5580700c802c11603140c4c5080c0c0385040c1039030078a40c00203c0107108a0100c0d52100c404000d00030700110702d00019108140c0e807070501741c10740450390b5140c0b4034090078080d45620785d01c01144213281c92403d045208020382120074190155101c562403148c003142c2400410052880030b0003000004550740c2c10311014207a8983d1150f1800000c205500c2c0008003441c40110303e100442d80403400407840c004d80c0040120960b0700910084511a50ba09845180c421f110b00c02c804109050351036255480b0081c480075881c02c007030803400c07080210721150056801d88648044145841d5590001c4e0f86080300c6103020b940d541c1c04910201c0c40340e42030340104818103a154101d000703564021380e444078000d191502c0031015140a8013 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 178669622 1250 178668372 178668377
    0x7060b0301052701020f040905161812051f050601020f011b0309081308010c0e121e0a080d02073503090304121a0601110a0303051005120a0b060406030201 68
    0x3403440021082c3c0350000e00040414001880c0c8015949040019041908a8410569100100003520145114201481c911424000c4c00302200303200c01d83d8080c40740d0007001c403030002400e540c8040000c200700c1c00302d40100201d408456aa001410b007001010200d074014014031030254822687e420612803c0500c02c084600c04500010145c000e401400040c8030488980c001000300400c81e00c80441403001130280c003000071440c00401c0a0043c42114a8401d0b603106401e407203525840d4150024540b0f000c03503400c1854a24549482e071100e82006250480034201000015803018503038480d038002c080152040d42c108461301200054540701c1c95002e2003600420042c50740c0d0010750010400a994400d01e0318007140e15140d107903541001d890300701d448203c1d186c1030008184603859012003040b43c1d02100070b203420008407902140040e964460084050181039455010036500c185815044c400351a02900c580020003040300c890740d40c0c12004100340c5080d159507002c1102031600d07024543c00c03030703405030b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 178670872 1250 178669622 178669651
    0x2010b060432030a03020105040201200619090506040506010302130504030e210114010f0b07021e01170705070b010e0c0a110703050607080118050f0708101a07060b030105 75
    0x9842142094034100c41c1010b01c26811036207000300e030381c10000401158803035400031806040030b20016014a00c100162032940c010f512142da501d101c0001c40c2075020102841820346554403080303103401005501d8019181e8001c0800300402e102001500324100c0344255446405101081c13082d404803401650007c0000f091219848400d2820820041104002180d003082d003450380c040d01070071190307a806180c19803004070004000030a11450a01e004100071a00340e07182c5000c0f40e00050035014120000b400340d2400300810f20030381e480b464121107050458610000c41d400c0411014049401251049544400d6a40003082e00481014482c0c000c0400c0c140841c1009643c410075100141c0c0ba081c1142a07106030707040080821310420045028400a440e61a4554108160140034085c10300c05103d20341c1c02c1c001440007061070b20040550228191a114420361141030340440e0251140d400b043d41d5115041540001000c0f02e0700400d00144500d20401543c40100c091500313840040b40d8800030310020 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 178672122 1250 178670872 178670909
    0x601061704060e1e0d120b010819060b0307080405010f060303020601140d05010216051005010e04060f0905010e03130e0906060405040507180b01080a021204110d0816020102010b0604 80
    0x150010703480303811070605030707910700411312000c0280d040c1380010b00c04c4a40c03000d134060b15980e0304080400180c11200380203104e58508500061704031580071789070303c200070840c040c0f981c41002141d000c44003030035030881a50358a0810240041583c002500c00752565440e003c4603007031809582c031958049943c9074025150076840d140d034030340d5044014400030b0307044508500140d001a5080c4000c140715401d040e072091110303115041140c40d160400d02c14043c032515100050000340007411445601c075a1000c4049110800c841d07950703018010006006120358204214103002c920044054440854074855214081d5510018610204030541c0d061541d508800c0125607241016040300f94014041c4044030304442c0d642140210210682c410ba1111517070b0f071843c95200790390107035485170010f10001065040440c0c0030190703142580c2c0504010b107004c0c1001050030f266100d80d400b0300f40c80ca812525082c3c5070307000801c9094225440b000104e0040d482d0130205010b5140c40010f0f6400d84d6000503d2480420b0f0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 178673372 1250 178672122 178672133
    0xd06051e0d03080a140109060e0f010e0f06061b0106211a0403171608070311160519060603061104030f06050702010b1023040513051012050f0601061704 67
    0x1c0c0a0640c100031911101051840040383c80b005c1c1c000c080041d000500d00385030000d1121124005800e10104035010b0004000c4001001511600400ca0130300c402456102d0100155480c89040c0707626032480400744110036203100640c0844c0c220be00e041140c05800324509211500440001001415150640000f0640c0c0ca500b170700c04c81d80a03100e818961480c8903682506665120100c0300b400e00d250400340d984103566800130100d90848198203080c0030390400d11000c011203006400d03114005072000140070b01402010030040008200201c225580022541011000780215000680b01223042903034848003842c65008172821030703420038122000c00314035503120405000c0240080b000c540d280c0400c6c4445503504519412400302a49a0008144000c010181070040c0c0e10300750f100c0c5050512003001951a08207d9030307000c04c05004001103e9890b03480722107502101e500701a042e2a00c603c01401003041c0040c1c0094254140d004a0300386a90350b410884118074050412591080c892020900091 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 178674622 1250 178673372 178673387
    0x80102190513030b04080703020f030a080c070320010603020a08030c0309091005030706120b041a1201020d0204031101090b04120f020d02040c05041415070b0711030d06051e0d03 78
    0x1003036121a01c1d40b80b980c2e52180703801030b4019141690300003800184c0000709501007000b4121511668080c509082640e14043c1c103844000f051650740d03040006003074007010b110720f01400101110000390049110805031050081500380400ca00510801c0808100c060b8000280c4008081c0d080003103250400801c180950a100901000309000307410f000801d45941c07d1000310081c102a546980e020b0448645800c00c1e92030440340b0034011454560705403803040503000320080040080e1524850310711030340d104500a1055440c040022480071802204210007220100c5582c90249d1715081d42544403a050b04030341c4202e100d0880c8011701600784c1000100120101c505003400101107800100d2181c0204090341c1400700018001400050207001500d14290660310032075040d1540301c82c002407070501c2001e40c03180384c1c4082c000031841c0002a4402e0b1007010b161180b480f00390b00f46d94840d0941d5030380c1d201410150050901c1440000010709548480d0b01e0101c0703400100400743c4150f020541c8080d00c00f00c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 178675872 1250 178674622 178674637
    0x70b03070f09090207150b090708011a0d06030803011712030406090206160c15020a02090a150803071a01150219030219050a1a0402030d030e030d0c080906010801021905 74
    0x3004540005040f00a44003038000310380651400c011100200c0039003000c54100c90070142c1704090660610111503801403080c2c7c107498080c202c80c54200c0e0000000180c0e4001e40340701e02d000c6810b182c00442001101030196048400d610b9440c5855111500400e403a00600485c6140a14042c4000b40200d01d80d500013264507800500b400b8604003c0311400014a8242c4c0c10585060390003a00810500d0080c149108448080b80301605045110f580040c544000c09002813240c40c0e04c5e1108134055942d2078003070700020009942100c0d076a0042e4074043c0c0302c04609400214403c8011000099001605601010707401d00c81c6d4085d0030860032820b8000d01076000c001c400d804612898140140395003002c0101c4040e640148001d040c4a01d103450500d4000030f80c01c3d00c0c101cac03a280c044284001600c00280c44035152035541000301e109021a0185460b40c01004009801d00d4100140300050139085a910b41c000c880c80f401fa81c807641c0e00c0348201807d03071082111030070001060801c0700c050940b0960203003002 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 178677122 1250 178675872 178675877
    0x17150d12120c02030306030f012009030705060406170105090c03160314270307080708030a02190f170108070603020d020d090503190c0c090c03020702030d020f0f070b03070f 76
    0x81c6003905180e004072400200d515000d0b90000007401a507107000c000d07081041c51454002d11044124a00381040c0504c9401170300700341c100c04203280075203079020f100c007801411018003215180c80d55407100a04040303480344400b01071070000c1c002152034100003540754441c81198106900c2e540300c41340044282460209070304c04256a0b00010781840c10b20400940c0030b00c03103040520403140c2c1081941c80f0407181a02405a8076070041002100040c0090191202d05410032010350312030791030302002d0f00030344650040000f654000d095903038403581d04500001e15285003550b0b6103991800c405148052134200707020380b40c01d6500c0440704001c0c0314030a070014041d1040c1070b0005810b0000c044000300945d146640d0480b00c941001c61511031010203001d40c1c0300701d00c0740f0b4174113161245030380d0300c482e0a03c82480c0540c80030307280c69540916403d0b021760121810785e0340c040c08070b40f104072203080f000f5287c0b080600e00b510300b800703407240c040c648200025810f810369408295a0b450b5490341c0c0020398917864a1207984c4d09 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 178678372 1250 178677122 178677137
    0x616030f09120210062d03060c032304030e1c0b10062d030510030209090a020306060328020d02092503060303080a0917040617150d12 59
    0x403004640c0a1035601a1285224012145840c000030303041c00180d1001c5440c0c0d911306003040100c000410407440307801d241071490030f2404070034081421114031a90000b82c1000d0070240b0304022291b15510040004410248818100040700385180c41c04909071070150001e584048140f81d20302d00502a41444089a0b810001c12035070b0780e1307901c80c00c0c100840c1d10b1100c0642d002010840c1c142c0101101402d081e546507807031140315400058862640001110408169540700082d0007603924650b0f800c045c680041c05c3d613400d89000c00c45a0340d6010b103550124000e0103181c0209a25060002e1501d82c082890324007080e0726040c11440203504500184241c1c0d00c00d030000e00680250321350b90055801801212240c0031145114556440ca02c4051039034402014a801000c00201e50312243d8207421241006e80807800d05100c0c189060340c0c82410400c1030300782c000003c0000d00e044d003003220303a44440c0d400b42050a0390742d6580090080c500004610075006500480000e00082100c400810310305082e0030083c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 178679622 1250 178678372 178678391
    0x3021b01020c1323040506060301060b040b03040303020412150608010c0c06050c071712090a0210030203131b050102060105040209030705061e0307030605090f070e13020409020304030224010602061603 88
    0x183d4400b904210031132810034420a000c107115081c00140c6e4820310a400034050107292203003d010522892140036154031021001c070303003050f100b601218014030390103042c40710003041c5040c600d250a03104a03104528030316154001800e4401030141c0a08105562070743e503a294100e8071081d014000c010851a80794804005001c0050552555100c0c10040c14401e1511800c1d003898401c4040c0024242c00c61070f510444141e001640c80c143c03440c40f00d00c0f0601c1c0258498581c6041040c08400d5100c3c003c2a5143e80110403102405840300d00c0300b00d42c800d9003110100c0e40d94105000880c4500140c031501500005010701007400c00388001c108080b00c1c0b12000300070481c140301040d00d079001034071081c002030b886a44c00c004501c0d01e41c0606401442140f031303002507400c0030b800150034a0601a945401815a400d068141c0c40341e40c1d0580e0014444001d003550384e8680b51600030b44996070300c40004144c0140c0301040ba020200f4100c682d0507038040d9001055280c4a1224292249010f65100d004254490210300e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 178680872 1250 178679622 178679651
    0x4140a051e0c210f01030b01090614010e04140403020f010f020712031104030b0103110405070509010f14090303030a0606080c0c060408070606080a030e041d0c060309010617060403021b01020c13 85
    0x94130603010540319407040c1d41075182c403100d0320340103238803907411941071200030f0150300d0580d42d4900b038001003420166140d044010100d0041d02c114074500c4400b070076034020042415000f28007104480d210b00e0003040703050a055a624128058010060300907606030400702c8c43d040c000e42c0080000c1540360f100070300300b55881c0e941c41040c903402d8104590706181c1c0060801c45041c60f02a003038005a2031300700f542c100401074000820270130340c4a041e64200030701c1001203450100780d03000312000b684004d81520358034a4101d5600015066500c03030240007500d1400019403814416090f1a2012152070141003241c480c1d858a140c103410020003034036441e94070100020829001c00c240940c15100791901d0140030840d504100844a4140110404003c50800d0a44408000c80d105465110485050341c40b9260701d000203005114580086031580d4010b140c40404150005407148141c0c481ea00322000300305402484000f01544040440c0580e00c003000d000442d1a1411880c5004840d180b800148400003c0a4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 178682122 1250 178680872 178680937
    0x40309080a06020d180f0b0601030209060a020601050321030403080907050607061b14070f11031921051215300708151504140a051e0c 59
    0x3215003507030014006118913920b0280d56180c810200c52003090000c1c40d10f44500c9111200d0006004d4002e4000240e51a80a641078641e5808060140d50b254030071904040d5840700d080c00364501c64486c2603980c2e090b65180d61202504048100da101d401d41d211030b5003c0d01c84060280c0407031102e0081500110b410b403a0103000d050907a0107010042190381d580141c01210518401140c0d0030810602c100c2c0e2001c400020071103036001d40c080040d5040c802c3d5814040004026810120360600442c541c5806040307592744650746240c000d0320342120983e1020400302c4100c0c1c00303210031400700d201880b1082d00d024060300301e541e00000f04040030b0b0b03107102c02000042a1001882040c00b454152804401811044040d4609072250000003084c005052040d002ea5644100c091305020300303c0700002440924201d04c001c02000b002030070a010f90b00004078018213040c0c0850381500d40c50700c0d00c030015060700c004200084840c890038410711120b444400950203154001031440e04001001d2201e542204040ea04 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 178683372 1250 178682122 178682143
    0xe0714210d050414010c0c12020402070204020d060e011e06030e1c09060e180103020f120607030906054017070c0b070c0603021e070501091401061404020304030908 72
    0x11120f5039942030410300d00c02c00c2c110280c1c1c1d41c100700f04220044001a04003034054152a007000711020b0308105440044c0180c4580745009400900200d01c01c0f5180b40315402420039070b16950340040b070070ba80384c03603001448400c40c1800061600b6900c200b0030201e8026440700980203030001c181c5171600c10305041c1c1000028134102d80c0b00002c0400d4000c00c00315074800c03148034140f00c0c11a14085100d11900030310b5039194060001078402c02611030321980d6a1f032645580300c02d01c0c3e0b058090700d0f458600900060010001d80505807000c3d402d120000e50820515402c0c49020000880442d80114014110f1258060032070500b4a130b00c0042e4000001080f600800e02040c5d8900300d0a0603560740b03151078689280401340d40143e0900b5001e2100100080008295605540d135500d80141c5070401510341c01480d10745c2400064904100144a100f40581900b000300c3d00d034040d1500d1040030b80d505d40c2c1c4500700c84183c400c2d2600400010300900b401c0ca484d03001140c005019103030154089484e40d07800b60a0504040 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 178684622 1250 178683372 178683377
    0x30908070506010e070f091503060f09060e070507020d17090d050f07050102060906070804020d0209090102090406051c0b0901270506010b1207270b0c010e0714210d 72
    0x8004025590100740b4840c1c1c0122240340400c200380c006d441c0a032118055000ea0000d045406200442c058031943c030080080c594920360380f03c1d040d84e8240c090020505800b030300240c2010403000942060046044035000380e4080d124000b80b805d192221035014001e02d0800d0528817007000f804a4030307542c44045400c000c0c003580c09040044a5125514606100e1380c1c011419504901c00300b02d095900450040c1c0d00c20788504101d11a942c5510000b040c0e05444c0c1d45c000e510102c1360040c44000c850548c06080400e0058034100040303070f101e81c00c10100400c5250701c103041c1034038242c0704400900529262034021910800100303006010929442894016810340f102c080000a88001400f01c1048010b0050120504140c40d041d000741c4030040c0b1041c01801603060004418850381c482040c140c0030006001590599411207440d0401c03050f8030f5009c03200300481907017050360212800d040030541c401210b4503084400d148802800500c0403480100200007103548849500c0412000e060000f66402d41c1942d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 178685872 1250 178684622 178684633
    0x15030f05180f06040804171002070c0504050a0b0307150507020a060f0f031526070e070201061e050f150a02060a0e0d0e01120b120d3902010309080705 66
    0x9075510320342a080540700b8880c2d40200c003404041154082260b040d05c0140381ca00d84d0800c41d0030f0840740b801107000800b04c8414400998503003441038002e6a002515002c48090041c0d450300041c2509803003407103024035455001741c0c81c10012200b001c411748403c000941882801e0840980026110100550003000441c4803843c49045d80d550040700850078120b41d00b0100041c0d8410ba8012000b6807041c09204014081c41942040b14000d030800b03040307549028011a0700494841c40b08a43c05002a1409000741d070070840c020039151001c44910750b140142107040889a403038201005030664156010750703082401c0c20101c0a00008150062144a034107400601950400e880070400721541151004c00d20382166405042441c0d06c1428126407507024039214015820206100000300404000164041200303410510340f2480844c11441d01c0101c0e4840380441c242c8000030042c00e01080b00310000c1c0401c00200d10a81024118078615654010315000415006aaa8032010350384040415143e9038040c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 178687122 1250 178685872 178685911
    0x18051903020102011413060519020a0f020705100e061b030703081005150a0804060b0406030c031406070c0f03050403061e0b0402040b0f0903150705070c05060f0415030f05 75
    0x24043c808001c8004101910b851070b1000d00324183c81e86d0310354006c1c00d030394450b0701240c00c083c1c21800c40c800007880800115502c030b40807400030f49450010085c0c41c01601030b500b0001064507102e003e248080113603440e40300ba9184007030304001d00c80d8441d40140b109543d410000700c2c40184200047d2200f24031a40381c44213141448c0544101c441502d41c892881900c0c80ca400c0806003115034203991082006003002d14594640386070000c090078007542c010f43c126151580c00800c0c0006054114102c9006652000c3d60390782d10340c9100e40b41c040480c1e206000c501448096030000d068490020140d6000340340c003e082035160303900c210a99035905500e400d806581d00c00201341000304e02c9400c5030070307004480c00c44c42d240c5810440f001038041c40c180b10013544000b058012240c1c41c14840b4440e07190411b40c80d90002e00d070a0f50050710940050341d040d90311810188000c80c680c20720104654400f0426071583c0e0416260902d40e510800443c0d40010070562940400c0d41280e1050090ba40244009003502c000c8842 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 178688372 1250 178687122 178687127
    0x30304150e010207110618030105100306050609060102070b070606080601121109060109060c1112010c08011d0402370503120f0d0c0203190806040506120607180519030201 75
    0x9110741c03010503692042083c407000910700d6090001e452015035003551500743c00030f0000ea61051920b0380a4155003881d0801141582d87d84103041528030981d401c2003981c85d0340040c416000012940680940d00c0a2000d00018400d000a0840b161150130301080c15a125201c1608182c03081e0b0040c08019021131030b16041001c0800e030325440c038406035070702507183c6042400200300d9042e034070992003842040c0d0b42c3c100a01140c001e000d11100300103000e1200e90010030803101c1c02010744503c40000640038500103e100101391a0702441c040d80301c034070b0040d2916141c0800c15421880718213201c00d50003040e5808003620805528803501c0c1072290114280d903107003800b81802d0000d03800f01100781c0b48041104c9640701e44580180d44400c00707880d05c0007806201c6000c05900d58407031100c601c10f03840481100c4040d81d0341c0c0f101005200e00026203040c00740da2a444140000303c1c40441c1c0742100c6812010009d00301500c6030340c1840c0448840103019400e1a5141c011450204600240f1841425810300c14019941c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 178689622 1250 178688372 178688381
    0xf0409201201090c02030d05010b070c05030d050304080f042711120103060f090b0117011505090f09010b0a08030d060806100b18090a020d0c020606030706081803030415 74
    0x540440e91420300701c42200d4201501c14010011055075866072880e9140c070801c291642d00d40c0c400d13020009540c407110101c08a8204000032200382210103000328440c02d001c148080300384042e49440c3e046441e955a4200c00b07400440a0002401c0b00b80000150a2040030550303140d24a41458900d0720308400c100e80d026a0341d00441c40307000510400000c450460004090b038112900842c00050109080c042e081c050001c41c80701400e2108082e00210302045141080a03030301e0b4090000b04154160301034031a449000c148200c0740d0041d02103001481c4504075803445580058010300000b000019400007038040e41054100380c40562010600321141c03015803190710301401700e4500a05840c0f038240718186520b03000e4012182c40d4480418480241c801c0d0b40e40601d03402100411540c0d00d031520000100094010401d41c412060405030042c1d140e90011a0380d80c02400702902800047d41010000d0300c8145014109201420000300c040c000441c05201442c0038610881190300b40039424250f240685 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 178690872 1250 178689622 178689671
    0x708090114060a050105070c080313060306060309020a0504020d060b04060c0317010311150d090f031d130b06090d0605070807050f030a0b01020c0a06020f250e06060f0409 75
    0x5011400c18000b450707481080140444500f46070550f55441146450903010380759070f024841c075201c0801c25650030078107200c3c000f0a80d402039600b00706150369140c089050f10110320b0041d400c40701e070f10024419030034150000c10071030b03803441401b00700340e556541d03d1a070550280d03006400090030b401e200700c10551300c2501c1105483e0400600313030585d411a1070310050848114182c3d4466003011441141d07500000c815214214085030301005001c0b00c81c140505600d4141104400043e01e00ca448528a03da00038100c0d01d0402c0130700b1604a040160900e88001c018030503a15500c10018441c0c15610754500c40e60502c0a881800f0101d86420041c8d400341c50110040c08510034000705000c062190785444041d03d610548400c4c010440a01c0000144e003400c0400140b950080b50304540032034000e40008111401446c100212600d0100200c2c03040c01d50109807071140c143c54020a4108164000d500c0072036007040c0d0081c09030340b5080b403109401600d58080d520140c1102d48425040c42d1981101c029014107 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 178692122 1250 178690872 178690901
    0x1107060206240307050111100603030206010302040e060702100216060f0209090709030302060c07170c06010f0b071a04020a1d070f05090f01030c0207050d031d1008220b07080901 78
    0x2188030b98000980700d8540e4060f4074108142e40c40d94902e020030401c140c41341003013504020040b403912810001d4540c4001d00082c1c3c050350508004055414000035010b20842c00c3d070707002c1c000381c032050491840a54010140c082031400107000d44d03800f0480501c81d41c3c0c500d0190702030044c0d50304400401d2017500e100090a02c0c0500c60002e0007040401e4010611581c0941c030740750003c1e590005840c00c0da1048520381c184400159000c1403c0c07030141d50015035241a00d91210a82c41c2c00f42e0354510000503449180d1004010140785000c0c941c2d0b502e5074011840d00a07100406004c055903c842040704078100703a148461502d1064030030f1204060700410a18541482d510300249465a42c601040142c104408003604047d60341c40101c41c42071080c4442c501404000740940f180780c5950070000d0100c18012068102d0b9007058051185501e000e408488032480643c071a088180c0d559401c103010000780c1d0181d9502d000303428130f003000000d1403503040354072a10282c1c0715900c2c107050a04d0b18608441ca90313a00c50741d4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 178693372 1250 178692122 178692181
    0x31f09150c02151e0108030c070f050303070321020f0a171e04061b0c061512080d060305010603030801151112090f0307060f020d0302040b09101107060206 68
    0x2c2d80480c003220f03100c80c0b850b00c00300c00341c8400843c0018400031010300042d400c1400c0000c15101d4000c002000b04000d42400c41e0201c9460348241140d068613842280d525074020008a40028000d5080100709084514641c941c0c40d200d0b400d05c003e9921074580000c203d4000980000c0c000d80004040f05001d0110200d81c40d0b900e4031206401001425950700c21545030040002002c110342500007030030002030b41070300d55103d82c25654040c084134601cbe001183c180b82400b0400700800380f0040300c90111102c03224021070074400d80e210000140e03c01c801d501136481c1c4030750011002c200309014800007107100b07699142d8298034040c9000d0441d5850014001000707e4141c02c030107926000109264038079410018207544080344000666200349030503070700750035015001c030010b180b030741102c080d071a0300f50a03800780c1d030803007001c2c00d011001c0344940d0141d8204040248100c00d000e08003601c0c29088240b690030081c5c101c24030783c000d041c0340456603840800140e0110007040441e10020f00c8110204004010110 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 178694622 1250 178693372 178693391
    0x20306011403030409110c070f0503151504020a02151608011418220501020702040e030307082403030c060603070b0f0409151208040915120f02031f0915 67
    0x2903c0b0b118a1040e4003142d0340301c40c40b141a80c89400c04807440300c0c0440040b20544da50740ca0240c09000b1081c442d0912074080c0001880c52441d600b00f03111f204141d0a4210f030b4440315040b0400c0001e400401e0322904611820400d60605024829000e0041c2c02484071155654400381c00108200416000030060515030310740b00b24039440d12003402040c0c070103040c003c141940e1744514514201012480328011404001d000c401880019070040174068001c0e1401d1010b85040c50b1129664803041c1c41d8600022003c00000d28400403d81c50603040220908000c40d4415000700007901d140c0009060310020340100c000d02c021494200b0032a00145040c80d6402c0c24206c80115402d200c4c007541c0b0035050035030748407851003d03240800324480000c0c10059508108200f030700d0520341e00c3c030380041c014070b41c04520304a03c48038100c0f00742d1500302c200c0b9158000c1650072200c2e0303076982180f8500d030f0340c00707e0305441071007030840d21040190041710180d0240079001500030018105030544010b550354074910145054080c9 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 178695872 1250 178694622 178694629
    0xa050105070209180a080c0d050f16061b050903070609050d200d12090617012c07030e06060a03051e0f01020d050423060a0e010e0111070203060114 65
    0x40311002e404030751122156852036a10000c01c2c088006a8605004804c042d10070000c0340381c054080800c000707080f184402e4032200182d47c40e12619510040800b0305012840001c0405417011400740e1040402062244c02d9403451650171802c20f49190100d1000b04d450f01403414100f080d0001040d96242111300c1e940b8020201d00d580305001d1002e403021885105042c1e40c5402c3c0645800e40c0b4101900c0c02c9050021401c02c00d40104204508800094a1b01c00c0001d019100d0b0315000001c3d51351454101c180e920301903002000340c402c80041c00d031045900c04402220240d280c50030f48181307020f407400700d035500307100048908291000304a188a400c080e0410b1012a4001552002d00600e032030f41a01000007100003540742044050040403103600004000d0f990f581c0d103801c0315001b28811402d0051002c000e5800a0160707201b0410b01d44241d00040c0000c8640741103821103800c210303200f4000200300d032185c1c08280c2510307a800030f0800c01010004043c421400c0c1007003d580108200324a242002e50480e002 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 178697122 1250 178695872 178695877
    0xc08070b0405030118110409020f030706020a0506070c030f0c020f09040804080d03090b04020f01090906030c0e01060c030e010503070509030a0b0f100e190f0518010c0207030c230904050604020f0a050105 89
    0x6e0740280d587e01d02000854441150342c40c002c0c03100500701c0d003410b5a00c1d03a00039514a102401103030319000d11b034041044540641c0b0310090701503040e2501d06090410764012545035a1010059078002d50080159103c1e80300c8100c550300a500401c0d48075030f11401d0100e51868001c00902807000c1515004410011900d903500d0385822581c12500210391406000c01251860a642c008030704242c81c00c80c000081240e03502001c0c0031540d000190060b00d80c1d031540240c645c1030f503c11025002c13450038800c0b003503a03600c42e1004550000f41824481e05028a0201080c0307003600ea12011035221005605112405541c9181c060f400350003030313184941c02410080c040c10550740c050b00f8040020030f09243c00780012015085401c4408881030208014034240001d065811103000c0d904d4025481e00b1064404240b01242c5441030743d4006258443c003925060080446503004150004108100600030729560340e02a0b0141c010f501410003098036003072030300401c02581c0c004e00d20a0304c5211520010003060341c00000307 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 178698372 1250 178697122 178697153
    0x5010605070c14150d060e0c040e16051605061506070c0909020607080a0f090e09030901050d0209100c03030b03030301050a0509040f0203010e15100b0f070c08070b0405030118 77
    0x41c9035080d20f00c25002c20710200d0a40c5200c2004900826801c1c2101e10b180d004100702d410210220009032110303200010248690b004000440341e40c400060030307400050144001d10788c62441c0c624030382001010403880900305040c04071001c1c1c1028080c000c0d03c90aa00307000c60304000031034034607280003000d40e10a6006001c900c9081d03406901c40c0c0d4a03200795603c080607602110307000900280d4410760824001c241e519441502404240c0915001c10a00150550035101d100702c240110700d00000480156203a400c84c0d80c501d00d503140c00704400c0ca010346a07402c5045c6a892140c40310a00c4000760700e00541514110046c0c03a020740d0081c801000103135a19000a41103ca040d00ca80c6501e440e41c1c00d01400080103ca400f0b50990708003105402c40d0440041c0b40c00c09080c9250300100c0580f00c0031503041c140012131043c034071503140a015040c2178041060081070468801c0c1c1020007240d590b4641c0390704010680c1d000e0414040b001c0b03000c002a040a00801850700940606a16607441a03511100302da2942c3d803 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 178699622 1250 178698372 178698389
    0x8031c1d0309131104170f0d02031e130e090d17060d082b0e01060e071407050f031b030c0706030f020c01020309010c09170309100e19030605010605070c 67
    0x440c902d01d200c3c4a51010384560301100d181c0e61741e9a1100c8020742e42200480d100282d5220300312000b24032600200398040400b00320f034040c5207401e100341c4039600e0ba0b00707800112002010042203032001c07002d00c84a804008001d40c915589180c64030070103440c18601481c1846007405680001102c040c0031003400340798440d00c02c0b29403180545079424441540d0156660000000e80d1110301c904002d02142d07202c0d0380007540380f2010300c01c010065070001d0a032200f030300ca01c2d20b0f6040100d01041a4601516803180200f0030311140ca400c1c00300e5919980d1500808510420130381e0000101c1c900100300e000d803004004082c281c011071900565644080d42d461441c4164006c2640d0b03009108078154558049400b00c003280002503491b4149240300c14000c001003080440443c82541c000901d41c1403540c05528848040400303581410601c205104441c2500b003140b1003008100c0c120171136035644044404441c9503200c400030120f42c2c10f41ca04901119410780009003406002d00c000000207840e86100e100380c61405 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 178700872 1250 178699622 178699639
    0x30c1605031c080c0918060901050a03080301030825030908060a09050d1107271505090103060b0103020412140717030a0e03070305061801060902091e0a08031c1d0309 73
    0x490407002c65003d641c00c6558451580000c06c600c2d0700325202014011b03281103581d80c03016603855041205c41d541c03070b10004040300020300c0100301042c00c200185c5050b61a00f905000e804c03504d401d40312205203030381900720b01150200009101e594403c0004030303440100b04504110b02035aa0302c0705580e0301c5240c012441006818410700c0c0320904140701007030051000020041801a03003238104282900c09076611410140b80440013481c1d04107a01c0c0c410200e03003000d01039a0315642582c4480c0013619003601070906064003040b0000701c405034030b500104c2050140e5001845011819041410034140d548050054081102e918400c19004000c5642c07100850a102c3c50900c6002c1c0880e0a0002e01d610141040c011281008900707843e10a01e031540701800c5000700030a80d2116483c0040303015013429030350040c04d0503003d1034407002607810451034280018050090640c3c1e0b07a20300c1c0d140d035004e406903030200340956003160320f0f500040c0584020120134042007075a480580a1ba03d69034003c000c2d0b828030a0f40700 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 178702122 1250 178700872 178700881
    0x40e162604020f120312090304030209130c030f0f140106060827030408071d04030203030118020d0f020d06080105040203030a031d0a0303090308060f09040212030c030c1605031c08 79
    0xf000d010507159140500020300240746915090380725003007004554080b580280000e41c2550021040360141c0364020000c95403600d89002241c4030f101d400d28200c2d8241884400880414155410a0707481c2d8070802043c80d00701454608140c02440c0d0008002d50703607040600c20701280d60080070f090f51151140501040020000f0100b00150021081625450100040100d500103011032660141e501c840035240c60070b9581c2e43e49460324901220041c0050f0070500040c000d6809082d907040512050031000b508140c40200349404544415130480d1456500162071001d0240c0d601402008140490080141e46400c0c0c0110703450748503554140d0308040d500c0d5400300c100c4402d118884414040d2008441d49070819180c054020f00510341c050b40450701c4400010103902d040d01040207808d10103050241d05407225401c1c800b80ca04200403407000c40c0428000c0c28902441080a0120f0b00d030040010324599182009805a810b500c0e000903019804c24010b4496040c0500410403035a05241b4041340c03141d45 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 178703372 1250 178702122 178702129
    0x70b060405070c020a0801060f06020a0c060c0201031407030507091202030709090305130e07030f0501080d0f050405062101050f030d18030c1509060e0f04020717040e16260402 77
    0xf650000307610064110010401c140158460810349485024903540307940ca41c102643d40700c0710b110340185140d015010600406105641122045206045c003050340ea500d0340e0340c0074226004680f4400029641c50030003805580c02400c110052020081d01140c2c200305d80c02082d08c514240c0580010a516010b030041003500c01c20484410b0400241c1780c4510703c0e00c2e103403140d1034050240d0305000080e04211001411300d0f807a1003a01d049600b40740c0240204841c85100f5a501401d01c0043c02c18400c0034040003444e6117603040100320808038054040500b54070310904680d800010381002e8011300c402d00c0c3e540c143c1e460000e0000080c4d070685c2003c10a106001040014440d840e4100810120b0740020010f65040355500e680300d01406034407406039490300d50720700b02e442050b040091030b031140c00b9043e0707040541081e40c001d01c03400e401181201e140125030100c141e1261312540c0900568845d44040040b8091300300868010246107140c03d004034501d0035075000d013203030300c81c0d1104005000800100c0c1c115074 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 178704622 1250 178703372 178703387
    0x1506020c0f0f0901030803182a031213090e070803030103080c0307230c09191109060a090513060b07021314040615050108270703050f0a02040f02070b06040507 70
    0x90b00800c402095030712454168a542c0040c0d61120745040c1c0c2c844002e04141011131b410a42d51429a07420050074580800610842c00d08000e2a81600400c0e50100192042e80002c1c411350380d1034500c100b2051300c0c000c000411511b0316010b0f254660800303481030060b581e01100b103d04481d0000b00a54030f861100d20494214425404028885c5000e62641003240134210145061410070b07900350307801c640c0b0030814010449000c8443c07000007003010500010301d018541c8184441d00500300030030304000c44000412a0781c0e000c15142400701e02e8200b0100002d1901c082c075028056440d4500740136141c03801004450900030140006d00c80c400c0290806508591903002101c40c009201c042c036040d05281c100140140541210070350030404404000c03501f54001c184090040d241140317400020244e440c8213141b50a03c1c101104c00b240240000000400d5041182d82d00d4420840082c02c2c40c1300ca00d20401c0100ca41d288071151801d401440320401060b03400210279800581501c01245a03500ca8034111580c6 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 178705872 1250 178704622 178704649
    0x1030b120d0206041118010e0a022506050c0f09010c0303020d0507091703040806130f0b07090e01090509030a111f02030406051b0d0b06040906080c01031506020c0f 72
    0x600c01d007035601e00e10340d90004009014500030540e44812140e000103212800b911440002a0340e40030100400c1200c20b5800b40950000310001d0041c10126044558000c0703a010a00e000050f0305910114000d00003d881199000024003150500d40b042e50034040c116801581101d9050090150004090500030b8040703400520300310034204014541808003030403c07190340c081d07402404140803180c01c0c024000030484065911190003052242d58440d4050b00741ca81c0b030130781110145070030804100068005440e2a01900c0d840c2c07142013000d402c008002c594a10141e009004050400c8103206440f00c2c0482100c03035907005894420219a8140c0c0b030380f07280c0420807040c3e0b0380255524100c034100140a6000d9400b0f588260403c1c000c6807202d212540c10340203955140081054100300d100752024042d07000c5500200040e056a00b8aa60b0b81070034012220f40c2c2d4051252500310a101000c1c81da8140720340c000c10240909050000750400030700954580701d10a100307004014000f0701c12916503600d0035500c1003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 178707122 1250 178705872 178705909
    0x1e130b01060305100905010b0d0902030a0512120906040206040302060c0f0f01020a0905030d05040b130e07050a020d140f0d060306020f1e07120c02120106031b05040207080901030b 79
    0x495a5901d4020000e11003100c10001c030804581c0080b0700d50f8000d0141e18103d91a10010b14101401d03c5050401402c8454040380e1520491180b280050024480c40960980c0b44070211380356001000c0c0e4820382180202000d80e9508084104001a6a05020342c2c0c00e6a4060303e26030746031845c6058041c039181403e42d2804662140d0100d90f00500750540040c98005030540e83c051200365180180755132004400c101c0404100d050005026404040000c2d040c0c070030040444407800395441941844100c0280c1c0c402000900003d01c20507904c0d010010244410181c2ca0030410001c0501c40b140e06030b02448010707030922000010245460002c50700301038003444d0004c408542e10f00d103201a42d0096404041600800d1250705100144416800309480300c10b900002d41d0120000084000c51f10715102c00c00407039008042c80406410310100b44120b4000d144142e1b07a42151402c1410310403041d80300b507804188a0760040150000142c1c03c001916800a42030034045002d01201c00028280105c45040402 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 178708372 1250 178707122 178707143
    0x140706050d05181b01030e2a1305040605010e060f100509030a141608030f070209040c09150e0c090a090504020a0b07050601050f10080609100902040602011a091e13 72
    0xb54103408500b1004c038103000d8800b005040c0c00c60340c03180d48404421004400c0b0b01468204040309641e41c0c03d1a40d02064010564841e10380d14103509412500103460503205039a50b540148608188002d891381c1106049841001c60528100025820940107900388200500842c80003810344040040046603540601c0716100041d024144c0c0d070b510b031011500c200c155555a140007544071408800c0b1680130002030f210900d4043c064003072060410307010300200c400003010f8600207045c2c0c000348502103140707041d00075191010b40f52000311020140d001e092107900074002c1160b0111580c500001030200c8055010100c1c99540c3c900000701102c11a40c0020018400010081c040000200720301e03050750002c80728051211000011300880c1150805084007140b00300c40420f4a070b260640000d0743c48164a00d540c01d54a4907403081d28240e800c1a4048400350f0b4480c00c440342e24247d00c9031107014000040d60456014904104042c0b84c6400700c1800740c282c160001d003c5507894054400c05a019604041d2107107 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 178709622 1250 178708372 178708393
    0xf060b0f130603090b16020309040e011a04022506090b040308010f0b030f01180b0307470a05090603070f0f020a03050307050901090302031009140706050d0518 70
    0x19819401492845501d00318114049401402449103040303441e0000040c6807540c3c0d03404494074810076403c80000940c801800505503555a90060444510010700040340c100e4010407407818a182484820b4890f40c014008580520307401081d00281955180e04104094494144000140406036001d018800030800704801e05400400250485101c200245142aa64040394840b40004d131581d0405016450040160000141c0001c224421081000505090200c0001c0c9420740a603c40d602e04030480d004281d003d000c0c0c940c90303400f40705500f030a18240403a0720311103840074800c0d012505002c507000c01c03200d4409216406032400000c01401244c0d4a0810700fa0103403590b0900356100000400d0503024902e21403011841021099054a805003036442d0300805541d40d03009901c0c8a410040d60398400000b5940410400880c140c54007000501e15105042002c0701140a02da00c24a0380c2c841d4800304141039000b01242c0708512140e00c00a583e803289082c008110039120403087c1c0500c00e12140c034 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 178710872 1250 178709622 178709647
    0x70e01050d0507270303080604020a02160306061401031e15090f021c022a16090b01030c110304050609120f011a0301140c07030201020c060c0310050a050f01030f060b 73
    0x5142616840070410200c19200010f13401c00200e03800010005a0b0072404682141800d8015207010042170055844c5c51803098829a64020582d2041d01d01c0c0341c50364020041c07000c0e428070208621f042840d00b440a02d980c0d42d5484903100b80e50062811a41c0e417400c400c101400c5c5001d1400150000200522121250083c484003a406c03a2401c0e00e200c1a444090441651f16803085a40c48030011003000c01c1781d511b00a188a0407810500700080902070480060441c944940c12200580300b00d19001a5841c2c180d27000508854005624105000d403550413050344e80000000d940480f03004958032a613509201003c03c81054086c2d49002c002d1150000448640320190810101c200c8060402200d00c0e20303c000305801d0b520003484404e903c2100c0000f185040e05014010440180130340000f46c07030301000074452880d008003110500c04154010051180680d00c8803000d000030700301140c0b5541e4150a1034001000c09500310b50490501d030352041241d16200c480d4102900a100b803206940e15000b0541d4034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 178712122 1250 178710872 178710887
    0x20315071116080d050403030e041a030a0302061f050d0b060102120a080406140c07020111010213030f0b01050105040b040512071802040504050901020301081504050c0409032001060806070e01050d0507 88
    0x40c3d503001e010389041001641e203c1c0040d0350071660180d440110304480041404000e140b94588054414142103418070a03403000c00000312241e201758010812843c0040f4079040780c1c1c01c185510300410080100810507035031001c4500c5442504900604101e468000040c1d107080a0368841185807480487e03400c00040d0011011481140280c805000d0107040c500e4030300d100181191000c1d030101c0c06020303080142d44624181c81c884103d101c0014903003841492140000c2640c2d13031044421a10341c2100304100050a03000c10300410080c00c01c40e01301030520002446a006038040e041c0141c3c402d040c11b00d0b80c04c0003000240000c0003c0030002e5100310551100001a5006003d81801141000c021031807168051003102d048500920182559803104101440318450140050b40c0500c103502e030712000e9960394800c44c1e40c80c07407103504c80054260044c0035503010555110f04a07031460f403500e0002c220241010461591040542c03806c1090400320b400162003a014000406041c149080100001a41c12004 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 178713372 1250 178712122 178712129
    0x91c02150d14010305030f07050127020a0b070f0201110a0605010605250b0708073018050706050f070605010902040812031009050a020702130f0513020315071116 71
    0x509005a080980c00c2c00c69010083c0300082c40c1e0342c000c10100c0f10f54001c10005d052020300c52400030800103241244a0703640704020b14106105000d8500307107411850f100c000e150050150300c40f094200841d544034414840103680020303052014101000c07802910500c411031446910000410103540c5649000740142c1162206901c20a031011031005d2401d4450000b0b246140e10441c90046942c50300e20841e91000b001e800501070044420005202c2030304040b44c0101c02050f40c400301509403024481ea010786100ca0304901c0101e0381c901030b003004104085010b40603034029040442c0d0302d46110758158040d02c80c18102a040900e090008117050505400400448400408441c50440c16244414141c0700580b00a403013081c01c0c44c0f0410600209801081d4400c46481d00182030241d50340100d01000306560070b030110640d85040d820141183e5104003500280603160f416008007c0f50b000c02c1c0e56205186410300c1c2c1110365000980601c2c440c40481d214007102d002603504111800c441295891030500 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 178714622 1250 178713372 178713397
    0xf270b0c310603050601110a060b12070603020304020102070e130201030b0f060705070302030d0504060815010c0f0615090b0604050906030c1f0f0e15090a05060a050c010b03070506091c0215 83
    0x4001c90150341c4030f00d209444801f81c24014103400c2c030300ca5035480c0050902e10000e80c2c11092000c1034292107181480310070002e00c03482d1400741e641c0c5818400281044800d403c80d038035044441080c0010120490500d00c4401c0e420b00b00090010354880000782103003003003038120703601c13200000b5080304014004c200c41048900c01d0302182c09261040d0000c1d141c0e030065002c7d1000045084000a2800c4d6401c4050584903a0605080c11014515103030ba88030113164510a944960301d500c1281d01c003500d085284002046d8543c410005403074a200044e0652080d031141c580716a400c040811841e41d02403246100c40c0f000107003410300d40c04000003441d803682c4240f4038210215035aa0701c40050386014038517030114201d0050001c1300162040e058007005030480303200f407a040152083d02080c5500d40c64000c243c4092a81c4400e515091206030341401d43e13407480010b0780a6000400100700548800064515028045544c00b00c40c03180003d250956030301e18407001c3e500c030180d002d108040300c500100418181d032100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 178715872 1250 178714622 178714631
    0x90606090212041b0510030203010509060d210908010501170d05070c0b07080d0c18120209060402071401020a180509040b07050315040f270b0c310603 66
    0x6940d01030890080b40701c2c0c001080c41101c001030006880000a0340c0c0c0c006910015044140c0310350129403e080c014a806000c60b600100501c411b00d06030340403640c0801c0480f4440305130145035490f0042010240d030180381240482901403440c83c0940f0020003d000e141e0020070056a452300551221020510300409038064442d0036080c80c1d00c100111403c05030482c1540c0c00b00752801000c4409503010030703007d6555180074040303c03001c84498081d00081c560150f1ba808503071002ca40e114001041e80b0f03442802c1d100c041803450340058031601221b69201a040b50300513100c1c1ca041c141040010b0300340390a49119440000c440002c03541144800b01503031740015800d4010754a80061010405069034003038113000c005000210a00c2c4260000c55000d140c0c0c511410200d040302e0003081c29034007401c000e0107030340c0d860708880c1205041c0b90f10070340c44603a41810450740d04451626401c62090020340303c0310550200180072100c070541c000342da082e030b4102d4419591203172281481c40001001503029200001e41803 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 178717122 1250 178715872 178715879
    0xc0b0a3905040b040b0f07080c060702070602071404020c0a080301090204030b0f0c031824040b070207050a0918151b0527030a0503040f060e0907050d0b0d020a0801090606 75
    0x1007040c1c9040d504200c614600d8142802e031258420340281240c120b42100030000c1c01c000400c240050110a09900014621800c104c1c1c0080c4c1016103640080c2c1c02c542c080d6200f00304510a410850760300040989005aa07441a481420705100302c2032400380c2840d02c0000000b441007000c0d03006000f120b008203001c100c0d41d1503000400da580e20302a00c0344840100c0074004a40030740d0258903c0c280e02d008c2902212000070003030a64014444030980f20400c5005034400300000d025105065503401052480904045030800001840350341a0340104a850360356488031504006c24040902405901f00e20b00094400c11211241c000d880e01201800c3e030b0707040b51322100d801c150182040d40c010320414185803800a00c6010816000046132101c0c940c10301c5601540404134809000500103010031002500744507062110140c0308042032601180140e05c0c0e5410812036a0340101501e8680403c80300c00300328401c4000028840341c0094001039409503018000040d260415440340e480701c3d108050a102c941c1d038 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 178718372 1250 178717122 178717127
    0x905090c0d060f09021e0112090210050f070b16020c0a050901050f0409021c0c21020904050c150a120501050603060907110607030b040e0d0c0b0a39 65
    0xa80d810507001100d030304980000a01a4002444464014000041c0c10b0701c0c90b0001000f400b001d0b020182c0401808044118659000d42c034001134162a5006201079407070f84d8080b80718040151807107001c110740812600c090705500c104031020705820031104505424400d0030184090081c4044402502ca0141c0024032414040000d00032580d00501401d000c2e2307e004180004141e901482c9a401950f4110031030043c1d0750907001c0401008507200680c031490191130441000541500b00c15540f0365003000042c201c44a0400801c20039905881a44064490340340c102e1038122816a415031080400c0d81140520b0740c000c01030403c40c1055900c0c06c51100b802d400f0001103030000c3c040c040d000481000015501d04054840d80d4210240303240c03445489504d072150500b00032003582d1042c00203495100400c8a8501401400740c4d4000d0907000d4842d1504a0002810138000f01c500107005062003000521030a2255100e0104581001043e0025034290b00340c4140918140c400c0e00c4850300d4040c003142a807071 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 178719622 1250 178718372 178718383
    0x6140604050943050109051e0f040230180a0624060504030c05010f02060a050603121c050903040f03060207020415030602030603072301081510020304090509 69
    0xa681e0781c0a80b04580c80c0500340319003c01e212050860303400140000c20180610024000100d440c0300b6900a42e42e41000c000406c0070a0070b6010a02c900512007200d020080d1100001840410442d00030301000c403c10081000703400740c0c20f444035100c40400c1503040040380040390101070000da88402005a0b454a0003a40030240d440d4228000da4440c02c500e800240d018ae00215000011001c2c0d1025850314007221044e4000300e42010f0005030012804004103e0300d0800c01e4040d00e02400c258810180d0940c00959400c0018415000240c0392004200252001d02008280c980e610650741c0c0d50304841941c540404c0c81c1c11071590320492802002503080c0c80c010041d20300303a440003004104002c1c6580c861801039007061a05aa005c0c1d95921140e4103c800c0301e032942d0055100d12400750b01d80c40d10714101401c0030299444088641c0c80b4a0a00c843c1e000e40b0500032080010908041c170403070311241050040103041030152034011401000c1c2d0582d158002019004444441000340308a07994510001d4a51 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 178720872 1250 178719622 178719631
    0x90d020714150d06080a11011d0904060e0d210b061b010212130218040809130b04020f0c0f0705030a03030b01050d090803060f01090503030306010c02011103070614060405 75
    0x300d5103036030a0a002d1078040410300201c00000c0035207050a40c0f02005004540542d88090526030101940e0020420344400f011072040e000d08003500036420f009a1084240405080c1c02c2c071600a41000804100e510751106410121810440f84080020000548644d80c25580303070310110200305100d4000c88090003000f400ea0406030001e41007166403c00080300c2c800807418840383d1354003404081c11508030411036030b10584005040002d075403000c0c014005080418140e0302800c4004130100b0001c20030060882d800c0c44015104440780658003d140001007100548450f4020f000099040c910200c5001400c0d40082500644040424000c0682c0d59480f0070b00c102901600a05d152070302103030190340980080c20060501d5468800c1c60070040c0e01b214104101156020b8022080c002c150524824500340d4602c207003401200241080c00299590000031302241c10001c18081c07070011640b040501028841c4c0032400c4940b650000c0ca0030b20003a010201d49009126024400145103281900409014 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 178722122 1250 178720872 178720889
    0xf06110a180b04050103020a0516030807110c010e0f1507060914030705120d11130303080106030b060403060902041107050105011802031501080907080304060905190803030f1905010b03090d0207 85
    0x40624180041d0b0207504015508c10610400b40641a04021129a0030503100d209503205c1c0305600c0c1103080a0501800043c00d4002a0f01c503200760516a6000b0914451000080391040406000030001540c403941c21398182e0098000402c94504004c0c2c1d68014400f0580b00d4071541c01040c0c5585410355882c042e40101400c070340c1c40740d002c40462089100082616011800003c12180c0c1c4c894041c040960040340d0141500380c0d290b20800038941e001090300d024045602c0c1c140601e802c00c2000910314040c50201034245691544540c0465031303207600032141e0320304841ca0303180c9070001402c0c054001d01091044003200c02140e042d030f000c00100b1f842204d105481014090100540c000c004507407680d0000c00c41801071041c0e881c08104a1002c00291009120a541d122000c2e800c1070180038007401d2807043c0100c18048008244100c03100402030300e0b4440d90300052940b641c0d8548820412103080d140c2424080f03868030300041800c02410004511400c1402d04807a00350688c0d8804a0380c40080b441805d0703c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 178723372 1250 178722122 178722127
    0xe010905060112050c0a180b220f15060f0909090b0c07031202030a0209010207050604030503071410090c0e0717011a0706050a06170703080d090f06110a180b 69
    0x49048140300100168094001c1720b440c0d03c0c00501003404c40b4203c0d0881c84440070308009640c1c400c2c080340122015100d0641d0801a00c0c0c281c0c800c1003e400f1502d40c028040d00e41c0f80d0702002451906070b4040c511b165540340a210b4070690313892000d88074441078405180020403400004c42d00c207905015420455521451381e144540c0d03a60381b1021141c01c14030046041007010b2606504c460103038000707035015039030004005039542c44a10001e40342c00c900c0d9100ca40109814081013010800100c103840c0c401d80c000708204032100b044201d0a041911994080700c2e0103240003c194203010000f000c580c1540c1d410051a070b00c45d02e9055003a20241d60b8030304107010850080005200c520112290302c0301c02c88036134034801d08040c0241c0e200d000350303a811527000300346a0b6500010840103042e10101c46011015001400405046854060551003039200640c11152103400341e9003003100941003524883c0d0400410484e4907543c0105150b15403050b04403200084003104041000341c0210004000c88140d56030007407 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 178724622 1250 178723372 178723379
    0x30804060809010204230d1703060414010b070b1f032306151203070f0b1b0a0e010804030c14070f0f080703021009030218010305010f05040b040b0c0d0218040e0109050601 75
    0x6101486e55010540c00c40300d002c3c400b078002004000600d5900e100004455268501901480100d481c8215030210b8480041d004024445a0b201115101c5400074180740c0190749040f0310032030740c0901d024401980c0245020000c1440090035102549541e10413891203e640c90340400c0f941c800d8260740702c4034100d80004014682e80703070440e00903205407403010a480c107285c5180c8581e50310882e91038054604090f0141000348640a02c20040c1800c910b206540f810300380040340c004c0c540d0b40e05000d82814002602d010030240360040340c10140090740b01d0084810b624156203026100c4d0b010380304111a02c00f00c5040031850003a542c03081d034182d952990061560602d103030200b0001c00034600c08142401544400480941c654040e521034550101030040080d500d1460440d01f100c804003224208a8a0081800000381c004509150002d81049250b0a251074043d0000c2c0148a80111a40814400251200c1c42d1000c120517203c035100803281000a44021a0100d0a80b2400d01c002407160300903078010b0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 178725872 1250 178724622 178724669
    0x5040902060910020705040e0f0c01020105041e0c05130c020f030c101e0207080304120c0803061201110a020a230d050304080717091309200316030804060809010204 72
    0x3800081c00d00d00c105c0f103010340d5500205003102c0c000c9030062a1500301d518220408041007000b2940844280b00811143c0b5083d12000090b450309807a0341d120003001114a03051001c0c410b04030740600001070401e840c8018000c04d1000904070900a030700903000b010301c480300701c01c000b02c196542c0000c603c01a1803c02c42402d00c03000140170b42400d4400100e10f240d00600411007500c094000180704550f1282d41782007505003038083c8038949840a04100c0c1158034080011411b0096035000075080c0d40051001c0d03510907000d400b41c8800d403c030300720300a0040350306016254000f5804100d0360281183c00102444403500f41c24141c8a24401030407070b40140034444010344180300031640103016110460816141e80d0b1f0f020020411300801505540000c90340c90f40610304048041c03010f8581e80b00800021505039180c1030500c021205a88482110188040254505000c02610800d1242c1c44542c41d41e10380c41d0003801b64010b070003400d001034200000201c40100c14802c5500361a8010141d072040407412010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 178727122 1250 178725872 178725889
    0x11416030c0815011b0f0302160506040605030c09121e011103070e0a08060403030b01030605010e1e2815260714031003031103040f0b030c160602070201030501050409020609 76
    0x96904105016017912280403441c03520a0445102d1080d400402201d414001d260041504d0b02c001d0451450703104006e16528401154212840d50825581360343c8d805054191a02424003a142c01418402117441d80000104a9801c6d2400056070b0414201107101802c0c200d40b030029104140e200100082424a07000d40182c1180020081000e07034101c1d211801c0608200058408a0229451b0510f83c0481c0da0140035000207004c0030710b0111106072802001903070702c40525442d49520108009081c481e511070484142059504010028028503048219180c2203040d2003a40c045040309500d4020039442030b10074001181181960509100307160350242964400a050b050900c01102c2c8503440420181c0b01851092106a803c60b03401450341c200501880303007030340c19040207800400c02413060082000c8890107840701801e030a0b880c1e83d25842041d80d544655029800e80910306070203003040058540061164900c01e0340d09000d5666603106000540310304e0391000790301c07003414400074115041c02080f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 178728372 1250 178727122 178727161
    0x60a060513052205010b0306160819061d0a111204080904020904050a09030906030507092319031109040b16020114010f090608030414060d0e011416030c08 68
    0xb512100759403080f81d0042c030000d40010480355070351100400480391809001c0c0c2c5034840c0114094030100d5040307131402026964001c0c10164100303180d4144c8903203580c1d994001e13000303403601000a1003a42241c1c280b40da80c00c44201c2d402c035101030400c4a04da10346000e0300c088d1445040703680c064010304e0301c840c0d440740115049000722035001542030041c1d0387c2030b5840340070b442d0140d00040c500007400c0b070f15414010603000c1e0340d4010304149810031040c0541d43d41e200322441c0c02c8440c8c0713844011420500c0c901906401910300e21065000403c00000d059285410b14080300b02c1c6e2165210030384020408050021403c03040720040d0003960380c18001070000032046000000203645200005112810800c60740d9840e00070b800070b0f0002c4880c105d06003c00b1400344550b06c0a400940000d40c00c0900e8080d070025001240c2c211a0300610021400800030011600107040d102c100303200a0004141842d2600f40004049540480c9001c00003028030300c1d00e00a1240d10010707003071035a680403150b540340740013030b0304901900 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 178729622 1250 178728372 178728391
    0x70510050c0c06070c060e0409110d050c0a09020909070306080a230703060e0d090509130c03061103071b05150c131502070e0106050a1206090504030c05060a06051305 73
    0x44004020fa91058001c10f142d5105005054003141401e00081142480c00003450080d0314040d66a004200c000424000d0428101c1e20800c168400f8034200341400b0300b0440458001c0e01d0f481c00451241c04580143ca045101559465140e80c0c4003182101556018402d00c1403e4000070351610110312070049020005502e91041c0400603003204080d1325101444d44245c034816960210203011a13001d109052a4001a1074082e15031810440098010381020300300f402c10889a1030000b04101d0b52220f41c00c01142c010204103c90103c40704c207000250f2040f229000003034020541c1c04214510400c400c54069042401801c40d410f400b54420300c81c21016250760604031051146595036050f0041200c00360103070822001d03400f040b4180c0a850260903800403403011342818010310010340c1c05416100010351502e0b01110714600100c0c034000078440d6030000441d0b00c1c106400c02c81410742001c046e8501a208104072441c2d0366030601c54004039005400b49951040c81d0b01c5a1103006840394208580040403039 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 178730872 1250 178729622 178729633
    0x51c0b060702180103031209080301050f010e0d11010905041b0c030e1905041b0c0b040606170d02100e0705040f0212010611100204120f03090f090e060603070510050c 73
    0xd0b000990641c01080d4607180500803040103004150b405105403280c2004c0d480e00344080002a034400c0b145000500030306000303104901503110181c0c400d2088540c100e4001e4824454083d06040a001c800d25012000d80070ad00b21840c002403a0501b0300c580c0d068240c000f03504801c0305a041034200d8442e1040041a8208041c40400300017541e115802210003ca440203000d680f20310340b10510066034440c25819100c644003d840e01d101302e03044014051110f038000d18820300c80d0303100d1518000511080d006003c085c90546481418094006400d00c00caa0340ca4080f103098a021400c2101034583c52100303c01a07800090040103941403c0e0082078881c03c400c40054100b112801c190581c040c4260711140000d08900300c0381a4040c000d2000c941c2c1440707440801c0d450141001d81c0208104002140246401c0b40c00c04440300703140c0700d2600c2e180a456602001103845a4558008015200c0b030310044541d801102d001c5001ca1800046640c111580a0b2094803e810030b14400c0c0c50039001461a42402d0068 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 178732122 1250 178730872 178730887
    0x6021c090e06010905090108010f0b060a09030803180a03030506010314240d060f090c061b080708070b010b0904060e0405061308040f0b0a030609020306010e0f0f0301050a0902040c051c0b06 83
    0x1b01c011803030207001c00e0000001e081c0051244171041c1c80c03444800c3c5016804c10048000c01651101100007966013083d2040c3e0b4a464182d240c1c0f640840c00050110b480c050600a10b0400d41d0580005004d504260b0f402d1207440c3c421080c80c09403070400d84025080c540243c4902d04208244800b451a40000400911114200d511f50350191450b2081844c00366a40d00722040412071007400010140c0202d10749071b00e415001d540c1da8103820001c40c1c0301401d03003c2d02180f88408c10460b50101c0d80d525920a540d00d0042d65103c2d00e107520b540102015522680c240800411800080c0360100d00c00c6803c01d00410542c0c884183c1880d0700d0402d450305072002c000801c408105240390000f0b440080104c5c6041ca5650311210a00608851440c1c108010707460042040c4005aa40085181c16010017214800c40340454240041c10075680c050206816500b044100000c52925a00c5044500e000fa00c042c070004444403000c41d210311803103203038401001c0100c015268054050707001d40d000c0700c0040c0025140110 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 178733372 1250 178732122 178732129
    0xc1218121403131208150405040f08271c080c03041508061f02030304021002030418020306040c050f27090a1b030b011d0402160c06021c090e06010905 66
    0x2c101c40b0240e105915001510422031465111180d850325494244c0403402c0c039804103a414506401e50342d106a8581c004201486008201540529406454555180c00008040b849038007442d24001e01408203896885403420800102c00424800101d220038100da113503180713101030700300c83d10047c65840140f0010821494088252564070943d0301e0756005441c1034030810504096918540c0200f0404901100216070000103886d0015030466480e5840082a0001c91550003103502444444600000c0400e1000803540154000c40054500344001240ca25099400b4801c8181d04081103030704110026a08004140401961902c903044050020070b40001589141c0281da41401f21275507820421038142026210708840b410a04041c0424a00c4800180c017900c00c01741410144000400307410b0856a031541111120149101e01c80e0260445050158101d841c50040001620583c000030945103404c2d1900c615414487d80c51444183c2800c40c01c011070f0402604a505000d07450601003015034 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 178734622 1250 178733372 178733377
    0x9010c06091109100e0606090d080d0e1c030e01060501050301050d0c0503150f090106030809011412151002030f0315120a050f070b03090a03031104030606090c12181214 74
    0x42d2140194110701d04000d0284041c174400740907540304006c100003161068450a00d413203039868210000a451300d0031800364001030204000341c2440e601808a10820320403c1d404851504a441d540030407040a0070b02c08a402c0343e44900615000c07503001d000410162a041c02c914080c1445415008081740d9100042031070034400041c0c683c140c6083c101088a1200035801169026500000900809155480300d140f5407107140540d80c10011a0329007580104080401c55001000150400513540341030310084248128102906209120840050b0700c82407000054a071402d9604a02c0d0349146c80d043e90011070f210310100600d4202500014801459005001c9100043d000348064414881d6010189080002e00d400803c020601071040c4108460001002007000342d050400040c0341c111600d41c80748a000750b50004007200c5c00c0850105401e440c50301324034918107954840d4034444450a010109540c83c0c1c210325808480d17407480c10404030352451004100381c806400c2411840c3e90f01c08099402c0c3c0d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 178735872 1250 178734622 178734631
    0xe010803030402270a0507022404020306070f020d0e1f110105010803070b06060c01060b1902010501151704020105041d09070501050c060109150f080606031209010c06091109 76
    0x6800100421042d4100920300801c41c041e07000f180030a404c910101c0d1501e4000c081c01e10600540d8800000d17200034001c102d0b410300000964075800d0380c2d46011440c00030680007201c00300d00074054100442c0d0141d014a0501c1c811b14070540240c03151003030b0b11100b25a00d100e40784503103a019608020354a40460b28030702d030010032603050f80c480f900c05030b11012280c00e444041e0704c018a40d5200f000290086004c1c0101d041c0c200307908483d1319964964a1061030b001d031a080d084400040000200030006009141e5404040b8005800034452aa40c407650007406c000102421000302d82d9400003517103000248030243d81c1c09441410103600307183c0ca034451072803410070800c00c03c20442041c4080c81041041000010b00070704092a21034584403da044030340e2160418810400003640b626a00780c0301072810f11500020b0000300b209049059030f50040340b9a1014241c800c12700034005c0d8803e018201c00d05400315003c0d14070603182c01d10800401da070baa030010311541406540401002540c40f10300c0d55403290a80c001c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 178737122 1250 178735872 178735889
    0x1615150b07020a060206010b0703030b060424080f040201080609190f0603030e0402071a090f100605040b01020616111905070312050c061803070c030b33190e01 70
    0x8480262040c031003c1d040641014065500001c0100107007000304044805442e4189030100d0080703c034030003180e258022070f0404e1100c1700a034108565400000300200c0700030025580e58207400d448000d46041c0e00708050303038060300050003c00024000e0810b5481c498010b01c0030708000d0b4010811940000c21900110f01c04800c045d05c400782001031560151031b503108860100c0c2d04501d445a2035a41c05645011075441c14090400100000e0f00e404060001014910688007910b054485030410040109418041c0074482c40c0742502000155100003a210301c51901e0948803440b00c2c80c0b6000a85c1d107110380316181b1034a84a0046100414400764800000961107900105036071815480c040700e003450140101c5003004410300000c5030406000506c0c54015024445280020a10301a054107602c2642400b80004024980c000308100078045500c0c4201070210350101e00030020301c0084a040600300d003a014543c025220015070385088084c0110444590702814421503403200094050042640450368 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 178738372 1250 178737122 178737127
    0x5101818060807082d0604060203060907030c0f121d0607020c01020a0305160606120516060203090f0906030307050a03020102121008060406110f1606111615150b 71
    0x390150500a200182a411001d0901c050501601135a01c54442400c107801e803070018043c8104411140c800d0095113501d8054480900d014103020010750700640e506030141000e00c0006550780c0c800d11848800f0406c0d5aa1615102a00300c03044030007800d14000740c10240c0d99510388031601e5404842804082d08804041c129130718000384041d007400b42001320320703040d900710705044000285c1c048110f1f04074061604a1100f01d0116007004001010f0540080700c100d55910914000c0c040c3c0001e01c0900b50076001d4410311071546a01c800c030f03120300030400a00e40222024032404554a42240305a81c007900103401c603800c0ca000340d2100e40c85c01c2c4840c4010783c09070f5400030700c4460f0400302e00344445d40310b8042001c0500e40f91910070700e0341e5103030b1000300050301e102d42c1c0d07100d0b105080c260881115502803003903180a4071000c1441c1141c2100e003c10808880300c1e440c0100c1020005220390503120031385600d049005104403a41c0342e9180d500480001030440980e0303085441051803504520a014142c0d18503401d8 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 178739622 1250 178738372 178738409
    0xd0e1003091106280e0a06050a0212030c192609010209220506010f0c08030a090c0b090103050a050402090f04051204060305040302060609101202010306080601030318120c051018 78
    0x100301021043c0304100b00300040805c40640310092402c003110602e140096a4041c0144201d041104562010305854000010320427645c42100c007404419180b00000090813900f01c00c1604d00c6088010a00c09142840d5050252070150540280c4d02005080c0098604044030001a146021110b0490052695010b40c9a184c540714401c981e80070b0028200044181c451000c09424004000001030010900200150001700543c01204203140c6c420688480d2035110f102c1a444d40d000f2070300c2e031800246001d0005814444500500b03020316000b500c0c41055032a0200041c000040003441500c2c54402c1c40500310551003c074005100030042c90f07400050300e05181c41d000703051842c00f0f8000c6100b003288000348103034140c0b5004408200c0b02554541e41c02d00121748010380c0581b01d40ea0080300b46000d418000001c1c55045914a4030103208010304801094803000f803122071040500d006408004849418031160510341010b03c0c1c61200b500300000e040c1d0600200040c2c0366441e400c68003442c0d81454054 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 178740872 1250 178739622 178739677
    0x3050601090b011407020315042409110108041a01121112100c020c33160204050402040902040903021005060d0506150a0f0f06020d0e1003091106 64
    0x550240000700002e1040c14aa440000c050303400820401115070300000d0710000b155410014804c030400440004802c600c0c05080040904e42116400f03034950341e1104800c44030008911840d05403d90240310400c51103650801140d54031802401103459103200480d100740030b880483d190b8020092903c548810f8083ca00d0144031541e481c8480c41d00030210300b0103141302d00340d010600c00c0d8680b180000000f00c03040e00a1089141861602201d50013100542c911904200244143c0502c0e45010700d800c40e500200008142561082d06071840e031104589030000018a07098002c150841c0c0001c1001c102d070555500014215500c1c003a048016030b2101c00c0d503496507506c03070143e82d60143c001c4600d0000300716261a5241c03148801001c0004050480c5071141c080d03907440d2845000b502201d00c850002c66210184140000c1140c015079000d4416803070100c20061107101d4414190001504400001030b52640613005005900c0c070441e400754910302d02c1d00d0591120790192203070024a144000040d1700c540b140 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 178742122 1250 178740872 178740883
    0x60f170d0e09060907230c060c0306060714030f04150e150405151306021e0109030504170109080a020c010809010506060307050f09100906030f0510120c0b03010905010305 75
    0x4120a000384600001c116949002d90654800d00035510000540e459400031545800c5080381c3c01403c0206c41c14041c44000b070b180107403080080b044102da50035213540101003c1c1c0e000c00c458290740b12500304003c1d4001216008180c84130340e203000450b810a030702a000e02c907442c4c04c070f504007044110064641c6880581d03c00c0441007482810781c0c101c400d180d00100b1055103485036028060184080e01400040780d0520f1048a494515400b45a1407058a0304030094136402d6880c4036807883c580c4180510918001072017045982981621694a010b240080c8001d0800390308290000c0343d541c80020300081400900140b004120541c0500380242c42d040015110b144003401e80070480e03140408102c1d41b170300c0d40070843c1d800ca403142c14815200d010401e0b110b00c840c0300b8500c04541204007102c2420085802070b84220581d41c5907201400001a00c1c49060100c46045501e6460b8008008003082520f44508088029500546100207a50703114041c101d550390080c0e2211080c0d507645c0d80100207101c818040c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 178743372 1250 178742122 178742143
    0x90c0108060a050402070206090409061b020d020d1b0b04030f021e060a050c1b150c03070c1b080f03090102070e042d05100b0301060603140118060f17 66
    0x80016250401e880032682209440c003415014070340c001100710540d9106400c0e280a598001c03c103109004261a0900180c01cae004490b101c0c1c0c001401074910700ba170011698800741a07656008054002223600100c40b2044104040c2c00001680031000020481403407904c0d2040d402a1121910200031100003450b1126800b903008541a01114a485124000c40c0d1036801c01401103002c02c0e50345408002d00c0c000e01c90340c00c58404464040d00301d42c0c82508040350520102c2010104820107954004d40800f030703803000321400b2000811403000d900005103070441c101e020711448217280d40e2081c0c0b66210f1500d00200c54041c8074440d0700100c0c0d494441d40c5d0401200e8090b088241d00980a42000d40e44d00485010040c008440801e2517030203003148405040c041d403821070b040307007c8a0350202030b034544030010681000030500950802d000816240d000340111100320348c4180c11180e00d60718246060b403070084041c081e840c0c00ca4645900090010000030003001034000c580b0f02d04000c52841c09110b00e404141c09 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 178744622 1250 178743372 178743377
    0x512070314161d0604120b010f06080402030d080c09040c08011e03030203041701021303030315050f03070501120905012c0705010815030f0118020a0b070519031106010e090c01 77
    0x9000304505a44010520f681495100ca58180305180400080042c01240c001040040c04160721100340a00c0c0300e1054120307902d5000c0d210780e20340c403010111000ca0b002c40d00650141e021030060200c2c0c1f486002511313405419000702505020021000034141c0e039024800704005103900e801400030705400c4034a0031000b03019151020b409440c60780c0194590095102d0340c2411160b910100c0c16482081d01107400030a1884400544140c0783e10b00074000300503040f05a44092a002c1c40031405051204015012850082c003c020907494900110f581d0310111080b641e0b065282e02c4898000307602409035480d41026604070390310ba034044410280e00c400a01e40e030305003030b80e208100800890360440303041500190b00c0122100d500c1007060120f4a00180900903401c0c561a0450fa0079641403600f818108040c800c564050b962a40d41099000d10b0043e250083d0440d0803041400c418540c0c82c0c686419150311905100c81c02d402c8041da01e505103030b405da2108121000000400c58803031030620400c1030441c400d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 178745872 1250 178744622 178744651
    0xf02180315041b0b030103140c010c11060f0909041101080705041d040303021308101a06030106180305070b0a1205040b06011107080f0c012a0b04030512070314 70
    0x80c1a01c6511840a0000740281c0e0f00d907002000625034070040c81010741a16008503959507568a040c1304030000c21a102d419a0050100500e410340c4500007108895030001c008510100400c0f0411680d640000c200d844501230812032100300c1e0302d030303da52070307116a00540c0b071801840124800501284002010201048801c000902c45004074440b40c00c02c0c0c2071a40c0c21242c25544500c0c080c0e000b0b22a803d52841403241002c000260070900040600780003203010310600410341792904a6400e010107444483d400304080c80144941c0e0701c11443c50005404244800848d10361700c1c1c803054141019500051440140001c038038858035041443c0c02072106011804100f28030341503c44900c0140090700c0541003084c803481c54141c1000420480d00030f80781032001c0d96044141d03215029a5138203503013081408101d00c00104030290280c51a400d05018088808500c0d503d02550b58651f10710b0010400c40038400f041c0508442544003086513441043c0c1520005440020f0b400c110320410b90040c00e440c529443e4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 178747122 1250 178745872 178745893
    0x21608070e06010c050604110f0303040b0d0902031903030f1104050d021002010f060609030c0801140a0c141602090f0114010302030a06030203030c0d090f0f21060f021803 75
    0x191010484002421105594462800413540c3c4000104c1c09801840b6400600c024000d512014040c01a0110741f4074a0382440b50040c541c490180340f203601c00c443c00c28804041e00030b806401c00e01c404c2c2d2008081e01c180b55100001e248480c60007003800d800003551003c8903100c4510030f20421600d0030f01c2c4124103051918040001e500707154803620090086010710b9551141038000d4000140d480100c0e441803000c50748074400103080304128817054031042d0840000027040b000612400b0600800702516401c20768a02001002501840101742c3c20440b56403841c0705c40062403c00340010151020110b030b0549a140100824040b0150081c400c08041d1001080319080401c0d6070748401c4001c2c01c0260b100d40d2180c2c014801850103901c0a07405003c009598050b403034010507481d9a0080e10b80315002c04076126000400c80303401c14019101d00711085003003440b2428020004041d1006a8150500f0395038640e60f40c0303001d4034107075400340320050340102c1c140401e40c80344002c030f03250100f0940c01008026030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 178748372 1250 178747122 178747139
    0xa0b010203090f01030b0d0c060309170c07030b040804030b0703060914090d0309050304030606060305180601140915030d030c0311090d0b06010c050105090622020904080a0c0501060b0301060216 85
    0xa0f1000341e903041c103589403020700568031030540e9280f22680101c044560304c0c1c0d8a110140244c00c442d00708036564140e00ca6000f400d0f01c881000d5403091001c240041c48403d0942d6500900c0074805802501c2529042c040040019a1000c0003440342d4950742e000b2642514111b515400e0720522400c1090f065440d1080007858040055a4800b1255a02d8041243d0713440d03083c03803820b40c4103d41000d403a642c01c2c4600800d4094064001600842114043c0d000c0341c03035136440c515101c1a00f07000342d00f0885090071810110340f83c1280ea26402c6403001c0c901203400c0c4866000207142ca0002d9980304042525008520640d0b5010310400000030b44007024645003036103000002c0c1400c600d040300202081c0044000c41c007664400e0058081140d8031200800c26400c041607400c0d030343c100c1100c2c0e5025900c14405404000d0b0310401400c110284d0180c00e0b5242d50700d956070352100c2c075000040300e00100f1002c070442401140d8240200001814140050b079030300e5060a8000382021200b40d00c5829040c1001c04c100040b94 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 178749622 1250 178748372 178748389
    0x1603030306151e05090a050a0920130e04030e03010e0c040e01020901080610111603021903050a2003160e15030a0303020f04030c08010c03050601020105071b08090303030c030a0b01020309 82
    0x2406031402a0b685c425800020300745145a80046410021100300403070981110760011082c000c403100d40040c542000faa14201a2091040301d403581181c42000704800c142c168511608140b0034100308901d19500c83c042800c41e6610002d0b100c5a62100c0d144814a050600c01c6070312400c9a50029840c1480b0321001a1410340050200c80c084c92244800c0c401d9948900001121024448203407440d100d00040c0c12801d07007020f800107078400c484800172208900140f0b03005a003243e506c0000340034840100c2d00c4400d440c0c83d03c20100901d0818880010047d65414482080c1c505003448504c02140c2c00e1110307420324028010884104504040610744041d0f40003d1006030b01a49807a015a07540d61382054140c150140c1d910050110b5030f0000003150004040d00304c4012601c0390380c0c0810141d83c2e00f600490907140e0a98800380441d400c16130343c0840800000c8414819401048964508094403010a181d0707030048070400b9080700040188010704a89000e0594100d100340b00550070088180000341c040e1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 178750872 1250 178749622 178749677
    0x705010906080c040f0e0403020f0102031303050702030f060a0c110a0503070213060506040f03060e0705150c07031407030c120b0a3209071a0a080405160303030615 72
    0x200d000000100f00c40440c4046a01800341d8044040c039259484010080001e4144c400320003500501c640b001c02d8100510a6034802e40314100620035140407520151102c1e1700c46001030340c06001e01100e1031036044041280e14000c84900c080010702542c0140000d115034800b4600020b26000550b8001c00b0541c00003d5030b0260f40c04458a401c61001515044010100d503400950403050204001401c1c605084052044078040c00c01445804010034000c0d49840c9140039269101101e01c81304030303500080d9400341242c62222001c5400940c5c81c3d03203a5951603050f8540c1e40205500c000c0d003c1c410842d00c0c3c45441c00411054124a14101ea260f80e22038a800c40200030040141c0d07104550302c001c00214510881c0c82081c10700d03401d40e0f03403c1e960b5480c251010845501080d0302c1070402c001803040c881100c161000e1240d020381420017110035011940d000010b401a5401d00c034202030020084180041d0f0002144291000900300d0701d0018000060404c8002100c140080030300b02421040c081c81c00c0342d111 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 178752122 1250 178750872 178750877
    0x90f090b071107080a0b0403090b12070f020f0106030c030203070b160303020904180309030302011107080906031f0e1b0a0507060e030f0d060f1202010c0f111008060405090705010906 80
    0x812030742800051904a0356072240c1100c0c030810070380031700b0301504802950007580251345503881142c0703440e00c0c039840b442040c620101c50034003000011081031140880307100791800d82c030554281010300c020071403e4031400e41054032000e2041f041041140ba003002200000c0c0181e41c0e8003070410700b5100340805a940010030203001c0c542c000601d14420f589a0b4450b00d000707154004070024090a03410000c021662901040380550700c1e040d01c0ea01c3c071074889400e8034443d9920685007441c1848000c10701c5410b41018105c1c8480c00d00440780074214070b130100c200c03074040c0c5250001c44440d460040390440c2031405080c0d080302c00d00001c009030300d040b86c0d218048034542c1d40c0044012580c201900c410610f94868640345c01c41c01500172440306412131068000700121003181841e504066161200716143c0b1442410090115020113024030010303104000c01c1607071034050a221402d8404044c041003400082c0382d04c500c006001d500c208900c41c9494800c2a401841e02002000050706101c0060710b01042d0b40150401e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 178753372 1250 178752122 178752137
    0x839010206040618020409082a0c06130b030103030507060b0a140415030605070f0e12031b07050d120215150f0409080c1c0201020a0509060c030d0510090f090b07 71
    0xd40a80c40e840d421003076004c2c00c20407c8030b4407401c15240a0b04152449142044d640e0302c80c26002c450315001003140342d60480a88812008902000001da210340f003d8494902200c1c0c00060351400400618000d5000380c8070070fa07480710329140401c00c840032182010f11550040c0418448144405009804040c0030380300002c6070030341d030b0311100d00c0407503a6071004200710709120400a0700c0340d00c80030180d40701700152a80c0b0f080301412010000c0f209515110789203140d10a02c8850345811945401d4020050254182e400703143e02c1d4808510241e184030300036141180085c101101e01039040014003103a15414400d041030703082c158140403403203004256040c4106251420b54220f513580d6409054080d070b000b0703c030a54a02410580e01c2c0c680c40103001c00700080001482040807a8010b00032501c80001c0d990340c0d103190604980400c401038004a1441107144802d01c286800380c41144030341d50007200301c5085002281d103080380c1c42c0162200450b0b00d000180c10000c99100003100d554045030803101c207062421 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 178754622 1250 178753372 178753391
    0x6020c0319090f050405060612100f080115091802010503060303250201110a0b07031505100206090d02010c090504111c020304121106150a08390102060406 68
    0x91450080418040040d81071900040e1040d8214888004684401c030070410940e0f5282c0821044403011904242c00990400a20b03d4401083d5003003988441e201e07140c4100c050b106c0495000031546900038100f60f039500c11a8500d00c0302c0b0038103ea002851a04810301c1841c0303c00500e600600400d0304000e050210120114100d943e0600c191585850321810301c6240d1003009054241062268505901046c0780ca080842840c0340442e254441b140c0180d407035411500c0325071045009243c1c00b541040c0402c0444404502951544c1c40207107000400e9009000340d05050709000d0070b01071041803880a580c9003e241140a80c1c000010200f00d03201150000303002c00250800d82c445104030801e10f03083c042012940d0922034065030180d0300941c003c0d401d41015804043d01070b04e03130703403100c00d00800a5408107002445400c00a0300ca038800380005040310350300e2582c40d0b40e400d20f0001111880b8840703000e43c2d600c240001d42c80a06801540c0e041c0a5846401c80304100041d40f03403100508060620307901d0700c084a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 178755872 1250 178754622 178754647
    0x7060903030f0f02041517040b07020a170d0501240e061615050a060e0103060e0a1b050f0d0c05010f0c051218030609030a0c02030f06010b0a0801080601060207030602 73
    0x12039011440840602c0b5a1240c80c40350030007503209025007546d40341d504400303a0029124900001d010b241881044040e504d95403142900000f00038000c40851003100202000201c0d40c0f0210202b1041041150b40c88a00b041440c6054440503000f44481c450400026403103101e800300d410b860141141440e000790342d050404551284950014420700121001500041115003c00b0204105250b0f6082003191078002200042d41e400d481102020301442d001840401c0b400c0d4814041e01d1500c00032650200c000766038400e695080326520031004c1c81d80071020440d50401c10391082820070120b81c05071034030445e90740302c00e021011405040d041101c2055100e61090088809462035500802242c011301402c1d80d81100c40c0d40710134200c41c80150181a10121424001159801050001c01071030601d07040400445208071084000d90740f40c400c03031003010102e480c14800140a480d4029119940302c0a5607070141c8a2041a40690300c03da10001c010080c0701d0713002c5556015698042c1003d81e40b0700010005 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 178757122 1250 178755872 178755881
    0x2010b030304030311070f050307030b0a0209121c020606061902191101030609140105060307140d1d070f06080703020f0a08270c090a060308030415060f030201050706090303 76
    0x16a030188000180403003815080791a6001da05c4040046801c2c2a403100c0b4181748000a0303109040d05640500414000281080d1440351b010580e04001801d00810400240d042c15602018003039030340000e060652500039001e90b8103074101d4240001d100724104600862140d00c03c40d040e605006c0320500b05000464805d01060358040c100051140a001850800007481c08146454034003003860907000084030781c01c0340581c5944110100070b1071400d0b1710704002d0154560004058008000c1112506504403400e40003400046000650000d0491980e8902e81c40c049103126800800741e100c55410050b21030000484402e90f542481d24030500d4444079400d402a0107954070111055102090200103564440c9400b4490f04001c84042001e10511078032107007503107910641e92820f41003141d018481c1c0c20703d40d420b640c000c100400c0008181d43e603500c401229800589080303641c00b4000380384040b070b40014090180a0702c038500540c490030f0314550003c1c1c1a0722449100509180c0c488095405050003a1301 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 178758372 1250 178757122 178757141
    0x9030807020609180a0c0906021b010e0303070503090307050607170a0c0c090912031b0503040c0f1d0a02030c0306010c02041506090609090204050a061b080a2a120507030201 76
    0x1940060a00c016010500c40d001701e81e911803035441c0140040b0505d01c03a8074848116920354000d0031211003103450f620406620010918180300b103203a01c085854900300000c161240c0558003542d01c40b541102010b0a1030303000e600c0184908801e01040c07001c10300c80d002c850034a0030019015590352098400544411001c0c0b44040d00d250012040084d120000350010030049100b00818044441100c034154216036090500c0001000014182c1e114940034600540d0420701440403503403c41d940e10b905070700ba28440d42118400c01503e5100810b084101070b241500040b8055055042d1f16003584c00c0b04403404010300040c10031070081420350954446a11900b0080400c40440c00341640341c0e00e0282001d0303002d11403403000a181d5400040d41358502e00c295000d48400600440f0250324000b41190710341070b2681034000345c10040c8400f0340051002e00c010600010f0f41e441300d265400c003a1070303d0204401e040718200201c601180c800f02c0055001107089042d40740c0c0f4100240c0300c86403070a089005042114 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 178759622 1250 178758372 178758379
    0x30c01060b0a050f0a260105011b030905042a0f0206010f0501052b0c03050105010e03010203090a1202032203020f030c03100510050a1d06030f03031b09060304030c060606030c09030807020609 84
    0x107000b1031b150350341c2201c240e050300c41c02e0300c0e2041401c428080944841c00008809400989074030820302880c80c140c2c01c4000055048130344c81e940700840011041190742524413140110b201070350f0401c1c1c4030380c0500c0540d00410000940178400392601d00081c0081c813424550301c0380d00044002121124141100ca102550301c0058100300700c0b030035414040c00030142801000d0200d00c10079000c85036803605000302ca03c603420303a0015000e084510b5640180344030004501d801503001c103000c062801401002005214030012510b100307601e142d0b0052003158400d40c00c0c554000d4100e441c00c0301031503c0c005038181c0300c14002040050503030740301c3d8040c031658211904041d5020b003091500051a59003c00455484208500300f00380d42e03140e03582055510032210740c0c0940350360020310001e0a08140d0714420383e10f19142c10300c8203150010745000070b03141d50f008450880c0420300695060701440313018810700d0098080d03410304100400b84040043c000044a10000f000e4001c0010350320115201c10090720383c4402d010b07 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 178760872 1250 178759622 178759667
    0x17070911040b1b061014040c03023106080c1801050910030b1c020a1e0504061203030c08150d0c08010207030504170304031e0c0b0a02030c01060b0a050f0a 68
    0x500400102010303070036941d5680d109040104000210664450084403140c5500360141b0340404148006041c4641c6000c05040c2c0c01e0040c20a401000024450026420b0a00c10303a902645a1200e55451094201000301300c1100d003000304001202d4221805800d80c400b600c0700800100c00101c90a2040c8480940c108488079040c2c3d80f0244c06170410018040d00b11a07200702c10304114440102c086186201940c0040d24840400c481c1c02c0c1e001c4050340c1500d1007201c000040d5142c1d000320b820350710720b544828503141c03111403600c0034581d2501c00d0070842e05051030003c0321424424280c44c3c0d0510f104281d00d2040091035141410003020300c81c071000810034000250341711034540c20050b045070001d00c910302e640000d40401c0c01d012500442210203503948941002c40d092204c0300d94041b81003820b2400c1310070707501140c00032511241a0000d4051040703154025503450038140c1d0543d0070f4540e030740d001d0f07000038009200c040c22503500a029110081ca50524854031150304080c202c4103015044850440c2240310b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 178762122 1250 178760872 178760887
    0x30b0316170601120507060c080d050f0a050610090b090112050109020306011202030f0a020c0109051e010e0a05060403030e030d051005040b010f080c030c070218040c17070911040b 79
    0x14184a91600e50301d090740c0c0a6130b41c1d8541c1c407048042c001402481c1c0d400c4220103210b03041c000d000700c6d01210300414049003440c05020b0074000310b030410f6859010b403a0000c1c0800c84880b24a0103600e42c0450b040c0c59804c0510b421200190181ca407038054910300b400040b602d8181644985c1449036070746100501032150b03503560302d1413800a6200f907800e240019040300f50000303078800700c2c02140c1c001c0c161099540c0d826070380c150040e4001c0d0480c40c2906115520351040c2400700c3ca04103c08103001400d03138151054511000c0c121400c44012422402c016001008402c003c0f50011031450760143d05800c02141010702ca0107035070700310710400c030545554a25050034040559503442184050750b0040d0380c101f001c0c40346040191000039520010400040b5058000340c8612a03810146800c00340c52014503003080465030000d44000721a80c0b02912040b07021041100340842416008014041240820081841e00c2040c41e100d02c454020484041c1e101c2007030420400710042124024020340c070703043c1d80304d02d107 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 178763372 1250 178762122 178762139
    0x15091002070c0302010908060702030306042c0d030e0c0108040204090201090302100807080106050301180c1b11130203131101180603020a110303090a0605040f020d0c090c0c080901030b0316 83
    0x702ea000507400500c1258010440d05000102c0f0390092659400440c210383c2d5020400011b400790503821050b141d0718402c5050100c08a9140e24801000903014042c110029400181110305401c58901a607004032603401c2d5136604840783d95080fa1b0160b9021650039614001030f69400c00aa1000f500201d4101440c00843c2d400003805018151542d00c0d012641da9840e4100c84600080c011101c1034407041c910900c1124880c1c2c80500c0b83c12080c00c0800c24000d0049031203c0d40210940306860846d2100c0c600104c9240413820401a80004581182142401c4014a000000f142c1c8002d020300c04210301100d503a80225114a035001c00308088548080c0c880744018040e400580d041c8011032000b0310304421802c800700c1507910a802c0d0800074018807a030f684440d4090640070700150f81c80201c82008401580300d40501e02400380c00b0381c071030030b0116140158400884803003036042020001c0c089803440014000008607801c0c0b41091a020600e0101040003c1c10001684850350200040c000c00041011 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 178764622 1250 178763372 178763393
    0x120209061603110a03080105090a060803030907031a07090519031e0209061206060d17030403050a09080303060904241b0906140403240e0601090c050c1509100207 71
    0x40c07280e41c60800000d03c21140035a9010071000c01030119221200601142c106024013680c0800e03044004141c10350b0303504c4030f6821030780183c5288041c1c2c1c008203c18014041855040c98140a02c901c1a58061401c20340090080c4141e019007440b40c4110000c5604120314200303040055608541020086650701c4c1420340131910080e012400307000381d880018405e152100d00ba6981c170306030b01c0261140303545a40401c001c40c603007200c040b1010060f039207115210007851409540700f20302c41d4a44660b10344030600c000e0320302113566200c112103903c20420001191501e0b600250001e0b800003000c0f01900ca090382c3c44803030310300c0c0c206880565032610010030144c0315441c0e4001907200c3d245e112500c0e241d41300c480c00c40785034a02c200050a14001003104000148440788150346100c2001e00c0404e10848129542c41600d40054100780c1c540c0c00000180f00c0b41d0b40c18461f51300035500e40d0400d0340c0341065410001e91180c090b0300d007507108600781c1c2001800c00d02c2d0034480d0f160003014003681190f0711701c440d140029486 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 178765872 1250 178764622 178764667
    0x10504170703080f09070905010b04030224090d020a05191406070f0221030c03120604180209100b04080f060604050c0415050706060801020d05220312020906 69
    0x1032004114280401600c4421180600c1c0c069403141000c2d9500c1c8420820860064080d210341d00c1901000112003c00f44540c8e8080d00815142c0c55803240380d40100500c0e00c68055401c500811015541c5402c0c0121350122512100180c4169891a03801d00004012107029405160021201d43c40b80d0003200c00200040103584500032181c14904140c0240440c0d4020000700a010800ba107490602501c1c1a2400345462043e0000c0c00038030b48400480719096403c0342d5284111648041481003003040f1032031040d0390140d0292402c00003c0c0380302000c0d46e000011003c3c080d0094944401040640000281d190040c010701080c135a40d0310395a03885903503a208040c0d04044180100000700309c49191601425005140301c5038810f00309401c180041c50214862081d0506002e001c012000008030349000d55401882001c0005803034161000301c07a8181c45004200d80599180d942810b020b40d1524810300710201d80607d0160803401d5141e400310000c2c850301221583c00a004500b101017003a035100d982108 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 178767122 1250 178765872 178765883
    0xc03060c031d03041a03090f0d081e190519020c0304030c0509040309030212031c1b0c02012106031a010810060807050607060f050a060602210d0b010917010504 70
    0x8046420082c0c0c2c0c0300d02640c042da04185180e4492480d2854042000e907401c001810240c4044610803d0380d6403820a54281ca034010400c1241005400d10301c0b015800c0f0b51070382e502c205542500e030045d410320001c4000060f446240382e13a00d0100e014005a2410b00c0400090703410b00f155240400e4145550303e401c548802c517505414820040381381d060880516004580c1500c0f4082d0b000d055134200005c0a0642900340100d1000b400102c11521400e000b480c2d0180907000c0024802c21892070003810550a01c08010500c074541600d540140d074451180c03031482c00003640c80701240e80e05003160300c09000180c2c0050071402847c0c84581004a407211082d0480e203100d0200c401135840200703e241034601a00c40c04443c0e403c185820400c80c24808024001d0510483c2c000502e81c40409004085600540d03c40540903500e80b030a1021940402416034001a080171080381d0710f21300014100b040c0b14a4400c030035965201c95200295900594000000c0e06022140c0360080c0000b0b58039900030401290306462 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 178768372 1250 178767122 178767161
    0x30816020f03090609150d0902120a0210110708070306050f0105150f070c05090a06030224090d050a170d110a050a200d020f0607030204120f0c03060c03 67
    0x811400055128840d0110002070b605000b186010042c0540207110900c0e0069020304a420340c1b54485030081501110076800042c00305c0d81e50061094031219a122011154070503a4110050784c0d5080d04a00b128a59281c24014000c0414905061030b03171903031083c2140e10a43c01c01100f0020b654100d00d00c200383d11294404641e988004208407022084103400403a00d0802c03441d80610001001064401d00500f546c071605a036410210b940e0303203002c540303d4100c4c680d120400d004504c2e0810082e4210740ea141010310149001c1e8044402034440c2014542c45940d0020014040000901402c114a41c01c000c0c0e800030f846265070304a000b54007202580070180d00c0c0c8848420a0180c00058a03201c0c82180d8580781420403292003902d070428070000d0000031401c007041a11422600300518510a42107601078081c04030300d109207601d03120026240030140350040c801440342c46440950100300903008500c030640c09400e4203169000402175000070305420304282d50070b121a03030550000208060720600110 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 178769622 1250 178768372 178768411
    0x10b0a08031206091303031a0a080c09091b120109020411040911071211070b2d030411010507290403080f0f061306050a080c15040e06010c050a0c030308 67
    0x1070310500b10740d002041c0c1c3c05e580700c810100344030b580712049004100d200c0e0222140c8070800a001159107a004040c00c0c2e015288140c524100428403540050401006000d400400622600d10301b007400d05c075500400421302c40c0c0d05c44540c25040345120603009001000800d107a42c0481009506c2130040075483c60403d4201e12200b403000045542d040d41141a120418a201004450245081e882d03118030b071046060206d5842c03003020003000c01c4030941940000042e0700c3c24849560b40d0440c0299488688284104808a000160140b40440c424600070340d980940f0302d042c5901c401d10001070186c00901c9080c1d44514012442034901882c025102d4480a41d68143c09100b80b140c2112040052a2140007007045410100c00c0641409400840401c04a0b26036001c40e005001c1c5500c02c2d03001358400500030006082801c9000c0800c14008910343c0340c0b9007410482e00e4080c801401c880e04100038002d88105100003844038603c0103a01c9414444215981e08006040718410346654222412510901 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 178770872 1250 178769622 178769629
    0x3020d0f02030f0d05070b04030c050f010515040603120c080d09050c0103050c03150405060105040b03040b060a08030a0203070f03030209190305010507050a020c0f040e0d020a05010c030203040807060e010b0a08031206 95
    0x2d4401303501d1a52007501d821010360710595450f0000d80114140120300307450f540051028000d100484522800000b100e14020782801e100c10b01520301e00e030042e4608042440070600c1005004850406400e008155290174030301071503148a0340c0c0045110a14182c0c0c1002045404540a09150003d980c14080c5071100401074a00e1f00c0142c5a00190a0642c8a110300905080d00220b074451414101581829992001420642d0040f60115040f049000c100702d451314040c0c048402800d059801141483c1c1c2c3d41c94080c0d500d100f0000c020388084100c030259020940f00350102c0c0c41250016044407818542101c0c40003012000d030000306e609509010010380030394410f6007640c0c07034110340d64003c102e40c02e5440d0034000700350b000e401426001525110354010121040100c801242c01540c01000070740c07060300b8524215015074035140e08140c010414000030036000c0c02035841940d04844002346040b440c0c444140140100b0aa0304c1e00a2060200000c40d400f001c0050301c8401e20181d440865662040b040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 178772122 1250 178770872 178770883
    0x4020a02160824070c120516050102030a1107050d0305191103070e01110c12151311091b0d0912120f0e060f0a0b03011109120c030c061303020d0f02030f 67
    0x20200054160629902084040115540c96151b5080c014500790b60034600200e025202001941e190b0340010038440c804502c0d210301c1c2c0e101c10742c5000c01d509120703090b51051744615140c40c0c140109529140480c035040c4010340800c80d02c0b0b0013050100845000c0e000501b401360001c0764400c01207070000c2c280800a500808070501108021070203050054442d004000d41d480040400401e1842001e0fa212116960359048600070720708509800001005840c00b14003412084c3d007050b0042c441d250502c1030611020031601c030203c4007208495241c0d5008034401e070080080c8080a421404141d05600d9507030380081e000b8107811140a8140841c503800d0501400b40c4000300c0c101e500da0340c49107000400f0b0740c07441400360f50440e508001c08202200103400090030f4540d4400700c080c00a1380020200400c1c0b800d5001615131450180103801480c0056000a8031030002c0b40b0000d0046d1400681c83c0b0a0301c5e0039444120186500422611500742c2c2400c0c8031062442c00301c0101d020348240040d000864200050 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 178773372 1250 178772122 178772131
    0x30506060f060d091a010305010b0a08010c171e04140c03150403030506010c08030a0506100e010c020609040f2408160311040b12010b1c020a0504020a02160824 70
    0x5498001140302802c0101104502680c0c0e545c400002444030701c009a000324002c1d4084ea001046421150042040c0c03d25103a0041142c0ea2408407180d23485074202401082269260f02002c44030366034005589502c1581d8007448400381c030000108000c0110072006c950840440104035070480c18130748141aa039010004203101070100e03c000190009102e604102c0d405901031412200003003565031740d02007580082c1c1d03020b00900c1d2940100500f9081000751454440002d01c0c040650802000c006405401c0d07402019014560020704560300303444d19003042d03100600c440010000308240307041e000000c0501c014400c10008003840006084000098803130b10303c03207503441d0522644d444c0d5a83d50020001e01503285420980301d100344105941e034aa0306000d9060840d00110340c6840c090300b00039901c0b01107132803007000743d8003d0102d6000da15110315010603504207503401a070711382940c0c00c16898071900c49803400c00c03e9502d6001040401010940300d0402816000d480503a40b503400540802d243c0864 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 178774622 1250 178773372 178773379
    0x11070503030115031112090123040f03030b0310091a0c04061805090114131b050c010e1903080703060510120e060117060903090303070f0624030506060f 67
    0x700500110700c0800d03140e00c0b0310a0382d00300040d0214080c5074041160b04515100c0f00581500300400580310030a000ba1500c42c4840141d45080104524840c00e070390002900c007400c500034200070750f810140603034020800b0210040c121486950031040b680042c0442076401c590380801c03000700c2c0c1000d2100075a1035005031882c070301d60340c1401e0501004885001d4140e40d0004000e40c10f040c0024107841d10218240030700221000208001402c00502000b261094012200e452801d024000310b95100070f811029010141b41044d0780783c0001c15444d01600301c0344c4003140c00d401a0481c100301d50701140407036140d4030300c20340701c90340c05950b01a4160102c039010b1140c0d81d040165206c20b9900707180300d4400100c068000081c0080c2004503d0360491900409800c1051401c880024841c117101081010645c03108a24004610b0302c8e000c1d0000c243c40b03002c2d18000402100080d0404001c2010a42250441d46150048101c0640c1c5210140001f00aa4030081e00c0030300411020a5044c20a041250034024014 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 178775872 1250 178774622 178774627
    0x151b08030414072418080304090c0c050609030406020d0c0203190614160e0f0a030209090708030d051012170309030c1006050306010609060c060213050306160311070503 74
    0x1e848900840d018100c2c03000c282e0081000100b00401e80014410498280003c00580d502480d18083c01c05045081403611402d0522410405603c0000864042c0c0d5202840451307007090092094440c2e0f4444031006103640074290030042c004074000060004c44400d40c0c22035240180a41c0c003500e01d044013102c081e4040d00030342e075510504503c00c0400f1860501c21440014224508002c1070348206080da41104c000100b01601c146480d030059004020890403180c0300444d02042000850106035840007d00801010001507400001445540e0041114005132a034038041981042e009001c2150144c0a07446032400109078013980ca04d1428606070301c00803514890000071000c00035600010b06601851000b00003081569405118942d029411040c012030301c40e083c02c2c205802e02605800480800000e140c04201c425400510390442e107401c00c2d0010ba98a8408002207071000303c9410103900b62180005005801c403400e140d0365100b41e0320f658100201a08042c84a80324440e003c400352a96105 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 178776978 1106 178775872 178775881
    0x30307020a11030f06060d0201020703080409020405011206050102030a0e1c1103010509010c0503150604030c0b0705060f06010c150b0315011a2b0b0a151b0803 70
    0x2280504000200d2091032561400006c0066125400400b000025a4000c2c0424006190441d8005580c0c03500da1401c18040d50080c8141400164008103585407422940f00342c00a0b114168091840c0c440142002c46103140f1045003140c2c402850958078101d100c81161603101d040c460302c41d24030000c1d41c850070103085900c001c4c44e000c0181d0514803003d010540c0003007185d074000c0141c0d0302c0c1c840014000010401c0c40c000d9400003017032800e41c40d0300401c1041e00c96002e0100240704100302c4440b6034549600804954060b01c240303020504070004000080e1503427035540310300107240b040000c0d4907484400081c5031001c186103d05040000380c0051121816a000000e401d4400d02c040c545440403011035100101e0010b2400b1000091000481c0f130440c100c0d4010160000c40103103801c150a44030900b0020000407131000102244a0304000710107800d02c40340ca5070345160810003440c1190303a0b = true := by decide +kernel

theorem cover : BRFrame.Cov 178597122 178776978 := by
  have h0 := BRFrame.cov_init 178597122
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178597122 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 178597122 ≤ n) (h2 : n < 178776978) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
