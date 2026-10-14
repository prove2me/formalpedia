-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1640
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:00:32.644998+00:00
-- url     : https://prove2.me/submissions/dc8be436-d7d8-4899-9985-2e55ba1f1eae

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 294784172 ≤ n < 294964028 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 294785422 1250 294784172 294784201
    0x3020d050f0d0603050601170f0a020607060e0d120501150203030105152b0615021f1b11070b070f1113060b0901121503020f1302040b030f0106030213030201120e06 72
    0x15100c3c036003403071606c124940c41c035689c1007200e010440c150070290401d4014280100034141c001e210351404119010b608034038a280c45090f288a800040c2200300c401000e007400e00c40e490161031903d2030035006100324080a9038a22045c803996015003070402c95060104141d00a90382400b050b000d24800c0701d403000b0021000740441e11092858140f0b0030300d000405e56454003507544880c0d80394001d0803d082201220074507241d2101c0751404455140d9403800440d2801c0707030b2b2612400d907840d01d4446900c20196902490300ca25500f00f1031460004103c071002103916080c0c0002c2c080c0d8807101d5040c102c42820081100486200442ca0010b410300b02d011404540806c0644840c1d8803e03650300c0c3d02110804400c900303035100c100540240402e107034000c1c4094148101285103a010140205441d00b10411036401241d0155000d151206004014000c1500c2601209401049945400d50070086c1b01803081d801d4a2079440002c0c140040c9448030000000036400440742035201038141e4850f0b01d8030a5602071400d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 294786672 1250 294785422 294785429
    0xf030311121b0c1c060506040b03010e03130f06020703021e0307120201020d170c0c0c0603180d090602102711010e0111031206010c1b1a030403020d050f0d0603050601 73
    0x103000c1e01c06007252909000454904c0c02140000c140d074200020f440c1c80c0010080a08907503085a1601071b00c5040d45c0382400358030300f4108031000940c0d4500301074040b18041c1c01c040c0c0090b0a080c11640040064076400120b100c01c0d203404690035403200c181000d51444d104007414a250301070095040008203c03203414071180c6694000c0c0c0a8840031b44c9030b0642262880d03002210703844004280d4000c108010072240c00760010034201c200301c42204c420100010f00340d4008450040403c034403207908180c041024000e0f1106841c0d83c0c100481344d203080c00b0000e501c443c0c0c0c11038148003140d03580e48004000425009070301d4101c0d02d0301c01b410304464801c1c00c03c80e901001c03941242d4003040220380c081300c265100e17003070501180c0740302c00185040c81c86086058103000c00180029040196050810010640000400507040c0022a0248102d0f2401802213030350075052100c0140d0303910610800000c0382c0c0101c0c81c84007012171441e2640d9942e00101e9100c001c0c0c00f60003018825185040e01c040700b00000001d145058 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 294787922 1250 294786672 294786727
    0xf0203120702071d190b13090b180a080a0507020409020d05100515010c12030902060309010b01031a10210c080603060108010b0109030809040b04050c091005040f03031112 75
    0x5441400ba5135012084040d14000760140400d480d83ea0300202650008020b400010b102c0c0040240310f44c00b0034240ca0300c404084d100040000e0611a0042150100d90000c4070418081d20342280180c4450401e80603031446a0188080003d15030308550301c95004c081e001d940204034182400007810b00c585c1c0c0701c10b9000c00d145c1c154903003030110b8146418a16199501e0105a4403103510080725610102028100048502030589071114400140d07543c0020358400c2507803000020701e0a41d0751000509698443c2d14034041c4682d410090111030700d900100c0e00e500b84080c1024100c0c06408502485030340c90b44890200e425240065010049602c045041d000d800b00318120380072a6261800e042c2210444041d032804071740320110810029000398050010020014000101e0082c0c0b00081802c1d1039084848030f00b11000012881154607080600c2c03d021102460150304290826413011201c4c0030703034000501402f002d207400c811701c05d03006c010355102c2c81280b00c40300da1200780c2c0da00d001d402c17103500110b0740e0312 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 294789172 1250 294787922 294787949
    0x30503040b0c07090624110703150219050d061401080105060702120607050d06050f09010e2d06040c0903080d0e0a02030304060e01020607030e100231050a080102040b04060f020312070207 82
    0x2805c5d21031407c00d102d160540e000750504500e540c0d640b032003902305c0d018010707401c917028000c40030460300102448003408255110740b903407111243c2090040b101140c0090030103440e0300703441d940681da010a0141c192402a6100b503940c2609000041c2021b24405040b60701c4e01ca01800c01c0b8059034486c0240c442d11a11000c24000541c5600400c0060b42d03105c04415086103402c4010007003603420403e220382240480f07591000300256400f20030014594102040c450001c0c40060049500b40380c810307200001920f00d40b50703900c58115a0f511100d445040540652030303480d107401e00e0f101e41d82403140e4000300b42d001301184c0d905e0703540d0342000d002c1d00c0c2d11401135800f50280c50009074803035000e8018a03000d58848000b42007135802c9807041c0c41c0207402c100b0402c480804c03500503110080075081940c00030b00c1c0d840080d1054441c6400100240701004cc0c000d6190359005001c20010303480c41c40181c5003079441c0390800f01c0c1c84015082007245540203176054180c00544990501900c1078000c43e60105840d60340c0350050 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 294790422 1250 294789172 294789239
    0x2100911100801081005041a01081513020d0b070504050a0906060314070503040b04110d05010b0301180f11180103031e0c030e090c0d0e07150801030503040b0c070906 73
    0x40c2c030741c0003d1040b0b030b03070603084124101100348103544059405849194a0029071b00b0b140c410480c018426042014583d004c40d0b08003414001920215500c803821685841c801d039010390229030800c4035140300034800b005032408111024004d10a88001d09000744c00081456a9110803a001c0e1400b4803802d03010900c1c0109140d5203202c1c1c81501c500c50300b01d40c0c44551960300c507a070311820420402001540c0340031718291061036542c0c03078404100c41140150008918612814105400c40d410700700600171400303a1204030400941b200300c40c540c030241c0101452074440c2024012814003341c0e48100541100303103400100806030410071031032804170510030302d0b541c1d03480c2000b054510150340780c4081c000c034494401e20300b22498051040ca602c442c0f4100c0d00b07814a96800c1078042582d8021f0034030080d94110354010711100708a035445680c8000245004070030303549191155511381c411409101d0110741c0020b80912090020412000200302458041280c1d82e42d44608a81103240c500311940c05a43c1d008080323 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 294791672 1250 294790422 294790427
    0x714030307020105041203120203071e08270a0f0506010e06010c081804090b0a0905060f0106081b12070801031a0f07050702030a1b0f090513030f0210091110 69
    0x903a407a9074180c540510f40750501c4900d5001c200c40e035400710208100800791100048017400554020101c940783c4403da203c03072829442c03154201c0780e0440b04010802080000000110003455480b0320300c5100344410785128000b1500742110b1140c00342100c4204100c800030420000780d440c1c100e50050301154140c3d01d070100115203490a2a0b005024000e050010000d0743c640304c881d24188003801440010a0895940c9180505000702c81d1480496502c110b035a050000030f2005d182e10440d03100c0000e400e981020000707022940082e203e00c01c04201c03014500c801091715411a42070882d0035510b05064904040010a645024001100e801000d802010b00c00c60f08014081c0c0146076215004846a8400e0411142c9401622069a0511503c4058004144680000380840407001720750025142400130460710f201c8550300071054203141400300442d80b400642d0034110743d50300d481c0003164252000c5080b86412000ca0361000520310380098002003294800c1c04d542d11020640d504c1c8040350405805 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 294792922 1250 294791672 294791677
    0x619180813060323130f06020408070618030b1003050304031101030609020903060c09130e030d05130f12050c010203070e0111070305101805030f070b15030a0f03050d020c07140303 79
    0x100e003800044181580c071054810302c0713040e0f486442202000c00054040d02c0b808400c01459000b6a2403540c00a02404043c01c00e0042c6009405141095980c00104089003400740c02c907031001500d002001000f1500c050440b950040c002c0d9002000c41c0e46641d16414681364078a04541c409020078945500000e4000540c0261847c1c3c000042c0900566a0f90595064156001d100f500303901c5a02810070806000c0c1a00c42c801c0c160b02000011038503a01c01503546012110b001d00300e041000440300c80c0c9000a120311280e00744055000038001800c0918100035070b081c0c021501d4402ca1035001200704052250710071000001c407080ad0b81c3d200500f0008172901d03500c8020700e000c080c19135003026004000b815007580080501024011904854065640702c540c1140c201d01d03003640898100042603020b11400e00d00f03c3d500410210300e2409540030300c80000b03540750344003140140941c4d1850030a20506004038103a406400f400141550b4071003041c09641c0c0c9403086402241c41781c2d0306a01002d08142000401e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 294794172 1250 294792922 294792941
    0x13020a02150618070203040503070e150906030a11040f02190e15040b0c03041e0f09050705070615270e030c0309120309040212090c030a020306191808130603 69
    0x1c00c80b03000c20300f0410902420401802242548005c00c0002590788003040b441c00100031490303404295003081c2c40c0b5000580c0302810302ca445503111906026030b41d41d020441412403980f00d2b04480d0300c4e0000360003007405080c42803a070090b41071003c00e0005c1e0b50700d40c0f20700c00e48019a06a07285400f210030b01040203101c40f4002c996400320403080c0010f01402511000030044821113008817810075540f4a002030311200c0c1c060f68045200941182004441003844105018081c114414072031480d201d240200940502031002e06201d072540402000810502d120b440a0120070303190240401c02c904010700000005030b0342100c2580780102e0000c1e1680f02000303482680c6011400345151803544420840340c003968803032544580c00204010007060382d03948020881144402d071105640e00e4082c00131030422030f000e613400b4002d40080144a00595000c11195480500c40001c1c00d07204005940c1d01d40244081044181d03000c00c0c95601c0c0040c0845035010f0460070711444014144142c0728041101960076405 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 294795422 1250 294794172 294794179
    0x904080703111c0c0c050312130906060e0d2306150409020a0302010c210e01110309030a03030e100501260d05030a0c0e060a090302010e030a0209040209130213020a021506 75
    0x295200c418601c5180628204e9024000c540341c00d03030b200c00c0020b01340010a068100d02d10400540170b485410040001402465941810410b542c81c00c880a04608150303001244280c0311000b20000300070140c0140a9290780200c03481c12080416080c05550f2401070315005900c41401a42482d0391506024002c00325601901050500d80785034010b5130f201030103840c201c401c1d52050b00280c3c020555007004000540c650750300c480341050458009095914084468000c90b0406c00031141e8a440001d43d01805950515000604a01c3d0700c01441c2003403140343d050200c0d01c1c01c05000141a01c0c0380c2e07080754440544183c072110440c2100c0112642e03400d840300c0400104400b480000c2c0d14841ca5800002030050b14140590030007080c2002609941c040703002000410310051040c025940c1c0103101c0c2650400540061004128030303000030340107c40050000780304900031000500c41c0d4031080541a412a40681400d40011039884614060340001407441c0c0144a001d049005545121081d030740202001f6 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 294796672 1250 294795422 294795463
    0x6060a1409091e0601030c060f0e120c06040602031e070f0312061d070f02010b0d11130501030803182a041103091f05041a07090302090408070311 64
    0x1818010110301c0201401000e0081c4209820007406140000305042c001101502c076941c10341c50710800f07d02c283e802c58002c1203510000d4110054100c0078a491a1208541c0c41d441c00002e600c1c1e942c07400c031240318840d8100394003040005030345400001800d00e4070b0603500e14204080e58008806040c1c080e03080054a050700c3c018200020034029455002031781f02c0d00b0008070700b1507105e0341c941d8942c50003504940303003100210041000c42035110b4444040f44c443c500c0280980000280050f51060b00190040c2030070307540a03d400c507032b503a803c825000d12000d0240140300b990f1796818540c4030380c0c00845d1455484010345000c500c0030100802c0010700d504081c120014400c2c40201c0610218a52402403034200d40e848030007203402003000001c2c603c5030010ba401000d642001100315920700c42001400c4440034242001d0100003400744448503081001104a0209540c171648110707075800b015030029400405200a01050082134001050070500a80300e84a00b90115180d1954803030a42c00c0800221000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 294797922 1250 294796672 294796709
    0x510060e091b091509040f111915021509030702120705031b040b030a051b04090803010519120c0e0708041505060a0305100204090b01080903041e120b0906060a 70
    0x10780700f880d4014444040c5104284810404180e0201c0c0603a01903514419083c0c11b0b000704900c2076403e86042009580551546403501540c10301181e07280100e14541c5109c015601c5500d1003004100909546003088010030705195521a45a901050b07060f800707440342c58105000c40200280300401c40320007600404807502d803000a8072502489060580d800754461201d5000c541d07041017040c0806006038041c0c4440e0000b288600b400207a90640c0c0790050382032100040c003113600501a80d0448000b660400030070715a0000c140e0761b9260360342000c0c5041c802d00c0d20810030710541a052030142c80701904440c2050b01c5501d425036503124202d40083c0482c0c201c2c074200c00101156003140d900a80c000d000102400e480e6510181000d2600d03400741c40059010508201d802c1030360103401211030083c00d00c0c0c807250508810968030f0780f199001c0c554401c118052018a9404148461030007089002c0c0d1038840d040740c41c80d06615121003902d130440c0b24071900c4003284951408203020b0044424080c00344906150 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 294799172 1250 294797922 294797929
    0x140a05070309090c0e0a14090a1802031c0906050c0607030b040b10170606040b07060b0d0b040b0a0b0901050604031e0c03080703030c05030c030f04050a0510060e091b 73
    0x8403404604009040d880040c5658441c000d10903410001d4540042c030030031200901c0a10400380e8014040d0507494503417401980c441d140410b030008102900400e002042460000160120400c000e4142c8604000d60f0b0000d881c4090741c18107a041d990350f00071416500c0c14212220b000303a0704400900c1d00b15001092055000b903001c0000301101800108040100c00000703402221081e04c2c04020400a40e00d0402c51400d41c0801e540c000d10465040d4101400d000a5042500420100801a50380c90030208116603920021140b40c1e80d001130042c040d46080e10b80151403d80654080040342d0030a1084406803a1860155050b900064002400c09103192110b00c3c04212200010110a04480c9654082221000707614003650242d92083d980d2401da03d0020100d4844038000800c02405000340008406031504481d0007801160281c1001e8403642896420001e085400605921070b61841404440351074008804580c1c8d525620312881d901c2c044102c0e1a000082a440b5505c4140d1090140718903 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 294800422 1250 294799172 294799177
    0xf15010f0b0313080a050405030f07030309030201050f070605010b1b01140a0c1b140601090606090b1b1c02011107080403030810090f0519090b040204051305030301090506030d140a05 80
    0xd0304012240d031042c1941c5138260070794007484551002030b900103000e0042d03042c10412420304111b4200100720847c07650302e00805480244c08000e041150004420a6400300300f415a0010303034100508000550b502e0002c0c400540c46520180007039201c0c44002407003100c042c4501c2c4580354010200c081c103030392500441d0b4002c1019a444405000e0706000c21203103035042c1201010f43c6486248403006091b42d0281403460000c05178001d44205081c4442400410391290745401195108504240c4a50114401d004015843c50f000f20312032040000320044426400450a82e0b5505500200300003444007100c0941f078070501e040a80318031000c10007040040c6c4628030141e4000b2102d00c1d28042d40ea00d030300620050b209003004002d042915002404900d00c6000303136104030315643d41b40401204d00b417079640b21444d40e0001c0020f807080d6607070400100a05041c843e20250a5802001c2d0703542c960710342113080020b0405541440c001d115140b5180c403200e00907400c1c00442e1050f540344a0810303681c04412203079907 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 294801672 1250 294800422 294800431
    0x150c030807170103110405180c010f050409020d05190b031e070b04120b0c07020f0d02032d070509060603180a0204020a050c161508060a080706020f15010f0b03 70
    0x460103603200c0c1d00c0b0303402250010740079520400030762141042542c100010b0b03e2000d131420021461204180d41624000141d40d85142400e080c00304010100c2e0348243c03041d0040350b203d040710a00000d607144e04d0385010341c0101e12034506801d8002440400c8217100084850401d045600740e0300c21000403104000d00e00810101d80d610030103c811030380c2c40700c004112a0f00150300051864240502400811000f07822a9078051518000c41c0c0c106a03440e000034215941424102c4c1c02402c035159404207644007400030031840525074048a20080d20407480796801d803104070412046008807140490607151a00f080b900030b104c028110fa08585500c0e00c3d00e050110458442e90f1f551050036441001615a80082c1440d000710f0b0304c0d8282c880162102c0d07181000c0c0b5203a18154106801c090501108181a440d60031041c1c0510b4420165615440030440f01641608004040c2c40b4002002840950005620f180d03c850b480c156003443c190a00b4000042d102801032050110922000303101440b007207009981e12 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 294802922 1250 294801672 294801677
    0x10030f0c030503040806090c041a0904050f07060e03010f020a08061005280806030703020901060f03111201081b06090d030e1003060807050916030902010c1205070309150c030807 78
    0x9441e52030380d4007880c640c8582d00c00c80443e00031000b0080d00e1541031100102c48081900d085c048010303409400b502042c4102c8400e44540d1a040c0840c051090400c113600c42d01341d0210460740b02036103940000e81034002c4144498801c0d802c0c050b006203203810600945524020130b0302c8400c15030b03d410007003201c6038003c3c45200342000000d0000700c0f4039500c3e40e0340b081500e000a6056004003903101d90000c002c01e0005001074081d178071400341000140c484240080c11500c2c03c2c80d00c0c1e8154501028100e0141c000003080a910740004101c401c000c540540405040b54041c0040340d00341c40601280320f080c0701000401c2e96120b4030a1100205900342040764660321482464515940302c01000094100c0d03580c91000710000c2e958800900902c0790800c4401c0c040c0200701c1c0c01104074941508549881608020f46204040e01d44407489d007164003c120b4040015400001d0411640034400001e01c079402c540350680006000d94000541c00d0348030401e400f042d113040c0e51303200c9801070651004d9664400c090501d904 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 294804172 1250 294802922 294802943
    0x8010c1718030d050f0610030e10020c0a020d120e1c03050a030609020c0601080705040e0a12090503030d2408060a050411040f060509070201141315061214010510030f 73
    0x318850f0a210326441400c0030300401e401030400c041880807910041381e4501c1414940344d88510448000a03840b001c40d8507085001d40d8817a07840942504142c0099002174001081150741c1c000c102c250700b8909001da40f10781d00c1c42060000b080c2048514032000741458014040214504080f034402e400900d11040c143c2000b1910a40d180b0084040b0382c8541e100000340e0b00420010700c100c10060009034010701086400303200c082505c0814a0311b6104018004000c0d000a030b4000403803038050080200102002400d503034503104a904040040c04103d10550714042030f4000741d20840e002c0e0390707503402610b0610009041c16a12680b09000400010f4402d4a4001e0103240310318072a9168003880554800c84000851841e150200f070114000000c0c1050065904001424811110301400281e002118060b008016510703410410320005225900c0401c0d07604080c808030755006603809902e809031103041c0000c3c10950042c007140c2221810794002090f4680e054040020420804072464864082d00300040d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 294805422 1250 294804172 294804187
    0x9020d0314130602010b01020f0c0a170c060703020d08010b030c03010308030a0e0d0504030507050a0b0901050304110301051528060e120f0606011409012016030c08010c171803 77
    0x410703200b00c1d911000c0140e45900903110340c2e580c14081c004000030410010404000c070180041e0700b89d100d900031002d000d0045415401c014408100003800140040c04c0c25aa4001c107044c000d490f2202070440d1f001040342e503800000e00c140c001044070f1003601d81200607811079080d540d4920103584064503402445881b00030002c03030030905000c0c40c4024221030319401c0c0d549141d45040360030103036541d1200d4843c80100340c04102c9000010120b82561500340780c02e95880d0365a107001074900c850152081d41540c42c040420010300e0304000c00c1c0a81060441d509a041c46180b00d680c140000030926030013800c40280c0080014030f0041c008590b81a4005004c0d4604188502c4414030381a80e4a158000e15882401401300658100c50360680d450518410f451a0426200011741420300041c01795012007600e001d20325203500103000103401e558008500740d00c4942e0707a040c051100c48941c050100030b54602131240032907600a03003003850720b0980e51668500555580d18403e8640b4812078440c11103020820200 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 294806672 1250 294805422 294805447
    0x60d0b0901020a09050d08070b06210703060f0509101d12030f010617060904020a05090f07030f091e0507150f1e050919050312030a0c0309020d0314 65
    0x124490940d8000068844010310001844203415178400e82c0150955407010010486610485034166040f06041c0aa900c404010408601c140c003070001d450207003000d011501030004074840d006c882c02b4101c188030348401884030604441081e981c40c402030b808416808080c20307068000c05a075a07203075442c10f60f8402a1404150806030400d1400c58244400001c2000204080003110b01400340d500d4500c01c0d1120840d41c2d20102000580554840c1e400103002030119524084003c01420000c0c0003a0103d08041034050740c05c45080c1c1d803403400710341460505401ca6690b407046600c80744e040900c0882039601c1011003810705400380c40035a002d0241c1c0902284a080b40f03a032500156110381d6441c00c03080012440200549026001040300260042c281d046044d8010261218140103c070f198845810301400b5945444040c0c1c01690140941c280a0310b408860308081c5102d0085001e0074081c074a484d41d4120304443d0803030f20095000c3c0f200e031100780c046071095a031014080e114900641ca800d0b0852881c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 294807922 1250 294806672 294806693
    0xb01050c1002070c080607051e0d09141b0607111804050a1401060e010b0d15320306160309020301050c091806090a020a140703050c06100305060f060d 66
    0x1d8807109a00080d5403410003100c1c0303088400500100f00070381603605004400401520034003115110400001c00b01a40d00c6d03d201c811100030307156680c401c2005040e80d140811030010220700c07810b8140a109040456070001940c04c0b48180801003945140c4110f566400303c54806000499421806c141c80c94400d0411038501c15010f68000c0c001030003003202d0343c0b0300b00d200700d03121192a520a0f4105141004801d100c031080c81c0c15150f5440d109926407100f02c0b400c074020000256401c2c4400a21030b00045c4c039002022004031128100440e024101d101c0d100510010302c2d640d8a0550140c0c030203c00100b01c5100054240010819841c000c0744002d11500000e0079141c094034101d20b040400281e18800d407074905484e0392142400307408202c580c03621740300182800b08010260008a81c0000b4000c031054481c0c2040304030300020300406510381c6000d080080594000c800541414400e5501007180307140900303111412a5800001000140d58418801108a101a0645400228101445000540e000036 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 294809172 1250 294807922 294807943
    0x10608210d02030a020408120906070f0f05010614010905060c1005042a15081512010603061803170411040f06080109030305070801050d020120030f030a0b01140a120b01050c 76
    0x20051b89880c2084078681c01c080302c0070390700c826424042105e60481d44a01040c2d0710443d4010b01d02821010300790800980760988000f000b0710075482d01c803001c9002c419212000071040020b98a00791059100c405003d014404c040400300a81c1c4001032505440c5440d41282c0da0141c410b034a4440381594401000c000b06640f000300c10f030f60001c69542400742280308208800c00e8440351030081c09904043c0040f0f016054041030080c002ca2645001101e412400d4001c1c0c001117070b00090401140146000c6030007080c1f400c0c0c104900203240850b404a0851020035010300a40c1c2141240070a000d00408200040105403100a030444e110100051000d4083c4101c207183c074025100851189040c0c14000d00d0680d05030081845038030074840000240c2d82c0130030640c140310b00c2c050180300e0041000382c1e0940707580544894202d10796030000030843c0e81c1e952900100315000007a00c401c1010b507007494400380140030b890700d410b00068400c03d1a072400c06007608000f507540f0b01030400c14a0180c1d10b88546007059040724 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 294810422 1250 294809172 294809191
    0x12110703060b01120b0d12110a030206040209060114040909060f060608041b060210020c1009030f090f0b03130f2012070302010c080d1512060c02010608210d0203 71
    0x18a50b00296000484150036620a40d0204980b240749030002e104d20058903400ba1079a13600c0b904890185001c1ca8080f402800303000708481a410407881e0003503954608503400c0340517509600115015502450074a54210342078400c084c2024148810751004240d00305064521a4645001541200c650b20901020b054199244100e62916041000711448880b5442000300e503002c0080120320341c0402c1888144903945005070361412034058103441c0c03030030480403454a946080c03640703401c05801903244020740b00d503511580d1110340d64000032508100705e407090041240007040084c02c00c1510740340c4091040e00c500020907541d203ca86820701010b400c440541c041200c0c0d000c035030005152049a103150b80c28550000c05046065900082031030126110051044001141284090040383c01c402100181d07108036182c5150760324245401240c0d00d19040d20468a4814800700003072060142d04261500f290040c0803041000400301400c0e2402034a940c44040e041c0102d034242441800194040e0354500d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 294811672 1250 294810422 294810431
    0x3120c050306041a2206080304170d02060108060f06010c170307120204030507090e190303090309080c010e120114040f030f020d0909200a180b04121211070306 70
    0xc1e420b00045134203142a06241012503e086001ca594070f500c4014050100c07640c4071050070740c465041014000036084900c0c10b00001c200801c4807413000340e10005403070910b0210780c2d982c2c0419200381c0c0c850500303010351440b507045980012881d50000503a142c00907810314052869004a460300c1e070380820100c4908600c904004140084150701011b90104031500e28001c500d0036103169070f05a40c1c1c034018810722420944447c001e07000964280480d80c0301c15440075080ca841100c910f00280280f00c02c1d00124081800070201095000000606c1140303010181c480c42d050700002010844001003026160449648400711010b45e909030b5000c81b030041e44a506004049004c5143c050800c89030340c1a00d40465100441e100388540d40002400c0841d020300030b0014414408210040524404402071401c0180c0095112800b99102000e508112190400c0054141d140c110b0780d00c2d03601c590b128030070f011207001c2c1c000004226041441920640a802c0c546698181d01d40d83d00c1c2450501d510513079040c0e44c0c1c8c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 294812922 1250 294811672 294811681
    0xc18010e0315090c10080a0b0406150c021809060f180703080c0105010e1311041b08090c010813021905100f02123f01090204081207050d0c03120c0503 66
    0xc00c18440840c0c4d04071140310021050541c024106400102400078007526084000b0090316a0b0b0302c50001380c81c00105140c00303018020340c0a010580c3c2101c040780076280f0103843c0100a0010500c5a00800802001e081e82da01ca80316245548003003d0700d0814002d1524000743c00c601c20402c001c20040d8401c400054032a88980291401c456050b803019107800c0e084010012115504000000510343c000141c0314554040004a00100a071040907c6581418a51580f100d5000603080d48a140f244c000c440d003130072600c4011510b92005840507290b4942c982c004900501d00201c3c03117903d10101ca500f504032190380e640014001881c803105500410900d100b001001070f414065401a2031100718980d1414a80001c1090024130b003d1101c82d910710120303229040100503007441d1403041a061907001855840d50000d5000f944203100300c0a40d031292041c24074006035070805648045800c2000740000210141c403e0b80c50301c402e03410480070001d6440080307103414894882d08400086d99562240c80e03241c03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 294814172 1250 294812922 294812941
    0xf0f0503100501030f02010c08070b07080105100f0e01050c01140109020306030f0604170f0d061707062f0a05031804050c19032705030a0f080c18010e0315 68
    0x207820200c0700096081c40014008140040002c0c2d0038a5420318002023491403606255103d0301540c035004000c5104c040510000725442180d183c10303120222103440c1c090030642e806840707844010380c550004c41c15030130303042c491980540050200311140a001041c1083d0442000d940034000341c0240c00020b601106112450600304020400c180c0904c00400c103504150f10743c2c0070200303504001c00940e03d600040544400568500b5513089a5109505100003034a51021180000700c55069844511a040740019070134410030b0b680030703c0038255070a4258202c3c1d1a107000c0b45508a882c20583c64403564034a03400083c0b040000b01400300c00d1400e005921160a0100000c2e036801400c10203140505001c002074642c515105440912114200000c0e14003040c0040c403c82c00501c0e4018903551681005c590034440084001c0201c03c1040d0341d601000d48031080161482041620410009001448940c01401c020300621466410504140c0303074425644001034500001c40030302c50142e42c0c022091000160 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 294815422 1250 294814172 294814183
    0x604050a1e170d020702030a0b09010f2d0b030703030507020405060105031618080f0a0b0a0e07030303020306031912020105090f030703031e02040608070f1e030203040c0f0f0503 78
    0x8100703910051011880d01e0b141025407070860400d0300180e0024505064810300e50464210316800740c2a2003410032681050154090200e07aa41d92035403e01c7c004281c21090f07440348407846685030071006041a411144400c25042030803010814695440032410599030820100c001184a40c1e903503943c0350114810b100503108040c003e03a06220052003807201a40c01000c003644205800d281012040e04031006002d021140c07980b100c449170065442001014002182c101c0f40700780070b81d40e4107105844410450044414220250300c5a410072102400003911035001581c10110040850b1000454250342002180c00d10408450100d01000c8000101d6028003413240d001c031003a0b0140c102c4d0301c92304a1658407403003400d1000702051f0f41c601030841445034002d41780c100b00c8079080e011510355859400c00341c044d500c282d40703180100d0400b503030701e07041d00303101d0816941015010350000b280c02a00303d500368040d401c05401200c550076240d401166041141e01c4080003042e0201e010000149004141070402 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 294816672 1250 294815422 294815453
    0x71802090108060409050a080f0a030b03070302030303061201020d1d3a031811180112080a0507020d1b0914062b06060302011407320604050a 62
    0x11401448640d800341e800004141d40500c09440100b0788060324540b890400740342082c01040c1740d0010413a0030310381c40d82c04041c05841569840030032481786218100b59440d50540310003541503000b080024214142010000c5480301c00704005030802c003001061900b6940000414907003210040312151559104004150208800c00c811028500c95071024500300042100c002c1300300803480e00d4603450184650310404488000c400101c1098101d0309c0c0c104400d10303204625030310904401c0d85110070300b80005a0302e41284c2414001c88410040c4e41c0ea2001143c011101d00d50510100b4807816008d62910b02040c10300340c1c4200d5482c9282c1208280c681840d241c2c0e41c006003180c62401c0744041c030b1441030050303842c0c1081c81242c120780c85c2c803521417a6004c901802300300e02c3d1020701c010316183d0811420340c0260050b80e2003625114034041310a44810700074014114041c0440c9c100a10503035808620800d102070384010800030f28171880782550b21a19006003078a00701c400745d100422410034001c01d09900c6039030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 294817922 1250 294816672 294816719
    0x3180905071838220305120301080d0c02010e061c050c041a16140f0c0105092d0a030c0801061401050d020322200604060f080402120102030907 63
    0x2007181d90996100b040700d0b10143e12602e0400100005a00300500084d18140400c2c202c0041007450703191041d90a1000c0c5100c2150684035030900c1c0303802c8821903000d070307816203901100503c1d50880a0001302c580100c80754050f030501101d030b00400a1074407550001d00006100e801c0200c005c03075821140d642120340c000c0400031601001d11050058044d40134020488030b00b890100d5450f00040b046101c0d001d02d031500001d00c00f42d0668a0503845940104420301c45c03140880a0f51103500340303040151011712840300703100e40c0001c51140c5100400780c1003c0000e811a85043e50014946084001c40d41e181d0700341c2c2091741c01c0e41c071000041102d103a00340510000b074108440c12311010385400d00060310500514400342200da8000c0009500c51041e0310071034440746460780d50b4440a41060825108186800c03600728200c4507510f0343d110040c10150111402c0f190990307034801c12000d07035481c12540f064000e04100c0c0d004907a4102aa40e0600034000b0350700500354440500b110914180500c45a125800a034100b07 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 294819172 1250 294817922 294817949
    0x12010f050a0e1012050f0105090304030b0f040f0b07020109050c0a0332031308060604140105101106070e011e020309062203060b010909021204031809050718 69
    0x225120305107600c0403074050b07040e020459250710810700c00303894860f000006001c01c0a2950428040c00180802c0c541c1c030810001c100c2d61701e80100003900c80c410707408040d02b065000c40100d80160b0303035022042e074018018a02e269030510380f5078079089048010b852032001030391914004400e112050003030603c0d40e071b000c0380c400142030300c2c4d46d944420120601c0c4144010700c1c681501e805a008107564010203034440341d0140e075500c410904100d00540c1c01802400c8440c03159000140c6030703040905c0f40d061000c2c145803648056030700c4d000c100300c41501225410000c20130f0700309810240f10003c009080c000e02031030310307032002409044000400c6401e07902c40303026580d416401a07440c52500401140d04030107090350029610780360f4262904a08040d24400c0300907000a400c00402c0c44a140c0c401c28014809030703038546a1a64032400c40b0181c0c01600f819180500700b41c00880c00081c001c0075011500f5144035152a40140e0340c01c90301c000c41f0400c5070550081129540140040115804044054903400090342d1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 294820422 1250 294819172 294819179
    0x903180f05130c0207171b2d010504030204020d1b0f0c0314070203150714070c18060b03010306020a140a08040f02041113050a1401080a0f0f09060212010f 68
    0x3089207801e900005015507642c18041202c83c800e0150310061b0031800c0220302c4040609188584c3da120312400c2c1d40c03162081841020107890000c540042070950103000142e5003416205000c2d812030161800b03070601504200010042c2c07036500140c194000c0c4c1040c0061016004c402a03e1081071446944080107040b281030785900d50042aa02030132505803808440d46001d4008010341c511800ba0041e62510a2000214042881d4000745106840f01d03a04c0946030801808030b05a18010641c1c0240030075500d06003400489035802d414010200d01110200b5159620340032000258030a802c25110725400085200f0215003200442000704800340100c2c1c640110090300502d0b29101074001805030b110701d003900065542c1e80e003004008680e0008520b954403808034940d601b0182e644100e5003c0e518081c0000f031980c51180d000c10340818181c44034202c1d0360b184022503005003110340281c0d1340d07a40e644032031000030405803148bc5151403041c040140d07103130000403000c44c14030700590000c0d00d00445482c0c1072 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 294821672 1250 294820422 294820429
    0xa1508031e0f1b070306090b04050f060717060406030614010306140f011202010c0503031e010b03160f020703050102031306152304060302030d18060806090c0a050d0903180f05 77
    0x2500340d810041d00a040f00c6401020590401e00a54005800507082c4842d02c3c06203c0c103414401d00480c0304004680c1c0310300c615071007503841d03004c1141d111001c00d41401c00b0011243c204840141d0080b0002d10020707000782c0700d40d5068115403c60801100c1031880000500401429100b50305640180312950030907845e010000c44544176050251101001c02e080c040c80c01c590241c0c15607180d095011080d251a440d00b51401d40b04000201e000090082410380001600140e1400312400b0300d807281d0758201c14504c4400151009444003003018214031a1540c000042a02840518050b030020301c100c0000780d140e4107100003a00c094041c51121900e0a800822000d0008030b40d500100100c01c45034403c40c040400018018000c13540041e4040c01401001110540d1204200e62010b260605040342035485203421103112000b1140349030001018008211011032580242c044840c0c2c0c1d02d08149064035850500040d6101c08001b180841d070f0095043c0d580d6003110400002416030404000440c51030503000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 294822922 1250 294821672 294821677
    0x90206040b07080717030603070b0903030d09080d0203010906090506060c07031511031003061103010f0e0406111602040b010c11060f04080708060402030607081501080a1508031e0f 79
    0x14140e1038400001c501c010030015405032800a600644c1c151404400c1900c17058543d03100700e030294401c3c0640b0a02107203811190f42a58000503002d0011414200c0c05c100784001001000c40c143c0342408144201d01081d2000c0c00154083e0400b0303040803c950746019805000d81c0c801410b16446024148824080e1290000c0c610003201c0d0801c0036445040c003232030515401000ca8034422420100c00200300409110303080c1c84001100e201e020708000c00410f1081e40d450a000c28014000c0c541d4040708108503070315558101c150481c1c06180b0000c1d940b440078280c0805980420682e41600895900340c0c1c066140034841c505003002c007030806080b131041941e544c03c028130b185041e030b500c08e81001c2401a8418410340a880140a84c0740449082c1034450b10596038480040b0b8040b44203204140020b04000d2081c10f416021b0360300c24191050108102005407080c180c020b1000684941d210b43d0024904002884100104080c2c405180e4628203504880b18202d004008500600300401448a998845c80c04 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 294824172 1250 294822922 294822929
    0x60b0405130c030f0c05041e080a030804020f0904200a06020d140408010204081608010234061a090f250302070501020d0b03061605160c0f03030804051009020604 71
    0x100001d103168809000d900038401c40d012031004030705e450000048241c20800510503290364211940710280d03900070140500509010703501094001e901c00c0400207016640702a04144014044101c0c0c11401d40850743e0041300b1102603801c0c1540020529041c00c510b9011030840708252600f02d2024100000a50340b1301e50961420104032043ca444020f29010b41d06032805004004029559659159800313035448403e8071100c080d842030701500140b08807052080342c0a03000130380c2d800c0103c00e0145040b4150301034a41c00c0082000c009041c05800986175100b03503900320030031344201d0340207002c907078103024140d0302c0280315400d000d541c9014000f900003d036560509180c41c040c1d400030a00180c21044002e070103507a000600940c0081074080c40d03803082c0e820080305640180c049a9030750382c900320386800d0142c00c00d0210000c15801c0044803030b544081d00c2103800082c0602d80907545141e443c4461034000c180c1d41e0081c2c0001d4921002e100070030100788110420700964400520a40c070140c1c00050030340c0320741d20 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 294825422 1250 294824172 294824209
    0x40507030e0d0e03100c2304080606060306060c06010801241406090a030606230f01170a200904180308060922150501050402040608040206090d0f050f01060b0405 71
    0x3070078a6110f84d000c000c124000390581c841809035640c90701d03001e41074804c80c441383d03c541d03098200c5100d020f040e01c2c415503040b11102c900a05898543c001800844e42c80940b00c182c10510421440001040801c2418002c0c90000000500c3c00c03101c0485401a03002c3d800744e41c1c44014092003c0161081d41e060041450a044070410350b1481030368001030300c0700c0c007d0740b0080c462400d00c400000c12100001d0408092000b5003000c2e42184080410003118031140c2800b54081080c000701500151840b800641e40801e14a000050820329002150008024000800d40059001803902e0407410306000c2c14072201c20041070b00c2c8065816a03005081060700609280c020300840d400100c01c80b0700461680700d030503290a190241c00c09503081010913500c5080c0000592410900001a83e04052086500301c920381c0d62050400e03100c0350b00b0420b050b4403d0358a035a002841c884034101090681881082040c8108010080d84100319651425903940c4d0340a5612594184010402038580443c80c0d002c140980 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 294826672 1250 294825422 294825437
    0x90406020315091003050606060a05031306180803150a030507030312060f06050a090f050f220518010e010c1b170c0a050708061302060309070504090c05040507030e0d 73
    0x6002c4003840320451100030f42d00c441540706015002101d5500784098a0190040d600c7c250303184814020035100301801100000e2040000482503400d801800b00035600c02c030404280d41d400a84100e500c00c80170003050742ea041001013400001c0700820742c1050006d82c1504c40c14040c03842c0da200d140d102d95480c4400f03401e11051440d0448a080681d00000141c4841c000d40440161180c20080417a0029012840032403201c2402040c0d0915030b000000c00c8079001080b0b03608081c214002c0c000d02c1e10b804650f08080040d40d0301c5060107041c5a0003070f107100e00088981d00443c09009100079003501d030310079220030301c90740362003003982203294000c40c9000503a1446480d05490181498840441e40f149041c1c00c40200000c1880d80d40f460000c1903c0095501502c116081c1640300c84405807510025a07250a000403074240d140c0c01402d250018660003542801500c0300d1595a5000c203043d0751000030101d4418210040602c242e141c41e22410303801180905e4100548580c918010707954130442840503040c017051 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 294827922 1250 294826672 294826681
    0x1030b04140a060605011803120c15020a050a02120a08060603041b0b03070306170304090c0908030d02040e070c02130e03042301030c080420210703030e0f0904060203 73
    0x82420024415408100301d440a0109083c100c00a20080c059140080c220b1130040203000c03541040700c0150780d000f500500c1c401d59072060039105032100080c1210301410b80407000c046405c5600c0078184096444d10f0355660b80d0300050703000b41003a90468000d0807184050146815144e801170546500000985003d6502c1c0c44900300408500700601081014119110001c40c0d030400710406140610307100e48040c40004d07158000624600c40308544140c0725881031004100e91207a0b908004962040ba0500c19001622042d1850846d80400600450507170009400c104541c200300c20594041d00f645449100c5d0740950740080c00e80340810280b0740029032a00d000251541c07050040380c2c001d0141d00e261b040039100c9c804c0107200c80d00301d01d00d4950210b40383c042126041070240c02c0f2648035a9100c95208040c8201c01c0a07c6045140444040e400403026593300e1400f43d0183d85100303c007103051008200461031850014040c1c0d0b540c00d030203401040c0001032500f194603480710302500294080d901603140d03680c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 294829172 1250 294827922 294827933
    0x7030b010506070f0605091e0c030a02060f091005030402030d030b0d1209080a0c05191a031b12040b06010f0504051203090d08030711010b1f09030203010515040506030f030301030b04 80
    0xb404e50040c00d40c81c500014820f1140c2c1c0020400a480500c450b140c4051409441644d200c40c0d031100c4150305030b040303c0d201c2001450300301c00501d21151003400b498100381c0a0408140540d901c450060b01044002040c80250700e42002080c1000b0964078090000041160118103d2110360400a140c00c4402c0da40301034440c000e13040000039000304011621658458240460303c07040c4c610415000e49000d80e4031a0414101e01100e4023682c0041c91001c0f04d0380e80e0008181c2d580e40c4020458007480182e042540081541d01000340b000c010111810460350a140c2040b10140c13401900e201d0502c40c0b030148010034607030413905032011204101d03007804900c2c501107044e0f800d51140d81d4401c2d0344010061204000c00545801035130203403107641d4481c03582c1c011111742d641c22100d001030519880b965140c00302c41160b01c40b000703d0001411728a0004003140d900d83c04a801d448056811284d0400000e000158908252141503800700e0110010401d95036071118058481c4410301014000c2d2802d035000805200 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 294830422 1250 294829172 294829193
    0x60f0d0609080a051305040506030a0b1e161101090b01091d030d02190309030c0609051009060501090c05041a03070c170d110310060f03090606090c02060907030b01050607 75
    0x2d070008095503450450b00c0c4010025400104201000924020041240e06003032068502c03510300500100154074460300c0b41c4141040084c150100122149004c0e10789102c1c200301b082c011a0740d003d000c0e28104848401416200145070210b100e82e240000210204444c84843c5044560051000501c2130340c500e450421590391110340311f005d1000061505444100f68000c00e07032200c02052020410741107000032800d4691030034020b4002010442c0d00408950329521242920348200100ea42400700a2400415612011001d4a80701e075100010854641c0d540201c0380d1a09282c58400d1800341821881c56900c810281041c9203c1000f000007440c4601840000a5168020500000c890400603031a040e82c2c1c840e072000586075040000c5406c104c03030510162400350130409141e4080d01c2c10018211008504548000e0030551150f09a6000c10b1851285030060501850086034806420b10042e00d040d00c090811800c550007004200041645813181905513031003240e855a031050f642c104203c0a0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 294831672 1250 294830422 294830441
    0x7060f02101404120810050f01030905010f09210210020c0c03030309060405010b04060303050912031312020a14060a0e0d0606060f020609010c0507060b0607050d02100e06060f0d06 79
    0x254030340150344241102680d8028410f502c5070004842141d5814812039803480d003614514445138000c201840946130107181c1c4100f10300b040c034002920b43c405840381429103010040b618050341c2c2e1000341405205c909a04001d8a40d00310321589a044081d00e0300a40d0350070701041c4860300c294040f0b550b41181a0a100c501680c180c010b00300c03900ca0800000b220385070300c070550f01201c841d86000ca005001c1c0c180b41c000c84c000c40e50961a180e06040c101c8041c40380307441c3c084015810030300041200c1d0010110b4601c99102800010001207958880e030300c14800c000351a074021185088001d19601c0c003980c0c07030a00702c804031100f91800d4580d1203080000718680131000140104014101240402c40c2c2c1d0340301c00c0f02084440c0640c02c58886445184001b8200c0f024425100c0004404100e810003207050b50300059005c6d20054a100d180541c2d03030700c0c0c0034100545401400300581000108a404002d58000c2c1001c1d0b15084011342183c0c1850707400601009408280035028541c440300030018050030f90f1008106 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 294832922 1250 294831672 294831703
    0x90102130611010e060f0604021804051003030212090d140a0b040f060507181e0305030f0301181406010f031509050610030204031a040206040801020403060209041103070207060f02 79
    0xd54071100003900b0802089484072543d03181001e8250443c00018016001e00d4502c0c02c102480d8894505000c0a90310464a4000055040340c0032a000c0c0c4441c45524421070f058115126600c0c1503140007414103642221406281a05101c1c82c10240d031100c0170120f9035548140c2c105514064105018280080e0b20405084e010411041105000781502007840d5180318210400250355a000c05980b0400c804c4d50769860600710300700a1000c0e44400302803040740f100c1a00701005042d602d641d03042c81c6604c14461107609820210041040603d4100c1441c1c2001d08400144249a000d040c410110391000f8440c40c10011480c0c04859018020fa003c01c5240d00820000e01910784c440c08542c01801081d64058050700309803030450382d03861107071080d10192a80300c0c0c4910400300700001c181d401400080d0050364045001c0000280040c0709200410040d40b040f0350150703d0383d51440402013204c410281c01400102e040007002051a40460000d00761421420801e041038084d030000c82ca807114281c0c10020 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 294834172 1250 294832922 294832957
    0xc032a0c0b040609060507170c0318100606171e270f0706031a150c1006050307060e0d15020405040603060501090b030705030a080a0c080417011416030203090102 71
    0x70b00c040342e0810240180121703400d00c0b583d1102182240d111000f4140d10748240810b202003010500e0110003940c1056041201d10178040c40312a0303960070b241086903a0018955501c000700000c50300400c3c0c1e12100911950302c202c40f40740460000041104000c0d9041a214103400050030b54014404080380700c00c02c8105540d048062425915a1000314a039400c00394810309000140c4c0901c0780c043c03190701014003241001d81460314810310400b4044803951069a000a00c0100b80e1102c0800850220340c407240c6002c03c2c1039142906060a00303c850300104c04209407120510455280c5110044859501c00c00006441d035890140c84001e001d250000e641c41030801d800042442074941006040e607a2001040180745210b80030191b44084038412160903800901c840000302c0d00d4000549500e45203070030a240720351070030303621039a03546e115800c170000c00f00c008241d0286040c0240308820300c80d1403403c180c0c03020303040c0000d8800000741020181e0040640010010700f201000390180c0e640c09880001110 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 294835422 1250 294834172 294834181
    0xe04081603142208070f1707030204240b0a0504150e030f0a02030c060712050f0f030f01140114160507080304030602280503010501030902030a0b070f030c032a0c0b 72
    0x580d200c89083c0c3d00f0310100040840071400d0800424400308540c28480507481062500010f41201d00ca0344500c410325028420000003d40c885000b5602420301d5141c09400c107400b4003100c1020801c0580259001d004140126680103070820100c4e01036524800d20340303074850a4086c007180d062007043d02ca10307018020140340d00c40c000710004040729224800c40a40d00c0a032a03110601001d0701901034041c20001c943c1c0d1648161501410050000c526a10109841c001d83d000001099601c295032a01d44181d540004105901c004030280500f80170920380000b00760101d61200c0d41c940070b00202c5145200d0920410f404009041100070010588542a01e40340c035034a0420038001e41281190140c90042442c25034052844200800300781c81d1103468650442e400c050044004046c2002c040b60144070f18400303600404e29413200140320308065918080c40c00c401c480002d040c5d4100d8071140040c035081075802c0c0e4014032400b0301181041c5004000042d1500908002c80750381402e94800740504103001c0500 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 294836672 1250 294835422 294835447
    0x181908030703061208191404030c0e0f25090305010603060614060406120f06030f0b0702120702031e070e010609061704020108070c06061a090a0e0408160314 69
    0x35846580292403c01c15242d0740e1030450704181d1058002403a9440070014901140c0c01c40f080015054030707900d019031a01400d007040c5512940160030031740b41000b01c607104000b0b601141d99140d502841c1d0802d02405401c00550100601c20007080d60340d0008610105aa44a80318902c608000d603000740091088580d00e04040c4003d11641c011600c48003c0711480791014100a4100c500b2150117540d14030540308541108001400420062044540c43e5500000031a0000940c100c0d030b039000f11040c2d076442c1800d44029207400030503080380d801d4400c24007050000d43d50118984c800c03940500d02882d21180c0c98012581042c01c0c1b504681e0310118a0400400c08a9020b007076907007031301c02d941c840404414a000244100f1102180c0090010b00058005200d5a108486442c0f24900c0703500c01181d003644654103803c1c902140201d1202501010410f00b10600d4000103100080814100303030113941c01c00e500c0b0400b151007090b030300a820303022104003101014400c024500e48248000c5a050700e0303a100c0c8008 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 294837922 1250 294836672 294836677
    0x30219121b08040b07050409020a02030a02010c0311092206061706010503010b04060e1906022116020d03020a0501050106080403020d1e0c03050d05012c010e181908 72
    0x10814080e280014250726051259003100e900d00198031680c607940d40f503940340da0b8801802440342e0200082484002003900142c0050b103003600031500519180d50015000a08460414a84104250070856101e84007500b8008490403110306a4030a00c54220100b000865403940e0300410b10000c1c0350460020311294008c40e44016210160552a5540c50701001140e143c0003e008500400104010400c0840c4c0a40c03003115500780f010b4940582d00d00b20300007900a0814030740c0418050303000b0b40b20580744c60510444001c030000d201d4404138207120710201c403030f0004001d25100a004000e40408502850300811140d101c0c0744d400802032026607100c070002400c203503007994201d0140c81442c2c200e51199003c2c1d071852040ca22418610800d03c01c1340c02c012034503006441400d405000040012405861440c064540039108c1a0101881031740041d0360360241d07800c2250383d0281405035100502440d0034000c0300b283c0188010400140410b1403030407084c2400c41e01003a0607407000c6081c1c801003c100c6000301 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 294839172 1250 294837922 294837947
    0x903030402030d030b09070309020d052b170126030f070308060d02010c02090606040e1302213313110406030b0402100311030108010b0406120b0604090201030219 71
    0x5446481004050513005d90314034003039881e402003c0e40005819288030fa0f10428110f40001c14405140b02c20b901e036103040451120200c80c0198040382c0d45d400c1d507456440e1101242c949032030590550000c8902d00101400d0600504030700c1c0c0c1c0c00600390301485030f01d0340c42024070390301050031380b42d6031541c2d0241c800740d550203d0000c038040b440c61400101d075841c040000d5212103406071500d9102e1040d641c20800c7c134050040c4842e030f00c103400b4840841d0a400041c021441140031291a1382c80119a004022849000c3c42c0c0360300b1403a02c00e0804800d4102c1c045409100a0b40c07500308910005c3c0480008095000303541100f2035645001820400e4030041d91440b00c050b240285914810f81e56180c040c0015905a804060964212000810014200440c42010002031440c1c0013070250504440308440754000c0e0301a04507603445440c0c0c0100d5140ca0b00c01d010007065148111155021950b0b60b8240b400c0e4000e08841c406c907501c4d43d1036020b41e402601220028112650b040c612045041000b8000d49448403 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 294840422 1250 294839172 294839179
    0x1090f0e0402030607211d030403030201052203200304030210030507030f0c02030f0f070b0403020a0302011104050f06070512160605180606061e030703050108161a09180903030402 79
    0x10110b8045e600800724075904038011104001000d07850b08090010b00050340380d13954080c103c6c144c0c04240c040c0610240010b14803941c00421581440100250301450703401d110707035000300c101c0c0c0d10000003900080764403002d01d5070962420f0f40341c080600440c210b00581e4006034000c905c1d941503c04480e81640041c0c03055405407010023050503200081000c941d40c3d082e0200162b84104030500003505184041c0c5010140e030002c19203001b01c00c0c2d50b80100d6030415102280541d001d0804c4208141c2c083c0110a09001348034200c41c145842c110004106680c5885d00a00403540080c0702014400c0034842844d080f112491080e50350038418103405101da00d0114141c0368203250401081010962511500410365000010301007900c90b40100304441e405400c84010301320300ba9403e2140401010090b6201d18015200091036614020800d4280a0310600913020565902c0060144e658818200c0c00325440640c1c00c2c5445044c02d001140a0351005e00424694050030410041e020800100462240c2c2c0700341d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 294841672 1250 294840422 294840433
    0x90a030803061927060306060803370e01021e1b0d020f0603060a1503091109060108071107081603050705090708040f03031416090506040609031101090f0e040203 71
    0x1680c00980d00395640500043ca04c280c840c0d144a401d04202076081258041c240010b80c0f46e941c1e5151030071100b003540314054640000c00c40c1d07841407055002d008000304c2060a5126035051160305481002110032b0003005004014054149a901c04c00124950b031500540b40c000c000b10010b011991261100b100002009480030340b103046050100c2e4501126a0140c40036400c030100c14104000c640008008903003003107210400046210000d81c003c01401c900b920001503008071070812420702d882c494202400b81c85c0e4803007402556640211070304c0e440601e52616098513807222071482e05110305030707001012600c1101c42c115132501d1f81c503c80e41e048920400454100959403428440080d0b41100c019001c9a800000913010075100c000c05000648039203030004000341d600941e11503c00c401c1c4c401d150340d0601900c0c3c1032034072500720160f00050401110009e0600d46880ca006103d0101c600004000b0724180034907032050b90080800c43c0140285103003500100e503c03800205021582120142e11905c01c4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 294842922 1250 294841672 294841699
    0x1091203061a0703020f06010f0e180a020906040b04090c05120106080d0e030a0807080d0c030501080c1c02030a0f03020c0103020310062304140a0806091908090a03080306 75
    0xd2241c0c00c100c0c1c001d0002001c0c0c01401401010702c5401401e800c3d000d50258207204507644000740040350280c0304203200c104489003466006000490b0081410f840e80e80001c030202009100080c020341101d90481d00b5860541d102008140070304100b0034101d4002d0b04000d44c50041008030000c54060343c1c015100c0c0f840035042505040c0c207940d4244955080ca030484610703402000c0c412034029558120207000c9039100b081c20764865909900400301500c1c5010042001208a0b5082c000d812503d40645003d01c095418800e0f100c0c1c841d030b444074170720380f15000d140000034040b10030009169100e600101510034043c2ca42c281103800c0c0540ea281100103002d241c0c400b0006600910a49018802000e00320100905080d42941c8180100780e200490416901c8070303084c1d0300c00c020000c00190000f60304020400c0021424024000d01c29040f85003c2c2d00a50308204203000b0010303a000424042c3c0c00c80703014200483c200f580103031086400c0c0542242901d00040306100c0d00b200218015441620200c0c01c0201 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 294844172 1250 294842922 294842927
    0x3060204090b042f030901111c1404021302070f0203070b0307090906180e10060f051002060c0702060a05070b07030209100507150515120d020111120f0a091202010912 73
    0xc1003d04e0001c00044a5078490456041c40017455001ca00d0100004003c40381c41400342e0b26411694107401e001281840c0300d000b81400b8024012440f010030250b807002d0526034005844082200c80440d241b603400306013142442204070103590641e8000c0c0994180e281c071040d124556070700c03c03104180850f0b1488400201c20259202c2c5904035000081940c1308d003000200450050210648444028480c10a004641c03013000c2c481c410007040d0040743c400b903162900007402001d0301c82d846142d003550480030802030b150200e58101c48240f82d0480781903594a10803c0c0035600d5014500010700490050010045da554042e4001c064660045890100201d107191044070769100d0100300504600842402051000d0980c124a401180e40c5119607804071440000c20321811045010406951006206900140e028800d0b404420702d156034040c5800440c260140c500702c3c001c0c0150b203100c151440001c00c1c4820740e92002082d9a0b018100c0d404110f83c0c901c00070f020b0089070350152032100b10b035401c43e0403150 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 294845422 1250 294844172 294844211
    0x2003070b09030a0e04020d09053406020703110a0b0a03050a0612201f02011a0a080a0809030106050405130201030506100f0305040507120309060807030902011205070903060204090b04 80
    0x3d2072982c86101141d913103424803002c0e4000118001c00c6580f604c0b9940e00141050100340040002000b0441c0c20b0307004141c00c8400d44140848803071000320142005d11407254003040d80c074103494002000a0841c0c40000200f21108a140e0090b260300c000800c0258075541d254210600948440e10306104664607040d01e82885043c41800808911b24940c1c4a0700176a451101c500d00706000030038022110140f003005d88110b03d109021a00181d40d01c001e1005805038048000d05141001d0300c0c4a240281042082c681d140c801102c0500394550200e00c00c0e003255000d4001030041e1401520901c6542480e50b400e040f1012002ca00305d0210341480c00245440c10005507000603291195103000f00c015200406074000c000150058030b80c1d004441c80840c9200d1100d0448019520035580d00b50103d00d00b0b00020038940b0050115000c050511a8500250303a0145c0880e4041c000c00c0000201521000343c00c2d039420090b6403000b01841d001080005008005501000c80524152000e112114000aa50701e244 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 294846672 1250 294845422 294845437
    0x190815010914040e0a06020c0a031205010f030b0c13060504150309021302070c0e040c050a0b040b0a11160608150405010518060105070606032003010911102003070b0903 74
    0x30000c5240d40c0c2c1d450f01c0d400840c031091140c1c0c140c4070b840300b10f510380000360b034854102c0c03a111343d100729481c104042d40041900c0c1080113040041200c2c1d4104680c00440d2903607882701030300a40c0d004000c0748000082c081103c0c0910815110340940640e100400780040d04148158107004a51014510840b4000e000300350380356600408800b41c201708900345078002d402901082e03451410300e050200d2100c414007880b0f4042c0740a51485c0841c0c910300020440f2001c401c0d0031905096100380410001c10343c82409540c982d207a079080c00c3c2d0f25202051070451908110b4010350200c5013503270b40001440d5400900d0380d0b0080e42c80c54604000030a2030f84c00e1005554084c455160030101e00a28a40541e007080403840d00190705141c45450034107152107100c19601940c2060b50014803005d40c0710300c0401100c0400e00d614009800074043e0380096100c2e4880c06005581c414000c405c0e45400388191403040b000c91223060b829402e580d940030041d141441d56504592001c0b905900000d02107030b800da038004140c50310b1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 294847922 1250 294846672 294846689
    0x1080c010906051312060609112b0e06040c080f03090f0405041b181b0519020f01020c010b04050105030a1730070f05040f0b0c031908150109 62
    0x5441c0c41e00c2210a5400001484860113100f60042012005900e0080c040d5005000c0071480d2403c20043d1404c036030812641c5030090030301308001c0d2000c00740c0602408580e9600c0c6400d20300e800c0742c0fa009501400d14642d42094900030f0404020400502d240c0d91019121490b040b03980840c04400c1c15540ca210317500c1256032000c00e07100f0415140c0b400703400007a8030612442d4108130142d0130000a841010a580091002c91040b60320303008001070718440e02c042490a12a091000e804100c400f078480e10400902d40c4070019801200f42134580200200c6551102d1070000f10350f40e507405004540200b40c0441490f1203070f41001e00009252400065423400c49400c8400c100c0c420101402c9481242e01100700048818035007141400310085407982c00038440d031640c41344030081c5030007207004008280d07411084003405024001805110f954000f81d60944051034000790b03440c46000400740c0307140122441500e4400c40c009c040001d160b44800b045024200500c0320010b0408050010750345000140201140b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 294849172 1250 294847922 294847937
    0x130501060809160b0f0706020904060602030a080c090f12070e0a06090b0f0603010605160501020d060602190b181e0f07080a0b0a0b010c020d110112060503060703020309070816030b01080c01 83
    0x12190030300c5d001410064455100103162151000101d8107443c81035000501603040801c0035002c81da000360140ea0311088507281145824181c0300050a800f07011510307980103210050710658001000c0080c60050070740b40d521251145820301148002e408180030b031041983c04c0440394121030801105030300041100814143c00c40e030800320304880f190005404c0c1e80c59810100340900c00708a0030700c002d00c0c0f88034200001003400b508054000e40352100d030100c5103200c15405030643c0007040003401010340043c0840c00480c12200320304019840c01040204104d4620722a014542800c100000c02c0262442c0b844192400b059840001d982c640000450141c883d90100c000144c2c090030a60000d40f404a0504001c40d40400c1500482c15864488204940402c440e0203500c45a40c2c0068240c410501202c0040c0280d9042c000829114540030342050203142d00071000c59211034003800080d020b407800c42c00300c0c0c00076082c41d44880082c139160311013910080701c0303171307002107000900455660b104101c180c50b101d5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 294850422 1250 294849172 294849187
    0x1d0f0105041104091b080601060f020d0e01141c090210020f0a060b060f0a020106050f040c02030702060d0b091914150918030a0804060c020303070c060209130501060809160b 76
    0x4d0300381c08500325646003222002c0070310b2109860b001c81c040d0183c00d00508140d0704050000e4100d030314500c00081554080340403d40d8a0f9404003c480c00c5110070b02c0c2198654070045045407640c01005268121a000c081450401d080f00c1d601c0300030102d00031101c8240701ca41c0341c070f026a00ca00c610804699079070071609668020540d2034200c0f001040b00034203103506d0f00b40c000800c14519000f000741c80c80141d44600040015280040d01810840421142000001e40b0908060f540303104101000380121404240380103c2d21007a480703410422400341003001d040c50500c0114921440543e091810140740c0300d59a447d400c415a5180e04c144c040a003940540c5000f4010030040010003005402c0080801e2004080305070144041c0c122600c140e140c61416081903e040341c01d4030f4601140d501194418020010103540c01030002c054a038000030700581d1900341c1c0c0080755402111810740c04509050000000d030b4190b0010a0512880084054a1403065000c6070711560080b40d1003220b4100c2004e00980c0c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 294851672 1250 294850422 294850429
    0x140a09020906040b0c06040c081f0510050406151409221d010911060a020d050c2e0506030a0210050c0102070609030509241e0c011d0f01050411 63
    0x20036181c0e00041c001e50800ba5a2040c0d2007a90b0712048a00690784c1240c8140000c110082d40c0c2c480250030490040c000320341600b60041c42c6c095658400b00c4080c2e880d89c001c100780410881c01c060142030040d00034001c950b15990220000b060074070380c4c500000c101d0615001498050f1059800c11000180303e6281114038081840303000709035603290721026986056041150104403d507141a80051001045070011414602c6400030000e10f19401407808000c114a026400308001010385620300b40381c3c0e03d9180e110f007110f1611180907c040c90158100c540c0e444078000380038214400100d058000d010641d652401e0580390f62203c907009410201c0b0101c0310208501950103001c22240708000141440c50940f2600d007a1130f4042e100358082030001407040c6a40c14001a403000021859005c500d00642c03030100e5100a1040000b808801006501c0300d122641d0751b2011503410038410002400b0913080a241c1383c0a00d0240d10381c0e86494030846a042d00c0142040c0116482140c01100c001102040401070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 294852922 1250 294851672 294851677
    0x30504091e06090501050a08031908040317040503030105040525080a02130b0a0806240708071a0114120705121c17070c02030d110c040903050d06140a0902 68
    0x120320076074030503211840a1040520402c03004003004034020500d0b501d1304081c0001d06500d40c202a110341c00401c500c0381d0041240240c1481500280782c000e11903640c0b0304040b102004101090102d055500c0b09220600900201450588204660400941d15050080c0c40030100304071031205031354005041170502c0d5000740030007036205045100161600740c4681d1407640d02051600002441d200c04100e5250b619803200c115640300c003041e5681d844a03034401c06641280c000410420300c020340005168020800004283c4103a1070340107080880c51503045410803810741c0240079030340306218001403000f202d10306010140b07032212910002c3e240c42c0d0300349003e005070000c02d6100c021513449140161405a482890041030344a50756481c10340d10030000d4031124518001030950030400c1040109000580d070007040d100b41440c2c83d8101020b5003d40c0c10f01b4613041c0000d200d48240e0092511001400f403607006402410002c5a43c0001c2045985826604901014000c1c00b1078002a85142c1807107180c10f00d500 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 294854172 1250 294852922 294852941
    0x30c050916080916060914010c080f03040515090105093c01020708031f091505010c02010309060e0a0203070f061e050403020306011710140c09010908030301030602031e0403050409 79
    0x40d1103041c14449054003c90a161780000e0009203440420024070303440b02ea01c0424000f0134a03080e144100140c41700f40940c01280c1e0035011704400000800c08201080108845c1030b01d18042d40101032400b0001c45000f003004035a840c6807405200d4a010700f012000e06005008120305a525502c9982500d2908404407a8580d6032450341d42000600c010800d4180603601c0f40348270000015050141d07108001c2c15050300c0c3d1144451a0030300d1401c5041c0b1030080c1445060390307028a0000c040001500048010b0210b02e00c0240425150100c0407000c29404a000d18950b80280c04841249036100c0801c4171009181c0320b234900003448011800300c03224203550002d00142e044d140031400c180d00d039000a801c3c00c50a81c001400703003c95007080e03142076400703001e01e0300d0341005c50008100c0501e4551180840210040002c041420001401401c681c01002d00380d02401007482103d0b100d41e124600079001354015108011909440080f00d1210ba00c2e0300383c0144600da0540ea0541085c1c82c1007032a4014264404 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 294855422 1250 294854172 294854191
    0x20f06070c0314041512110d0504060b0a08012c06060d050a1703040614070c2402070b06030c1f030207140a051e1212070203070813030c05091608 64
    0x2140c1c0400060140160005e0004c50300d10212510541c4800ba04036000c030488034406505090741c0007401d00c003160984900c2e90103141d000c14540d43e1823502d0402041c1caa1030f01680a101440e01240d200320562102c40c6c120080480a40d4580180740340908400150103940641e9001c0340014140781400700d040c01d5110302c00d0040380c11020582e0340b9000c40040402150125420100030002403040501988100d8007000e085521340f07007000000100070003900704c0090013422903281080d4210702c90014003180c120059008548840d0545444100d014040d04d11034402c1c410101298820f2410f440d100d181c840fa40e1415503440c4074036040903000ba400c80c40f4152401458001c05d9000120280188041d007803003440603140d442001180210172481035008100d040d8040d60b2107110001201040380d000c4011288004403907a10740b41c04916602c52540001d0196030302040c1e8100301c01d075010708a000c1d284507038080020a601c40302400303605d51080721410b01c40840091224210b6015114542e005142d20 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 294856672 1250 294855422 294855437
    0x605061801170a1a01080c120718080618060601090e1f03080307030c050c0a0602070203030705150103110907140c0708070f0608010e062404050d0f060c020f06070c03 73
    0x1450002e8460100e41e4544078580360785100e40c2500311551180311044e070909140055050245001ca05ca00078460300c0c561150000010030002e50255581292110b1003a0300c0c5900c003516031607100d885481c20307100c03040420b20f401c58410024001083c40341c8200703c11317510424111b16000a003009000e020780004d040c8840e203050140401c050113490320255024041507030341c0c4d0822410040c100c8035192100f100300081030105548a82000c11070740c02c9650002e4000d603c44580d40000703400d42c480c1640041030b40c8121a060170007612100031043c1203030301851080071034070a00030520001d5003013141c0e2040014078102e6410742110640d40034220140488003203610041d01d4410721450094190000b180d010400780c020000185d11102890241c007801d2070140c46400c000c00459896410752088001b0403014144c603448843ea0041078a0040c44e00a1402d05942054203103851120070056003a146c2504110b218151a40001010b9030140b08041c0104090750380e02d02d0484400d00500411030801281 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 294857922 1250 294856672 294856697
    0x61302040b0406111c1e120f06030201171302060d0b09090c0a0909080a230d1b081003060506030a1401050907061103030a1a0d03080105130605061801 66
    0x1140301420280c101c948a55080201000500d803500ca200300c6802c0c0031042c00c08103005120380c008a040d25040003220110707045007042e10180c070305030702c7c48034034400d80f07850105900902c03c1c080d000002144d000ba01d442902010300c0d412641ca01400701c40900c00031300780d5640c0d800103080ca04000c0c99a01070800300010717094031000001e0a050300503191003505602c220080b15044c502407542800915507540204071111041d500c091042c0925050f59040c029403000c810130b80c40002c03e14030021400c4800c0c1e6035640200e0804840101f0401c0e91142941440c02004020140103868903801002807040d8681010300d0b5650b144058000289142d806000d9000c040c0001841800100401d00300100049180d1034402101458603001d540404100006038002d0b6494406c0807084079000050281d001c10f07012480620211291139410030700341c0111403584421b06259003c8110f038103a920842d00042140501d9522206a880d54010030350700c02c004011074030340141a41001d43c0c0220040c1080c03c69080c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 294859172 1250 294857922 294857939
    0x403090504140103021201060e060f0402040e01061110020a1b06022101150309030f1d0901120b010807060504121a1003140a1104091106030910050a060b0306130204 72
    0x66000b200c0402c00c064070040c41107182c665048494002280020440c9906d0f0261040e121100504081c1c012290420704d1006070700c885c0c04580140032100300c01c0b0001e507565030b00249103804410f94540386026030708181e0000f49090003103803464440e82d950340c014100700c071182020b14007640c4011602184d00b00b20000140c1d10300303110440040040080003900350b2602c01c1d4483d1031402c1298031001c041c9000c0482e40000d40145c5003024070541480c0288020003103100d00c0000c0404503080039031007a041000000d0b0708101d081c0710f0711010720440d00c886003070b44d0310303d2078950300c0d0000c0c0a00c03408984188424403a60b00009401c11300c4a02810805090003003454031303058160070030b880301b031034114042e0300030310511800f0070b5000c49149214000b40b0b51050507458080c8a104195681ca200360340b00d88141081c0000d05a80304a101e000500155903810305006039680e4031224001c0d401e1407810700d0002440c0e0702241c4516001c0b5200005800d00c3c607a0b40c0130410a1210b0300102c5d10509940c00e00c0f001c41c4412 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 294860422 1250 294859172 294859181
    0x1403070c0b0907050102010f06050325030c14120606011b1703070e0102070b0708030a050403022d1b0d0303020a18080105220f061a042c0a0503120403090504 69
    0x203040029003003884c14140024291104c142c0941000b41c18450200106d450019042c00306c601030354004100c244142d030320801340b400c15500c0941000c150900214910900d0b911018408008648250881e0724402c6415242e0b00220f6003140801d03101402407520740394050201e038a80d4071650703e4142c0255403c11030441a001550041c0003d01044483c01c480e5804000c1c08000d4002283c205040105a65812801784401021480400c0c2c0300c03008030f81094000c10000903071180c5c484a000d081510a1260800301070704440c10b20030761054041c0c0b21031803c01c0c0d00f00041244000b8010f03074082d1509440c00d038060f6005000c1481000f06210690f0b0400b8906000000070f810001d00105080c02c10410107030407040401d07000c0755001c004012000c005401000600b6901c1d074009004242020b43e00044088100c02854464005080001c0d82c0d01d0308005240c07400101840042070080113402c0012544c0e82c0c2c812030001480c1ea8001c100e00c0340181c1035064021341c070602c2807030f20307055072511600401d090f00d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 294861672 1250 294860422 294860431
    0x30f03020f0d060f081203011211150a1101113906040f03080705040503030702010806060d0e0f010c0509031b0a0306021b070816061b050a08030a050c030105011403070c0b 75
    0x3041e604c0148010751040c01070310700461200e02d001d800c40d4101800034800030219040240300b602400443e08241e00d4928201907030076282ca078520b40310205010003030440c280d6a04554025445c01c0b000100300541e16081e203154403400030410b480c2e04104d07551f01c42d61815180002c9010382c01440d501440b0701c82004914402e40c41056650100c005504e00500403a4028210a05000007480b00b440300f03480000582c1c071010780900c0c24401540b00c590105110780f249089903442c1e18108003485441210001d00d480600003050002c02079107a6000b0215041d000718021140e00d038008045000410345583c505940c100300c0202039151160780e0340e48541c22644000d07c074000d0040b40585046445c0f20a0040d600200000d2014051460544051168060041c0101c00a100071b0001084035880070104011182da40441200c0c0d0000036428840013a4004850110025003403030b0000710071060000569040390b0040c4c4442402d11a610240703102a000201314004008045803082c000c07030041903004c0e014 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 294862922 1250 294861672 294861689
    0x1d0f0d06050108100e010513031206050301020c010b011106040206070206030a0609150312140d1a0612060a09021e0a0201090f03031e02030c09010804140303070806120a030f03020f0d06 81
    0x20031484e000798054844180c98505c01d070340341100b0030100d54210300c40c0d807045a60600d0314900e030800b64080103005041c243c00c00d580540c03000c60205407480056020344100c98090300c882d201c07030a160b0507003941c910003120000c0d002402840300100604002c0040c5811500400001c03403100e85800c039010445241841400d96142b06280420912800c8036041e16001000d240c000712052000118206520842011703030300a5540340828000581d104840849000006008566400801c2c0c01d0000018003604c50b2881650305200014100d1818821500401c0ec01319242c0c002d1103e089012100380c000d007c004003035549444070400060005644034800328841c3e01e00042c0d0605480b40b5900901040f040c022a00d4030400078841a0351035030303056a2540304240390421003a45e8902d0f00390900742d214840760909100210500c115190040c00091241100f51507518108d03e00078286940d800c6412409404509185420500c40740306c0c0d0010080c04144255451034480754a41c0ca00860305164021000d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 294864172 1250 294862922 294862933
    0xc0306020a080f0105042c0c0a09020408060c03090a0f03090506070b040c0503010b010e2806020601290d0c030b0d150e0606030d0f090306050112060c1d0f0d06050108 73
    0x300f40c042d01c4060241000b80c1d4100010010350f082c20104c10f40070042403500340f41c11030314038240e0a03040100080d50800900740042c802e80e680a031b600030b03400c075024522403406100001041050b07120182c0c1d100b024031400411694044d602c0700a014280e00d0800d8007004036000f0013044544943d4010320400d0320a20000b01249002e0416411220ba84e4100611030b90403c10510640d80c4e0060301420781c3c0c1411140741101d8201044001010903c4118548400c0840180010403a8021071800e0407905110740e1305803401040d0b01001c04c10140000e402c0e008001c24060400750154907071141c0c0150f24241400a80b05230160001012055421030481d01400c2c0707400802c0605219000d8112003800e08002892281404800a5201e00101e1900810008400d00107000030b4441c904020085802090400c250350f111081c4d030b0341501c01c0c604240c0d4140c2c1802020b6483c1440380217404440c8520000890f60483c80c2c0c0100040302d00c0c9400040d0703220740c2c403a035080c01080542c41200d0081464000915 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 294865422 1250 294864172 294864181
    0x504150c1407050a05040209060909040b01080f0a0b0c0307230406020c0a0e061c02040c091e06050a050d0615050a0810060e090c070b040525050604050d0c0306020a08 73
    0xe208401807511040c07a038014400411444e1144c00741e0030103503941107402507201d5446401080c1c06008901c149603101c500e80c0180400e1016582030b10307050341d00100036104e1074803e11102e240e8402072074800400781803440c00001d02c1c44d5001406560840700614000c4442c0204c02000b0000381c1d940c80360100c1070200014100695070301003001d0402154103451710100949005074004044500400081c06405100d11558040c5032004010034410380c000c00400001c5100100201001c074a03000f80030700b41002000074000c00703140151907011150143d60342c83c90240350b228100c1e05500058010b80c4130342d440e14400316110800580050f100c150303641d00c4d81c5d11000034280040400c0130207000c2000c85410490240282d95001e0170701c0701c44460640d640c240540b08e00d804e110062054000240002001c0390034401081780100315500c80031108024007000c07500d031000c0020090348a20074140c1c45141080308011303074180411074251031805038060821040d0349456800c183d0b4000010100020480e50421 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 294866672 1250 294865422 294865433
    0x5090d0c150905150702010c020d14010c030b12210d020304050c01261311060d0603060b040e150a0e0d0c0201090e0402010509040b0f180f07020f0304150504150c 71
    0x2c0050004680c0c080349201d4502a42c1c16174803c071103010f81081070710f8140c0c000359210f1a20003095035500800405c80c55940c1091a402011140c811400090401d00f00340d00614001e0122141c02500303401901e82050a61401041840c86002450341d518050085100b011807600c061403107107004002900804004400040409040c050117101043e05610070281002c0080001c59000041e1600450080050f0a01605100603000380075800361000582c0d101801443c0c20000c101c0b0703c10f8106100c8810f03002c080000355144c02225024690084410f241200404007225806c00680d003000640a6118062242001e1130680e14202090740d030843c0b082107580c0000b00030010b143d102d400c814942010340c002002489162421840340d81c0b04c00301812107564205050804080061907201c91810300031200c072440604485410151245c4030003d004a800840c80300100312034200034619050410300c01407039250007108000100715040c400030402008002400003030003450703210102c3c80800351518 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 294867922 1250 294866672 294866687
    0xb07060209030601080a030f03051308160b010b180f040b060a021f050f1512060910050c0c21220302040c110718090605150316030f0305090d0c15 64
    0xb040c1c01d940a043c3c440042179011080c1d0030b5008c00c41c640840c40e070301c0d025424000790541110207840040e00244451005044180c4008854481d01c8030800750380e40c2c0c2c0300c10031160007005041d160140e4240c80014441c60609131120229a008000013103503003007900401d400c1d401c01030302000540e0204415481c3c000d180ea04a080c070100e050300600062034612a000ca680340c018001e1064107500c0c502c0c030b0301a07075108080c10032000b1140c000c40c3c4c114603240020316601d07162180c0d04005146094003058118004a003184c0c0007160b614000c01c03e030844000103180041003418508550b010a00069521060b100d0302e10000c1c2e41005021a0141d00314010002199002215402406000004400d0000317010031b0000454518040042c0c40e072031140d103a0790203801c2c0703103400a000038905810171201160b180303202d50b03001c1da05030100c1e2024000b030117012150386141e00003e0130340e2220300c544000103031068000b00010f03c0080c042c501e03400d585a80d40b040c031417199003020001d40700e10703055080055886400d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 294869172 1250 294867922 294867929
    0xe010314030304030203070b072d03060602030c0601050d031206090c1103120610030e010e0a050d080403020a081b060f09011b080105190f17010b0109030b0a0b0102070b07060209030601 81
    0x20314514200f941e0040d40c0c074403a100c0000c22200c0440c000030510b40c01205541484201100000082512400c10140c0d14050303200e15004a480c103070003c40c03600e100100b500c551486001c0105410303400c21007001038104c1200d07400c90401641545195507080b107402504020034052030007181c201d08840010b0319942d01c40502205550050240340310a0040210468100300160382050645100d0fa0b401c601508400c03581110b1913003000440c140720382002400c2c81c581c40c000c8040c2e650b103103c0d00c0070446469409440c050010380c80f40a950000c20314560040c1300b01d01c0441c061310380b40b034166070400381480c004460f10069428035208103c81500d0a0080240603050f4040013003001d4a0580d001d0080c0e4018069113006500f00080703108803100780c03ca220007914005c850090040d0b41c40c007084002d101c103024100b01380c3d401c000d0001c1695000340b000c0713000e980c6d00c98050103281d030701c9070200c2c4010040c0f400601d0440c45000c10009420303c2150051070706901554026030703900d0346e101c18145002410791 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 294870422 1250 294869172 294869213
    0xe01030c0804050a020909010f090b010311010f0818150c07200618040e1c02100b13090203012c0715020a0308070309080d050906061e040c020102070605010e0103 71
    0x10040001d001041d52007000b40e040b030750151580c8800b2400c48c01014032103070302d4010034075044804090062907101c05040700c0c40f075442c140503001c543c001181c0001d42d09541d000841d007850080f44c090102d1018514a22504a00b100c402001280909203400000c1d0355103600741c0d42c001031701000e001d268030007200e00c10104c042c00c0b00502003540128401d8400d0420f483c407078000350b01403a161641e49410101e880c00a1070200c44003103a101c00c030811854039541c0658094810b0071500c2105400360300a440105500a00a010721204518040c010340f0101c1402ca03455580d03000c41c4850090703c0704c0c20a800e440b150b402d255003030242040e0300e40703000c01d55002540040c403040c42d0240b01d00d60020b2000038072903242c5045d0b03140740c8030070f4000c0d0041e15421800415504000c80e0f42e404021a03030b482648541d4a40c0c00300c0303856403034001c1404102e40ca4140180ba00300d48186400364641001d0300004207200c0a840010301d014134135110070044840c280c0050003410706801c010420b1003019200306c40d8880150 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 294871672 1250 294870422 294870437
    0x424050a14180309060901110703030305090615150a110d03060f0905060f04020903030c1203160f08071d040501090c0e0109061704060e1005010807080a0c0e15060a0e01030c 76
    0x10740c00c0a070fa9000c0e01807924070460740024186070b2640328a0407264245166401c440200741c4178580503016010031946440715201e1340300010380340011044001c100c19405490749402c0d10320201c000f02c4507881400748906000b0b030011060008101007020b4400f016160b50001121400c0469560103040c20340d1101860394200340c144803041d0703a810104070018a04039001a901d80d52400401d045000d00d845848542c01400a14500d8410b208004d41c8107034101074042111082d8144151800d40d09001c40c8000628400001080a4010808000c0c0b0a980031110040840d58800050a645003600f26540c066140e005803400107400003483e410026003400d2004290b0700301540208918000d2921207051044040482c1c18046d255010040158408050342c5944241c09044400781200b071090b6481303442040b100107000c0340701040d804085030b400a007214241d407500c0071800c18954083d0180210104c0b0010101c2d05943c1d030310003085480500d0300d0700d183c1c803a9100c0014003203810941001080c41500d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 294872922 1250 294871672 294871711
    0x10602070503030705060a05040f02100f0e090115030506210321010e0a020a030216030c1406150904020f0607031e0305220528060e0c03060424050a14 66
    0x309221fa40503220b0000003e0319561030238980a2402041ca02941010009044284060344500403e201001c2516403480d8003c2290a1240c508824810011141e00d60220147c0701c034440e400282c0c2041d4000d0016080c0104d000b8090326014483d51210358a1303000003954000741507038462003000d540f2a42c0e146082903240c402c5400c00c1c1c078002000c114001d80c4c0051104001c6010750b056032000b481043c0c07145060050341c9000780040035103650a5449904180700c0c4030400700d00044c064031a05c4011a50107403150404c4c01c2c05020540540b0482c2e01003400003132407003903896203000361060b18042d544100d100107a0094a211404003810b501c0704042c2040c0070480e0003070f10044081c9020344002034482450f8a2403d01d80d080041401d215228001010013030f0030795a00901580b006940034440422241050840c0e1039a180b540e50450381d09a08600001400314400c21600c1c1c6017a2910382c04503404856100d03a20f002c1320811036546c904e4554803400794182d000040c1d00254001091100c04041c001e0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 294874172 1250 294872922 294872933
    0xb030309090f04060e03031003031112090411070602030f0f0907030f0807060209150a0323060907111002071406190506030705120c040b01080c19050f120106020705030307 75
    0x1c001c0060003181508000700d010040d407540010041c403900d81c2070b030381c407170070420807403410780c9150320054000402c80384c0618091140030600060304180243d19600e02607203981800041c281c0c1c803454072022441404038101064440c00210311842c124450ba01d26441e00d402e0528224030007a2080d24a640a401e050002404942c64030350701ea608500182d403501c01c1860004064170032085011382007080440902c00c0c464031200542109091914248000780601a0701c0030542e4030600007448450156011070707424242608543e0300641c0320714180c01940720410300c03185441d95809c00c0342c4c0c1d0345038002425030600076010700030f207102e00d05132000c0c0c83d845c14400369408200140808041c00140d9810100b0480e645c00c00114001709406410500080291071101d034440450460150013642066169499907225a010030f201d000100b24050402ca081d00c4c0b50204d0100a1607108217001d0104008001002d4040150400342400a1800c101f0341c14040000e0038100c081d40a60b00943c13041c000c080c00140f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 294875422 1250 294874172 294874189
    0x9020d140702030a0806060403060c0f030f0e0618010e160806070c03080f1512010218151209011104031b0803090609091510110105060a0315180212030405040b030309 73
    0x1400f03032510001c5c6031144800507000c3e00c01d60380020f21a81c548401e1516032038000d502500b603002c1a440800c901c4c9641003084054601420b0403800c650081e000281d4002001c801c1d1005600000e0000500300701340c000814070305200105003641642055404010b000c0c0b08108499112b06c0c945403002c5008603680e0040d2401e04050800c074000005100020042c07400d00c2c16180c2d001d00000d000315080095840f00074000e610420011190f2615003c43c00414140b01c043c9001100c241030440e49008641003501796481c2003d02071b0041c554030f442c0114040300111002c0e1001d0340c041e2403100b05070f92010907240010b21165100300440e400c284105081c070382c0e81d501070b620412000c0d5005191a82c445001001c3d54001d00850f07644400164440200d00d6844001800d5200c1784000030840b98840ca000c0181d000c0c840d1000910034548100e01e08a200d000350002a201708a03000d0001c184030300c03640050007400701e0304e034460f030154000302e0104494a401d010384005140150041c616283d401c0005c2920700 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 294876672 1250 294875422 294875437
    0x50115080d18181b0c020901050405040c06050d1b050903100603031d0103061205030405010206010b070f080a05161b0506090a0b03070c0c060f08010e071d0102031309020d14070203 79
    0x4020f400c03000025119242c20405464802115040480c9049080034080603a081380c268021083c4100209003401c0c5446014059034025245190091528004136103c1c1e0200883c1103100780c07144801d480007080e030194100e1441950b10b840351038401e07080a05103400d200c0c8000f02c404904140c030810100b40c00c60030445011242240c0c03290f154a45000603400f030aaa03030b21050b4803c3e07801000c20248079001c005003040c1d0300d00341d00f9600d46980c2c80e80301407100d0141400280c15000303040440000900510000d01d03400f010b81c14440e04200505000d00300c1a45880820389540004031741185100006c80045005490102c80050074039050700042201c0f6103590103441c4002400001180e24140101105134000f44e01c11840703410345860b1840107000e0016102148042100200080f40054520074013900c030311129900d10a03410346002c00c66007515000b101e1a03044d4001040418503000103003100c500038251241d0007607035811a1200710822100c0b0703c11591101c42c0e0701c2d000e000e1241e6000c000c54100 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 294877922 1250 294876672 294876689
    0x1c0206181f0b120316020307150806012f06180d0512040c0b0d060515030c183c03031c090614251b0b040609050115080d18 54
    0x80d0b4001c541c4900200030a81e036a132001207014035850300b1140310b00c28445e1007030741030394002d40d40c0310500303d102003454400f900410340c9a00000c4855110b65031400a040420310304c075885c42e8054003103060303440448101c0d207080d801030410889104180d429038506024038030f000b8010000303048c0e03005005019207802420f032080b2510100f020320841962813005010005041076544000d02d0302c0400078003080c414075004911003050300410307041030026a0711480003020314918060604445c01e480308209070720745a000014440c1d071044111080503038980300d6410440c1c041d08442501d090b18070014002281403090f881041841d0b0041c48030500520403003102d82012a103a00f05207001c601030700c02005480f400c68048010020068142d25401111100b4405a406010b00c280d000711031030010400e0182480c024130190302c0004203840300705944503020f412700150034201541e80c0c03420340e08043c00305445a219001e0602403c0028003d10300c66980c50704150302e64001c0c40801d030764005101e01c2950503 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 294879172 1250 294877922 294877931
    0x10b010225090504111504080f0a0803010e0901060e0a0b0103110901140c0109050111030601230f1606021b24010e1302090106082205060402060c1c0206181f 69
    0x401c5100100425002001011b482d56012210320004607038206200d1104948604000c0c4107a029020850301586170b081440c00f4a140c3c04c0481703500c0005405440c019413503685010001e80c015443c095203003e02415003000c10825880030004040c5c030f00b00d24180314544030410007040103a8100d4808801444407004945e00c44800c0e00440c0c0c010180d00401070925420414040d0203101038500031031040c5000d07294100c04109020b004180d40399101c02c0791556040c104000941c058100000c8c001c0703800c281248280b130428560340d0400780e0700911040070b2041210401c09000a03403c4c03040313210404008100d1054a0005200404101418403900b200c40300c1e100041003104c0c442c440c5d01e507500c07030300901000e0385940d4920006264090466170030402690902c1c010300f200305000001c420042e0030800821040d281c98080000c160f204a40c0709003503104d00c000d2554001c50007500b80c0c0142c40c1c1c9401900803841d15801c146040c2121414001c5260403c40071800b107078021425440160800390f00025 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 294880422 1250 294879172 294879181
    0x131103070f180602030409111e0d09020604090c0915020a0f02010507020d11040c090b12060a0510020109051603050a2a23040504171c0c02010b0102250905 68
    0x4407612114240700c00c101c41e03080008100c039500080200103c54103030b5002c120088c19505034080030b008001d850620f010f03113800080740444001c405045882d03842280000c040207642d000a4142e40241c0c48044050b407136290740e80405070441041801441400c071110540121107c00a440b02e1010800500ca548481c10500540e44200e0075103e000790301800515088100e13081000c01940c0d6015040d100c2c40c00c01d004034403820711440a8078221a180442581083e128032508800c94030003e142036000202050000368540e690b500c1d450030000380784c0002a10440c0d5086c50340c14000083e14001c4080005081040080c1000451101c01e54012035000c1c402442411815446400020304814003010064040341485030091008150390410b401103550500d034000740016510103c80c05000a10084044840003140c50020248038941400c1d868640718a0034400f0110790340c0c49114030042c0e640f6204014556010000d40ca52403c00120119050310105c590303102e5003c81d402004c003100d0301c03100442c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 294881672 1250 294880422 294880427
    0x40c090e0f1003060207050f010b0a06021b06090d031d0108251716080a0e0303061203040b0d020307261302030c040509031306030209060304030f11060c09131103070f 73
    0xb0040c561020341550768003140e0402035551402c50a491003107510b8100c1c21012031a203000000115030030780d009400d822480304001c03501401c8104000340c000408010141c519910f4154070b9501d0341c42901c81c803001031603010498480c3c0e240500007506202001c8240310401000000e40080f1940703954490078851550741e822950324400860034101c03504a0801d122141906042d8400342c140f01c1d82e01c0110355a510503002c003c0d520441502d08281d0400c00100e403844c1000d0545a49501d441c804a0b0702c0d20f9590b0441c0141644111310481c0c800794080240413039190310001d1140944460749400305002507070700500a802034094a00d03032140011a44100454406101100705a48020010002c070b24082c29100d0b01d0358084c581c0032044030145038010400a00a1003640c00d940030281802d03081d95540d99040e00d100704a05100d00c14401c0401034100090b10030801284500c42c013400b0300c4d03210b00300001800844a8a0114520036034140f00752409034400c041c2c01c0e42e50100141ca0710140002c01c09409 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 294882922 1250 294881672 294881701
    0x4050a0b150a02010b041103060d02010513060305071e09061b1401020a0e06040f050f120105070207052b26070f0b071b060504080c01020414040c090e0f 67
    0x1280d40103110030005901c603508001c00b030680c0b14142d40013805640340040420049944102ca89884003a0901c00701c0c0b402d080c4006080301c12441818464034000c0c00e5045180d07500300607804040084c1e01c3d402001005a40114910002c00c50381d10300d0340d00c54044103030250540840d4003c00d07007000030b43d030a000c0c140b080300382514a0707894000444582c41145130060038040d610000022010401e08940707442075092120496044540f01688441e0541c180300811010303102400720650302c07c0702c031106070006000c284566030107140f85800a1894600d48404d000c0710a0110543c01c105480c0b00c000154065076134507001000310381c861201424a450410b600941100c0c420183c4007204003c60b103042001440d20040380c2142c010503c070307074065842c100121001403244242d00410380701e00d0042000140d054005541103849010114100700842548a00b20b030440d1b409942c82c00c1a40180501900340340c440e00021702980d14128100e50b051130745195500304003414201d601020040011415140b0100 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 294884172 1250 294882922 294882941
    0x3190e120a0306090b090f070509191509050604081504080412030c06110304020f01031d061603050c0310030f2409050114090c0d0501180602120a020405060904050a 72
    0x4550703481d00c5200000400800042c000d0003086454034400003101d14194480ca40700e4503180d4a001e02079910114111200c0d0060211603070040c01517110601c0d13200102c480003002e01440103014201c085140070041c2501c9003540494080c0c2d400704030602144101151080c0c820b0541e001c0381c0c559494a01c1c1540f9140314036800034038468080602c0074101940b200880038803500541c0148405039015013407a1481c80141c1303009500a035803101400c081c0d4003a030008005d074201d00002d1280c085040c0312650030600b00700c0702d9042c1d00c42c5a1120008054041c03086580080b01c0300c0c0424107500c0c06c00303000042c2109900000d0b0181c03040c54891010000442c40b07000d0310244101101889038031140814020305144001200c99508100c01d0b0345440320b540030f007070703104148140c0146603480800f001d00505158204007550155220200c5820341e011350704130310240d180b0030000187d51304141c0d02d0110721031401400c5130183c0e500402041003290780740800c0d501d000c03208540000d00c80c0c90740301002d401040c0c000e0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 294885422 1250 294884172 294884203
    0x70f0203120a02040f0801020a0509011b0b01030b0621071a04090c03020301140306060901091a1e030d020609030304060213080f0a06061401091a040b16060b010503190e 74
    0x10000b207161030350080c0049072100903252800d2501c030784001d8280e002d509400c6001420a00014030345e584070b03914140d0602c0b107004040440140644030102901001d03001a030f489c89510051002506103c2c1e10340151014070807244c40421880250151a1509845400c0e0854031310001402051a500202d8005205002e000c00040c400140040c01942091103200c0c3c04029000fa4802d09090100d10148150070042c0400c60a07824604020000d00349031010480c04240a4112440c9071030f00d506488800800ca02078018210f0004105840d22908036281c1c011174102200303104040f240001501d401a0703020300050703101d40c0845030307449003690560710100701807155000410b2011400324884003418080c4805109041d16076040c01841d051003d881800151043c00c10064000700c6c0b00d0710001e50401d03040c036501c1c10b95140c0f21150310341c11201e00c6c42e040e4400c82004500f00100307441a038500d0358003820480d082d403826280f460380054008003510b014035118501000611070911070540341102c000d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 294886672 1250 294885422 294885457
    0x60f030403080f13030f0c050c0409050a060b0d08030a0915060e18060c090118030218010905070215041118100e01051c0311150424090803070f0203 65
    0x24140148031180580760f6051507450f1501090030880e64804105580d501516450382c800703001d907001c031440c0350000c40c2030385e441c000c146101c030321a82c582c06941c010034052001066840c2031400c00c00201e81000c5607186c46400c0344090003000580798400c1e0b036030003282140700141d0310006007016880d076180760308651246440e00d0390100e0710b41030011003c0c0c011107055089500c000440722a2968402c0240d401401c044030030300c2005d01a61181c0c40840900d49000b91410f1034543d03ea01003001d402c20001400c1c403240e400030050101003541c0c8501076000100b4401403c44c030240020145076104c016001074a1b010040540d0700341511924020101461150740c0314040740f511400065a4405c10301510202070005400080e4900e0090840c4c402007160076191a600c40c541e5900381d07581344000801d1072141c05001448101d607400392054a20540c0107a0400c4034001e180740c03c001850b12a80991001b00e441c1952a402003070280b420b80b58440e503d030a02075900001000182d10354010271055a0207000c0c40c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 294887922 1250 294886672 294886681
    0xd0819090608060a03020319080d150303022a060d0e0f010c02011d0d030c140313150c090509060301020d02070f050c0102070b121008150f0c07110906060f03 69
    0x544910200d900c560349890071034840c082000313404000c61101079450390108484000704500d4101c4a10703103a04c100300c594907101c42d004200c015903c640417003d0b001400039070100180741e0144080740300e002072101050180303050b50006d41d02042c150160b00b4003840e004070381d107c11a441c40d44135400700ca0200c400c44202c109081402c5010b02030001e0000015401c24000d0f80083c040c412071004c2c841107401c0501750180343c90004400401ca10303140384081044800d02100a0207511b8000c41c0a400d54155a4041c4895070070000c80d60100c00882040551401810703007607123640401c00c1e0040e51801c641d000c101c1d454050010380a40103c62042a816100283e0f0000300840c08101140780d43c800d5040e6000350041800584e1212400d200f9030030200c0c010000030420f01c2400d044a035001c01d900300302515103601c6000040c5015030510581c070380b080041f028855841440d0720940e40c4058584179044c41d101c0e8698886c1c1c2d1250307172692401e004901c1000801c2c1e4680e10402030368a00030304118025100d142 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 294889172 1250 294887922 294887927
    0x905010902041505130b01050910020303010603151202190515070c0b0406020a0821090a0c050a1505030405071e0905130308060d0302070306020c0d0e0d02010e0d0819 73
    0x501040403403195241244401c04402921801d5088a000402000c8280c43d1170b000b51025144070341500341041030400040286540d030780c0750485120f00c20760040d605d940c10b051001c0d0031244103188030307100c0441d0518100700601840c004410300a905503030030240c040116001400003d8250005c41d07000045030702c6c4000004d0030700c001d070070301c1401f801c1c84c1c48000d6038469940c0d000d44075501030440142c02c040d200d840820030a00c0240034a520390740c42280303107030010750f803c902a880994000b503e40d00448040d006000106246002a240c2150400800351500d200d0280b242107c2a200050010220024051000500850300103202c960742260740340160b50741c070414041c06070003444100b41c0f500022031074801034003e100b0b0f034055041e02c401040c1d4684d9810045181540c8404400714803440c1008800108240042c00d5502011001401d007a410000c000e80519207100b41140103d140b1045a4090703a480007421160440940e91258580d849041161413440b6240401306145e001c0e100c2d810020740e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 294890422 1250 294889172 294889181
    0x1506030905011104030506180c0303160201170705031f0506070303200720030309030d120b010c0503030f1902070323071a060111060f010509092a06090301090501 71
    0x1d21400081090390301a00405449002d240406071441d030140c80050b0f11186141c21118000b030518085031900170280c030000b8078540c402c102845142403d80303940070842d42c00010010031251203900407003c40c0b0304803000900c41c2c00000c0ca2080300e042101001e40301e461001d400325001e0300028000542e00d0f03209041c0500070303125400301c0d01400055503005c21040100c40302501d03c4164494180d0802c400c40c06a07c032000d4100c85101070307141c00100684802d542d810010341c0c050540545880c41c203c4402c40c1000b044550022055041c0201c0e24900000030707001108030395001c0802001d6078500c1e21034022110802907101e1101c1146071001035400281a0040e000303481c0d00709031030b00d100c0d500c008801d0030412500410348000c2080c41c86115510400005602580c0e00010600d4001c0e415900025028a00070040e2282c118100c0c0345001485903080c240c00255216588400411040c41d07002400b6140016a607003020750082002e00000c180d50ba0b00084802c0c8060050081c0030f91012414000c0c000c0c03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 294891672 1250 294890422 294890441
    0xc0a05070c030c030b1b070807060204150305010906080316060513080c030c070f0510030507030b150913020a080a0b0105091f0e041a01030f02130e0108060c0412020d06150603 77
    0x83c1c44240019404003c1034442c0c03032406d08003641d80781080301d50754501e1900c5e00300d00812100d03a5020710010494104202c80c0106c034011030ba070041095450012906c04441d0160401200e03a0003c01c4064100440c900f07240780440d42c403510000d541e644130005103494182c00cc40003020348600054a694900000018054008840c025604020360356000103c0300e050a11455810a03001b9850865144c0079520842e401200c9040c08503009140d18001040902c03070160032400d246010401c61400d091042d1210340c600242c660451400606110103000b03c031004104000c1d4035156010b00b0380c50f910610070f884040c00c000e8400c50301da6511107260401c02501040c440300083c4122800441441d25005078074080641500759485040550011409815803e4001030700316020003940c000340080386840030092040949800a55040c01c50b10303420144003038030700080103400344070900c0b03441d410704440109503034129010408481c840c40d208001e84a83c040710b040607070080e20300084032034160b0815000d4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 294892922 1250 294891672 294891683
    0x31306050103080a021605010c0311070510030e011109091f0503031306180605040b360306011e360b0a080a0b072304060905040b06070b0c0a05070c030c03 68
    0xa00c5c4c058140d00d1b01030200e4071070140019400c0344141d010a001e21541407048507500700380e0b09481e0716800402c2002d07901381902c01c006552100c5141c0d18400c00c3c800c00071400100350040345003c8900c00002d42690303025010000b1522400d541da10545480e007074280045c00050203030394445c000c1c1841e409540c0e1491042c2404640100c0303041038641c40f07260100040d200301e0f4603554201402e10a02008581098014480707104d03011941e58501d100b40b42d807007003458070f0085ca0440c1c04011007040c90704000040e80300da250202046054142614900c002e80b003030701c034032303602c0640c103c0700c40c20b003948001c44030b44e0442440300c1c02d4a03001c00a04245401116a01c20161442083d80369104c140650710354036036201a0486140350041303444c9901c2800c40c21140b90300b03241a0000f001d695905a6140d07400350b40200049a80c4c50b00c10042810280101151743e40211211380c00d044154456512090004050000c0f200c40010f00e450468002d4094410054100700041066034a0b4a054180d0300120302007a200c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 294894172 1250 294892922 294892933
    0x30d050f160201090201320301030507062a02040b040207140105040c140d140a080f0a090f06020c0d0201110f010207050c041b14070b0a05041209050f0105031306050103080a02 77
    0x705507005018896402d0303410380d80c1d22850341c8060b014032040500240c0d1041e120300c1c101800c1d000010850040c5000e1801031b005880141e15001c000b61540c011901c198400c0c504808001c220550010034801201e50161030100c0e510881200160080c41000002000c030042c0c096142020003055014503c41ca1068080c2071005496a041d09401220440469404448243c50000280f0314443c0c0080c54840d502c2110070420301c55a815460790003420800e007401c00f01040d800040c80e1303c14100f10051071a100c082169034201034000352a082c00614060085815841c0d020469124038580502c2031194000e40310000d901c0304d18103020b507000810031390700303440340c9074462405152034450965584400010402c44c0c058001041e80e1001000300c2c0c43c8144001408690089185a000070b4030448036400c00060303a1400d0f00d000101260300b54103810400143c80c80511441e01c40c8000c00c00301450908045440f540e4520255825003034028005061310304003000001000200405025054480c0d02500c4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 294895422 1250 294894172 294894211
    0x100c170c070b071b02060d020d11030f0f19150b0f04032f094b0c0f0904021303050a150e0613021809100608060c0714030d050f 56
    0x81e070001c6104150302414480313008483c010718010b00145440c07148100c026040550000380101120f64141c03022006440010801640d10a10030903207500100000700c03014182484100401d01100c84520110100da85100e18903400a00c03035440c1d0001e1104a80e40366680e442003100c0411a00144402c4507401c0c00145961400c03601201031000080d5446440320701a60341c0c1702001981d4030090a000c95a030983c450900e0100d520300203c0e03200161907904d19102d401c9850f09014104080c6101c13440050f8080309110750881550300710b80031a10401c00c85510355010701c0010f0000d110b00040c0d00b010180441d400410840041481100c50307006010046011089000201c1603031034003200203549401040c001070503042011000703540b00f40082c151049603031080c0c028201c440c20940b4004210740c406426882025052b0054002030001c2001402081c10041d0441126001c1e03000001c1150440c0703170340710f01146810425640205a0104144640d0400000f264000441500d800c402d0001340c41411 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 294896672 1250 294895422 294895427
    0x1512070f05060c1b0121090b2401210509060a050606070302100207080706020703020c13020406170604150e19050c072004020a05090307050909100c170c070b07 70
    0x50f0074005401e005009030720f00503840700c4c1c0110000895030b41408100d643d018050019003031907040d0700424080c005002000345c20f045103a1326009141100c1101c00c451115141d640d41c003c2c0405c9043c0a0829601803003040e460b81c404035440c0da412141c19454002003004180001032401e000b4048071a0410072620b905062004074883c800c0d0140160f80228840403a00c21164002c01da2980545050b5007040c5040c1d588005030303130182e1000d03001a8000403110710985000a00c0748110b140d010340440c5407501d0f0807409400107c60240000701c19a80c580064411303200c6d074020f1110001050500303d85c980c0c850452450800741540c42c40780700080b4040448441070584500f42c0589518050301c0d042420710741d1403900907440074400c101c1e03140d0004044515070725680090450081d00380c07200740d00c074807108060602e0100b140e88040c0c440d80b46030003404041c0a001c00c84031036030360f030b902000300d2a00100c480640d21505018003c00c69042c203942002000d014102c00f920040380700d86080d561039210000704 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 294897922 1250 294896672 294896677
    0x9030d18051507080903030706020a030b01020c01030506180618070206100f0609180b04050a0209040e0712120306080724031a0103090525080d090305030708031512070f0506 76
    0x1602d1181e00200204008a032211028001c01e04008048a203082c096035150f40907600410700c800042a190110725000b507805002280d11102c081c0703810000c500e40040007400b01500982004610600c01d0702044c12a15591407c03c08003820040307060741e900704510001d5540d503040380c0750180e1082580001c0350340c1311200041802c580007543c490b0350709401c05210705030003103034001c6600000c0d44d1240307880b000d6202d50141d1441080f21741c0d130058941d02000140400c1d960790608200c00340d0026a000c0c02181c0c4806299481c2580001c1d200e13816052400c0c0642c01804542c00c00c0c003892080040008042d01e6810100c803c558250071000141200c149040c2c040e190540c0b41c070040380b8005089444503500c241d01058089000780210751a400c07901610980d40c45224101d145c20900021080c8a40c00d000c019150444c0c00d2494078511940c99900c400d0f4a038040c500000708008000808148203058a0105050b5003e008001906520540c160195508807500ca1103524000c0780000107104e141c02010b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 294899172 1250 294897922 294897949
    0xa080c01021c0509040e0c0a0b220b030f040c081b010314060a05060c070306110403050706020609030409180b1f3003020f03070501090204110325030209030d1805 71
    0x750389013050264070400c0040c141071812080c05128221010f03005651f540300070750050440b480b059945412170010080900003a02d020728024a501d00704115807200e813812682d005000314a605480c0e100d901d4503080d0980c41da4482d1081d80314040e1800c1400c908466001001402600c08010084540030711180c0c61104a41c0c0e1584200200340800c0a401d14a004200d4504202c0035218515160354600c01100c460540030342c50800301140034000c2040c10094400988081c0c0000c09903460003c241d16500c0c882c40c000c03581d01301c1d144d511851403000901200000702c0c1d031040030007078a45022110415090703020620b03c02210811400020f00d07080004405100344c1c5c4001080c0100c8940c80640c10524100ba58200c0c11403280e160654200798060002d820064490b500100b8820341c50f00410040d511007010044203034400300180140d010130f00d4543c0c910400c206000e01c40302c89040380305030700a025294400e901401024812510b1035400003010b5101081441d40c5000300e6260380602181d55803095 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 294900422 1250 294899172 294899177
    0x1b010e04050609280e06040c0801090b1b190503070806041509051005030604080c0d0305010b180a0305060c041a09060f07061503030f0206060904030905100504050a080c01021c 77
    0xf0109448450b031250203582240d01040e40e26068200c6800407045484c11694008950800010310042007142c520303081c02012803000030700500a00f912005c50018004c4d02d41d001c0345901c0d00b4064030051f010029201800450a0322840c91304c0060300143c2207500413159440000e01c40300015071180340c548128844410f45040c2d281000d401d18030510010880640070010344c00d6a2840001c90740e07010050180300d40c1c400d2120075211101c60007050b2030402401000f206050804005001245c2c02c003040d6100d204c4c0000c2e100020f400203c02203100c0780155080684075014070f00404c900405240000c00031101c050201d800c1d074680e13022120805001e102c00c000c0d4052b401300a41c0703401014600103480c1240c02090f0000f1080742c281c5034984040e9503540100e010514400c280400150140b0200b0340c40b0030150f81d880c00d5864269002003105019000d180d1140701d005500c012840d2241d019200503002c09802400d07059142e880050f0b891410b001c6d003d005100b805050003041740900c880804a40307854 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 294901672 1250 294900422 294900439
    0x1060803030a2003040320061b0f071b080d02030304020d0b0603030408030c0c040b0919020d0e0609011d07030804050904080c012417030414121b010e040506 69
    0xb5941a0064100b405081d220114201c1c12030996601200003035014074070a0b2a003c008010b281c650f081c0c8054a0300c0e141a145c1c21074003c00c03640c0c120034040b03685c4901140042542d602403002c0503c4042c05265405001c100d9042d4180b401c40345856400000d850050b02143c044008c030203401c80c0e40c0c3c0320844009402c81035107000e40d000030b0000c01c0d070160031910090036681460307120141245580c00034842c45141c0d0b80441416202c0c1e042c0307442440840a82515030a12500d00000c501d11041d82c07001c01842020b90000302041c2007805a404480c04086210694010f8104518414082c04903120030398400034000c80d0380d11910000081340011268440d4070203007032500d000c04210318240d0060007034541c0d200411115003200c5081c803414684c2006542d000c2c840c40c0c08900040302d240380907005009000c50400b900700e01100000140c500315400d02c10114030b40c0030810b02092181c11200c444c6004e900c10580c0d1040803c0e1131410b4117892000a03a21910140c481a0030001550707020384484d80c000502 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 294902922 1250 294901672 294901681
    0x705040207021c0302060a0b090402010f080702010612050a1407080d14040b071b05010f0219020f0907050304140316030c030e1201020a030b060903030316110601060906020f0106080303 81
    0x960007900020340001c040c078100043c00f010020020104a030200c0058102c0d804002d44e200891203030800340b040540d04100341c0e00d003945c0007900b400c46010103074091041040000b04860301c05d41114010f00380142c1c0c510726001711490b04076a00c803100c070030486200d80d445045c8540103d000400504454500006164020b205401590f880784104000c17070f050700d820040402c4c1001800c008000c041e102d8403529040110060801401e40c080703400041c10400c40110800c80c20381d0009140344440d030040404190781c5181d00c0091406d803880614242c0219800e01000501a00040a58400c50041c0e50010301c007864000c1d80b5480380b1a241c1c0b0180d20a9980d2a80c60209111b042004099880382c14540c070741302c0c0c5100000304805c01056801089030740008040074416894000c11070001d4041e910981401c000c9000652240001413243d071341c40d6448038002074418400c040c07c89907107417400150b03016540c48242c02003203c0498055080544502103030105c9285051040204440140000d1815500d6 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 294904172 1250 294902922 294902929
    0x4050702120a1215060e0f0a050114070b07170106020f0d051b01061719080919090c0c0c05060304020a0311060f0409050a05071404032d1b08030c0705 66
    0x4818024003c01000b10640804440e0f40e00c14800d010500101810b2400c0c0b0f8090020304056007115220700400030180606d540ea22400240c40546400f420034010b42c010303202400089004e0704c140603003c002e500c824020481c0d00200c41c80d0600003015108481d60303072502c0d4182c4c0d4614440001021590054189184081c414005026020403510f40105040500281542500c000d03800c9910820b01c542c944044001080007000201440e0880130100907a46e5142d0044601031141106e00800c400c11880d401503400140c07100c00340180103803c122888140b180204143c03110441207524408000c0e0114242c0f500400340c9125030f600810040d102800d542d075988008022892060700b280003802520f015290f000301520123002e2a0341d0001d03852800114280aa40300039019406111321141c1608031101c44408031820340b9089160340704450405e840403030402500380d04842d6000051840c1c14208000c0340c0845200c00300480f0051456030312400c0c80358903445007108405181e80561820006400c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 294905422 1250 294904172 294904177
    0x1504050105090130020301051e100609030602090316090e01050a0905030712031112041b0302010210020a050409020f070309080d020a0b150607030f03050c12010303050306130c0203070b060405070212 87
    0x1541407a01300e0003c1c02d194042802e480d816210a866914100c0d80c00e1740c02c0c00b40f00341e516440511001840c1d03400303103072410207440d1151901000e4860741e000603042a664074104401c8903a4450070103034004880d86e480c5004000c241200c00480a0b5003410080384a8940c14000c01c2074158010340614540311142d0b42d0408004200250382041c140c507070080203105401c80029204601040070244010301e46031400b000480c101e040c402c800a018540c0138400f60364001342d107603100d090541005039900040d0b00103071154042e50b071085080b103000058a00700740100c0d20291181300c1c40f075158566001c0d290761000d43c8480388542c0500043e0b0112180c85c4c00b00e00681c0c0c0c1d80f07400010007821440d1440440d400708450f580042015000704041c01c1032800c003c0c1e0325202e2980d016800810440c00e02d10760611298101c5070610014041060200110384207558003182480c814510103000c001d203480c142c1c4c02948942080c6e01c1944d00d680307442c0004041d4100790092606c50352056029000d5000d50000003d00d94 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 294906672 1250 294905422 294905489
    0x1b170306030c0603010b1201050904030806191802190c1e060e16031208010303080711010b19090b04021e0f0f030a1e0c1706030c04020315040501050901 67
    0x14414020300a070b07243c4030000150b02a20480c40c0c035541d07c0442d08a103004414069100780e000398044e50801c0003190348620384c0791f0401000c4405001c900d10481760110034100079004824808100d25440e00001541d60007030192601da081e140c1c5406c0d9010300107503004240038001030211540481c0c00e4004c24040b0481c107210b203116840010345855403e5000c1d10303044500d0488445101001c4040c000e00c240c207011a02c80203080d21f0108079079070450360010300d05280a0940130a02c00e0144c01064002c10070b4007c0015440060200120306d441e240071407180001511030300104031300d000070342c54090415000710340c400c50000e06045001c454945049140da4000c110200e40700c10305001c04440491041300650044800d0403020410f41500ca155041da0303200ca8207000d103400e10307002c1d41500040e002010104900b5451151180702e64038400404e092164414510344e11a200108215885414203210303400c1c440e09031000c02007a0f80350010700400950a0041030260018942e01e5400b000411803500f40700c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 294907922 1250 294906672 294906679
    0x130303030e0f0a0f0c08030a050f0a1b0b070e15160204060b1201090515030a02090c0d09140709090803010e22051506060a0f05090d051c1b170306 64
    0xa07240d00102c0c5080a46405080340d0036091105007000303200017610300741e01410340384015502d0b28143c81c201a0040c400e0307446007400c240010802ea07144c180103c1051091942848001440da07400d864500c03607d0204072030100118800303001d254103605050344142d82004125a80d0b61a00550305058482c0e1201800b0481e03209850310004241b503000c4501403d0b000001461081d102e5041801a4080e030384010448104030f6004440350130107940025a0042d03050b01981c41d110070fa20b90a0b032282103403061007003142c1c60a0030445100100402e464690703101803000b80c01d813120309440f000410180c403860b403000303400c030b038001c1c0014070064144001040c0c016a41100c0704540c800c1d000c1003c011000b0059003959039030020401001080d601803010f6600c0301d001c45500307203800b01101002d0201c0c0c58a0b074641e0708100300070560070115150110404883ea80160407280c58040110f10401101d401010340c0f0f00244840b82002500300198240321080e9900a00060720108280c2c8140c207145c10050100d5403 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 294909172 1250 294907922 294907933
    0x20307230d20011e09020a05040c09080f030a050301170102160c0303300906110310051003020c0d030b13050405061f0f090e2b0311130303030e 63
    0x40c1080241d50100e07503441d1900356070001c1240003007042c810420508803075039040c80d401c5203145600c03001c0c0810056140380b001440100701c2c00480c81e0040310341c120640040c680140d5071510758010020408507400c0b003040b6002a01260502c03034890041c4000100480c500380700600c40700001082c8582000700c0340b00010300701014118624110a0300103400e0700c82d15109041801416440036412240159007004071100788045004504500d01c010780000e40a035803404820300300300b425002181c51005032148903440342480d00c09603554080c54407a003846042403004902c41a4060b000361103400321004040e20707004152101c15000b03414220304a40c3d000c01085845007c0c01e905200e9079010720f0068004041514115106540c4c5203840034038240441d829074020418404d541c80300c0015961031a00101c2e04041003046903142c88110300405082c140c0608e00141001e001c07103405400e0034000da90034080400300c04085034241c0710341c8110742c4040c80150b0090001c64026040000c0d441d0341c1c84100d03031 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 294910422 1250 294909172 294909233
    0x309071208031314061e070f0c02010f0e0a0801020a091a0904110c0615040c031413030c170703021009030206040f151a1525020604030605010602030c100c020307 71
    0x178140201210542d038002c0401400d8104c02c80c1080421782e119085060920f5a8120b180020b4400301c00b41c14028100b204071f502d24074405100e2000e695000d03601601c0f2030b080d55110f5407098042c2d0040d401c00070009011100c0041c003410070428204140e1a82040546419000030074000a0800313229801c00001c0100300d00d001c01c40003005220301c00c2d07d4590034000d448404800700402d0b511991000d400305418560103104021904004540040101007140c4029420b85030942d001c0780d2851014041009a4852844144a490007020384911a0342030320f000070b15000f84d410440702c9210018005922203000200040c10503082100103070300a500d20486603c02d08003100594404603018601e00c440c0201d0310740c80d428100c249d1810180d182107034500b000495207443c3c908c040c0d211302e44840e2044e0409000103544078032007250301a54204205200940c2c4545000c0d50740d40c0883d000082c3c0741300780012480c220845124a92041c821507001c1c503e0400961501a2010668080381140955440703c40 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 294911672 1250 294910422 294910463
    0xc041a0a05071a10080c01090915080109030504080c0105030c0a08071709010606120606080601050708042411070f06030c02160e0708011a0f250803090712080313 71
    0x1d80b0f1070480300c007484900340f03030081021429415581c071110040d480032006030616078100d00e80c507017520140d080c00200344611120805108940c0e40c412000f80d4645aa4070040c03660120044c0203691101085401c00b640000c011280c80c8011590007100182c00d1200c41500e034858205260452841c1c170b0f208401034501460f8020815066031a400d45039540c140030001c1c207401c11180300101002c0b00003006442d01c0c041c4003808061000b05000d040142c005440c0c4104603d850654015140c0441c1004241810800e40c11110001d180030002241115840c3c040e0300c1400200130064905401c00c001c01c1519104013500600281c207003481c01e46c001e400d0b8090040e0390f4500100001d20030a044450315007481203002c0c05065044e0814a010300c21a0201613200710903030201e9400711210b420701e5584001c4da2910a01c074010030710804803050342840c080414061200090350080d030b1140d0a07203404503918506075011611105005100640500c00502402e05241001d000b09010703035009141c0d4803820048 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 294912922 1250 294911672 294911693
    0xe01020d0f0614030312010501180e070e04060b18060a03290f06130b0d09080c0d03060b161e022d0a0302031e031608040503060c041a0a0507 62
    0x701585035840000704030f1101c1e41005188000400d6025500e44021100340c40e02c41d0310140200c40c10b0105948020507c0c400c0b12071528010000d802e03e02504d801c0c44000200008030005003607110320f04002011907648a03030402c51325960102d03012420307000048018028107800c5002c6580078580d03244403a0034502d00c0c0d8400c501c5408445400031100183e0b0204004800c4660707c2964001c007020b01204034040041c14a24003a140d255055603150f0011001c500050b02c0003100c02801028081081e0300058030005601c240c0d0600d5440600905403100d2105005001c1c010101c2012000c100144004c00d250f00205032003a080114902520340080d004200203481480d18600303110784c0040441c8036420001210340c11400104e604482c0b81d86141c00090f65511000c0341c02d1904035958840c210708038030810031246099400d92000030300c40014100000e03140c1040c4602400390281c10000303488072044ca01181d050b2401a007000b0380c0d48150141410b0f840e0000c0f03901c802804401c21000c0c02040c0710940 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 294914172 1250 294912922 294912941
    0xa0f0207051c090e130f08070605090f01022a071a071a010b09040203061908030409110c070b070c030501051008010c090501020d05090414040b07110319030e01020d 72
    0x148042c110181d003440c0004203003002001080300800c0140302101e210710031660082c0250400940000141c24005541d03180c841c0000c01e10880001e2100801021360461391040c1090400e0f6040c261451100381e00f40d120f005419210600200d5645000c48101440d200c841d101140889000f0b50315040b0450403202c0c0c940e5405000000818402d080002a000700300507042d01c3c9407856041d525201c800c405600641950303a11403074000c40041d10035110310016220344050b0045a013130190381c03590b03015104da0080c061400300b903003001c1c040c00c01801c0010440d04103600401c01000c40a18251512600c1d4010340c030704030346103190b0810010101d9824050326002d43c0680251900c980d14208a25084590000000062080d001000c0019a130045401c040c80000c5050039952600414001340007030003580405e0035030003510030a20042c8920125032070320a0425840368584086c0d0032075880d43d03e0082030721008820940800c5007030810300c640c00c54440b01c200c03080050300380900c03094000d00b502c6201301c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 294915422 1250 294914172 294914183
    0x9030f0f17150307061106010501080a0207060c031d03070215090102030d02040915050409120822050a0201020d0207030c050613090504050a020a050d08030c2b2f0a080a0f0207 77
    0x4204425510b014000c0100074526410301260320801b40d94003684034503051081c103041c06030000c005010440c2940480c1e8006a0040c000c01610602082c064000c01c03c07070141025000780c83c83e1904148400004940c0010b4005024403030039001010074a4440e4440c1d56140c1c1180018010b0320215980d0340003400241c0703900e07003001c20004140e00e00c0070703c0e04100d98069803113142805408400b0070300348001d03140b4143c0d06140c031181e1580c07800c01c01d150601c2c072b00144880b58921000079806100011801450a0340300740d081d90030349018444202c0ea115010700000c0d01e4101c50300c0d8200124903080700204244040c41c107026030b00a0744c4401880442d0011101503613550010540c80085251211030311000c0d000072500c1112002d115120462507020040008510080010706013450200d00c81118188100041c6a0500226000e607050044c1841018100304034080104801030800c15200c1c40344058003070a003260805c44c0100d03040705c81c240d02400c00180300d5555040a44003100d6030004010290241 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 294916672 1250 294915422 294915451
    0x212091e01020c1e190e06010e031c030203010e0a022104030306030b16030608070807120f050102040303090f0b0909070e0a050a120309090509030712120203130203060a09030f0f17 79
    0x40b000d1202a08101840381d0485c0c40d08501801150400e00045030400001c2c40c2c1000c4401078000803038034252141c00008440003440c3d04090070542d242d00110b0584802c001100441d884a2242d4070030b030700514101e002d040d150b5107a0070340c2c05160132401f1507000d80a8900400d800f42c0c0d0b030721650030344081660380000d20740031441c0c0e4089240d0907024200040111074018105c480c45c081545071240d0450080c0100c2d2108605560b033881407210318403500e40d0f000002190344076aa481c01034031100c1544502c81c0300b80e4135440b0010308003032840140e841c4000d020388a48002e42d02e509085420700780100d0b0301544440d188001041310b8130b84414440103000507141c48528030b801400c001e404c071403150740030050260800d13041201d40040801910326040d0710a96050f551900306100343c4800a4802016021510100c01c01c0b280000b034a9240c10b07681d0003507050315050f440340b8014178240c408440d0050f01040151090f9004184240e0440e15000c903685010071174244001d100c254200e6050780d910000c418403 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 294917922 1250 294916672 294916729
    0xc0504030312060b0412020319050606190e07180603050105090609040519031808060408040b0c070b0d0915051b18030303040506040203012a030c0c080a020d0212091e01020c 76
    0x40040e094294021258089c0170f0410395261a90303090010640d070300403901a00080c50190041d94484060301d4448120480b91604280040c1980605445003201c080000f00020300c1d58004e11803281079a401919010f403d030f54260a111200e0301c00b0700200c4940c840da441f2200300786004030001c01914866611000004004003c40400b40c1145e00300884680044c1d09010004d0100703c1100d04035088240f000e40ca580e10003103200c0c1451a5607002031200c0e0400a64550110805e600c10714003248503d910504100c40704603510101c5404503528401411a2110141046d036118080c01d001c2054106003148800144040381c21508140c400700c8803a48020180011480c003130080c0c10307000240480008034004c100c402e0b5403201c1c24030184141415030700d88190321138034810078108a00e181c0000405a8032a232030800295154030040400700140074010040c0c860302240d2040702c21400c1d009003032f102001450b680001304411414505412f602c01c91046c81800c1d150b00080c200118409100a2283d010 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 294919172 1250 294917922 294917929
    0x60a0509041218050d020d0c0e0f01052707030f1b05090f060f190309020604080604030806060a120e03090904080403050c01030203040804030b060d0b16120c0504030312060b041202 79
    0xb1065602d1095100108144013945440c0703249600030b074046400c000001020704140140400e00d820121440307945004100034140300e03c1049040350000e41d503081840c2260f00c1c0e680c01da1483c2180303444050f208000490f5086129402c070398000042c000700000d2522880101c58800240004607401045003c11b040b5054901525103c2d100003042e0707002e9180c04050b01d0041142d00c075400118614100510300304108030320990003200b20704d83c0a001e451303690f512020042d42e11603040f94124000740303060300001c9681c24008252000304200382c88420300108200410030140081500c4c2a0462000307004c0c88815958a0500901403030140803030342d58581c11801d0a07814000c4c42c042d00c03810b150042041c080028000c0c0b080300e08481d04544fca010545560380019030540e41618050480b04088060110b1a203008107810381c20080da44418126400c160b01200a440c43c076001400462018081040480d016040800540c9515000011401e455101407248c90700705400440b05c50030302c00b40d10000c40c02d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 294920422 1250 294919172 294919187
    0x100e091609020c0a0f0501020f030f061201110306060705030910030c020f01060608010e0a0e10020310050f0303030106030e030c0307060204061d03100c02010e0a05010c0906170a0203060a05090412 86
    0x440c0007020743c500003082c0340703c070359411215100034424501140040c00f40314080d41964145003032240ca0a0707a07410159003c170b00d0040152080c0d8415410403810002240f814862070201c956103200260941c2d403100d0400c000c0c0d801c455802e40f00c5000c20029100699201422246046070350b0f100010082d054010003460101c00100c415400e030316224040c070085070401e20a40c1150b4480d0301d116a04c5d6a0740f0b10720006070005060440d01032081c40e02c0c216249800760090352081540201c1422a95510310401020301c80c00100d058054004000600c07000788250000c186003400042200d20b00100c2000c610702e9984003078426203405501040038488198810411080542c41c540210f211314410700c00251140004800031003a243c4d25604501031300d000f03400c40e00f418210002643e98800d41070405c279020380500c0109400003230f8a03120206481e8052503000010755a17a01d0184203c0e5075404804000303600240841d540621015000226030303643e440c03032911403880b842440030b602140ba40041c2c242c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 294921672 1250 294920422 294920429
    0xe240409061a0f1c020a090e06100816020106050319120302070203152805061302071a040f0609050d020601053304050a06020609150717100e0916 64
    0x4018078010000544280945030364200303100441341e40d485820b140c42c0d00c0745010000000800d001042c2d100095800001d6601142e44444140032103548510400000794004001340d0040790303003d8081100c2c00c4081c3c401c850616800d0000140c41e40c0c4034000603103000c03d89980c840300c80c000a0307061f804022140c011085440c1d10380c28290300380690307540000c0c0c850740055040303a02290000c0c005004410324000c022071044204400380340d0f0042d000c07481d0025043c00c640e001c0c05182c0ba000444002000e078400ca0307802c9600804003804050090020b5200104003410541d0080c2c401401c100100744d25101d94903c081c13107240108040646a14042c1c1441816800140b041c203c8640c150383c140309503803000c208130300c00c151041070002e035200e8192114051a00300a4005c214424082065500010498040c50101d000c4800f030141036294080e050702c044401000150402c480c80381001c440002068001d04803808210302c2545889a0881e884811505004154050001c0c2c080700c030f1503604504042e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 294922922 1250 294921672 294921689
    0x304030b2203050307112a030c0f0d020d03020718020405120d0906031107060606030204030203070e0112020405040501020d090c0f050d08220e04031d030303040b070e24040906 77
    0x40140d0340b00a049808000d040109000440034001d450100510011260a40c0da0002c406540d8104410b40103441003490f00fa40644150300c8803070342601d8800c082c2032107504010418440f6404035804d100460765840b10072010b6118003100400d00c03094148071220b8080c80307044010f031264034010800c8202042450180e180b50002100034040340e512007541403e88283c0c1c02d01044a0080300d0300c210039441898006401d55203410310200b49198141c00030011280218111000141c03904c02d8011803a40c280300f0741d182458503a1541c2e005040c07541025510a01960005007484010048803095030300b03c000455003071551107030a000d03000024840350007400007510913142a241c0ca82e1054044c0c41080703440f50050681489100d00c030035880d10300c640981400c0210001070b041c81d1902a2041000407a020400120607004022500340002a24811900000764402544402c9001d981440752190496000038a018580d0003075100b5590383e064070140503000d10359441c94440410700b15030032504044034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 294924172 1250 294922922 294922981
    0x60b011d09090703050a08030f0c0c0d030b040f140103020a0b0c1905120c060f15060703030b060d02070c1508060a06050f0d0501090b12011e02030402030703050304030b 74
    0x260281600c80e80190a40c01d440c0400c16480b204040c80c60950283c0c00200103105921400041120f4040a507020b11464490600d29413228400d02c0c09500a03030f590801c503584107004816110b4400d0b0802000e001c0080e0001507103001100e524001e4440045401c0031240845004208605041500100800400300582d08040515408036251403d0301c0c2c036000d003480ba007580303078080c00700c148510103800081410003075850540740c51054480c4000c4501002c640d4244002030341c3c04801000341c2a400384010300c0d6a251040b030b0f58054005160400070150002420f10044144a41e144000c00409004407a40c44425107003c000d6413461000d005c0d0b18003081964002d20034107407103150707095065801f2414590740710440c1e020104900c1c01801911403110707042030000941c10031154409000030505275000b0390f001c046181540c1c281d4241c895418409211214000a40302c00303540a1038001d840242035840c1160340f03440b6203107550082d80003610b0005080d070a01c450145401c03107100703580c8030f030400108 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 294925422 1250 294924172 294924197
    0x10f0f0c08030a060b070b0a150501090e1305030a020a0b0a11040b0d09020901060903050c010f051801020307020607030818061e04111005030a1109060d09030c0507060c060b01 77
    0x1016140484001001603070080040394810520703412040260400f074030900c0d2564003a003031403261090182c1c1d1080b4030b246422070080c0704503015582c130800c2c0c500c103031100000240b41009500710020001d0041000c02545420100081c0d818002010050116070041080d48031a081030f0480b81400f5051000c2e403171400d04c0c107554041001c0d0070b036801c8072a11841203071518203005c3c1c0040a412f06030300c025403104406002141e890b402c001c441c81582d00a600722401c2c03030304000055544064040c3c070140441c1d0b05109881508a1022840026041c1803041d00d05146083e400700d0340e42c1e00095001c03004144a8800c100000c90740c41d140c00121040e03c3e0007045c1c1e034140000c1030f07000c488001c00d40c1c2d59426030110008060104103102c440e0344440150409102d40b009203c0141181c0095910020f41400c00c0c0042c1d40b850301500640d64030100052010345809041c815400081036101e0b01102404004803582012034030610158000b4009902d5011800150b40f4100b01100d0054403c40d052000c18039191 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 294926672 1250 294925422 294925427
    0x12006090f15060a12050a0c12150b0109050906030a05010614031903050a0804020f03030a090e070903050c060309011b031a04060e0703090501201209060702032b05010305010b010f0f 80
    0x80c01150344038030045d507101806080c5541401490300b03000c0c040d68130501001482180b030121003600c09001c3c940410350a00c4920440041d6441c0c01252400280760460070704c85441d01b5103105801007001411180114416035550b42503621680c00801c074405054864517460805111a881d451a07440c05c00e10448090703030f0045c0160080050303441c00c210411000038111348032100e0303141c006540102182d8843e0786418009056a805004041c4500b14000100e00d4950185210500b500d60184c080c01840341e048041c0802500010481411507480756440b044150400c6012a02d5105030f0760301049151003801d6007869152030301c0140e4003540c41d0040400c0411910310540f504000c00780340c085103000c0503061082c05851008418015070400516050094002000a0030b40841300c0c28a500709035181554503403030f02c108960205c05600108085502840d000042c0390100745400c0ca8803030742e2000c0200e45403c40704260000c035040ea6440e0b10401c1c00351307048503000d07600d1056440d00111502d03115900 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 294927922 1250 294926672 294926689
    0xf0609030b0705041a0c011508150415092607171c1506090801020304020307030305072117090607020319090509041109010801021206012006090f1506 66
    0x60128802400800c1059100d00c04844c002d118003001c641161440380250045a405841010300645c6490b004d0a2480507143d04507080303a9805000d4240c0e903034064040304ca610401041141d07070960b15490308001160343d00c5082207460250001d83c00c80800040b040c0010086d91449680300035003408881c4c0061039031490f96041d042c0d480e0125445130301044441c0f2100c40040d40c00020380d070030701041c0c4034031a4062800f441140c0460b9141c0c1c22460303803600c0c43c900300e20090318065003541120100b88080b80c000c0c00203095491154000c41e06000010030b84100001603c0d08031400214004120504095048406500450314101514250410b000f004c0d549220b1581c0165415841403c2034440780d0291005800405c070291901c00325250500d0b1440800300030301441449001c8110002c5000d40c1c051007950000703600c2c10641092900c80100660b045220a494591420088911510300d035806004444c01800304400420f000d07540c401c00141050558002042144000c07001c119090307450011 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 294929172 1250 294927922 294927929
    0x7060809030a2703030e01030c050705060402010810031e20030606090717010b071b0608060d0c0b1c0c0f020705040903030212010311030d09062c0d050303060a0f0609 73
    0x10308115565092184039554010318501e02c44101c08030f20000103040e041003201c58101000d82e001c1110003011802035440d07008001c4003a06940c00040007400550190300b031245c20505090300d502c400c03980e907540d0202c107103400f000b207840200c80001d5000c10810384040c01808022a101038000219142001c2035640400403c594441d00000000c1100c180c0242d10803102d407500510309031034a684507224800d83e87d00944044559803800042400d90b03100c120826400d6031070b580c3e10f80540380c84209c20407442c02c00d40c00003034655003c000e50008128001c417006008510018200b0010000b2060161080350f040c1d44140c02171241c1c01a108480d02c0d030100c1c0712029120b0403500002c01100f503050447c002e0040721710f400c0628170403200100511042200007518094114110742e0752a6140d8400c4562070307943e118040116014187c1d803618100200d07110000005200c01420302580c5510026000b04254901910300c1d070400000d011550401d048100f020b01a194810a900c5141000c0280020054131 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 294930422 1250 294929172 294929177
    0x60a060522270b06040e07180b06030702010f0501080c0303070305070c0312090305070603021602010f02120d02040509100311010503040f021f021504080412080d060b040807060809030a 81
    0x210400c01c0348507922681c01040c40d40c03039a4081030320030301603522411010070040e901c0d038050400281107071506008864190001c10040c00070f19141c1403545a500044c04143e000d95610740000a01603101d0101541c468a410b070f00215130350810414000c1110300c1a0043c0c40941c000e0124035500c4c0d2000012900401c0d81403410340c1e540d00d445c0c00c1501c0440c4103600020030104051408141c1035501c0721105061300d0046007583c180710707550342080c0c0880c4039400e04101c01c00800d144440241d80076080c1e402c480c0c0d40070300503903091109401c0038201f941d1002c44200705a0364042018030450905280b221750050005100c0d00b035840c00c2d61181840e0010415800d410000000001002c02644650100d080ca60141c0001c200d229200d8419011100c42400400103114000100d40e100e11802c00300c40c010741d00010744134907090901110340000441208182d85100e4108a000764208081c4507020080984402c01ca8659007016115418109560b1001c010884c1c64424131200c45e001004a903103008007030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 294931672 1250 294930422 294930469
    0x305070327020a0512010c17090715050c101506080f011e030b0106020312090c010e0907050c0601090b1c11060702040b10020105150109060c171b0708060a0605 70
    0xc1c8000b41c0401555041945c220036a100c40e10342c2c4000540114555860b5a2242810b45050220000001c082150881c102d540706140410031107010260322101c1c800989851480c0080e6905001c1c03610080802840d8100d50791858082c080c080003003100c010302628074105d00355003031007200b508054406000f98a205d00203511003442890300b900403c4000d50307015040e507000d9030303682402070f40340e4000c2086130035070500020000d4014400403e1201c1201c00c140c5601462001000501c0b4210600074400014044108034020055004000701030082c581c085001c60040040c809108440d0100c848155240501d14880800aa101d002400f0700d0b11050366902d4a640d02400050080c0030569950764120a8a24551042c0e42c1e040d0003140c030070082c030b1101000e8071824070011100c0107030b07034496000010007010038240012500703c4d0604403000c1102489003046560418004401110002c183d0107130302040040151803000e010055100700c1c00c41d000c01c4145e00e05800708002d0005902c0d4100011440d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 294932922 1250 294931672 294931751
    0x160e06040c02070f0b032d0a050702030412050a0510060e011e0510050c0d1103090f1915020705010207031104180c08070503010501090c1e05040b070b0703050703 71
    0x70032181006002056080d40c005540341015103050f4070641f040c1c0742d82c200080fa511032801581c5c802e81c003505401c0f80488026070711141c00b04003d242c003504860841c0010080080e8030040002c41d00400f60041019107400c01e802d151103494540b0701606101c646061617002c00000110714110713030441e02c4c0780b10314540ea9040740402c0d40010060390000790303010203c540c1030412583d00401800c00524020110769800649a000390740c03402c00005030202c2c0380d2080112034080e042c480005640090003174040c01041c602c8200c0c0e42c03000b251940014401c810b076103400c0d000b40c1d1360400c408802424207001905a46055494440d40e1200c10758020780625121708070941031b0107203021104030b5160070401e0030303024035155000503880b000544038891280d0300f040c0020030103100312710508118195584410056010000c0d8040e00c0c1c141e40b207024000d000742071000061085100000384016880b6400110191401d000064112480602070750101752800401c4000d402e410300304003943c68038407140008000310b03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 294934172 1250 294932922 294932927
    0x32f1b060919080c10020304060b0406031104090c050907170a061206091103100b0102010e0c0607020f0102070306050f06100503070212130f0306140105060304050d05030601050f03040f0302160e06040c 88
    0x1403203070108140c442c00d17100517510025a4091801248282c2c02032041018803410041540c181c5c0c0800b5102064082007100d480c41c1c41c0d030080401c0e500c035400b0b00c0821503540002801e200c00854800000c1144c20310011180c60303402c810300781c0c451140c5504120300d07801c001e107903c407030146282c0c0180f0003940d80c0e1041d8140f2040ba40404400800103044a0103401410402000381c41810401400b560802030540d0b006400484d00c210034100141c01c85003406d4051f000c0003e19140200141c2c10741c000c4243c08070204105006903032150000e0f4022900906200c014004945503084100c0d042000c01c1c0240014283e001c10201072106c0c00e03500c29503c4076101d541d0030511040d40d0744055507160b46800d0004c204202d80c1c10502d0030031000d40804000383e0b07a54091003020b11084a000b440d0342c020f0028440740e14000c80144d5004081171403c941002c41c2020804c801d940107441c140e4141110081020070035904111b00151740740604112500c1c86d01d01011403861810241806e48980c1c0c0b5541c008035010b1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 294935422 1250 294934172 294934177
    0x90f030105100504110906160f08040e040c0e0403020c040c090b0c0601090e03071a0907030c0305030c0606041b0e0d080f03100603021306032f1b06091908 68
    0x1002040320382408003030300300c01800b144260b0b0b00580c20103c102030ba01100c8410381d0049900504102c0c0741c8450035001150541d030b41e9604640c81e003ca490351801103080840500041c14802041c44941e0a05081010800500303612028040d03407144100800650302007140c0000d010140c402260000d1100e0060310300762202d42141e040c0c0400460365070701411340068100e0407140c42600c100000140881529160300c20044040d21407032005014000f0480d2000046900072451025242c90a84994404034580da4603071040e50389078004101d2a41100c814025540c0180303044904104543c000314a034007800c60b80c00c441d20103000d2410000100c1d51981348001080c0366104698a50743c200d80340314598140c009031440030920001c00c4022503507900038401c80c0d200c0400241801510341c5811402c0303000c0c00100e2644070142814145104ca4810f411290790000b40d4a0529280c48075400580d0307407030402c06c8034a1104240d005d802407200560000c0b40c0085600140c800306c442600003801d1551407032 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 294936672 1250 294935422 294935449
    0x308070609241a060f0d0b1306090b010906200f010c020d140703051b0c10050c0c06070b01141903060605010f0c0308071112031306051609060509 64
    0x501d141101c0c408050810392400511982100f0814903400c2041800307100100f00d070340e5401c15001c01c60760b09010b008601401c0700e01c0310300601207007010b101c5000c5460701c0c0301a2290051162a05400d101c41d810700d0241d510403840c2171800f980c80c1071500d900180780350302010101c00c555800c4210300700e100c20103108822402c41d854009004510503036200a41d2000405c5a00700001c04001c1000c665101d110100c50f01290580d032440e080111045400c150464984107400061040c664000744c540c03148046020b40450544034280c42d8581c105115041c50a40710103107106240030020380d00081d58421945054840d41c00042d103407805c0e03640102c2e00b0400c02440030305da0b4010000000042180c245c00403c00e448081c0d980010b540c00c003402c1621034526284008011502c02000201200e01c220100c15101982d5000c450182140c0c002c81c0940c2d90050310200d00c03800075458a0001d01c8150b001d5250440c0428503070600a0044005c001c0804509004031001c03c04001003104c100d0340d9119035013408 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 294937922 1250 294936672 294936683
    0x90103030f050c070b03040b0903041805071e170615070f03020a080408010902181e0402031e070f08030a020304060305070909020d140a0b030c010c05070f06050a02190c0308070609 79
    0xd03107885d103840075107039041201d080f80e0a2416800060306400084190380c1142c03201801c100c5100010018000504001420101000b242d50300307901c0d0545481c041c121440e030807038072140c0d940750340e6566a44481100424041c01030181c108101020240345045414160300080300c2c00801c8028641242480400d500142c9503c1c2c0202e0701086a00b0b06500010226108484401c0364000e01503ca03402602d080310711203107511110550403003182c50711054950042c4018141da00d0b07203002c0f07160303880442001d072801c0c040b5a03c14001070280c1204501504044c008400095050406205000359a442240100e004054070343e40807641c2c0781d010f00d0520019003c1c000083d501d039070300302079040000c0078011303407004500810070081040300840f03200d5080280380c00340c058101c1556003401910f550744070399411100c41c4500744001608a0300303806040041c1641da074546940300c1c56100020f25000070b102c210758100711561416000640100b030325400700c83d8040e490b40c6c0c4038030702810923000500c01c81c02c000e441c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 294939172 1250 294937922 294937933
    0x304060c060f05010b130e040c050d03020a2913020603310b04020102010b010e0604210516031502040b030106030915060b1b0105130204050c070501060e0a1a090103030f050c 76
    0xc02120035805002000146101c0543c45550b40741e007e06001c00030b0b40e02519801c900d250500030b134103080c00409507140c0203004454545601d03603100c802091880d01e01a1004114601c0701d581c003901d0400c515005503d0441000c81501a500065001d1001800c0f030301190051480c02c8548140c18001c421051081340480d2826451f9030901070b00c61681110100c4c0194a03002d2264030543c080c185c140449400540001e0401e420410001e5401810340110502c500c0443c2d12440080e408002c4441c01c0c8904204003000f991031458200ba000340011410314026006020921238544c0600503241141d545281c00b1445a5450800c045801000b1120200980c00d001004c1080004800100a0b00c081a4801c03d80e058000e0601c508070790081d104030603030364081e4501d64050f28164120b00c3d04014003466991405c42180e890b03d0031038003a0f62000c031840080c2c804001c02c44c0d070340b8850300d80000088071307038184150a100c00180f0303400014000201889960004415a94810f0060b01da406030880c04603034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 294940422 1250 294939172 294939179
    0x15071a0a060e16021507051e040e060303281103070303050105010207050d0b0c0322110f04020703020d0810180506130209090c0d150306050601020d110304060c060f0501 74
    0x2805071000d4000d6410008100010610781c034084142101e0301c0c40d1590280424202c10080351303082101c050408000c020048c080d80b05c1481000c2e4480d4080d045034440b0396529482d0620540000800903c0180729401c18026048507455112100021080340b80000d620406002ca080d03a125402711198010b51002050801c00c05415900503412303507409030204d80c400e9554808202d080902800010140c41a01c404123400c0300d402d038041c5030840750003010342028084d40017404050f0040d100060320a0422005524400c0c1031800c1403603055036007503d00b9072a1000c0d03038030301a50b40c1d900628074034100680c2500084549950090b0a4041c1500758820a4846016203c030400780c1026a115803080803016140c1c40308a04031b208655024602425440700382e0b640015501d141d40141c2c4000e02503a0300d95086040c460300603940c40c00910300c25400081c03c3d00b0500002031810480303a0441c41406086604071032010340001c240c03000c071004c0d40f510300420f80840c40c02070042c10780c194540740550700740b40022 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 294941672 1250 294940422 294940441
    0x20913020d170d150503101505040e0a03030f060f03030804060e030a031505040603050705010516050613062d0b1f08011d10050409021207060816050915071a 69
    0x62425000442c0c061007180099242c84d105802140b06550303041c3e04c2015807910654541e004154800c22190f60340384619602c4000c10140c07900b007100140340d0303085460541704254241c071940c2e5450704c0c406c00030440941841c3c0c1a26240310030780809414041404009000c00406400c140b40038a0080f062782e403140d184501c080d01800d02291840600315403058080790074201440b49104407a000001060f403940b800e03005440541c00b0a40c2c98403c458000505004110200701c03070b82c0104425566405081c82c1c50901d501103810428002151801c508031494030300f0011168658040d0748a03e0024a03905901b00080306003120a15030001c89041c404840030041c0c1028080e030407a5072081d125134a2244192144c0f002400880b60481c1d11081500140010b04140e4400c0c1c0b83d0500c003812950040d02100c074840d2520105034450030005410404109408509585c1001a0740407401d01c142801c607948002a40b40d880309000d014960000310b40d5405002d680b0184014140301c1c100c8080d01420054110b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 294942922 1250 294941672 294941677
    0x14030301080d0309020901120312060320010f0c02130b040609021207080f04110a0e0a0c02120903031206041107060218150d0e0102090a0b0c060901050103020913020d17 74
    0x800200e805410b10110069000303010307a14510307070300600c0e040841e800c0021641002c4c4428000794200704c1e01c0b058407043d10340c83c0c1c495800a903014018084010104c1c1a10108044041c100340d0b0402441200034501c4580008003000710a50403140c03c851a840220701d00e00820080703d04a034441d007403150000700007409034002d0504400310b07090701c06d203a0303100c030300030f9510410559a80c1500f040c07000004000c541c4000038a01e1032940180f400301c4c49a40c61036045800001505c4401135617665001e0a200035030100143d4124041c015411410111060f0001e92a03028050b440c240b040c840304005803480e616a8806032520320f5201026442e480d403030174007400a400c071030714132403c0002800700b844540c07401d51100c5950300d6910018520b8400c5840d00180a000c200c000c40700a990240400d020f41c1d5151900c480141c004983e904c0e40310f55008110502e0000c002d400c0749502e914180040c0301503113440c943c40d41c1c03141c1c40c1a00c610700308c1a10710110f100c1000040001d40b0020511103899041c4041000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 294944172 1250 294942922 294942929
    0x230106140907030e15091c030e0c031b130b03060c0a17060a061d030f030703080a0608031b1603030905030c1021061707080708010c05040611030714030301 68
    0xc44111559408a003581110141d84041d0690f5111132101d41d04c05d8005551680c0c45410305094030307500c0051284107050748400c424180b012035110641760142c080304001c5030583e5102280240f4140c5960600810704800c0708654600401200d4540018062030741c001080089000d0201c41c0c00740b404502d49440d40c1c0000195000082d8400c600c90f507e5000c49440c58045d0000604901226190400c01d5480014584d284400f0031201c046c00c0714682d40901138058002211006955912901d10b0000d244c2c4000030801007045207028010304c03800340c001055891034403c0383c1601540004130ba00f0107280510b003007119030b90010b5180020040503802540d40c0101ca400b0f07000c072000d8014100c2042409010401a400002d00d908103001c542442c070017950803060048100021081d403141b1500c9401080e0200000700c50f4000c2c00100b00c209010041000242007e0000300f20180030444003c04500c520310403902001220451100365007804e004a42285911441601d01049075903007094a0760424171 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 294945422 1250 294944172 294944179
    0xc0609060909090503030705210a0b10021c1404030b16030b010201022d1209150108120306040c05040504020c0a03020c06091503070207031b08012723010614 69
    0x20300c000b41c02a80c600410b088540d004002d9030a40d07843c030780e044075240c00c002d0b40c52010300c144d070f40e0b171041440c54141040c1c01500d031450b010030070407451000e0201903030030072140303e003113500c01e40010b240e443e800c44c203280c1c0141091034125087d41095240030180e00590704050300c040710310720a000014486110a0a000720307537403000c2c880c030385003800164201d008500d8031405203181118440800600d141444811701211030160741440201500e180e00490115074075049030f400340850401d1031400000755401007141d100244070301c900c030707080e448081c0c040039201c54065911030803445c40140c0200142c1d0040c0c10050411900d070784184660a6440b4400382007540540110b00002d0410b040a104548113a5405000003d1038a0048a04101580001c0a040840c080e0000c044001a0445140d05008a10078a0042240d003490001400c64007000046042100000740b64844820314404081c3c9054101c1d40b40041c1d8091000001702c94001008114019464000c0106d0b040c1d07543d038801c240000096 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 294946672 1250 294945422 294945437
    0x9180603060c04140108190e0114010e010f030303110403023105070e130e030301260105130b04060e0d2712080307090902030a0f0c0806060306040903020a0c060906 72
    0x140303801030480c4154015080e414007442c0e00921341c2e50041100c2c0740c1040c880c140051800d40b00b900ea1208651400c00402c2d15a511004a0040d404204007010b014190010301000c1c83e500d0401d01c03950311741c194400201815143c890040410008005850040d030f0083d10f02024005482d107003400d048a052004451200e03548900110190284111032045006071a902100c064050030814402001c40740c3d050b11a40310a401041e8071010710195008100204480b0441e49511020880c00c2d100b41d94801c100d603140074200102c502c2d41c0d540300784207681c00003040c6407541c480d4140b000c041e21800c10554818411804001e00e110761142c2100c83d0342080c40000f0052102e0001c1c0d09161003494400c09a000710007140110111300c14000442d0003418031b04040b075400d5512000e29081c1e0f04215400f1418580d2080e06c042d5842c0c45006032010241c10b464120311a1401400082c4180000f512040c0a10395403501042098000c01009084e50703000000c16850598510000f880041c8901480001138102c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 294947922 1250 294946672 294946681
    0x22a1005060108070e03070f0e04050706020c010c0b04020303090306070e040e0703020a03170d0e0c01090b070b0c09010c0213090623150127050301110403050c060f0918060306 77
    0x2520031039008910583d640840c03510fa501c0c0c04c503000002c83d8200ca505004131400041ca050b90300d20084010255503a008c038452034542403d074100f2416600013010354010f4503c0e4116617034442d55809074540c1c04224040302d52920700219156004224045416110715000d1000c5542c01484000030341c0401c80b028024200d26281e1240c584c1400c1c44002d4001c001c522083c4000344803190481c11940450145a04000c10301c40c00d0b40584000b80c0803861507400c000030010465a1080105001c1d100320001c1600c1c020055880c1030a0b071000a1100d61141c0005c21010141d030b100d00c0441d21119001003174912f16909060038a002080131600484080e8030b4118500180c030440810085d0164000803841110b9803040c07804d80418102c10415410400000410300301c004901a0715800c0c00750104480841030b08140600d400c480ca0703800803c00c02e0300d061104000090000810710038042c0e0540c0c40c0c0761609200b00b0600d400d03000701c1600a80c03002030700d4044408803041601684c85800210119101e0303407103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 294949172 1250 294947922 294947953
    0x302160b0a060b0a050f0f090306070801030201030f0c0e0d060e0a0c0e0f0f0403030c0e1203131703091201060308120708070c021003090c0902030c0903061b070b0a022a 74
    0x144141600c01701e041480340080902241e00035110086003200c0b0607240a04410009040000c02c560301004511220018001d6591610800003503448100003002080c14000340a0b00040300b00c02c082d0710070303250380b0108010821349030080d44121a147c3c04496072141b0f1807030110b207500201e004016071f1141d0600010007100031085064041c502403035200c0750035151900d003200613240d103134011014441c501501c008ae584a140342111081603a9020310303240d44420302e44200782c0d1000c1c0d01c0807810307446080310780001c40004800c90340302c82c1d001c544100d1200001d14089001d405240e0001e13000c44804100210084410042103108a902d680d454006965440c010743c0c855450640103500702d01405290f400750b501a13400700340d085002e410555080355032042c008040c1d03030080f200d52614440216110304141420400d1541040b00b030b415141040c2c580f0001c4602030b0140f03980141c480c034800804500c000743d1755030440b18101c000c003c55a140405059849040c101c08a9035440a44910917031030300385c3d14 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 294950422 1250 294949172 294949177
    0x110403050c0d0f2619080a06062f0102070303060e0f13140102070b04081809090a030302090d0c0803030601090e133314010b0c0705060a0302160b0a060b 67
    0x2d50202d083c144003d426100c21a924003d1048040743d44811210075081c2000c075806031150400b1406010301c2621707a004010480c12018112410060401c84184107058001c1400041380c500000b016452385000d103e104081c030110404e90003694800a1241d042c50750507001041a03035464600b02d0490344800d030000c6400c00c8101e8030507131418940e009840001d01b1010030780041000e00d1001600703000154403404655401070b00c3c121805000061169410054040d070400b8103070086580807250b142c00c02c01d40b501c40200308401820598001030800041d40d541051414254001c02402021038841c1095540c0c0d41c000d940c176034040303030803030200060009039001100c0c481e01d005c1c00207001303040660b5603100c0b03540c0100a14007aa5540041580b50780040c10410001d1f9211440c0701144805980744071b0040500103030001c1051920422001071720b0280059120700320b85c0203a0780300795a0160400e00700c00902446d03a41114101030711405005000d4422101402111090400c0266594030240c001091 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 294951672 1250 294950422 294950449
    0xb1f0605040f06030c0c1505060307120b0c0a02070e130b15060901030507051e1207050901090e0408090909030c060c04060e040902060d09080304110307060905091801110403050c 78
    0x11000b540103200051090300301c1543e6150170300301491000c2495075046c00c00c0000300c40c1c402d52990b0303410030004940360401002c0001e02d04400d140140740c80035150400312003402406032800d180d00082c82ea4900d40708016400017400100f8166050713040c0344004210234801402d00b901c02102a03c0842c410300894004495040c200400052038407481c40c00540207003000405400c1444014020640c4000740301089210300810341c0c0c80250307284c001401640813038a01801c541c00b000b005004000203030340c0280707113401034901003c03841500d9540c41c07071300c04124410715110a0700424508207103d0745480000c00b8060b00d44030202598600c0c0c0c0c8030b080800071030065100d01400100b9000000405041c6684582880c070300140c0020701c1c01002d0308030350707050305c0000804440141e800030030402444181030700c84100d4041240179141b070300c1c60210014120a81401254803942d13200c400700d65000d00804130001800c0d8254001d101101c1d10790a00710307054000d0700c019101030281c02c4c214041460b282c802078840 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 294952922 1250 294951672 294951689
    0xc090c03061e04050c280905092212110c01120f0603050a0b040c06030e0a02012601080f150c0d091401090507180e070902030606070b1f060504 63
    0x255070307581007044410404024840350101c2c905080819680b11401400c1c4a9a00503018680e140c1c44c40707001c0d220480c4030f11b4440e8402e100c007410002a00b43d0000e030030012101c0480d142482c94075144821101d40c80d00302c0da5440e020001840c0401080140b000181d41107142d5224451080b500185c00e6031a45100c064142c00070301c070002c580c2e902096036402981c400c2c00502d0b00045981c4c483c2e1350103251860124082e1100c0c1500300c20001007004804144c4040c00032481c040c0710308110704500558410886600034148560344030003010042c08180202c0d0b800703081c1071400e005540d50700403030364451800382c0a000ba280250300d0340d01741500d0100100e5005a04104a01c0e2906036420300003c001c103a403a4048441c01d84e203002d81c1007403550902500300120b010b10054410940b61102d0442c90094401d01c04d500c10f4141010140200400b2401808888082a001d81e5039514100058080d100b9500000e000000240c1440703101c01038884c98240e6244490b0819030290340760241139a0901561298144 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 294954172 1250 294952922 294952927
    0x1112120a090215163807020f0f030403170f0f031e0a0e060106030b03030909100806010902120105010318030c150603060930111204170d050901020c09090f01021b0c090c 74
    0x400c02685e566100e9010300c1a0303000d00e015454064101255842c920040d50710204d03061040c004e550021150080c0d40d285114544101402c15007103e0041100e8100c003604084005806024900a0031b0703071091144114081615180034020018a515007818500e48100c100102e112802032191000c000c20080046051030b88240c100404130500030280918410054800200000c08020f254086c250000000d03031a10840e400d2000800340581c007041c101030030038102404003d00c04109c2c4030b02c15014a04000040b10904107204811080c201100005d481d220001050003a079900101c8010311a031202e049201441500250000721003002c140b0105d889095a4641402111442d29110590082d106202805400d4400541040d07114030404400c0c41342e141d107488001d0003c0d41d500c02081c203115040c80d0800780000e545500804510b80101c515102007065003800300007107003c00e55000020740d03403950b05940d0095a12040131103a6804d01c18121a04202c0c504000103501c2150250005070 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 294955422 1250 294954172 294954263
    0x6040b0a12050118080409052215060305100b0411070209010e150a142e0c030908010f1515211b1112120a09021516 51
    0x180c1241c40303000708440540da1000750500c8441202043d0060500803261980c03582c1c506607000301542c078001c0150307141c10001c0020700003403554802c403600020b8000158105000e00c2000010041909030406400e611480340d80415150300c0781c0005200d82030540b014881e0b0100c6130b1100459005006000390b01c81140d10062040c2002066100d42c4003201c800000020b0f80041e002c95010080c40e002201c1e0080c0d90000b0b0031103030800103048142c00400000307000503a444134500c4500880c0781058042013202e500158002d0503c540340e000044e01c403d80003000f484100304900340c02032680707000a0968459500700002c1c2c0000020800c000300100e038866441180385460b904c641c40007602078244060ba0341e21003102d0030448001140500e2200b64032458118004603090350b142c4044081d003400000410026245c0448403d41001d0704012580d0011501810b141f000500c020b19219900c0704200021486000c40407808403000d070702901500d941d030760020a105801018650700f00c144000c4865040d10302 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 294956672 1250 294955422 294955439
    0x71a04060e0102070906031209170615010c0b101511120304030306030503031005120d1b020d05030d0204061823040b060d020d0612151a040504081206040b0a 69
    0x801d0840520580c0c00554541c80300c00212207040e041903880c0c03c00414881e18003600140100007400c1c4070b0072040320100702000300c42d80d01c0c2c500a001284d0198402c4640c04a640120128503005910500034400ea29196114072039040c0756201d07081c40c1380c030010300b03100d1040e00400005045241d502e0141c14803c205070340058040d40041c0088080603a5081c00001042060020310f02640d0040074085404d0314050030070241040b1008061a15005100c0c1d131080c0742c2d00501d0480440d05c0f9502d00448180250000511200c00640040c0c558003002801c0000c0c0c45280c1d00420030346034180c4450351381003046c10364449001c080f4029000042142414402224408140810341e40001403000c15146004008143c80303800c080080312040d40c02154451003508540030b48009031588202604264541d070300d0313030180d030007140000c0804039640b68032801c8100c621041440201e100a00b0501c42414549024040e903400f0b109684502c84000f00411050310b018090030801100050140c8012803d124a0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 294957922 1250 294956672 294956687
    0x304080313021f0e0a08070302010e03151303021923010605100c0611070b010611100c3219090503010617100b03030a0809010b130608071a0406 63
    0x94030501e00c40c4080c0d00d001650349540c0c495261061404920184284000240c002c2840440760707440b41801e01c01c01d000c113060002d614812660248bc000d2083d00d103000200e8100590504c500b0b5025824604000d10349801d07070b1051411512a9003242c0d010304000d600e400306142c5034034005182200300100104001d00b1084062121342c18900005510355640d00000e4000c60060100400311300f100203a42d0500a543c419054002c070b20181c21071030180242e55a0044071814040c0505100682c0b11083e81404100402c4420301e80d4003004002030302e61850050015a50a6990140300c5080000340c6682d40154270109118013034100340710704001c44d0001140441c0751056a0508100048030005041d070341c24001c0d540200154100c201c003803441912680c2c14200041e038100100740c240200b4680b1502e00000319000c01034a40f501d1005500c0325484a80504055504075602901c464421000081c0a90001c41143c00c5101243c9030306555a07810100351454908822000d441072004000e6107004020 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 294959172 1250 294957922 294957931
    0x170a020d020f10030f0e010204080a0201050a1404091a061e0a02010212150a050d15020706141e010816030f1a180c09061309030e030d0203180901050603040803 70
    0x6600b941561020900307036008160b841002135103a00080003910814498403000c1d680c1c40d80298502800c0100803a56002000f4000b41000000221034000b144a05002510511200b0100c0c0c1d603156202d40120140144e4200100321019051100c13a0510b0020300b260b0310342141108100d580d944000442e03646800810b202c00a654003045804010115807224503c20060080103d400451311800e000382d025a41d045140581710107644080070079100a50b02110000d515800b5a0742e202c5c0d803038000301901d08688469aa501c800d8140403400654002010200e92440451081030ba0f903a0540ca950b0010b41c3c2e4400c0015038a918244041303040f104503401203d00581565850801d02c000701036606104444d481b4001441c0c041c2e446100c441808840f5108200716410001c50070504005285094003490350724a03d551042203e08150248070125400840181601e4a42100c41d10180d00c030b80c41701d0340d03004010b614240403654501d8002c15040c1601c034050070460441e540c5d542d50700000c0e0303c05071 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 294960422 1250 294959172 294959179
    0x1080607210f0e100e070e0703110313030809010b0f09060402370504150c06060906170f070303020a0b040c030f150b1e011d040f0e0601170a020d02 65
    0x20307462901d0240500858600e10524500003503443c41c610606400c003943c415a40d070060342001801003186000050160551398642d0842c142c50700c030000c060f801002400150442c011010003008440703203000b80300e0f0751282d000751200011695003030305441c00c0300e9030020075540c80b9040c0303607581c071a80c01c0001c15990320020243c4010b04e40044c01c864100c10034040c100c0c41da681000000301d068421074000f01c200c5903480c14244582401c4c00c20000da003818600e100d0180401c1903c0d10640c003440307031a821540060180a02c1000341c1034841c88100c050094640c84501c052042148070450100001000c10880340c0580c050301d0300c1080c0355110b500261000d04240c41020000f9008030115101d0219888094450010030006001e249141e20580394400b20003441207110b24050369482c1c8540200f07160401e000d10f08030410241091112000c036500300002a0442e01d80305102607501c01a41c0900c0940203d0313421514540e0342e800c0500c48070411a40341900355082150030b080141425a031101d440d61008 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 294961672 1250 294960422 294960467
    0x140f241606050115020f1507050904090c06051305030604080a050f1207050d050601020c010c06020f131203020606151801030608190b0601090308040b1b0a0c03060c0801080607 77
    0x75103030369068410a80020340b0680c058840045696010408821040f8a4802800c04050741d00c81e81214170000078226824450b000803055115a070b60303030041400a50050607070102e9911000c006200f90003950b04841000f01c039001c0400c052800140741d42c80f480e4003a88407881c00c0b0061808680c1078005aa030680340c4e410910000d030303da01d401c051151242c0c0301e070740d0b80c036444400c2a030401095400240a96055400030f0301e4101c150303684540821620f03904600d000d0f9803070802281c1036141d44500207081c04c042c01282c03c0441e40c01c00301c0c005e540155020341c1c01c0762242e03180e200800c071041c0012001e075110303100c00f003211252002030410b0220ba9014141000194556500ca14070b00f03100340410074602040410a04900f000f41d02e1200035000380082c60809402d41c29640c501c035041c41a402422642c10010541e0303860100710601c0b540b14a00a041601e07000201c6143c203c01703421304c60104986550803d041041c1881c85484c0103030485402200812007a16503010680d01201800c0c0c81c0110300215 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 294962922 1250 294961672 294961717
    0x4020109231314010b0a12060305060708040c08011a09070203090a0311030106090515130203090a032703050d14030c070204050a0f05130b060906030a1b0e01140f24 72
    0x190325004e000f0403580344402d5440d12901001000901ca040c003400803d0702d4420240003050001504691050150414500d030b13886a091140310310103150301c411900c0d800c0000c2e007400c0704222458006082021b03909148680c50309001a41c50b40549003565070045000d010800c082045440d900e8848070000d40005101030700c4001d90340030784500311184070031000d4004d0120500d00700444403c1805200010840c10360030b10b5038809440b0320310f00d14041e041040d00c0410100400400c144000c04d07143d86500201d1442c2d80e86041500d0324070560030600403840b5042c4000306a0348180031070344140b0381c2590603403601c0c0c0c40d50308000050030040c21b0034440036500c0c8244140c2100a110311b5014146030b030059070143c1064600502012401400c2a028030904028840c0315240041d02c2860603034041d90040c150250b00d030602ea21215141e06c0020b98800d0040002450001d42c440c40c040d0b40402d440d1101140441414002c20900009409100c21524040c03103000300e034050701514104014044c01040e420a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 294964028 1106 294962922 294962951
    0x306130501030b01092d05090708060f060607050c030604031806020a0218060607120306170c031c0e060c0601060320070201030c031d06040201092313 66
    0x31a41c602c040e10319146c0c03d07040300c0614901d8190200e403001d03268200141c84180c49400c1c850040742c801040503000860081d1003003121582a0b503a5071600824060640c4c8510800d481c40d00444200180c107681c18442113000703901969801000050809000b0f100c2002036000c1010340d445010070800507240c210018100340107085e902040d03030b92508040f030b030f04e84210500100300644c13108500c031031035415520007820f85001d520300480005c0d03080c00c52940c584440c842c20764103a00c0690401182040c0c409c0185203aa06890601c0105a50b800481c8036074010444600300c42d003100005001da56454441c1d440000c0b4441d1010140c410b840c9014032581c07180390340181c10183c881da41c0341003032030081d0040300b080f4501c0100380300502c501d22001609d6410a88040340004d0000c0000154000105c1358071480614002c2106c0100803036104000c00f00c3c1d0703c043c4920307116484104c1408280c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 294784172 294964028 := by
  have h0 := BRFrame.cov_init 294784172
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294784172 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 294784172 ≤ n) (h2 : n < 294964028) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
