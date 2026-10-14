-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0666
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:01:28.93641+00:00
-- url     : https://prove2.me/submissions/18a7c072-8691-4f9d-8c43-b1d9767dd8c7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 119604316 ≤ n < 119784172 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 119605566 1250 119604316 119604319
    0x30c04090822090f200307031b02030c010e0604020a0513111614070302060f0d0b0a120203060106050301060507240f0614010203030c071202030c0106090903080c180108060f 76
    0xc1c920190502c03507002c0c0031402105461444c103058090300400c3c601c1006507a920344410701400e10340d802c1c000149039000400d000304160701e610340e01d00030720031419000026007440d8000d59211540070100e6821689076103003442090b440035060001603104c2825030401d640d01030701c90700c40c80810b007000070010380300010304404000c8002449224541c6814040803120b44102414240210700c08106580c40310180406903000d0340811075151250060801030a0780c038201c440108650f42440005084a80154001084207085204200071448c0a01450b0b000d0032442c03c3c580d00f1541040b8008090f03008181008240c40c40b9511107804024114107204011900c00006111241c0c088201c00054200740c800c8210009010185044544c004000d5030700c80c000c02c0710401d0030903441751580300b03000c5d60381d10300d85003503000c10000e06803c0340081c0038138405081d00315000b04030584145002050310304014110725812106004540b10741d4028007075007590745000d103812089a10f0b0740c400500240480c48646 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 119606816 1250 119605566 119605597
    0xc1503011a072402041404021305060a110a050703061b09050607080729060a0602030d09060b0d0b07120c0509040f11070c051e030601032a060e040506040209030c040908 74
    0x45003d03500d42d001001551410001281504400d100f400160b0140e003514200444980c2c10074805401e000d40a8243c100440c80c0034540c1c840d02200d001e0800d21042004d07641a00880000c3c020300c4a030303018031480f004642d40b00f07062407003070386100400101e42400b415110b4940003400c482800028002d6811303403a0460321120034015a5520b45609403880111003110b0079105000500e103281140b4801c0886915070091440e07d0f482480e8100101003510048401d0341d43c0304c0015159407200300b03429100300c4c810f05043c0e0440c100001c01824110400c001c1c92005030400440c88051503100d010744240d880290b49c04102008403c0040000d00710100c00442800400f00b0503000340080d1000346400c40340c042d1071500c4082d4003c003c0541c0c3c4800ca21025400d0303440140100002003d0054920743c9000c2c0402c040706840ea124a805c18800180d40a100022003103200f044440c501482082d13002402210110710f8101c121020a07183c014149119200301c1d601c195003014031020004851040080d003200 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 119608066 1250 119606816 119606873
    0x1e060601090b0c2b0e040e031b01060305010c2a08040302061308030a05070b06150412030509030a03030b010815150a02120a030c02100b031b031903020c1503011a07 72
    0x25542c41300e101e800300240101103115200e04140c0f0074000100210342c051454841c840585040b0b41c210034428500c1c5642e20000080456400c2c4690b81c0088150380c0c940307140718049502407410100e44210405d0303074682220302100043d9441e0840d41229416201c0c1d075100c0c1c0c042404075601c03001a40c05603600f07000009020b50040e900070010900d403031185100d40350507110813003846541c0806105001542c0d60030007050241c1030084800c20324a501c41d240c250b10b044035640209007828840c40c2e0840100e03885000354403d035a00800c965500c04042e5014007002d019000c000340a60300d41074242106e01900084507110a44240b00b403d40306101e4108180d61040300f0400100105000b1200d0030041c0120310421010704864000c0e041280c600500424512042100d0b100030040741011031a4540302d01e003440000c0e00410000341524a00039000b9241110b8898244821008821480030b0441010030052244080e01000554010422003015890340710f680782000f5904075524003030400c0d0481284 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 119609316 1250 119608066 119608123
    0x50415020a0f080405030706031802010c14100b0a12020906130b060c0303101203020a240504060b0a050103020f04150c0b190c0302070506070810090e1e060601090b0c 73
    0x4100320350080c6c08131480690b940400300c0807907480d03102108042074111296009917101c0c3c1902c00b94a801480341d40d92010000c00345501d84181030050303103442030311821030710b5551400b40400b00061200910003004283e4650000741141c1000b81010300c103407005204050003450382d0b80300c80b803005005085c03030303581d055015009541c4c0c1c3c200316011481c20811141c04100035000610003c16954103030000c0c03241907925960651801080c0030600c180007004240d03c90f2295060142074020740c00352000140d100c1c800402d005041c0c2440e0000c505040c010051113003000e41c00303000c6130210780300c001c111202150040c8003140c4038080c5500c05001c8041c644180982e1a0644d0801203542d025140100f20f280b212650545c1a4000c1d114080e1043c0c02140c00245924050480903a108003a41c4001c51010b031283c00c0748e01100da6007007000c00281e1044e9a0605101d030031490303070102d54108200409462429000080959005028400b0b01100c04200000455010040c11902d0480380b10841071000d81d461 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 119610566 1250 119609316 119609333
    0x6060d2c1c0f091716030602090405060301060b09060c0c0301090503030703060602060408071209030501112d0405121009060b1c150c0c060e070302120c01050415020a0f 74
    0xa0a520003403007400e88125025000b0200300b580d410390703500d90418103450291440d00c545600000d0307180502031340030b451690202c8002c0160185204001c0180c40e201aa41808100c0e08000c10f41070190380f40c200309200c607414010680c0c82504007122840e030380d954650710560600c412140541e0b00366003004c080108000d8040065441548241e5040203025130300e400407692400240c2d40034107490000c02c074400101e01f40494404002c1d44c1c900b130a500d0540d0f00c0e610f2a08440c405040d5000140d408a4070348420740c044502811104035070035600f001c4110400803240c4501c07170b512a091150f040c2c0d030361142c071406d03013445540c003034031240201000989940c4c10f00d00b026020400c000d92241c291822110700211004c00d0000886810014000d001400c080c03ca000415140e01004140321100f000d620000e40c5500540d0f041030707030760009010f0442c0745205010105522010030480b40d0400e810344600b50f40d01406440413285806201e400740c010003102a41080d8449101a00f94030011114909120032107 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 119611816 1250 119610566 119610583
    0x1020d0204051c02130b03011409030a020106090504051504020d080d050711060f01141c0602040602011d1b0a03050303070e090603010b010804020f0301021201090507020c0906060d2c 80
    0x1682c4841c00c4000343c0c1c2d8010014a20024000c1d4490b024114000c03100d50a0341c0a0709180d5006030000a50042c00e1840340244a0700712061034a9500c0040c2e45c904259081c0203400083c14040350038005402c0a94505031124650b045118502640400081c113541e034103010b9140c656040f0318800d943e071411100101c050501200d4440101d80d480008018003100010124420000400010b041c0e074244070002c0a0350384d038810402d901230080d441002041a503280e1081040b84501e10041c0e85615064010703003950030962819010003061051029451400b050060640c0b03d41d078a080200e0100b8000110b507982d081c0c03c080e10b07510002c0104001c29400c0090b42c2d02c1d201e0708403010a8160388450805007130310303d03040b0701c240000c0b80000400c00505100e0039180c08031b43d0050002d4104990b4613911480030000764810080262154241b107110f60b01841088034450b82900c2c100114078004012070218070030f20b500b41c1800d0b503580c180001c0400c0e4000d00241040d000300000341c80402401041e80e519005c9 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 119613066 1250 119611816 119611819
    0x11413020a050a05130b0301020405040e061b04121203180b0901050f010503070e090f0a12080705030c09091302060406020102041e030b070c0302070504060e090d030e120c0106050301020d020405 85
    0x41010118040ca0b000d04076030f0454100a100c44800741000015001070016050119090b64080c4400b03d103a43d2240034900100c00040001d00b0140f8005100d1303903140c085490f00e011416420041071006a02030420906240e4201034007074419144000210014010281708041186050700c0c0300c005c1000e08103403c1e01411040d002031046494045034102c1418003845440d5169000020811902e04c01c00a00782d1b100c0e18500c140c40740304041d81c000d01e0604800d02c0e01207401025088426030004c2d04072942075000016443c11740e00318540038203c51001c1c4244800c142c880e4501f50002001145441001e000881e030161905880d650b030303103501034040c1d0842d02508100e60201c00300800f00e404c480100305c04803a0400d290403950b0b00d40020540d003c82d0101004ea0441c0a5084041166100d5000f004000c01d4004440311051400803420780c101201401c07031b401058140000550180c0300064403070100c1c2a404561543c0d11300b2248514010701203540070715059400859a06031004c0c40f580a001103610 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 119614316 1250 119613066 119613079
    0x1031406070e100e0117090303060a12023d05041712070f080c07031505070203070f0b2802040302040e0604080f0708070b040605060406090908030604050901141302 72
    0x46030701082d64440c8045040ea40c020014001d6111194420440d048400e0307018188800401009090007040004c200d03111200c0da84004280100c81c100721456030300805c0c44d5100f007090703c16a5400203a00b0104a1180243c1521040c41c040041400c0ca02c008600c0e0205c0c45060700c5e001c207014010700b00750020b00c42c100c7c4840c80c1250040c10b860011031804441114000c40ca4581089a910010548807483c0c1c03e03500594280020702c0424410002c06000d140201a0001200600001c2138141c600061480301150030901c010400585040007a40505620048c000e4a6944d030404180006029107003c01882d038500000e110741c1001c0750b0060058038001e60f424040c03515450000350361000169402010907208221011540214102a103240c070721600c5002e1401c0c005032030303e00c1c50a13802c1e02c080d2001c5030340e9414803c40d446c092155800400c0c60283c2401507400c10f0301c1d0362026000040c07480d400b8540b190001214035000390710040f4201d04052a4801d82d05007860011200068003504038007074035 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 119615566 1250 119614316 119614321
    0x80d090302100509060318010213180501060314060409080c160f0501050301030b0f0402010e060c01021803011b05090f121c080c0415170a090501140408030601050307090e01031406 79
    0x188103c0c211184028050b00b6a07146448010510034038002c003503140945550b007804110005038864401500034030700d0044981074148811a80000c07524181d00c1201410300d0070600201c8810400e0020341d122100300c90008100c2c02c20f0030710858500c1007540f4907149004111a85d402030175141c5403030040c0c2e07080310144012561202d005544c1c504c0280000781c41d180030600050302c04103400c04550f6006106140000140c62088003165030354010504000742c0340d4001c100a08007282c079526000302050118000e00403116804030002c3c0d8604c5001000e070030130400041c00369031034407042e488420040740604082402d440058680c0d8481120040303400480040c600e09030350592040070940e00810a40c403440f40707003924003982800c9200104080c0020300c0a840b1920000700b080c184050f1107595906030106610702a4a40182103805803404850310450300310500005c5400041540e034801400c2c00d04d43da03a0303140c42e1410360742031720254001d8a40c200550f00220400c01c402246024503108042140d4294 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 119616816 1250 119615566 119615599
    0x20403030207090c09030b0702160b090319033903030504050d030b01140a0c12050c010612120507021f03090c14030c10030e0a08071109070e040c09080d090302 70
    0x1314949082c0301c0004002d440f0901c04250300c60b01c407541000305030040f04c1e0850060301450340402000d40c000e4803400004a03000d411800e0910004545005100c05220034800076607010b09010810b118110580c91460b000d44003021881c8030000900d01424030425007003206140c014050701048408035002d014660341040078030b0013805041031105058540c0c01c0e00300040388400d03845070885001e500800c500003c10341d0200314030810042c1070030b130755945242d690151903070000d0039148503500651a00c001006404081220741c0040d40d2210303a503240c4195590518000180780018070148030b01802c81c3d288034100b0f8183c02d540300068451007581d01c07699031681ca420401c240540842c2d05034054100c03c0c02c03500d9500c1c1100c1003625080150400040708048440c0c42440c1c14040310081314013940003c0c0c020b051200b80e10105c149132100311860320301c500c0e103680003d0456010340c6140b4000c54581603401c031940c0c020708025019080d250200e92028494000043c6032180078402a405001e81c04544981c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 119618066 1250 119616816 119616821
    0xc0f060f0b0d11011202071b03050c0a03150504020303040f0b070308060609010f0309082b0501090213231c0c0602060c1602030c0319050c040b010c060b1503090102040303020709 78
    0x2c00b6000000c0d0b216207518000103407a90300700003061040e45903080121a00040794000380f0781c02041c035211012045415850024a850003010000d4402c405c210010130000e180402a40d0b0080101900860b0390380b25880400e103103001d607400000040350030303090204a060007640540022800fa54840b0074580701c403014451148544a0704500290301c1d01e180421103030190304005261441040201e00d8962243c401004102c0d840b42c40103000c00020304000400882e500410f4058480c9800442c0f03407541c4803010400c0084944100e204c94088450f6280704896940c0b40044105009055240c60070141500300c1c5279080010401c071240030820f9404100240f000980f03a12400b4841141c61408100055828118a207000201e1303042c813075440401804d403010701290440034102c240d060668441c501d4660b04022640d40740038012403801c1c213012084e0303074007000540002d900f101c0700140c500c0700d000100c0ca80300c0310542c1121041e040081030182809056000388100d0303000c4c1e42501c40c00c0c0e49940302c9a00303 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 119619316 1250 119618066 119618089
    0xf050405011707110303010f0512010501080a17070602030c030403030e060103150218100203070c060c050c01082e1809020a27050a060314030910030209010c0f060f0b 73
    0x60140b03121903030b2a0a001001608901981410030b00d040ea0018240c0ca075034004d07040f4440307420300c06004010030f080ca4540d19088030000c1d0b009100d10740c184800d0954442100801902c0700205041140300c503821402141c42854000d2800e40d640c0c078007283d039040554415181100080d15110b4100c00c2c4610116007030303040c5e070307071202a09000b050201e01260203500b040084a48840424500070000d50350003040440e0b040340e6802440d2520510305251011403050b61251090080c000c802d58005079012036144480142404c140d166a02c1d402046001144c542c0003c18104090079440500340e050070442c0070407a50400c0d400c001d0501c01c4400f54080e1907c0002c0290400b44142c001c0c080b601c5164505941c0c0f424420449003640103043d14401032320703800d03141303a44c1a40da60f030320a10074031105490307042e85207010b00000c61414030392402007501d6401005800d410141c5c0407802c1c15080e8864031031425110717044001c4003070424007800c0000041041c8010b050405180c2140b01c4068203000c2074030030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 119620566 1250 119619316 119619319
    0x11010c0c05041112040c05010e06040803070201050a0c06091a1503070302040c0203091e030709020301080a1407052e09150807090f1514090f150405030703080a0f050405 74
    0x30a210300d00070900024054000e0709580161060001400310300d9003c0755648160701a01139020b03d1854800054000c58004200318054141000248200c2500100b264900b550a1900c00da490020300c4003260100c0a2880081c59603040000c0754040c40b00141e04640b84483d88000d0b845662220302c0360501c0070181411590305900310b02030070070152070a0b901c116022050360054914000712a00083c507981c1000f0660341031100100050307001030404010440c090303c1c6802c400c6185504240300c060b620701c40300c00000c060254082c1d00c215014018045200140000341400826034580c0400351a03243c40c0521082d1269105410314501d54428280e03541214410a011302d5441c1e04503900712003510009040348103010318a000011201315204013100109100082401d020528442c000c00038030b03103541300c03100d00f14091019894030350314440031403c00c1608070390313000ad112030950348049a4052a4003403a41801a80e02c0001131226250061a510800d41e5551741403d01448050340d00380258003955 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 119621816 1250 119620566 119620583
    0x30106080d11030403080307020f0c0613030f0609020406060e0f03010513030c0302070e0109060617150d11090c121303080714071209050312041a070f0b040b0411010c 73
    0x804524090342d07500d034400c5000070a80386050b4581e10303400d04992003520400d005a00204c0704404008040c0800201008102c9201d0b24002902803000344195142c00054610700c81b03644010304000440d07101029040d400340c01070001565481026103424134940d50b0700c1c0514102d0741541841d240c18415248a0004850070442003501078a048441d4513920404070158401c2640c04104d008180300d450740203100150001c84c03024288100284040320200c284610f034076071101446501007030322416058035032066801d02035002c80c2d414000480906440c240c0c0e000b45014080c0440c0b21170307840051010356049400d0421036222203401c881030340a6818003800044e0f100700444c41e100d104803c0312041e0440b51201904100301a107601c4912300c41c1242c0ca00c00b00b44204000c03c03e0307060500103c281c015005c21604d05145c9044003604550300400c0d1401e12121000075030364204203e594250460581000c03c8501e00e1138580b4191080e41d000742d4040c0d41581810301c104d0640e6129105042d402036000840 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 119623066 1250 119621816 119621833
    0x506040608010926132903062d041d011d030d09030905131d0304060203160f080409020a02010b1516030915050d0501050604030c030f020105090604060c02090603010608 74
    0x7210070b1001a41c48130301c0c81c200104441c5207082880398100025145810100c042414a070072101c8012010b1600c0324111041841006041d82c4e80030341c00700001106041d45038005065800d0b01902d030340c6880040303074400d14000c031201d4081d2001c510b50900da41080020801401d000005203c80c0c03103000500d40d020340c001c10903841d040400790440c0e00400c1c42414071612032521034000610f03103481401102d00c0f0581d1005203082481c02d10460b40c50041048000d58981403e20034002e48034822805000c0398103100da4009010005941003010199400c50038554641d41c5407071148004c0d500448918005608108191100c0d2428115414603840b513090118a821003c0000ca00440300b00c2105500340498510000b030310001c401c00159101013595503031652041e880b201d0000320384060b001203024000c01d02003480001e03503400d03e03c0d0640c1d070801c000c3c0050074403501c0102c034584034046010750094000305002802e07640100c3c1b03550390309108540810580c1d0ba02130625080302c0d400d1044200c83d5100d00e00f0f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 119624316 1250 119623066 119623103
    0x801020414040c0801150518090a0903030506011b0201050f09040c0c050c0402090a03061d0f070303021c050a0809010608190501050a150510020307020a0602060601090e070f0f1205040605060406080109 88
    0x528400c0414824980d003520710000049049c04202e528081c804e440d4489101016814851158007130400d0a14200304590344400e520408508a4000e040c03000020302c00b07500d0788190043d140042c3e4001c005124161903d0001001705e0402030040340c1030301c5a60811000e610305070003512011100a0300c1020349900c1c41e1105006043c00302c2401100201030390341404c0c0c6a02c10301488519848980007442e0051841c03030009c5c500b000310052000130f02100c09080b00d0f151360100490f64240418074000038903869000080340141702ca0391011a1034411410740e42d407024030740c55010f800c043c019002080a40c8d181c0c05250203442c2c01c0c060002220222840521051074009103c1c000701205204803418600c4a074081214407410707801500c096440241002002e603403010b1030130081d208081100001d41800034010b4880d1400307903c1c90040c460b0030002c4641440c030500741403e5a8580200c1400241402c2c01e10a00030107065031407034002e500b0001c01248a110500415a44036800a0040d01c492031469 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 119625566 1250 119624316 119624327
    0x9150a05130204091e0804050a080309060708031b030f07080117070e090a0615050306090d050a0305072106090606090305070e0703020714030409050a0911190801020414040c080115 79
    0x420466a0303920440014800b40f500790200e00c040351064006c03a503110304010410503000e4040d406503205034001c101c00480c948030b0a09480026132f100c0c0c0c0b50380e22a298030300c0d4882c5404141c1ca019000680120800449000905006009140d152556155662a05024403204484811b25240c9070701440c002c010501c6a042c03643c1e48440c40c102030f18048110340d40c41c1f0007a141124120340114080c07034400e204c145014050a078221483c20014041d96048003005132483c0100309162090540c2d80380010328050107400c80304030000c90490052070354045062440d000740103074010030f04918985207011a10034001c6846406484d0000c0043c40d0b59450982d02810401006085208054003441083c001074542d03021a820302c10550043c41c3c4560402d40362004541d0001d050384455418145001c0c04903e980705007045204023901d5110109080d040c50307091200f030582c4000200d620000300050030080c0d80a941c3c6404104071400d2000c48109101124440400c2c083c550060120411100c1039502a2 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 119626816 1250 119625566 119625581
    0x40f110702010c05100903031506080601120f06120506040c151403090a022d040605090a0f090203190c09110a050d06080d05180d030905040f060305010509150a05130204 74
    0xb101202c0c061807100e10705c0300596115010480100741c40f8511442e00305e0207851402e01902491804410601d0314038002402d8501000d00551441d50b00c010401c4003800725040000500710244007810440079a180941d60707142c040300d080d1841c0c81103400101d10304240c1400c4404c11511642c0315940c50400b51451401703a4800f0b4156110341c450000e4600040e01e0f0b241e000c3c900c4605103800405003ca100043c00c0050310219800d0b485986006002c0c82690f8416510300c4e0815800c035000a902c1e80c1c07806000004000002c0e011354140f14049460014000c4e013030780f42e42064454004000110751303443c554026a00301c40140320300c08000303200a00001d44900054410090003c1c00810101e42d2907442d80c0c1003000348004000000c40000d00422408000b06100c0300c04e010aa40c01c07000030140c0e890042c4018850b010341886580c840e00041c240f400b041c3c0280e8050f540040080003903081011b6900d5039040000103000312100c43d100024049003003880340c28451784024119000c56103055007040018681d1303 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 119628066 1250 119626816 119626823
    0x30f2117060d110609120a051609200c1e1f0b06030117030d020f040905090f06010302090c041a2a1902010908030318120a05040911070210030b040f110702010c 70
    0x80740f411ba20138038104010305aa90194024001204a0618011000c2c010303800c107050950800c01c0c1085460740605003151403401c0c40810b240c8030041440401e090845125080c04914000100910200070100c1c8002c030003296908051a4030005a9082091342c0540111641c041d005000400c2044601001c201d654500c0c0400d880c40d00c0b406801d0300040381c0000802030408440403400348020b45140c070446030000008801400d0803c4803495083d41e035001400001e00600c5000045111024010b0070748000c1d12203a00480844910301c0d501090303130381050041c40040300801443c49810800c58165140300300c4c0345000392503112518041a036a50742c4820b4200d0400c1140e060003d01500103201441c0540e0344070200410703002204450619201e0b021851400340381d000c0003030b41d072072a81041c00c840c0ac072071403d0307000b1900304803185003400140038a80e0040d40107941d8040d0010f4a5030b06501040400000b10f40410000380003003006401c55100071a070521001003007200307101643c0214a0020603a10 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 119629316 1250 119628066 119628079
    0x702100e030a050703050606060408060403030b041b053013170c010b0a0b0a05040501110c09041a13030507030302090a1e0504140f01030f2117060d110609 68
    0x80328008a0310700300c5400e0081ea030a810440d0b081c410070000307100040c0c004030101c45460a060230802100d0302d90002074801024180c2c0e490034071145848a402000c45900c03403a144c403004070310124028000d036206016000820b01e140e02c1c500302203441030400c0b00d112400c40c0448103155840440030403d003106503d01347c0f4008006e44c04c0740d0301a50180c0040c4904c810b0100045803d10120303003400b040c039a00380c100f8011658107003c1486916130060541c0c0031078030300746815002050030381c0030079060101c0c84100c0381e00801c1e0b1a04100500c02d110b803050b41c280900c28040042e950780c060002d0141000080000c0c0002c20070014600440e101e03030060845604020182d90b03941e80e4407001c03101c990704080340380050040041410089440c09200b44401c1e041686055240c0b03103032541c0c00c0c07900034005010090100401d2003a55085c0100c1c3c0d44050f03020400c13240c81c440291411800640081500c05810360b21600003000907411341007003083c14a2440c1e00580851003960540100061600700714440e940040 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 119630566 1250 119629316 119629337
    0xc0904060212011d13020603131a011d070f02030301090b01050c060103240204030209010608190203010b0310140306040611090a031515060806011202090405100608100b070210 77
    0x41651000780c000d00e10080c1d80d1400740d4800c0d8001200110003824105d54890244030100581c450000720fa81c8142031400c208600007441c036081c80303040600d440b41458601c1400001c2142004080400780d80c52600314445444d9a4002c400c4400b005000b890000680041c001080070300c0480c0c00c900e44898050404900b0180185c010b549007080c00d9009a51081280d200c3d458000e0f00c80b004091030030201c00040d031816045802241e41950103105013420000d1100028400244001450b292007041070b000303550301c0d6581c6441c00004d800548009651201d40d501c0000c0c40d000d44402500707000c0000d8090705469446440311001003c0e40b00c0f4441150004109115003076842040c2c21002c0c0d4407448001d41c0041030600e901007114003450200701c0050074070006012168000301425400142480c022000c00815507492001e402444403280e0400c0c14001480003070030f0348040c0322003a2911030b41c8803440c0d6a41c580780716001e10b01d40d05c580c01c14044200b03c0d01c8050f040071560100b4010690078045150b0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 119631816 1250 119630566 119630587
    0x2070219080714040e0f010f0b180c0a022b09050a081915110d0b03010501080601120c091404050f120a0e0604030503070318080a0209070302071a2d090c09040602 71
    0x905121b0038030740307695484502000c403016070711821a80030310940d480b00700540303100c0d41c00484a00103440100e09070404200b0300d030028030030082440e804c00e20340070410440c05580502681914407540800c00b00d56003050109a5080020b0140221210207008282441903141c005c01c00881c1450161a81c05030310030074142c0c00303500d8050118501a0303500f085603250104200901141c664001d05842641000300400400313a0000e2411f0654010324840c81c1e0584a81c9040b4a40d5036441d40008040e5041c1703ea84000d0307594036502d03c2d20542c0240240e0742200c01c000807a40d00d40320040089001d0400c00d104d9590503900ca1001c80603c02c00c068070361032030725032684c907070a141d50082e620450024002070300d1740000c0000000b2400040a14400401c2801c40a50024200b48002004081099400301c1c501c030620405446015201d5030900116105080540c2e10b0b0761900c040f1321a4200c0700c02030060324841c100748d4180e60340c880c03201e0781d0280c81c00c010008200000300707001030000c1c0e030034070340901c4200203e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 119633066 1250 119631816 119631823
    0xb010c02040509030a1805240409090b0103030e09010807120302010f06080a0212010605060a0e0d1202010506040b01022107080c03040b04380310090504050102070219080714040e 78
    0x9012050f00031a140e2401d000c0080003100302211034441c6000f541c5d810000741d00c50002e04004022422400f040c14a1040288200ca0240703502615007142000b411805001407808924142c0c2d0003035136441000c00324282800003a5500384100780d03007a400846c003005181d084480310743e0058880d100200c0c0403220140d90340e0503102c0707030780020b142608a0801d030307021450000c1c03030841705814040003440140e00e0b00740090b4260155991520501c40310180100c0e09940e8800c0c80b55989600c035003284c8101c425038030028005c0c6411607829018900d803500c405003540c0001540550b280810b24a000484840305883c0441c1d0480f2908503001c0c00c091009400e03992043c0083d10140044c10316443c1c540d80f50401c13200400c0743c0d0307817800203010035540c00e00f2901420607481c8424140c1c110890030741e2a103610200f01c00120311a40b04c86041072500090000301b01c010b4000340040e500860701551480d540c0307200b00f0902d1020313109266030b66000c9181042110781c18501030201240042000032300d1113003400207505 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 119634316 1250 119633066 119633071
    0xa06020d1a15090d03030b131d070b03012606090f06070305060303030a111e04080705040e030a08130b010303051306030203070c0201030504080f0403050607030609021306030b010c020405 82
    0x46980c44400c0c1c1c044035003865694880100003240c541c0c0807001c2800500081d482a0303102c3e14003403640315400d502814000c0e00040605400600b0823640d0160390348400b0002c200100700b0f404243c03400c2004070200900021007034280d8a042c141c0b14030310b07403a0990402220310307941010b01442e10441450103405109111161140307090902600f40304801d201282e082002c000c0881042c51714010038071850fa1400416a5030200b4083c00000307201b1129600c2034418040c0c000e5050031500041250b00c02200300502500443e242602118103583e10740c1c1c100130a0320440d42c0034400c10381c818080e07094407610520303280350400440d120700c02402e80951200480f5000903081a00891400144004402480e501d001c1c020f01d440c1c41d0460942c01c020070004c0c480030b46500040e04254890000c141404110411a40b0103014646580c0d03a071a80d030f15205440300d104881210210f8074212001500141c0c45c021106854202920b20b07540d542000c2d81a1300030321412019504000d080003080c00161070310b2040720b0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 119635566 1250 119634316 119634337
    0xa02300a020607080708070e0603091006090b130203070806190305010c0521010b0406030e070503010504050a051507080a0e0c0d030801290a050a050c07150f03140103030807020a0602 80
    0x4a15011901500104c03001c0c1c009401c111100341017084640c0d0000a0746110001240c03002d549442e507003c0e42c0c0c60700c21640d80145c81140341c00d0380002c900000c0d52118003440b030140c4407401c5100c0b488101c0e42c00c9000840380c65001c01c2d42c07600001d0003442e01010003110701250f80c44100380305480380c8440d03085581058054020400002d5100f0300c4090029442401d0090b12000c01300310360601c6020740641c081e0340700340b4041c140c583c2e4000f85c0304030040c00000c01403c0094000c005924042c10030710340c1c0f08e0042c6010386281c00340c0c0030b000c00114003440034184191400c1e00c0f1002c00d9103c2c001c1c500c0080c42e48018422141c040c000070501c0640e00d1215501005000c4c3c0e0f5a525194100300380003121014061344001600515406100300300b02c903500b919440710081c20f100c0e4071a056110300750350303a1007031401d00c2d4103034040d503500460101c0b000c1801044003103d40c4c1d00e05041080001d015001c85210800ba40f546800c82d60040000a2050f10010b9000000b881562188201541c03010141c0e000380d600c40 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 119636816 1250 119635566 119635573
    0x42702011404090506090a02070f03360906080303070905011407050d031407030e0a1202070506030a09030314270304050d050703051507050a030506030c0904080c10020a02300a02 78
    0x4551b240c00e0703020a0b000540070b01c0861038001a0340d10351000c180075040050502001c99501004844000c00200c041f4407203000b4180c0d00001103142e01d411003c90701070384190920300000424885c4000007503030312504183d1500d02076241408015140d040c84824094031404003005a6000200c041c0803480701c4140e50740b8045200e180b0f48600f40c4401d113006045c0d40030540351040c00c0f6161403000481070b51198100841c2c40f0450741102049080c05260b800c51600214004140300704d1840c190b0211100318001d5134100100030402e0b8160040c0320f420741b05c91411007000456403060b03800800c420300c0040307201012a490244e80b000442e4814011075010380d00d58024903410820300805021020209907200c03400340251030800d40c0640302e801808a0f41e81016642d00002d09292410007111400c81c200030310a421501d0300b4900b24105a0000c031a0b50300390b0052120030b6038450864020b0320100c42154000d46500000e0b42a0604003125040fa090f01c03003a4020740005101e0402c0000b003030211000d0380078 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 119638066 1250 119636816 119636821
    0x14071205090a05010315090504060605032a0d08040605130f0f0602151e0403230d0e070b0d0f0b120303041e05120c0109020405150f0427020114040905 66
    0x100301c00c03071400d41d000c0f506050130035440245085244203180c0540b2880ea0f000141d51300c2d1418140002c0286e500700640520a00180c1e00d000c9243d04605400c60120700075484000c0d49540c08d128407100220701c004e00a5101b4481448050f0298019140c02203100507500c28550f508e4502072880c0005600c28550300001c4101804203640c1400103081c040c0ca040c00c41d900701e090000f482040580c920680c888004d00c4800414100361207010643c43c4409143c0440003010605e441d10100d561200a40208061400c03500031011503011860300d007242c0c60881d2060a0100f450508000340140d510408842591000c251215a5500c8a80510070022000858817071810b842c201422103c03440304800011700318102000080d5001400c00a0100180625916500c1e9448501c2c050040c5103002540942000100405d02c40344084a400c520821100201c0d43c90a800900c01210030381050148020854000c1c8526500d0b00006000c0c1c882c810b1518100215400e0302805898009400032031006459906 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 119639316 1250 119638066 119638069
    0x16140703030906120501050a170f070608011d070804030305270105150d08070303020904020405061b060109020711190f0306060e07050c03070f0615091d01060303020d1407120509 78
    0xb041440381130a14100165410000010302c1c8010310f1194251103046103066007004102408803802c00c400c000c0891340d10b82d403241000340510f0030901a0010b28100e004003034500c8411264114040d480c0c41d1110000f40c0c40d00c0c4c07000c03005080010710018184d0551517142c0300f541410600c0c4c200785102400000344074101401250f102c1c044c5880e40c0c44c802d041c08134500c030114042c441224110b0b80e043c10016903544044001c50081d024951100380d0000380802c080485d8032440211541c0325007800c050794242c2c0c0c0c981180408034020034074090082c1a4086a803021814180088481c00048040c10f07102140e8528001c4e02585107500100d90703442d125141017002c14491801150410341e5400c00c5410003007035042d481c3d40d9004417030001d044a12801860310a10140e9400000358242144c0700d4450940c40d081c80c5009890300b81000380042c0d00504d1207455400040c482c0302d0a581d81a4007070890445c2404085403144040c464107075500008004043c001209000306807491000394660342d403145103100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 119640566 1250 119639316 119639327
    0x1704080c0a0318050301060b120915130209071d15090411040f05060a0c03030c1101020c0a0c0f0b0405060307140304030e010e12030a20070303020c0a091116140703030906 75
    0x1d004c0f6000b40c0c106001405210f00d61400e0780c0b04003200f03c03034801507543c5581c540c61410741d12514001c2c2c050100700c1440620700319490407000c2d89000b600c0c200b00d0340e200c01c0c50840d207040d2440307041c00c8606101380241c001c514240c8038241307019084c240d00500308428400000d0454103094040d201207540080c0c1040311001000154008050880740f03170307080940500c0003508591003002c0003800c0580e5a202488d40354080c0514040380b1030004001c644841d2010308030b0b5a07030001d00200796200e828407800024030890321010041611a03129030710f400d10b403500042c040c442e00b02520241c24801510640c0c10701c82c3c03a0328051882580282d855010518944001402c048000901180900e84c0c508117070200c41400800c451002d10b03071b0314149200210741000958400002c1c10050900d00683c41c00105059001903410902402202c05d0800d00780ea405040e812a828200d008180703040520004240075081d4070600441c900410509a46a5414031210300301001038004802062800c00248169a03002 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 119641816 1250 119640566 119640569
    0xc120a03061a16290408130905011202090603120d020d0b01030504121107030f05010209090121030507020a0b1605012711150a020f1207031704080c0a0318 68
    0x404416182000441604140c503c14010150001c0344400c00b0307550f1103501c40c1e00804280c2e220240022241410725180145034840d0110682d030400c03d002c04541400940300e0340703049030b548040ca612414060703401d11140c090010000d40d80750161520418820104500402031900c0c000c40062b682c03d4140c540c1000c94100340c8807181003519020820002a10440034104002401e06055034801e45c101c640e01d00e84286900000c003a07941031080385040140c150082c2c010741070102c0b4011b80c88d0ba00c0d506100032000121000406100700d0009403000309000700d00801c1c2942c00603100301061519a00091100d0340300020560780718480010544c1441001c2c0b15207c412420030b4040310480300d0041d40b100c1c11400d007590140c020540d5020f881080d59074020781c64001d072444c48071035840d00894040651100d04901c0300000500a040b4a40c0814015200310780109900d43c54110000f801207a5545650400030401c07a03401c8800c0222091a510420400c400030b07100c2d90702d800511707008042150550030070303 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 119643066 1250 119641816 119641859
    0x60c020319031209170d0501090e0f030d0b06090a0303020303100501111b06090405010303112116030311040801060302120708060f040f211d13020c120a0306 69
    0x5812038200080d4400c24000d00e440ca601e9021071444c8940c1441e00a00d510101030040100c0d000030f029181c1010381d00141d0403500f01440c1041040d0350b400c1103d841301858100c9131850740040000c4151190705a01c58001e101015111900342404040400d200107019002034000da440402003151a0a0102800c80580002c2c0307011116085060000f41ea10107130a031120340180b512005203a1300c1c0e00c2e10402c3c0d0b02e08c0d51006000780321302d59403403d0140441041c00031f0810740e8043d5035407600ca200b60390b032842d1544203004403e061401510101c0441d44039001a1308408150700c41145858550502d0058409020740c20000078200780380d441000701c07800d0341000307542d12900a0304c02080405000704003d41d1002031848546403030b80d900d00e40800000c05801d030003010042d00e2580b64085070200400c2c203001601c9611a012001c5051807502641400200c440303078810000c40c0d202070741039840d40151590060000448401e8a01d410161340e00da08011001030000703940d00c400f00200382500c0c541d6000d1404 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 119644316 1250 119643066 119643103
    0x15160903020f010f02030d050f0412021504030e1306150914031c090315060e0a1a130f0e030a030b0105030c030a0b0f030d0e0111070501020a060c020106050a060c0203 73
    0x40c41d40401d000000481c2414140901c5800d241042da000b4401c403550010b414508004519088403086000c00c0c0030350782550a1140441c6e188849400041c450200c1c100d441d5554501342e640b994115040d00b00852010f410459425109031714200034081d13031015046e007000c480d0742c103403160000800641055005200700068104031a0f1540c4000c940780403411040c0030540c0b00150186002e90ba00285a071004241e050f1000070140c5403000c65100c0c2050303e07502000c2c104581c40303c2e00c0301001d45183c803298042e1511001c100003d1403410031001c501c500300080b070100364a050501c0c5c00040359030000510a040e0000150042d4455141c41a01c0c012502400d2050460900c1c80620381e80e804003c105040c3d40d036a4103d1200e40d90f4910700c110341000d400904039124101038080051544143e2020540418075654504000082c040303816801d032030381070703000341000c0042d621800054048151154159541c0d04000702d810f445007050711016080c40e8541139060642481814035104001c0d4540d80d0148 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 119645566 1250 119644316 119644319
    0x2040b0303070c1a071a01051c050303191b030e0d110303010e0903040506030a0209041401060e01030506040b0a060207060224010b09040b0618090606070f02060318151609 75
    0x1030320300d0743e6403090f0781d210310380710301e102400c103c800f01c42e4414031802a00580c10080d41c1e40c0041c10144500e0b05030780040d24010880b1046225816500040140060182d00700b0f000041c4212011540650035282c01039010a44061051719440300b00d04175101100020f4031a407003400f070301c80208008040340485240c811650190031035210b0312404180994841b1800410100c2d61502e401c006507405001c00401050303407400e01c072040d00700035030007101c42c2c6000d5401c080e4020480021050b07814102e030195200e1a9107200d070785004400412004200da503029540da02c2000c09926044070403000b425150300181080c5042a20203841c100d00c040b07108688100d01000380e207030000c03513040c5241112241c500300c0d500d40d100e02000a000e82a45084250009400320b41608060051001200e20074000d07100c2501c542c03240010700001e40f040040c05002d1424004204006007861070045510007442e4041c03806440030007001c42e0074118000d41d003a0900610034244950001049465281000d084c10408140e0303 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 119646816 1250 119645566 119645573
    0x8030718092003161d190503010516080703090c03060207030309050f030a0e0d06020c010e0c04180b010b03090a051507172a09030a06060e0c0a050313080403020d05070302040b030307 80
    0x103080c040410001c21040c114401e00812038030440545c100700007070410101403440a814101c40c1c0b001c0c07140c40d21079030a010100e801e10580040d00c2c0290302450f40d40d4078440e920003800b503000d08130014080b280901216000004034460b4400740c0303502842960041149455404d01604e03018405000c41c8550304100207689034503401038940d5001070026100b2806071070041c10701000a02030300d5004002035007007480812117824041923040e215202240d0402c040c1c00c50005c3e42030b110001e100024901b4006000500c011031842d000345a21007a904110340c403600065580d03d042c841441400070382d400e0500240302c40d403900020416042d05100780d4101141c03510326054080a800007540348004088450642c0c000245a0101c8540100180c00c6801c0301110340340203402030099100781c00014070840041071032030380010201d0b05400d009a81d40c9085403540721030340c5611030060360100c4218008100000050722549051001c1c240948060b0138138500d10300501c07040d00e00210700144683c10403c000c1000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 119648066 1250 119646816 119646841
    0xa0b01090b190e06030703090309170309060c0f03070305030103030806060702030a0201270b03041202010b0a1401020c042901080601173402010e061308030718092003 73
    0x15140d0b031000c02200e1080d0380c03038195602501c28001e1504070000004009449030140c02c4820150310a503104440d5990301c040880310b02007104028403154008100800080c074106019000e000d043c2d200b030714220011101002d203182d2189404a010a201000420600d504615010792101e0190356452400700c03281d0000c0c0d251555680300074103121504c14803656042c0081d1900c1d5140c07407008200302050340c503221101810740046030b04442c030021001e03005820780d1040c02000f182e4040a056050f81c6410400c2c0c441c4003008144096045200c4d240c10700e801d80ea10760207105141e0303008038090482d402d0520000c03121078000c0784104e81403214060074007401e40d901030344071549031710b10094406564031030042110308000c2c40000141d056400380018400c120340c040c41d1850000840d0000c00c951012224081e8440804440078240c0c80e9004840300c02143e070031001181d11048034a0301807405c080c0b4401042c0451015044240465a0b600c44000b6600b036160029080e68001a03580707080d881c2c410042d051 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 119649316 1250 119648066 119648077
    0x50907031505041406010b0921120c150c09120c06030a0e0307060204080d020601081212070302090a09150902030411040e190b06180603251a030a0b01090b 68
    0x76140d58600c001428401103d28860000e640035061303600c40d5a54001101968008103901c43c480c0c09104401c6603100103042c0f9080701c091000c40500f80704222030440b1680c9800c2104e2010241c024441d407030750300c403441c03011582c800c2c83e4841816072602142410f0000e01031224145003040d900440300500560b4801c0160b0707900655401d804600090400d0b001030071800354003002000d642c0080303808182c4000200d1075070985e29940c5c0c2101e8403aa41d5030356035543d0314180e42e0309140301001000114100d6810f907008641c00082400c0151508003003801258112013551701080040f90303151940c520007448040040c0080032080380542c210309003500d40440c240e090a039000e01c0346a4a10203210816030900c0b5024110720308080002e00f100e4941440403e90320202c42c0e06104043c0d5102030706580c2e020420a074020382016004140315140304101c05a52140b510399481d101c005524001603000c010225001010b0402034015164240510100b0550740340381c0c2018140719508200b0b0001c0e50385407042d00e6 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 119650566 1250 119649316 119649353
    0x908011e05070905090a0605041103071b03050c0f06040501060b0a09090207030e030a0f0213020a0f030b01020708030d1505030c030a0f020d1e0203070b090a1202030c1008010905090703 81
    0x901e40c6503420180c468240039400340c0c2d0407125250800c8403c01071540301400f10b40c1d06950034410b00c0d2003e2610500c2c1d02c0221100004118144090b02c40303007803204848030400c0c0c400d080c9980f4000d1a100d4480c981a00000d02004582c061800c00080100c00e0207250300510507907007114200001140c0140c402c01003401852040c42e0b000c200c0005061188045a0341039801800703950041415041c03520a022801c20164007500294a800c810b5041520840f0301c42c001a030380700e80040020030011009441c4074100341e811071299a1010480d188144024100000b106c03100283c10942c104503c081c01d07159078806442500704a41148c0d0a460100f4580030f9035034030000700f91580803c1c0c400605100d2092102034868258912a0b030b01d102c14807a04042e14600071800c8a94050351052890b1a0340300d58540d064008181c1102000380391980440314119034801400d98542084140200b1100010b855104001840c0c10b00104020101c1d84241303038101c1d04a10203040d43c141562641b92140301041080c2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 119651816 1250 119650566 119650571
    0x23f07050a05010e180c0c01060b0f03010302040504060e120a030b0907021e01240e10050f06070510090c05011103040509010308160c06260609060d0302030d090b070908011e 76
    0x401503544140c54000880c00e01d0880f04070310b0800e06c001600c590451000100258a004000301d403040107001560440110340501d1403650f82541e00f400301424000d00f040f10800d4a407020100000030501604800d626011901910b58920040c010b00740d828001c080c3c0e0141c2d09003814840300fa6804904940303950f801a01d0b41828000b142d0f4110b005001001c0c903034651101005424a41c03421a140c0c0504655000350f182e20f1a481d40242c1c1400c040300b52166a501c00c5000e9a030751080d0404501030183c09015006888480ca0440d42d01025140c01810440701000606028481e540c2c04c03420041c0d40610400056060500344400304070001018003000e0b00740140850700c03040c0309904d4054012030560018101010720750f81d074006006584058110301c02445000c9160940b04400d01986115660003401d10b11241c9031170091102071400c000c0c1c1942140020003104007040c07032500910b980c0328410001801e1b58039101e40010a0990207400040c11030741090119a81012204600300d0b075504ca10000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 119653066 1250 119651816 119651837
    0x10290d050327010f030c2c0a030c030204050705070308070516020d030207030c0b0901021c031104030f0b07030c0203070b10050a060914060a050313023f07050a0501 72
    0x346107507004440841d10500c105403071415100c0e10514542035404000c1e00c030f00142c2281540142c2c141c8254064040019451500400035003103880181c4007640c100e1410031882d080414003140c0d0300e00842d0000d84c0d1000e40e00904100b181441d06c266039000d142498164101610382e64020902200940010100b080100b1400c0d50070710152050941309a004058006d220340e14034020351184000e01c0180c405140c412070000c6d090207950101e91548005a004e008040300c0f1002d49000410f112140b5001c065980020030403060000d0000c0001d940103c03c2541c8082a515080c1c40c1c220009182d9400c05045c6207001029540010070341e8807031f43d07001d603290752181d0b200d181c1041d611100f0b40c881c0740d2098841e20000303402e0303811260001c00d49030416901c080c0d1580b10700901c45240f00d41c0b40f1486c00200e081000540c51454965070026282c4000d250358160180c1d08a04000c11604110002c840307420b00c1c0b00a914030700070a2169482510040c06024842d10380400907220441600c64503040c071024100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 119654316 1250 119653066 119653073
    0x6040b011202030705091303020d1d0105030c09030601030f060501050a050d14010905060717010e040807080c2a01030b0103110406210203070306030c290d090b010810290d 75
    0x44c0002900c40503090070102d03c0c1190740b420f515007801e0300582c0980a01c0481a440c203102c1c0020308610034241c008ea420300d80c01c80d801180c00354070050001a04800038001d542c0d40365001e114041c021805400d135500440030a04040b4100c402c1070b8485449181c0700c0604000680303c0d0a1384e1000240c1181210040c464450002e50251040d0b0800900c58000c003c10001400c1c0c102031201c6e9180308003c80010b241c0e80343c07980614080350940d07000c0c00c0c0b803034180301010001d100c140040002c034402505030b03010003414460840c0c8490b02c0542604600da80e02c000321711196414030880018517024038061002d0859410f003241d80344240d00441c020051302c002c04c000041c0b1004c140c070903120882d400440d5649007010005000740000d0200311003017411107000113403454003502400760000d42d03180340380001d040e403040e0048103074810b000c40b4410f15111400e800c007088640304014004d0940002505000441401003000c0b140c504000e01090640483d10081c0c40200f055044144841aa80141c4807185820f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 119655566 1250 119654316 119654323
    0x50102120d09060c08190209180417040902030a05060405060f040203060103090b0103060603110d03020607031e0203100503070503030c0c040c030608160302010e010507030c1113020c03071406040b01120203 90
    0x2400341c034882c01c001d111303242c0d00d60003e0b14030701c284d030740040c41e0b009194445050801c1c1c0c1300300703030071a544031800000034000b0006444003140c01a00c94540c0c425852003803007054150303400c0f40e4007144034540c0c0801080790503d814051a503000604580c20400352411600083c40d80010a00803400307181c0c080001402a4041d500180b1301c29001108ac04581d81d40b0315010018001c240401c6521400d039030074680c4a400e11100741405203600d038016000d1980c4444007200200140e0428544503080d8265007030010210344001c602901c20615600c0009007403a050501c0d100d5103902440c041e500c01c00111201660114150071481c60403a0086208070040307004401801154202c800240905030310900140d65940265044910070f8a6200030100180019203003802162005400702e010490f0310300008002100b500060400141041e0510584c1a140c004a8101c0361014503d540001940024040c0359a52851500e0b2508010941071600c0d5640b035003142c00c184034040f0b039855007600003000c651313042c07 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 119656816 1250 119655566 119655581
    0x6040b0c0d060b040807050301050408030f04030c06020703080402040c0912080c0c0a2d050d32010c0905030a1a0c04031506031103070b0405101e0503010f0609050102120d 75
    0x207160a002142c3c4902c0c044101d0b034002d102c0d1521500c102c10000840c3c0c1410b0091038801e81d00704455a0850740c40b12582c82c4107500051003101042038484640c400100c05d403014000a078000d80e03400c1c07140c0c50301d441400201d0306ea01c4200d40034413030180810840c03000d441c5041000e095010303004a48510800b80d481f440e22910809035548001c480d8004545181c05203107290f1a040c84289206080e4062001c50001d8013040c00b031642c112740d6136070200e401f040d070200990222100201c250360205085c9802c07070103074401c16801c104290b51901c1c810105c10b54800c50800c06020102d0103085450b000f6034600f0304100c2c2c5404402e8107202030b400020b05910301c02003130340c1c000e6801c146110f080201d403111290042100e03002c2159030303250070790340c00c52103040010300c55003502d0351800b00c01c2c542410107040100d000701c110018070401c00d200034811411102d0722081c0d0307003002090b15030b15100d5061034185d5000c242c95030400c6080050303054042040d6039001644807041030299090503a19042c0c0c04c40c2030b0142c00407 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 119658066 1250 119656816 119656837
    0x803091309020a08010c02060a0501141221090117090d080606070501020708040501031b020a110d0807050c0f0d03020c0607141f0e0a0c0e061801060804060c0f0206040b0c 75
    0x112800203059813041d000f06c200200240e083d9049179541440a1080720020b005410f50140d80342613410160401c0015a60035207200821940b100c0805030015070202000d010111b03440f1004101c0802c556080150450300c0b0034104201c50040c5881c0350304c2a80d031a0040c0c1050100b000030070214049480b00c2080729840742e040380080d075441c030b6941440f070b43c41e61241c1308c2c0134000781c0b034000e410155800d00f584110f45c180051340035180d80190354940e1480104155902640803e0401004000401800091055503c43c1019229003544542004000c0c4d02c80e142c45806003405140c6000026400f113000c407440031084651a496143c0b03800d25a00c5022820000074a51203000040c6902c0310301000174190070b641143d0213000310003007214580e0f1602111180100424520101070001d803201e02c21699020714081c10fa041c0b0149000c4040c0c10b8100e0a901c080b000c1a5644180828001a4002c00020306028140303510500c1040034000e43c0c564004002030401400ca1000c6802c048103c0110f4606105 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 119659316 1250 119658066 119658079
    0x303070501060e010e010e04060c1214010e01060309080301030807170a020a0c05030f07050d1106120103060e0d080c070c030501060611100612080a12060b03010509070306080309130902 81
    0x206450558000c140701d0103a0802c2ca0703030000c0001620211401c0842c16510005c150351a10303111a07940f400a4074418403040140b02d0b000c1184616401c1c07a00c14800300c3c0c4484212003d180d49481034036800c850301078014400b01801c006c2d080d00490000c0d01141d044a90022501d69503400e6403e0500a2448024006105110004040300340c154009504400076018003450100c40340d0321010103968075020f2250318001d410000b8200814500b28194200003801188640701504080317000078810307030001442e0240304443c080140144200c07403151794401904880107043e900403250001d40001c0000b0001d003100000015040c04202c180100744c001903612100a0050710346900c2c020300f500505000a4417580304400c0d0498594985006110480d003403c1c1011346500403948454000794001805e020a0040180100301c01030030b40d01c540c2004000710138949849506140402601ca2406021201010304208050003201c10100c1120031125048491101703098510601c0405010303582ca01940c401c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 119660566 1250 119659316 119659327
    0x6060e040b0105120a12030c020307061b02120909010306020a180f0602010b0108010f030308090a0b0106030b1503090606040510030204050408030f242418010e27150303 74
    0x16040101d40d058803001c8419180000250786410b5a60340540300161000c200c007114908914000e5110f003a08030031030302c16a13146c134815403624825a200840464560602d45000442c803075810300c2106c21550000a10074034211903e40020f4400c00180000382c0115030000c0d10b455528000d4018155082c40d111030f100c01301d40d581703010519030040362181d0000b650031300095030041e40c841c011a505880b003010040c20b009046460455901d440140b8001d542e2056404910100d0000f42d051760090959603004031b054007151040c841090034400d008a607105050042c002c0410010540326400341e002d80b0300040c85c4d642c4484c4858104425400a5040713807609007840f00b0701ca4001c0065203d440e004000070b204e52111030300d5004032501986006207401d2480b041e00154030f005d11600d4030054143c04903031458030325410704040c681c0c004100c00003a03404401d031070740e05560400100380416070115580624415076040310f0144030445050340e510b509880c000664042d603000d0a4030880d4001500b141d8445 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 119661816 1250 119660566 119660573
    0xa061212090504060f091107020a0f031505090d080402150a080f010e0405030421021005090907050915090a2705060907052205100c061803090303050706060e04 70
    0x5400a9000d0000103822220119aa05043c0592000c0f01d1884010315000d5140c8405200104810303640301d00e60810801109015a481ea00b81c28013400d804011807580701d00d140740221a042c0c044800a00c42400d20040280c0d1050100fa490011074080c00c003001240e83d180300040844802c070780303022030b0540701081065445a018080c036104506005103104141d0701c1e040c41100329142240e0080c49940200320038498840200320041c1c01c104030500184440480c0d60000d00807884041c0c0080c005040462802040e01d400c50003030b50409a2410042e03e001810310200d401c6010401041805000000d10050b00b40ca03000d42c1000248640009000074914144603032a2840ea1810291a0641030030b020880511304818440e004090f151030381c0340341051040b2241c0c4003101f450a4480d8038079401c400000d6a07107501c001c1d400c1c085100d690340c20300215903113480c1e0704591801104518001c045e40b0b9110010fa0080040c40540e40c050030095103d5840d460a500074282c02d81280c10840005400d02040 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 119663066 1250 119661816 119661833
    0xb030c09040605071103190207120209011a07020603070c0227010b0a1101020d06060f030203060616230303061003090506013005010902040606020d0e1026070f051c02030a0612 77
    0x107520403035080d6049c00d84d1b1001c064030282112100650300180010041000300c4900440101418005440d0f90401496400041c85600304680c003401151414120760118a090303018007000080210840000c0704e0105010680c58805009040017050000781c148411070042441500d4030701c0c40341c02555501d4800030003401a00c000e105080105000d600005c0301e860190090307074403c18028001d142401c80b612004081d011403032400365040c0741c00d0725400d4030b0144030503501d403401d58070140219a2402c0500a21541c408440040030815291090003030020707401184d428110780d906845a55045c4000c1200c0d4610341c00100051001c070340102c40e5404010301074000c01c488a00841c2c042051a59071181a81c42c0c05034028400c00180100e031360b4134240c0c13a009040003403848a030302c0d140034040f0a0700800c1182e480c7c02e502c10b0031500010320400c0340050b400b02c28080522258a000d60030100c0800c400c114107503c0c10345905002c0d8000c400030303a4098003580b14070020b08c890106414180ca00341401c000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 119664316 1250 119663066 119663107
    0x60c0d0e0d0b160f0819020a27061d01090b090414040b0405070b030f132901090b041b0f0215010e070e09010501020a022b080a030b030c09040605071103 67
    0x204101c035a080c00b0080c0101c050510803040220b003450f189130b601b8034241c001e61085000d42c052007503520780e02010101e030380d28001005c000d0304d441441d40d50502c0000781240c118000403040284c00d1183c1800166800b440600454482194a0b40ca1b215140d001601411525514501820845042200344a9a661800d010380d001c0c50949034041c2d168050b25000c0d22080300c6c0303502807500c0b03000440c0603403045108644100340561005401003a44500c040a00100c2c03580741810352071400300600081545200700d000815048a0800220700441d00000d908910008500107002101e40d881070294001e011101c1c1880c146442c2950568650014a84003d01a280c2c0000565282500b10203400c0c003400c180e05942e4160020100c8511035402c02081d040700d40101c802000d4264101010040060203011130184240010750f2540c408407001011a17007588081071295001100781c46060f02c4da82000341d0055080309020641da03072000030a58041c61014100ba1403407000051004052000c551400c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 119665566 1250 119664316 119664361
    0x1302030a0f140a02090f04060905070b0a1b051f020c0607030f0c09180c1e02010603050d0207030206030406020a02010b0909011a01090803030115090819060506060c0d0e0d0b 76
    0x24440395140a082e590f0b0402e41000703402000f0040491130906071002e0341075000c1d00c16200403e107100c056640c18240151603000d004410740200c0c0710924680c2203900c3e003e82c0f5008445103401e03d02030340c82d071075512502c0a0000d0a100c01c9210b480d402170b1000e80403500da044010088413003034209800010001d00b0242c0d0304144692810340800903852040c15142c0441e0340c4c0c1c004101041c1c0700c80000c0001824507114113800e1154440c51002455054082c820072240550000100146103007072050805520301c40690454006080c00d100680c0c4d841c09580d0065005180140c444ca4480d0040e40100000c080603903000000c0001c00900900c150058032034034204c40404a88620b0180c01504e0201c0c00e40500909030300188014881d5018041109261004d54074104a00742d60342c0b42030030b00300036001c0c442d2000d0034030608101080c0b00960083c076800600940344586000b084444141c0c450081e41303114020001d91030005125941c4d5104446d8100343c000c46040828140054024603640c405000c40 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 119666816 1250 119665566 119665583
    0xc0102060903041749090302130204080616080f090a03030c14280e13020901092402060112030f110106090e0c04060501020a030c0f0206070f1202070f0602151302030a0f 74
    0x7080078403050711700e50104400383d80310155001c2c00d40e42000030358070809600c600d0142d1301f030000090744902040181d00694641e1001140442c4080c7d00500703181c0000c2118030409900014400d0b2600700103019542c0741c0d011310700060030b5100e0b500e04556100080082c0701660b58041400c2006046101003403403660345490340c0c0319800425400030b4803410200b1030040e51021442ca00302e2440d1202d0b030000d10300c00c0b405150000c0c20a0321345625901c4402d1245071850103085852940304101c0e01001b0440c05001030030140b0503281d446e96002094403980d695060204151813068100d00d030825044203000d000140020b000da80d00d50000940c0d40c00540c0b01d4103105a0401303000041c00d5001060404142e90141d071031540c0310040d07132201420b2055182c41241c105000704803480100340342d85c4410b0185ca11580400346442c10040e0000d00d000c1154000c0c48520803460b408009881d000143c043c62007a2595130b80c0400e42d61700301081c0315110000d00203501409100021420490480c00105c6454417610303d9 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 119668066 1250 119666816 119666923
    0x1090e0a1b0e01140306030709020f030a060503010510060c060b1201020703080c0406090e07050c120a080603070e0a0e01060506120618010305061311031e0c01020609030417 76
    0x7180c4800d00668018040307510384200d00c880c0340d0300c00002e41c2c6c0444042e04440c2c2903542d801c0e082c000c0703034000e41c286810000040103000591402e4003981004010072002030150b82041101c00708050b2007440740c041486981849c020800100e904020300d4000c00074080c0303112200700c1503918040e61040c402100003030381020000d03464003201002c0ea01980c0c0b11341d40d012043c9050264007040c07040f01030404010b1000030712010501d01c80070480c180c2c400300402c00d680d4669287d014040c0c0203601c05004244a500221420301c103880d0711002e010351255402c00c0216804032407010440c014002078000540100000840f900c50400c003040203130084100750784207003021221403202030550000307020042254001c2d81c00b1810741c002019042c058203000d4000b04045100c5000000d290142010b08009444403806a076407000009000550780120280042c1055103815000c60362280b01d640100d00202d050101e100141c03020401032000e010981429000040060708510300c6050051502c081240701168407 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 119669316 1250 119668066 119668121
    0xc03030f1e090d09080106150513031e06111801050315061204031b170a050913050910020f030f070207080604141e03181f0c0b0603070614030601090e0a 67
    0x1f684112440105011070141036542c4c12205644822000100c4400d4140d011002c075070f2107900001880e072120081d201c4d9003290702d445419204002c0800c15a031800344004454540c10003020780100c0401d103061070b60b070b0381c071032100422000b94010080c1d0440c10116001e030b07000f40001c000900890203506c42c80f24140c203000e8507100004540c0c500403c00104160290580420384c0b007d00601082030501358207101c0e000003c95580895000640345e95921001130000d4244144007801e85000c0c46503055141c55003241c40054280700241009000300f8188001400140c424072500010300702000c181c0301c5074100f90802074500140034144403a54010003220703410605245d281c01c910348034a50051800d040c5040c0000c0d038940300c2a000650000080402c80c1007280000d40e0001e001e401c2c82e190104042064241100c000f140240303400d001c0d038010142400302e6a009040204641c20104016981e640c03010f00484100031140d2100300083c01036401d0003e6007405400c10310040005049000071102c0481 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 119670566 1250 119669316 119669321
    0x1002030a0b030a0503040621021c050c130b0306040e0a080408060108070e0a0506030718091e080f031801050106030606110a031409032a090a020c03030f1e090d090801 73
    0x14002401c55101b040104007050150030ba600344402d040314642e2801c081c03201114242da02c10100d510000207004500c200b80f440713a00c121038010035034840003820300d4580d200b518441003480c01040d0302d40401200080103540e5542001480c10902404d84d1800f1420f07241075015070b0040c8c02006000e01820300080340384c0c00c00103101e40c111400142040110780350304040c003004200180105402d40204400416000b400040301e081c60101d040c0b0005204c0c00e2418403000300581001031110301d040c0c1c2e01c800380110360001d080d42c070440c3c07501e00d595680343c5600070782081c181c070500840c1c00554248800003607000c1d0903520100c01c03601c0d41e40ba14190f8103040a85251207842000340100840d12094100341805030503005082c4420700030f01200c001c14401d95034810810070015000f032030300c8004280d082142c1040b6103126040040500c0c1035043c1400c80402c1e940f80d0200511900d003105212000651100d1242484a01101340e1007015055042142e201034941404d505080003042c1c00200016100c041407 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 119671816 1250 119670566 119670583
    0x2040f0221060117040212060f0106020c010c0206070b070224040201120b010c0b0705130b090a0501020d080f0403031811120a0f1209170d090b03361002030a0b03 71
    0x142d542d540211a13680d014889480068030a0f6040140303c41042d0703c40d103080000a01402c10760200913095850410001c2c80c061951b0083c50402010411020042c1c490005440300b00394440409003150f075485004a01e41603071007a03608078065014101101d82071186003040e0040f4001ea0b10001221032201c90310081e02c001c009046d00241c1c0040241d808103102e00c1d01030b80c12001529026250005c0c5818000c0d04101a41280698600c001400c0d8018600046034200504080c00a84171490216101501560005102060744071007400041c2c101423295100c41d011360108080c00c1002d410500303100d5101c14840551a000d1200d8440d640492900040c2200380c1941c04441006540115550034603104400102030302403000407140407a1390310114413003c80f0784540d20000c0c40c03032913480a0700030031521079580020000b1200308103000b6035085c0d02d40076078000840c003241c6a501200701d190f10080c005982420807203901600038a54009080e5800450140072002010b1103003066420805840300e084 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 119673066 1250 119671816 119671819
    0x501090302130c03020c030a08060a1202010210181406040c0902160f0f0b0f040b10060504090e0a0501050106020703030e0402040f03021509040510030302300903030702040f022106 79
    0x1504904120b515250300881c1c044443c42c5009801d01051510540c51600f1900446000c0f911003800c022540c145400d0f080000e2880d0a1030030000c900b1500040e480700404001c0ca2a01c0341c64031080301103160000440e41c5c00d04d03401030000d0b6a542c20191031700d440d92002d03142194522003070900010004482c2c029205103c40001c501c80580a00e9074506201e641d2400040700d420b031a25070940c02041506070014454034482807141041e103850301c3d00401400c8000c0c900e55551092003418426142c2c0002a41c0c140e40d080c080c0000e4049550802030b181c50968400113001e5803d103400824140c2d800f01d11582200d100751113901081c1c550b4800c010990140380644298444005010030151500d941000741001e0f500b00c0c603501e0551141c01181c10b5503000c8450080c052203800041003019810010109030745540c0d40e02c0c0113180b07030303030314005598500035020802046e5000c612801c07184c0d01070041341c101c264000e01c01c01c02594000c0c801c4001c0c0d0404192410350500e48501c01205105202e0510f01ca40760 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 119674316 1250 119673066 119673079
    0xc0b16020304140112090602040602060903130e04051906020a02010e150c16060504120f03180b0c25020406050a0f050409080c060a29010206040212010e12130501090302 74
    0x10007001d610240e02081c2c40604200d076010b410b00050b1506e1055202c81da00030351002d40d44c0c90801ca0060724048014019000541c0304214091315010021a8a4140c41d0000c2c40091151510704165240c405600c81c0002d06900c00700d40384003000040da00416004015800174040e40000c40040c60311108540281d000141019000503c514000d5001744464110088006451303d19500d96000300d51089804684071520f0a1039184c0702c2e9041480d440312625549000d00c0250610b5401144002c07070000018075101c401030204003651400b40540701f8140700c03015101c02d030154810601405e0030030392000764011071422401184605248030120b05a800c100c5454140da45007400340001031404e5030003618000300a20007032241c01420302c4003500940c5162400304180b14141150b0143d60600062000001e09000108507981d8001c151143d0044d011914a4081c01c42c0620517805088180303005c09850094544013248880d071100a0041800074030702c000c4400303440c4e8006503500041800040e6010342c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 119675566 1250 119674316 119674319
    0xe040605090304120f02010e040e1b0f0607032307050d0c06060308030f040c0902130e09070801090f1a060a03080702030c130b0906150909180d0c0b16020304 69
    0x45854104503007003542507003124a004d540340c1c2c070001d050110b07000480c0e01103840d4a015042d583e101d0785251070240201c800b00500314034807421704c1d5118290702d0f41e00c0c078000902c4046100ca41d14140b10b81320756a006002a50396041074a801015030401e102c040b92040050400c44d119150304c0d50a684006a0000081000e017a0303009090380c521090785c00444181d030f00c90101200151484c000346000b416a400d004000742030900e800b5815502a40001111500c180159075001c40f08010200440381d4003500c4040b9600c442011a08001444c0c010350010360a0403441c41c108220402e4902c00c40303006d0710b607189141000100d07440e00190259034041c0d1081c1d00907400d0010441a00c02450543e100400300d840002203040400c0901441c40396030b0014580c0c030f2132400c42d030b401c02000d0503903c554111060401843c9180a401c458085d0165540c00790f8120000a000301600c9910902221000003c40740c0100c071140009114a021110458030044002c000c1814280d0200315207800040d280c0145040c503 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 119676816 1250 119675566 119675573
    0xe0f030909090a0210031a04140115050408010c0504080d111509010e0105070f030b01170a020903031605100b03150403050f1308031b030301062f010c0305070201150e04 74
    0x1c20054500002401291032a2006a440c01c0d10b24004041940b00441d1030914148940384860384050040e0041d801d104207584003a0200009506692200710000022440307440111507500076a00b10f64065845c4c8006610220b4103d405007046841180407903192815400c421149840512854034003a8001c82c158040c0e44072000d0020380c010220300c000146401582c00d41c5007500c00650307131074011510710031840c039003190316000d0060030040a08156150203081601080c0b9154024104803020f6808508000769a0b000d00444001035040240b40351040110304200d84c850341c001c0400c5c0f41d900e1400440c900b07241000303d02884403842c4000075076015070b01c588040e240b642c030040b001d4510200070030149001c0520301da44440606220b8000315100c081d051030245011568a40c0b0402d03541c810302c0108182a03004e0800412405e03614014501040e0140c0701e0802c0b6a01d6041e032404950a08444c00d00c401e5150b0f01c00b43c0718143d954004d100300021440d00b41040e4402c1d02414400c83d0900380000c010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 119678066 1250 119676816 119676829
    0x60306060d0c0804050606010f0503010e0601050918011e0302060703120b041505030d02010213060f0513060521061810050a060207030605010603060f060f090506130501030e0f0309 79
    0x50010380024a0245030341155412114100b0114010916910074001480020421598000000c2c03c0c20103400c000414013800324081403284400031041000040c6090b4400c2c400e9440030b03030020f40413403100d40d50720701c00446c103240900a14403107070010a54080f580c802014002c044940103001d0916045151724110340c2c000c4a01d60201c600c51700c81200c00a240c58509c144c841460141134813110070f03801c1404040c03c201040e0107420071603005102009030080703002c00080c00c891403070078019201b85210409a13054001ca100d420701c02001c01100040c2e0300d401400070401e58403a01c05416143c00c9a44040207118801e41d1201c0e00490103681005c002404240c0355500a01c04900d01c0420f1a40c1c1c50008110400039040400141c10102c0e0801c10007000340601e42c0500100d040c240051350400080200108242c8100403c000850b00b0304880c1c28002c0313182502802d0301806055031494545d00000344201c50340729190010745050050f003050080841d038201c0c00f01ca4a000342d4984412203013000b05 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 119679316 1250 119678066 119678071
    0xe060d0b040605030d02150f1608090a061107030f0f050a030b0f06070f140d0c061a0306070f02071202060405040902011202070f0b070509090a0c0201020706020c01060305061308090603 81
    0x100203640304004102a0303010883d80f05d1281c426402805440c585100400d113a00000d0700001c0c0c45c0c0709020034040c8002ca0f40496507880b0340c1c64038040c0190b645005603103140842c0c03408040c00d464902038072400e0141480000b00020fa01a88401c003141c05030b4030b000c48040d032100354180009030307081c440b40c44458401c0e00302140340c0d00b00401120380c050010001a507158000d0600311450070092201c6030412000300c2c1c100c5400314040000e061545408240600701402d100c500a003141d6590f050050701c207508201103107034040c000c2c084078601d2501110113010a81100940c0003d81700b00395000420040c402c40a26440c4d60140425041924000c1440050300a82c0710480c1400184484020140400d2001d048154000c0c21007841071050703401c0800b00c0c4100a44000108034042000ca00c2540340d8007100f54002001d0100040c00e800854403c074024007840740000c080c80e000050b0b04e0b010b40d40c150810420341780503400303070307485a00c494002c5110741180420043c0070100501071603c091400801959 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 119680566 1250 119679316 119679319
    0x5060a05120615010e03030c0c120604030c0201081008060411191a0d09050a06020403110906030312070e0a0321020303070c030f021009051f0b0607020f0a1715070e060d0b 75
    0x419058820002807d5400000250020781e00413105030034141743c0020008914150400601240d05050309c0003030000e0640540a13061041b0840820010036000302c0400050800c00240d503104d040503d44016139030108040c1e940318502da034000d4100580070b4100c0400320b03580c5808580d0f07084140503441810342c03c65a8a402c0c0940c0c0c546145001c03600c07d10103210300e40e1061000594880c02c5103009003042d0310318040940140448010000f668500200700c400040c68410918010345e1050401c030b900b6921142102d420203007185e40001004010400d0a20340b10030441d41c0c200b01c4a024004a951780811181c0c40001200c030240540407a004d004072000d030081c075205455481c0c50b8100e505050f2004120111040c1c0e021803081400c00305414001e000403030000d02c0900c0009001000240c01d1b007c0c070314005e48036140444001000741d0780ca201c0321001340380715400503510710000310071942c89013100f0000712000350002001072010342c0f04061503605110700030410360070304203140c20360700041a5111155 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 119681816 1250 119680566 119680577
    0x1c030e030102070813081203060108041103010f0c0f03060509070503070819150e0603011a12070302100201020903060c040803030703020c0a0c140a0e04231507020105060a0512061501 80
    0x40c004250154010034405c403117045011080ca00d0700d050355181140b81800d0b5281c0307050520500106a074000b00b5190040d410194080b00018040d00280c01040180500c404462a14150740c2c07806400c144040f0301c101072a00c04120b078607510400e03c903001d041155001c1c0000d500f000002c00c040c2c0901c0455070840f044201402c0c6001d100208282140e142d00c4141a10001d60441080514400181554010710550091001704070800403041c01400001d440b0f44600c250350b4888461000800c9141c008540081c0110000756070488043e000358800102d0758040c1c040c44d070016043d1403002d000c880854401200851455850075022002504107480c3ea48041c026144548042600b5411210280120500251340880800100110252154040040048590100300200343c00d48ad14003460074413110229504000c0181e1141002640c500581250307106000b48042c050741544041c2c442c080c1601d96840c200e840f0020072400b00b11880305100d0340c1d40308000149000c2100140a0316010060401 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 119683066 1250 119681816 119681827
    0x1205040507031b03240509191202030903061009050c250c152d020709020702010e092d04080d09050c0d08030f060a0b0f0901050904060e040605061c030e030102 70
    0x1840c24420240c48520b1146010907001000c103145c82c4a0140c10008440081000419004800d98a800e81c0c92000d05184075000314410107034024801c0f2803400382c0003416189945000e0f0710ba0340c490517082c05004090744c9080002103603418404200c420f02064103ea00102c1c0c55000002c5030201c0c0404c0d012501100392040002d41b0000e14981c82e0380c182c2c810b840d0764060a0b0340070a507200300c4007c4200e5801c0d80090751002c20050f9004103501c400d40f42c112170701590301c609600042e241b003a03a0344120360704215143c04004114401c095540c0c0421a1006803885250511084010891060394040c011040070440c40c059088142d010312055403060003a12007035000400001d40c0c141c070072842550f000400104204006901c1d080845d4441d000302e90003d0800c7c103281c241641800b038151010580d8400207124003650f0b020b1815904030340402001030203c59101c0c480c1050400003510212280c0e82094042001071501c81980d0404901e0100450280080744e201150f1100d111940142c26540c00c010703 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 119684316 1250 119683066 119683073
    0x1260a0204060e0f100b2a071806060906090e09011e0b0f100804120c05010f0b19030b060607060e011401030c080d02030906030a0b0a080d1205040507031b03 69
    0x5581d00a22150b6103a40c160315000e20313411079160b0f00901030300458400c040c091040d141010300b41c0c0c01503904800c1041180c0d01035602980030045a02d0142421711540074001605003003c00f4030160003001101c06e02039544c0d10030050381e01440d240118004949134400511800036003212050340b00408100100d0260480040c0170780b2940e450a83c0309015403034001c41c0144c0e06080c00f07001043e5070140c0701c01c0b2070418a80b10003000160058401440139220042e845c101a109001004850750400000c001d0812004040401000c1040289014001100b02c0c2c0c0019401c0c075804100300c03600300d515543e040e652001000026880000100c0701c9039622403410910708000d00c1060312062012170049110b5045041c2020707000b84c01d81c40300c20f5540c00800d1504040c0c4e400f00c15501c1182c400d448203500c2e40c44140b2200302800c005211590041da10010004a002000805e061000a10f8403404107489040000c070050700c0301124054003c0d0310240c410400170758460000801140c8854005100944a94 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 119685566 1250 119684316 119684321
    0xc030302101127191e03050c090615030705070b010e04260715020403030206010e040c03020415030209090601090f09050a02090402061303030e0f0604230103020408010216051501260a0204 82
    0x12100e1303418292800c0240940074031006407a050010014032654071a02d144d031000e82c2c0d0941030000a010b230f00940046802911a13030302404400c00014100e507281d2400d05001045a08820b0003907941151660001a0710400d803800c007401150003c3c00000354403080321400d0320800310405282c48040742080f02d80b000c10142c01c0162008400c034030001d41d8540c51401c00a03c0e194041e0003c00c0c04040000a200020b10726244043c11a541a00c0100c0c140500402d01d4004c06010741c00a50840b8280c0c1c20001415004910241aa0130360382c401c00040c401054030600300d03811030748018015405140080090310b002403503980d04c41c0c07000300110b02e49142c0d008260001100c40e44114081205c001603c513040c5441d1032a590000015581a8105031400040c20210f00e662906034800446202d1046256403294040340e0240261100965691300380b041c00000f0700c1300c00742c8151903034015150398510f03490b0741400c014101c941a804000031826a0071a07001720840800c010280c6204a034a0303200141c03141e0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 119686816 1250 119685566 119685589
    0x31709100f0f1b0c170d020c030310060806030312130215070512120109020703140c07140301060e0c0310030f0f0b09120d0c0e0a030c030302101127 65
    0xa000b0071404503030a440001c3d15141d201080d1100e0941c00076003812036201c0c00c407181d01c40d081908264040d164100442c0340b803280041842c00c85000081325000103c00000545c0114101904100c403a640d84c08202c43c00241503814a0f4541c01c1000100c498000300c031041038005094488842c1a0115580000d1180e014903540c01420100807548406000c001c2c48842d44244400789503c0c80d0105c807440e03a1070807071414041c3e0000c0a50204002050510404c2032a1103400140e01840e541c0341c900d0f0085503926024401c6000700b00ca0b040f00d050041c10103018100c00c680c0150b2210071a91a011507404480e0401000e9038019040040700002040c554107818841714000d00f04500c202080d8140070107464802000900180d008034814046d82500a044400103208920002562401070070111410031804110b1740d840410f81001000344001440204200d91082e0221107135030b020845240e0a03a14403200121040506100c904115000c00d0f9001d9248600d0b105004900349001d000503c600b070b0308 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 119688066 1250 119686816 119686841
    0x305070e01080c060d020a0c150204050f0f090604090f060504030504060f030c0c11040905060f09060601020607140f0403080a0306150302090a120507120b04030f03050403170910 78
    0x81142002010090800c190140c00c1c2c403405005070200e80000700e6807500c16000f540d06040d83c0007484003243c601c5a030382da134503141e800080014907805400000d406034010b4022a88034000c2e03403c03040058901041d0301d00141802030560441580d444d410000203040c03201050341c0c0c06206540071000034016101d280c4c80780e8800d8640c5038685080c210001c0540300250a18811305140c40305e002c0e07000d90043d240038102948518840c2c0345500c01c3c00402c4c0075200c0c00d80000c0c81c030b10440060110b003220344610710b4442d19915003164440e550b014012079540500f07a441801140d5201e0040b081c145440000b000c06001c500c4405140c603540fa0350700941e0340c1c04400342c0d0002903034038034007845441c40000c542d4014194901d002c1d400d0414120001d0103003c41449580e0b5014807d2902008000e000c1c0b0030000106403c0e0074420002030b0030705210903402030868003100000d800000d04034949002e03118090082d071301940c0b001301d004940340901c01c1d10700c00a496002d5a1203107a100b04107028040c01140c040c0b980c6d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 119689316 1250 119688066 119688073
    0x1a0702030c1f06050f031e010e0a0f1a06090103030c0302010902060a0206191b0c020301110406020303010906090501060804030c020117072006011419050409030c051e0606100908070305 81
    0x1080a4014200c81c03198004910594021a1740c0e40030755400a8040005c0400789500714100c100321480600404440c1c03004c0d01c3e24040c230100b42e0184008109640f05090241503d0540c0b21441000f40600c903d0032522190710080041c010700c0800d01c43c00a1189192281c000043e42e001d02e50002030168110448002c01a80840c042040c072100c0c00b01560b01000c074080087c403180b614900c9201c030b40030841e4040810400f00110220643d0380c00d4018841440c0d090340340e40c2c0e40c4e0f502c4100084d102c1c0c0c001d0203081e81950401a0004140c00540f05603412514590390b4140c940c3c1720f942d4101d031390503000c61003641002040c1201182e0341c8440b01c00035000d2911501c0301d5440040036200281580801d5130fa5035415000203004000b080e0805c0101c40c01e24104640c50030072034080c0c2c0f60011121607180c021030741040c40e00980c2d0301095008008006800d005908031013904401d0701030744100f4001c0c00c4c4031600c035400000228000d810000000200d185070b42c10101d8801e43c41d0b91055281164030b88c4162002d50 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 119690566 1250 119689316 119689363
    0x151107050c030c01020616050f0d1b05070b040201050901030902040609050109111908090717160503031804020f070209160809070b040303050711100e0306060d1a0702030c 75
    0x803080010040c0d50400b54050321000d00480d00103900c0341340046c43e0a00201d04510800749240c41241112000482c107024aa1540203050b10580100048441403a0600449a60485013409007003030351a190340c002d0701c2e40c6050b600c540c0111500e4001c00030305818103450741582001079480b405840003502c0d003a1f41c0043c0f50b44c50700944030284c13294182c002c4813103501080b400c2e101e4003985002e00c2d03151155003441c0b140c0781c4131183d225203824096888641d0301d400000800c50b9408002c100142e8030140c0c0c1506108480c0c94404040c0c0381e108501c500e000d409a840f03240c81560800750040c00810600c5c6200d41e0824840b50080f0310b46000460309051803406e071103d40c50425412520036600300f4894801030041c2801c2151340e00040c4540e00024041c0100450304004200021110004008014104441d08003144401409001402050b070b4428090600050701d58140040b00808a0b03400402940e115010140c500c00c3c101400f41c014400c5000070480308881c05000c2003140742c1100300d50700500542 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 119691816 1250 119690566 119690573
    0x1603030b030d03180605061203070308010e0f090c090a0f060803030f1503070e100906080c010807051806090d02100c05010f06030209161106100602010b0a080316151107 74
    0x2001c8201c0c0d00043c10301d02501d200c402405202192141395014400080c81d84541001580302010507005180500c03000481d0004c00d40c2c040011812030f414900e000b036050b181c1c1e820500724000d080321021485c0c2d00c0294004014500091031503008400d1840c00294400075103001400d95080307800007901039000201784190012000106503011040040e1400c0a07540e0000003038482d8021f200c2d204c0400e40200100d0712915030f11420b0401401401020040250784450711501d1300301c2c2034a07860228607042c000404181c066805c43d8101c420b0008410445e080107802c210f61500105440c1c0e1300440030300b00aa00584a0f5054459070812030348034182c01c84228034000d400e507803080c50303a824910706050003000140c41d6000016003003103014281c10b0007000e07038010464008010b501c400e4028840c55050007440702e5040003040645440d903009000414050092064440d900e20615600d036104005800311150000107540d1524420314030352844ad01d42c60800d1081d202440e001c079200890001307104040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 119693066 1250 119691816 119691823
    0x1c1b0e011706010b0f19030204270b01020c030c0d060221012c0103110d05010606030209030c04050c19050409060f090b19030209060d0b0c07032d03111603030b03 71
    0x40c01c80c104880d20300108805c0300306103070182140710007100000201540d0b04500a8060340d0241c0a06e1006a0722040d41034683d9000c071a0039880c11061074501030b0021041e502c04104200d070700380085d00500d000d440030400d10640e11014501910f159600b41306000c1e8258029004025900c0559060300480d4100b07034a41c0000c003024000640008003c54060102404207410141102e03007090128501d40b001602007041c80000c140000c10070351030014040303800c1d90107a000d058240401d804503000000c41c034040c44102c0c0c005440400e0852000d10646410090702d50000016112900d030035070510b96161a2071090325840c1d0083d0003a44040b1006101e0b40d45584030b2100340e01d0003218041c00c40d095001c1030110303560003400040d015041e0710001600548501003140000c65000313001d00900e15002c4009140c641041a01306d0004100340c0000c805024200b02c03031640200c1513a10508200c088481c19001000d610f05500044038040c403124151401c84102882c40f82e0190310042075413017184041504 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 119694316 1250 119693066 119693069
    0x30e1b01112e09080c15090c150310120503120a020406050714031c150605040501020d0309110d06090c0509010b040501081308070515061c1b0e01170601 67
    0x1107070b010404071603440c1410310085410340c1c0c0c1c0b40c1c06203000710000d0400b400901100c00c00689082c50000e502c60a0800000305580703103107146515001c16484031007040752a0501e03240b905510050319212000720880e282c00564114140c007114400d015a00d0102042e40c4581c007200381c50a80000c1010352010868044040e405440c1100071071030030b828410080e001e40105180504500d454102000c86110100f0403a4581c0b42d1421007044c4641400640c040540f015280d00c0b01a21104580000c0260042042d103007600c0d8160041e151055441004500030701c00c0100035201d03032000620180103a11550207568040b4040c0101080080050800400c00e48240d4401c070700500c00f500040000c1c68032141035800b913800901e0010074944074111034807841e43d017001002d0800c180005201c01041400110347c0d205a1500c1800a81507441a082210030426a2450180d100140b404100080ca0091390081b0b0004c0290240540645809100c500f1640036088a000c9029007100d880c2c211008101072760 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 119695566 1250 119694316 119694347
    0x4030f08010501090608040c0321030f020909040803190c030e060702061005120c1309020a090c1409011205090102030105041107020607030f14160303320601030e1b01 73
    0xd425525000008081040b81d115010030031001d070000c1810800ba02681000031a008640019072129a44000307070f80446015501012918084000901582e80c0c002d6034021103005000c102c03a55176036200c40406a00090041012600c0e200c43c0840d0044180300d0010881541d0b6000103410040b501c280d07141c05c001034104401d56102e00c04000c501070100341c4e401d040d240280c80390500401e0000c400c40c540541030300c1d030aa1201c2c01040c0340380c102015912880b602c9000700d80b02400c4642d90150407080799003608840c0d0004070400c06415020b80311340014158010181342c4002e01c80c1800103030600b00c0d4400d48500040d40d400100422081c5000d00800300341c6040e0031250f0f481e0140c154000b9a40e4422075000500340000c403181c5444180c081c0951b105062420000d040d0341d580c2800311b116510300140c4040300440e00d004454640c108401030703d20304c0c2844c9034641140350414100c903a41000d200800c02070405450b035508004030402070021448401701241038030000341840c0005803c0d0502c440208 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 119696816 1250 119695566 119695577
    0x140405061c032a1208160503041113090b010504050106050a020c10020f03031918050a11040b0d060905120f120619150f1803020415050306040b04030f 66
    0x8036480c8075104408044260706051201d03ca000f0300100081d603807801c0c0e085142c0940e42c0d644100c00d01c071140d2582c0030f400503541d0300c40e003030b1703540e0320f91403100e600c0c080c40f103640000c0d100b0b100007000900001885410320300000c04580d10214880b0310300095030350b0100c0c02c03149a091080104103608141c010390740544494103041c1d0510505e0b032402507849001c204240d1180c5400d00307158407498020700240e403140b01c3d52020740b0358034540390700c00403038007031008203d015010720b4416529030311840644c245d106035501502806010341d1640341c851901480001d0a0361042d41c40782c0c140010744c0c0700281b080103584214008110f04c821418010f003442823042d201d000b0704400b002910a10702c9030700103c45032a112560305d801640c49034008a81102004440c03002c05048801010421001070000c03440c001845035035010101c00030b4101100c134603520910b50b14580b0007600041c00140340541055051034590540b0010190342c0d40700181c40c00e10141c9050740c2c0d072010034080c0b00500d64000c0d0040082c0b062410170 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 119698066 1250 119696816 119696839
    0xb04151e020309041d0109031d03060c0409020c070f080d090b030606090d0c0b0706090b0601020705010504060f0507060606091d040b070c140a0501060602070501092303030c060114040506 82
    0x65203d205103c8524032665541e4160500c5c45490110100c0d8a001d202c020020501c0303515014105900038006540007007801e50114526140005500b842200360b2000315040500d0b0401c0d0602075001320700d851415004450000c038058400c00d0403c4020014080103012240c0300c40d0010780003602c2c1d03810104500e003080003001213586400d03003240c03541c28041d9004680c034201c900b060800f10580e60001e822482000a41d10280300320b50700b000600178050340c1a0445078660800683e6507a00300d01c07072503021031000d100821005029501070403166282d400d0540c82c004096442c00104da016411480106407240c40078040d10061500000200181ca03004842c40d04142c3c448030108a401000a410040600036841c00c011440540711110320032001241d4a92449241140c0a0003050180200600c80c03c1030000341c1c0c1d84525440000c4620500064818a000550700500d01301e10907940c942501c42000b4600d414101000b031140200329a03010054400114820070050340d1002e802c7c2445007211409 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 119699316 1250 119698066 119698127
    0x316081306170103120504080d09090506011d2404090f060602070303090e060126040b06030d120e0f0607030b030d030902031c031806020c0d020313031203060b0415 72
    0x2d4482c1503035080741843c01c40d00001d40c011682c1e842113030000b521b5401400e6240740c10582040c01e0b241519404030303061050f50340340c00c011645901018502410854604c90940c000d040200c0b040300707400d01e0248066010120941c824405602c2540001d41040c0c1e02e04c5880c64800c100d111340130103401a4030103401550718548009185120901071145546021404207d0070383c0140c803010868091010f1002c0d211120911030030f14840300322401d0b610310181d24001001481c0100340b81d0417054160301c4400700500c29903042d40050081940490280c810048441801c0c0000c00015101d0f02059901265807140c4070189030401d03498100340801e0606000c0c200006a80104421800c03251034280c0041e032008249046001d03100046040d0648522420303403500b0711805400402c0d03002c0007841102d205502884080b030792032242c00840a200d903103103070060001401c0043c503072250902600e004200d903922007488020030fa10035400400038500c0da0800c031940380c0c1c02500244140941101075040100c4022 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 119700566 1250 119699316 119699357
    0x90106020105040b0f070e090903180303040b180402041d090c0d080406050c1c090905010b0301080304330804031806020c010e011115190908040b030402030316081306 73
    0x1000c40c107607860b11800203546d46109400c01d0114110060010b1003600784400000d403aa8024900ca4010710941040182507080000407101121070005072035107000340749003c1034828012181c0155000342c0801c030028140d05188640c0a082024002c020650708148041d40d1038141480100e0340140300b010310b007074081603030201a41d046956a0030003a40c0c3d6041070705003908000807024080d4a410701c41c400707914400da2104403202502c000d820304220380c1c2d07210100004e45010074881c0303010680c410401409000c003030f604143c600f00710f00b807024603401400c100440222049401407400141980c400c0005155000446200c0560444901e8034602d090040081d2112003082c0e8030b0f4184818810303c0710959100c0e0081c8c80c0500030040a9400c150342d00c05008010500c142c40380c0ca00750106400d620060b00351449070b0101c065012091510301841c1c0341440220f6000240141e0b40b40c08140082010f6002800300720200b2072040c1042580c800c5c1900007610380d004250848420031944000005084000d503 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 119701816 1250 119700566 119700571
    0x1e010806010509070c060e06010618080c1c0c21030306090506030601090c020a05060108061005060a020a0b040f08070b0103020909031201031e080d020d0b0405060108060103050603010b0d0302030702090106020105040b 95
    0x103103082c1005c0c1c40d40342890750191481c03482510b020b03c503410001907010380c8450040c114014041ca002080380c2c6d580d00c06503450000c00c001a41c044c02c1c01810500c107081c460052a4018420180070740741c0b560ba107489680c0c20040e07141c2c03803100d4000550b03280201503240c42643d000d030001e040c3c1008241007402c0403e507180c0f014015034081d035680e8040c50007218020056040d030780e6408812101e4640e11680c1060300d501007501c0300302d10500c05003400f1405182250a035103403a80d007640103210000aa4603100803604024005a400303501880d040f0001c0340001c2c00500001d8000c2e0700000d03480d45107206006254000034641c9101c0d4109011a04140c12140c01e00da04481d0001503814507940402c900129581120303400030540500019141c1204600d40c000d032800000c0c00034100800a090400e020903604101c030181d0018440c5000140c4641c042c1c0c0c8080d411a501400015242c01c80b42e02103103031100c0c500429805030744041203500441c40e00f03611407409002a0310003840181001d980360103041e00f01 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 119703066 1250 119701816 119701831
    0x30d060519061b02040b0409030504050901051002030d050705070f0501020a021029030c04090b0103030219030e19030b07090e090a080316020c03070b03090616050a03020d0e01051e010806010509 85
    0x2004583c02075503070301d41015452840c0180300b000300c00c07068580034025034171501c2024019201400001584d207400681020b80c00c12580140d850074294001e0340e4010440240b030701c1e09001d414030400010445502d102c142003442a00016a9a009040043c0ca8130080c030360080540c0e42846440c9005404180d21001409840e00314014881a00c0300080d06042050034015007042c44d00901d03200b03000303914100c41c2c1228080e400769100110420a1178a01d90543c1b4400303004100c4446851002d0f062120944c0c0708060b248110500f410784030303030f1082e401d520191001d400040003a030003800111000d86660350015039010062154038142d6450821600005250a1554444c1549802c20a00a0003402e0b1107203801002d451061f40c45014078500f0303810949100c420f51003400c00240324006c0c1040c0d00000340c005070311068100184844128040c1d0b014807104901d4907191f62901c1b0a064090007583d01601e41060403024031200c6003401c3c5042c0d14141c0c00182d03540d020100410490300c4010319683c0140d41c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 119704316 1250 119703066 119703107
    0x501030c0309150b13050c18061612110f06010905040f08030709060f0807140c070803030f0103030201140129040b0c06061c0209010b1b030d06051906 66
    0x24040360580082c04801c4001c0e14000b204244204480c0ea15800380c43d22003002ca80030103540300e104500600304c1d40c2c221114080384004001c00f658024518140f40303551100246020f02e8000001d58070000d40b1100d480c2141c015045060980c08203400c014444400141200180610b03410381c00d071b165071103a040c0b08401c0550b5552020070144030310134038a401190b80001c0125564101518010102c01680c461034000640c28403008808070311039403001e0b0080c0c8141e50f0f18402851003441303c00c5158050010038a00b445401d00c0000c003a10244003451203841402d00d60711300b030b62550074040d0070354045171003070503a00035082d0040c00081000304207049100c919201c583d540c03003d400b0030000c440c440c43e00722013134142c40824840d4028031300003480c0344202c00039182e010714085050301003c0701d918490002580040703803400610444500342d0203014051440411681c41c4505e050000e81142d11107854840032079260312050080e401e03d214918210034958a04010365842d001c0f0040c600c880b003000920745900d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 119705566 1250 119704316 119704331
    0x307060e15030a091b05130b030d0807030b12150901050403080f0703020403081602040b030106150804060209040e030304260d0b010e0405340203070f0303110301180b0405090304050103 81
    0x1d5076000702d010b1607000301c1045c4c858002400d424000142840303650300c82c44038400d00361082e4803d8010344d88404070140080000e680400d400766481c2000800c0d032010955601480d032010ba9642d1011001c1d9001e060260034410b1034a15a402e22003c0100090082e83c1800113000019a0180410fa4030114402040c009900d5011003100640718607440900302840100741000c03019003502c10006810300c212400c20501000e0b400303041c203030740c014440d0868070030000401030b0496000340c040d0b1360702c10720400c00140381420110029040b55220174044156034004003c1004004c1c0a6402141c44a105440007204842a10034081107108007008601e5a5450b05c0541d0701e640d00810002820f2600104103200c1071414a11145440c920b400303400440203201041e004400850030015404242c0c1d5030301451400c0580c1d2200010712800c04000c40c20150707500007221030000008040c5000c1c26035441ca19000700301b00390100082d101c072a1a400d2240e0b1030711081c04a1418000304940854001303082c08944013 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 119706816 1250 119705566 119705581
    0x10506180403300b01020105060d030e0105090406120303020714161a1b0606180105030714030709060e0f090d02060a0e030d090501090203190f0803040f050a0b060307060e1503 77
    0x40040c0494014180181c0c3c100c4281031280c110404140c030a03130082006940c2e10f02000550f06070090042d0104041c3c4444500300e5206000500100d0809080403410b1070391940c07115030201c0100815400070383c1c0820468208154580040c008400c0031008181e07005840a0101031941640b0909003002e020480415140b00d0803825100207058269840c2800b072082d00702181c407a0400c842e43ea1045244180306444580401d0b4401c0c1a07607005002000f042d420404c50012001058914981c9849558030000340003196000742805841c0c11465a41107080480d03081d003031140050006003d58020607000240180d001460395031001c2400c40c0401e0761030303240910a040d449220846000c2c113080400f0041441415002810101d01c25400c480e0a50f81400300e13000c100703481c2c0100500d04d00d101917000020a0144c40516000303400741500d06080700c203a070380300761400c13a140d1400c0710707032040f6441002820316050003844d00502d51414121050807200000a0000340c84211401103040080082001e0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 119708066 1250 119706816 119706857
    0xc020d050f0604050f07080c0d020a080f0120041518150e0310021201090207020103230411030f030d0e07051009080f030a17061302030109020705010506180403 70
    0x100350400c0c2a100004400c0001035100c0c902120306480502c00e01a001041d080c0000380981200c80c0741000d01510301102e010010702c42004481a0381c0f03c081505c0c0800d1009090114010402c00000001a0000d92b01c6102041d182c4105150714260320078041040846100d06140d03000c00c5881c500448500c103134680c49040c00950f07411003a10100703500305440f0a590410480c0410b0340007241140d462540381000da106038464840c148611a480c0d0004200000494018000340b510504020404003200c0b5032510401d80e80d8a1058521105442404180702821043c0b003d90081a0041c1c802540d8a48405039648a08012541e80c00e90700c02500304000001d01c441801717820b00500000c20902c0d885001068110b450250300d0880c01031a0308143d0142c0c000086410410f20790326000c64482c0b042410b445003980042c81d2540082414000c0d9a443c109840158041c00e10001d0040e00c907441401c00e40d00b150001480c060040c1c4400100c80300440b03c0c0ba03030650340164180f0301032680b28120380f002c0c0131 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 119709316 1250 119708066 119708089
    0x30a0c1103030703090627020d03050c1203160e1e12010507081e0403080a051f03140c0301140c0a1106070e0405070c020d110a0b04030b040314040e070c02 68
    0xd1404040b06000c0b44a40c160042100701e401030f50140030203000c2c03031440c9840c000d0001c00e0130001a07514101c4401030a05400c01130744180a030601a04100c000700f0014100840810040b134003030000810001180d81d103540341880a000c5247c840509401180461286010f032441408441440b00500590b5600c0c0e04540e000c45c6180402803065007003007a0081d040e844240c922107841040516040048450305110038406ca4041d0784140e03103a00c2c2c685500000b400c015000030030b0b81c4d0000c0800c2c069040c0c0120200011485000708040c400b4841b042c0342e040c80e030170a9075140302ea4100b0b5000c0c0c0c2c0880c0203a401a030040d01c800c100325555810504166140e40c10b200e00c030720050040c1c0040102c1c0f03a40001403150054400e41d024072260750f034114221205400804002d510540c609440c001007966030300c50381480322000e840c084405403201c1481c8010f03007256200302c9040d00c0d00b80400c401c05500840c14008030a07104092810141000030403045118001d1203601040042810b1405640d2201800032 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 119710566 1250 119709316 119709347
    0x409020c0102030f0919080d0209120606122b0504030c120c0501170f100503070305061605190507020a030204110304200105090405060303130816050f06030a0c 70
    0x55a400156000c103010350404c6808001842c0c3c610000307003a00d00d011561220000440d602c20454203030569961034540c0202101e00c4800c0e5013407201450545074088280b80c0c4200342c40c010695880d11404001042a407460100d406800c100b103001141180d039403901c96400009003000d419116034110032200d9016a03030000c0c00c1d0720080705000441d201c0200704101c115004201e041ca0b1a5100d0005550050740b02c0f001440c10007452001404100c80e08100743d8220260b0780001030410313a100b000a07d0141141c00c142d4190f00030005000030312210b4080b0308452002ea05183d41015450410001503110001200042c4113000032808115503601e000036004e10743c014020444698080800a40c030b400c02c560031210034501580d07500d00c030042c0440303141c0302c044142d590301c2c5025050b90a10000d044c000c3c1c0401c4e0140300520800e0312070b0902210741e01c05480d0100050501c40d009408000070355969a1209004109690540010780c8555044a51000c282c01001c140e1303030726960084441102103130f20300 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 119711816 1250 119710566 119710571
    0x319170f03011211010302030609040f02040906050c0a031401050a05010804051002070c1502151504020705100c260a0c0203070c090c0f050f030106030b060c01050a09170705100e01020409 82
    0x482c1c0503140e0ba64210249001302100403000c1c41100041d01244800e80d0500d5110400e240004e00080301c821642ca400c0d807019001103070500c007683d1510305407402a5883c1e0940003021414405440e031510a25500030310000b0080d58551500001c90207031004c5001b4181082a0a0b0018041c498108010070074146c08020440d60381060b07081680a4180700d01a00340401c50180d40b0f00002c510000700601e1024031500e020320992118002c40404c420030070b1001d9017244c0c0038000d0b0004500b00b0300103001c00000340b81c004240700b800141d00401080e84803174801c8250f0b0000c404280c02886e8940d010350300014500f0001242c6043c3c1c1001d078614083c00400038845841120007140100090b00611400410354903241d9107458052400c2c0d03014000c9402104a02c0c5091004110251080d007210400035400b8103010b281c08102c11f00542520400c44000000c2c070b8540d00f150b82080041b0184003810000a40f00703606000040d1389040e2a15070000301d2040c0345480b5203400710f41210a50441e401003180c2c074000c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 119713066 1250 119711816 119711819
    0x3060c02150702030307110f06010b0d090813030b06100e102d0801060302040812220305160e2401051b061602010c05040909080d090302030d0b0319170f0301 69
    0x35038a5200711044000101202560b587c1224000381c14030420700e0300c10281105a09003440c001035074000207184100152100e96000105055000802c403000300d060758611403c0c11820102140350002c3c180358021144030250442c0c003035012008500c48001140c1c2c005601e050084202c60b00300144c400001c0a07044401180c0002c40b01c04210f80341001182c484003e01c3e030b41d880c000d500b240290b11810071141c020452108168448000422900c4884503a43c600010803100c079403070803982c0d0380040b111a0f1203d400510340103403214010004005051500d442440c002d000d48001441010301c5c0c07a80c03d81402280d0001c0da02440030341e1006918183d644010b01c1d16110700315a03c44040c4c40440b4108040001c00800a10600950000400c0c80c0c80b04e0f440d1904c0e10f0403000052448480c196104a401e01c4642c0c3c3c4c0946500815800034002c2d401951a484071800000403101e55242d0305119501602441c00301c8035440300480344846d0890315004071181c4204100f28a842580403020384403000100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 119714316 1250 119713066 119713081
    0xe0a021b010605010c0303020705010f05130b0108030a0e040b010e03120d0509060606040303050a0c0614010602060f150402091309030f021203010605090d060b091512030f0403060c0215 81
    0xe0900000030088000320029000481801c070b400501450380000c0d00702c00f0407000302e03000780c008042c001e1003100005081f50b802003050f411140d0544201c1102d02c2c40c0038543d018414600940d9024140c02c80c00341d458454000c01c05000c15106040e090b000b191212070b0040b15078010348d0500c141c1d44c0c0250540b11840204685448280cac054142d1a81c00c91900c1d0103d0026280055081c0c4200006498642f406056480644054000d48440e20400581c5450030700080d00500800300b5241142e05c0400c80b9505045c00a0309000c401060340085408070401c100b8520142084020241816600103a483c1280d03c08030f1040b100b50341160020506104000c010035500101109a11000f5800c3c2c0b070600c02c040201e1082031100384240b038005801070020219516101d14001501840340c0d10020309010720b440802c4100000315086600c90b0031225004100e400e00503207007030302054007001440c5005041103201e80784d8080c0e400003601d45551a082900340600802690402851a00e03498600b0310707240c02d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 119715566 1250 119714316 119714321
    0x501140403050d060b0c0a0327120b06010c0c150306091b0f0f12050c04180606080106020307080d05071103040311131404030c031814040c0c030801030308100e0a 71
    0x1544140c09141410015130940040f040c0c2c1d01b44130074007018191340021030f20116845a4101444400d0114000b86503142d81c1d03240e40480c00030b0060f844007901c0440d060800e00c4440707000510a0f418013a404000100151054032410140d070000c801044c5414080d140450083c1040c1e004051304514111500155219104141c8080c1c451681e0b2100c000d00c011b1000c5441c81d0045402801142141d0703110062039a440c0c100543c001900410705041968500e0a40030407200034034405403a03aa01c01050040c1d170f42c880c07107103401340405000131740c0390ae59142d503a89140d210b1000094209030350342010403c1070303120b8040d800c100540300044170385907512424181014403100d800c0a100311100c0342d041185410a0046800c1e882ea0304c00d040d002c1c0d980c0c1c1d8500752003025100300100e0401540c425854000c0c0c0654030100c02424402140e4034018811000384011209020b00400610070a1010a00000d031700000f8107065941c14a440d00c50b0340c076507030190b40c1c02c560b0a41019102c8142c49041100420496 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 119716816 1250 119715566 119715577
    0x303061527090a0b15030901110d0e1509070303110703021504080d03150303030209040b06040807051320070501090209040f0b060906060d0908070501050103052a060d09050114040305 80
    0x11100d200e95034890007400300c12545052513032904030720240d60f112020072812001e550711080038800410b0214140d241c000982c1d000725078083c3c0d410780d6419045068002013040b148035102043d5407580740d050059200c0d503994101d100060422001807104011a002840b0b030300f0040d1707405052003101d0b802c05901040341ea0072038000c42006210f42d0351206261842801410b4944000300c01400f6030130b0442d103046019602440900f500240c075141030350100d80351a4010801050380ba005441403d041c541000240c04032100128450390a03c44c8000d4048280840c031524141c500142030f80c1c808403850058007402c42e00d038010b50300900d42020402444800c8059420780c0d8498182400380e41d84441c00c010141c901a103100d9045802840448014074036644011006d40c0503000c2c40b03080108565525081d180260021119500300c0303044c241204d4805205100000b5000f0f0300c0d202c080341300201140950003002130341d001e09504c0340015403e00c1029401007240341600900e9039481d00c0c043c00d024040f0b5201 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 119718066 1250 119716816 119716819
    0xa0507060f0509010e010f0c0b0f06010e0306060f01080702100e06100b07050705040f15030602180904110f060c030a02250303020309060c030c07030b040501140103050303061527 78
    0x1240c403807048648107004070b4202c008142c4484d0681c400042c011101c000c0002d1988080c403188400c2e010114041003034041c4501124560000e10b45044000101088a0604035600a5205a042c40000d40d01c08001900c45072082c070f411440c51360303039980c128030f854a140703040107803146401e20120800d0343c0407480b21302c10700301d61020440c03d40d5a00742c41c882c0743c4240c00000e00305802050060055141980001200200e403410201c0e0610300c0c10640911403145500484407d41e001602520003c00480030354082d2004890143c55842c0584030140365580a00c40107216102c40d04d9800015580d41094404d01a070039402c582c0c035031808500c00b9698080d02c0d0300c80003404111201d00145501b1040400c81521b5042d4091401c0c56140030511401c0c2e0040c0001c1c003070383c0c002445800140002000100000c5009000546060816040c01030171140000032499580b1030060040c0301203000007088a030442410303600d41c007000115190140c854001c103e00f03a201e0b06141c1e58405442c800c1c142401800307160 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 119719316 1250 119718066 119718077
    0xe090303060315090619110a050310060c020d0b0702100920040e07060c081e070312020708031302040f1505040e03030907120809090705040905092e0e0a050706 70
    0xd10000f04165411181e41d0015801080003030441c1030303030f07101c00c030000119401c1c042070220340c4459410203a0404d002d0741c00019804010012043c3e0b12403c5040180028203180310800c40039000300b12403940302e04c1d000d09044220b5000c941d4003031080162003038a010304181080328225602c0c05843c100d1084071b070b1900c44001005046201d02d000d2107035030400441d0304000c200235031510038165804c0107141c2c03003075510141c24007180c80017032014501e0600910080744030903901c4066140141c12488040105c000f01071040c044d400c0001e602400b03ca40196210072140039035440c6200141c05400d03c1d165100c416810810f08004c0080d5501201090b203a084400380700090008400603900c2c002201d0042e01544490800c021010254004148450003840d00a207040e0312440841c40b0700c0815160b00f070001c2c9000070104071a049510587d0b4001f034040c005440062222601078001506600b49032041a8103900b045254000aa002001459104c4103039008100d480c00d01750b131902d08600c00c035400b055 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 119720566 1250 119719316 119719333
    0x105060306070503060f03100204030309051201061503050c0714010e1014010608041502030108060a060512120904020903011b11071d1005031015050a061407020a0e0903030603 77
    0x50003103a01da01c2241c040e910541140d03100c4040005114802e8503030354150155010f40e02d118041800240081c5004e07450f5080010b00d050180b0035000389522501d6102d91500100344080064004050196403030303890041030079268107006003821300c5684802002c01440c0d03a8040025001900140c03100000c107401d90b603040300003582c44010703103405080b0820101e403c0401802050b0140d1b00080d00540207000d01d1820b800d400c0302510880e032007a0000f081d2948a88104440d15101e03000340c1010f810700b90307008210382050403041d60381e40d000010700f00c12080e07020490300155105c60307040d2001c420008000344400b00d516883d015820030720b80c10440001d00801c3c0300140c0006c0008a2400705d030355421107122a6103082d50180303000a800b03420606c400483c0782d0b0009003075404110248000c50188400070b4610440c0e0050290031110740c1c0300c2405810b414208201060300600609002c0c0141c141441e680c50440c400078102c0025034000102000f0b01000307005010b040040914803602e0150112206103 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 119721816 1250 119720566 119720569
    0x3010e0a0506010518011a0705101406011d2202040b120c0702030d0e04150303050909160e0d0f080301060908060907030206030402040c0903020a06020d1205090c01140405040f0b03010506 82
    0x39905e034a0740820708001c50340100500d5126400f00452a400000002d0816283d07664183c18000e101a030280180d4903506140c43c00c0030482d1510350068024204003034100b075a80409164103098004552041003944070038103a022049841e407101c40801030046542d02d8441d0310342d44464010751400c04505000038005030b42c2c050010b0403660200d2300240281200c044c0440100c4098144000061b0407035207410300225068004a181b1014511a4460382d8445070044140049400000c040e194030617500056058002d40101440340c01e004c00f540c00d04840e21a0b0b040c0410f10400703541d40201124800800040c540e070740001120207542007241610340ca6240e20381c2c039a030b40c0c1016002c007a6100c10100301040052400398061221482941403511405940b03400007030324402144c1c02000960410800180a1036100064070401003018108000e03034200302040d40e80d100810410241400303003181a4075003949280b402d40d0000c1030014030030310407030b081220080058a030b18a07509000e50308180201c0d589 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 119723066 1250 119721816 119721829
    0x60415020714090105100c05060c0307030e0c150f0c0706020f0f0106060509120115090f0b01020109121404080102041d07031a0915030a0b04020a06050708120604060503010e0a05060105 81
    0x410b2005012503581c0c0d00b014108902d0400103000a000d01440d42010400104180f141c1c074809e00c04600d500743c0741d190280700a030a03503800508451f503a0b001001e60060a9940320400245101208a071548a00403203904401718440c40056440d2441283e000141950340000c098443c903421a041d2411040400300c001d084e282a4007600002c5402484040c48900741030040700c030502801000800c0d14180d01c80400c40904d21900b050801d1030b2603082c101074101e124000c41e00010000c1c4002c0020341210344400d50360352001001e140800c0075440081080407051416038000d091548000c540e110303902c00440305045442d448040d80c4074002e4000466441c001c4c0b2410400c2d110501003c0c4420b49914104003640c1002801c1c0080c052001194450035241005502e410030704c1450b1a01c610b082c203004000c0340f00d4440d4481d40c1007040411000300010f1129040e25000c400e48030808219032100d00001d40504495040301d070305586441c802140311000015100040e0340500240c41c01d42e41c82e2000d1215 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 119724316 1250 119723066 119723099
    0xb06030c101d011b030917030a0801090902040207020909160b040b190302040b0703030e070f0506190212280810171002030103140f010213031b050604150207 69
    0x108400200048202c503074407091440c1e1060525111288110141c0e100d00031612010040e40011203540b8103000ea040d03020704844044144c14021401d000b01c40d0300040c202a0f0500840307010750303290f160304004c40d2140c0d016906c103341d00030624000752a142450302d98030700d8850300c0303a0240301c2c84d50000250294160104c50660b03c5c0e181c20145401c01c400060601c1c550403c03601d60404d9400c01c40010a0301c070003006410305c14881d036004511100039005880c5411002d800c2021080e810003400c1003981c1d1140c0c1110341c2e10782800d10700c80740d20b5042e40b001e070b0802c1203c404180820500141441c120001145802c40d040c0b02c1d01203002ca101a60401125420b0085426513820034007100b041c451580010680e400021100f0221801a0904c00f50707601030340c20aa10403100c510041100c1e50707000341c3c24000b140002448100850811088003850144e903900d030300c009003000120502150604140025002c003802c00500140e5540d5500c030708010403280010060b00050203051004161514030102441 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 119725566 1250 119724316 119724349
    0x309061f0509040201180906121104230c0f030f2401050306060d11040f030506092406131118010e0d0314160b04031b210507020301090b06030c 63
    0x42c5541c90380d005649172110308a04e4151003429a81c000340c2030710b0a000b801d010b402d880203904920a089c1c0791050000c104c03401298032642c1030102c410a07914800800181c14814495100300c40d071590b02c916002e51051901561200382c0001c00c2142a40d10500040d0041d5082c90490021780c801012030407003440c1c546031060002c0c50800201d25146411390141005144607900011040300c81c00100e8403030b074840d51155060203500c0d581001801824010290710010902c040e0a250742c10445940300300080c020b01c0c00316080c031503001c04c1c59a02c0d60403001c7c118191107030080200040c2c0245d0b2280755040368009000e14110303034024032095480340140c201c814402804c2c003288410301d03640030f580e92403440c800c40c4610303030051000407400311081e85841480c41c040c0f0b00601c498201818000d25402100700c00000c40c0314440e0320710380002d4603a82e203030988240401d030700304651a00400881e040e22404502035451f40c03d2010810901403a8001c1d50301404c030403411640250340c0074051000700b007120509035 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 119726816 1250 119725566 119725579
    0x60c0301260607180905041109090303010b03011e0b0a0c12020c060904271203140103110409051011030a061a041403070510030f0b0f0609240309061f05 67
    0x3800325402080130203820038450f5840300585485441c01012100300f12007d0f507e40000340758010042c10803d07419038108252001031451503040c0148201c00f40f0040c403851690036881c0e4601290000e215050368003902c11b5a00555407900b207040018260f029055080d1181c0c800c0100b2030181c0c0c0d00000d682c40030b11501405d99410a12440c041000400c80c015086501c4982c003111480480701080262080c01d200e400d82c0000304000d080d008088845d105c20452607200f4120041c00820341410076260349040407940801c144d1001c1c98180d0034812842004401d5030305080084480e9544040034510401c507100007041a955600740c00f4030800170442c1610340903901004203015082c40c4c0c3c1800811030340701404480f4400d9845c4040350300300b081d01c503084001030364402e001d07131400c1070034098000c82c01d00c11100c1d180311444050005100d0301c02c1c0c0e04600c1c1308000203141c94050030b13040e114081103013030181401601c0340340600401c4c1d21040100d4a9921100200b010004040b0b0034031070340e40680d81f01a204 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 119728066 1250 119726816 119726821
    0x1090311030306010903080c070302030d0f0207050a06081609180e0c03010b09060d050c0d0305030103030e0a0303140a03060f03030f020d0306030503030a0207020d02100201200309061b040305060c03012606 90
    0x100c1f40c40345e0144c00449498080c005c004400340c0c400300210100c2c1c2100c2c0c1d50b40a2480041d070310003414110103400c0148102c049001c00c10095902c040306903088609800366002402500030155001042c640c40b03600003400307801420542619652103484c0020030725055072041d0600c41c0c02c2600b250041c036649503001204401144c42824901030014140c0e204a044580e4020640d00295a02c0781d014400c400107400000140201a841080f00c12007034000c3e00c00300302c1d59046d55005040c2200c1008154205103001c142040c1e075034820b03040400100700501810603102d450303040040c40002ea201d941c07000352240700810300100d4071a1141d03404aa40041c069411500d581003640302079800408203030b910403c80b425460250343e8020000d1405035003900000790000b000205221000d04041c604070050200307104001840c5400b0039000e13480503600301d040038103c81d01551000e040c002c80d000507245100c3d038410800d12002d040015410385a001081103041100c00400040ea051985800c09064010002 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 119729316 1250 119728066 119728073
    0x60602010e0a03110a1b03020a06170f07020a0f06020406030c022e02310911030402040b0102030f030705040e160c020f270103020f090601021509030f0a0201090311030306010903 78
    0xd01413001c18454080e584000b131961075010103c003030018186042005a40200210b01d45002040b00516050824011001030000d9035a90308000038003110313148100d00c0c00110720724402d1000340c0a0325440f0300c0c0074a80406c1420000020340041c01a600440d103001c1e000d0203003600000d0382440c240000c810200d01c0450040700e445012201c905006170b12a020700206184504003410b015041c0010324a00d01c0188502d0009411110320380d000301d20052074544006c1e200e01d100000c4a502035015140481d1420706600100d181d4030410000d804514404428061616841401441112a003441c0d0f0202a00c0e84018011034008115804000c21462038281e00141855901c564001100601c1000c0c031410907251104504404403002c90340e4100c3c1001070023180307440c0d8006008044c044c1d8030286907181c07d0001070f40d14143c40705400407400c5c08000003210a0f008104030744c600d0650348034040c3c803090400303400703406091255001ca010030341e0b0098002c01c41130004150792203088140e440181035841d580307 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 119730566 1250 119729316 119729327
    0x30609100e04060e150403030f0c03050c09190302120607020d0203090d060507120204090b03010f060b03010b07050a020d140d0305040809010c0602090424090c0c080c030c06011701060602010e0a03 86
    0x11804c5965001c1c0188404840001d802158407590007034602007002003803026042d041704c2c0e103018540203045c50700d0148402c0c0c5071640252045400c041d40e80e80c60b800510040003c4041084d030009600c02209001d440404001040d40c0c0e0003044250200c52004401c041c0603602e0303008220046400002c03401c3d4010200e01070b43c01c055048010b82c2040501300c0c3d178001ca08801d03030b03002c2e8110230255600d1f000100010f0a00748906019814000010401c0500b043c1600c401d9100c10312541c94002c4010880b03605101c001d1040c090140da004004120040161401d80c200c2c03103007015000d072240240c20711001c0080c06030060340d104640c407884040c90246031000549065030944016501b00e503003444907602c151128880c140c1c1810060140b03513100c52144500004107a250b40180c1c018a0412141d10106508100709846280e440703114a80c507644149001841e5014610b00711b44544218400040c010f00140da0711512000604000c0c084a500ca0300c060b420398001c8004400c441c0d02500c00100820301c6038 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 119731816 1250 119730566 119730581
    0x304030210180b180c030c0609091018060f12030f180905090609010e07060e090c0f07030e100f02070b03090a1205090f0a05030a2307030503030609100e0406 69
    0x200421000215103450f80701d103820084481d0b5116039901c1d140c0c074501040802c00c2c0803400a040300240154900180426914010001c501c1c0c06060b00c140070618550308802d0302e6002d08401403502c1c140321a1008410003400380351240c1c0701010300100010407021520084c4441013601520b41c5405160500c6044504400200381c0c1400052195000301e0315a1590240c94007488803d8020142e50901c1400d80d82115a2015001c00d1a4080202081040c0d08215140340754041150306c018283d4804061040a01c80c80c028406140400070301c40c410144c001541114000c82070b110b40741d0310550302000380e07007a003000003010015a0011004010420060004640c4102d640c4180c41041c5440c1d81d9420940c15040700d6540032a801103040c107101e041002d4401a1540c084420115a0340f0b040042900c070558014003408001c44542d2610030000340409652404290740100c07080e00e540c2e03003055a02c1ea00300b5508140304040740d401140028038502400825a000d400100701192240d80c0d91800401c0c00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 119733066 1250 119731816 119731841
    0x80c0403022d03031b01060605120a0b0a0b0a0309121119060f0204150e03030307200106081906110c0c010513051f020f060106021902010201020405030102071b0602030304030210 78
    0x11900d050349151000d2002c5c02010440142c0081c0080964810724203440640e08a4400c100c03041c04101d40a071014202c0c4ca81250710100002904154000456000b0a041d001400140c07000a501101c00d907250340000e00d81030084030580c410b100d5174002201d8034107511a80030440da110120014801141c40c2260440c107108000c00120f0050305007a98003681c00c00c0c0e00c409241c00d6074218803044c2c10b4112560300502d5400b14040c6140d46002203024224401c208014140c0c4400581d150280c024250b0000c005002c415046a51785201c0d509203400d1448001d00c22607003035060490212030b50b5120400d42e581a140d00c0081d01c503440da1400111070640002c8480a0070380d10704940020f194580c260f1058407102400c80150381d40d06461030181c030b804105400f40b10a0307032011004000f41a404200009480008500307a11503000f80c0c00102d000e03001c0c0340c02442d40b40d440003448504000c00a650010b0000740d40d800006419521101a0385074001110042c026801c0081c11154000c4154481203000d8507 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 119734316 1250 119733066 119733139
    0x504081507090b1312081e21090f0a060c03060801060312050313060c030507031b080c0904020d0501170c01051206210d1101061205100c0212070c06080c040302 70
    0x25590458840100c83e24070940d0f040800003105060080c0d405405440f00039911047c0785001e20300f202d040001c4400b807030b410b9116075461020811446c2e040c44500a21442c6a04460643d02c0c0d604160300100004522900800d1604800254009060003444201ca800ca44184071780c411601099a295000a00c507503140d107050250107000502912410340b200380346503000070b001c2c5480c0d10040d04941181e00341e6920175030100c0054a10030b038400382e096440300c3c20b8801e564440ca0740c030010902074000e0003088048203040400204240b1b8000344004400d1001c44c1c12241007601c10001900c040c410b0901da078000310f2052000a426082410b185d81250140c05800e040d9240d1454200d81004a5841d0441c0081c042d158a180020000d018000c0905040750b0101c49090f03c0b0380da1a951414100100144181c942c411118402e000307210401c0b0700c00074544416503418040c40c1006550140d0301441d00840c600201090b40b081216054505a0345d000d0008252901045401c1048040802040d10b0081 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 119735566 1250 119734316 119734319
    0x2030f090f1c02010305070504030506130201050c0d0c15051905040510020f0a031d1902131b08070201050c04140f1e030c040c140a02120a0504081507090b13 69
    0x2141d2803007003203000310002c12041c0810b005100050540b18094032017402c20900f0f00c003c0c004a00045000c1c0e80040148080b800a03c00b00c0c17005a580d4007030a4440082e5006040384020882c0e04040410b905c28401d840c5c0029441d410f80405045520546140e2031200060a40034a5034017154000c0350014080c0048542d502c19201154069900c0601065820140840c0c0110010b4040c000c00101c0c42404041a01c141700c81039805698101d85503074807820b4000030106034155258082000d121240c4c00b0f505008000c0006408216810b0b4040e40074001540c1d0780004605d507106120b183c2c0140b02c800a042e02d094a0560004000d51003038440700d070711451105c0030500a40d68403000b101606040032566020080800405007480309080c5540e0080e070070500e1000105a100d0b8490800c4080060002e4507207654001c04c80c54040c0060b4210029500090200803081d0028050411613000c08100d41c10b1041007502c0b0311480e8810348030070012520601e400e002000c9410301400104a8100c1c5502e03556 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 119736816 1250 119735566 119735569
    0x203250c0501020d1a040606120902040207080409061a0304030801170102210603010e0601030f0201050c0307081c0f0c020a120e09010f0806060105160605040f06141f0602030f090f 79
    0x9a02088140724407598582140b45c0f0421103920b07510503e1780171681003001c940f800340081c11030548903101c01c0885030b48030654811540c89070f050b94989a008032195440b26120701d8000000c2071107000c1c4481114800880f41040c425036402c41744101d23810f0351a11240c0c0d103450b43c4480400401c1c0900d40955400b406060710b449000b0004412042501a0717407500f9042520515084800103160306000c0e403c0b05006101050400c0403454030598203207082c030341d10040c4044590542c0102e100081440c0c1d00000d40c1141070744040d400e880303100b0703180310200300c8a80902410021500c09074641009604410050008512440308400040c140750900d5044404c0305400650070b40000d812000c0e4031804c203c01800404c4080007900d90201081c200203242c9424400042c4220041c8100240700c56101c0d0005030400000d01c1c0c003002043da01400a01c21b8034480f2030000012481161008806c90320000301d03440b00d400744005401210050b03009180b611800700e1060a4903404032480076004101e00c141150715 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 119738066 1250 119736816 119736821
    0x3080604021b01090b07031406090402041401061d09010311040507090f0609150203041211031f140705031315090203030c0a1205040605090d050a02120706030b03010203250c0501 78
    0xc42e14036000041e10b407158501010790000103042d46007050710f04503d4160710700e45000c48a4010b4400c44d42c1e0f41031075445100081c0904031160202da030030303030001700001f0b19a03420465003086000300b1003003140c1062000051040780d900c24030000e002c8210b1891480c041e410168001c17600000d1600e1300d2031026440b00300794400ca44e4164401c0d000503101d000200006844003038103d07603105c0b6501c080d5242030f1808140f106044008007000d464000400004081c0f5074017088074901000700741d0740a0311141180c0a00000401c10003d0034040b074400f01c40004c50080c403807400c803403040113016640d0f901091140c50388410000c1c0301c0540021241d55400a101507a0101301412141d5101e4005108010162404940d0039030b2410000c4144001800140490358014007510140c100950314180111600d040492609028000c003030340100759020408410140421114156980d0340c90901c070050401c010b241c00c0303202c01c903440c416890742d0301400307509440d8129107401020620301d40518803040c03580700c140c02c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 119739316 1250 119738066 119738107
    0x30a0507030e030303070207270609020c011d0d050705010209060d0c12050402010c1410062309010f0504020a02030408101b020a02030d0e040618050702011d0a0308060402 75
    0x8140085149410580d114002202000e4140d000c2c50840c01e00c5c0d80003039035076003403801800006004414400224015800d415204e4008050148a0242d48000000003540000302586031942002c4500b113001c90803010440400700c8c510b00070480d03840082d100f1100d6070006c1740c0442d00365400f001180450f076191000341150300b40f80c60000545002d01100074020589140e100c940d01130400c010800541c0e000321a250701160409125800701490402290501d070501043d00711062902e071001caa000c0d807000c24104154642503465102d11010b60402148076824030640c0c0c06101002c0c02030141e41050f0300a814405643d0040f03d05250300c0304589801c01001c6044211090364820140c07050480e034680540700c8010f02c1c000340c4075800325900840d45500c81d0302e001c1410b0040031040c0c03c4460b2255031080d0001c1c074201d903025882170314074a0b0460152500345c55160041d030a100704412660000d03804130400e09226001054031a90702d0364142c83d030000081005a01c030768207000840c00f000f81c00c8081c02 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 119740566 1250 119739316 119739337
    0xc1202182703070c0b0306240304080d091a190b030a0206090d1a0a0b0f090604091e030c0b09030306030a1202100527160306090c08031b0d17070c03090803 68
    0x21b881e03181020901081c0d9032074a0005000c1e8000c04401c83c10301c4802c0084a4105030400a40303951044400c0403003014128002000780241d91580b400520700710b17852401e500440b0010701c0841440c1f5008110b000751079004501d198950800090b04005180480007403c1405014280e0500b0421303684600302ca8058a400e812050382e074200030040b95100c0d601c41c440e0003000c05c5640b41c40c01c282c0103000ca0020304000f45004d0107151340d0404202440040103450100300300413031004410b00300030310b4000c0440e524844111940400440481d181080110aa03031140d1000342c000c0c0306a5070300780c960410700d070041e11700b42c1d040d40a08024604130340b0160254620510601d6082109407a030340340c0154003101034842c0408190000c0710070602c181d20b0002d0f0002180d0b002000811001010f040a4107008200c0c0e2048a50344000079003d504160044041c00001c00d914040c0c0c3c42c0c4c192880cac026542100440c150945100064001502060055081402640c0245811000c1782e440c0d03c0300c0c40c60356000c0d12040307 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 119741816 1250 119740566 119740589
    0x6090605090a050708120d021309020f070212071d1504090c031509020f0d17030f0f010f050102071701151701060f08060114010c0c1202182703070c 65
    0x510034481e0801540e00140031503070081401d100c032190b61b5907442c001c56059030400ca40000da4007040340f01038013500c1c02900714000c04664a0303c0c3c0718001c0c0459880200120300070201000d084441050204055089030681010186610007441000b1503114009203000807407220040104c40d180c58138400c0c420514410711641003038900b181890800d04c804d0f0010a003c80f410000340100689526104039a074103401d40d01c5600140d5145000e07001d4034110001c810340820003104029503030500c5400a4003815104044600c1a43c80e0f0700b0325103056000380100b502507841150200003482c0e540034030380000f4020301c0002401424001d0f07074072000c12150f072000c800c103110603414000704035080c4181001041600c00301c4480350315152540b9150f8005209030146040708100c40d111590168031054407969121064a08041d1141402c500310141c080c1c1c145d014203c00654291700218807034109024440149846c092900a5440c005400c5081c0a2409180c04140500d400143c2d080c64034070301515500c000c2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 119743066 1250 119741816 119741833
    0x80a03080f0a020a0c06020d0207241503080f1327051003050a06090317040609110f010c02150415030f0c050a0801060e1804050303060301050a02130605070609060509 73
    0x1c0104a0405000404202d1042000001300350308a40c4140400e03901c42d4000d078856481e00010710083c05038001c0030700440c00710400c4040705042d039109200c4205d0a510204291810502c16582005150100501240e02004601800b00c0d150003c0d1031403001c0301e4555070801d52a000241210030510348110440224642a0b002c2400c0d580102070380720310001c406209292458071903941d6040d81d000090184d540d902c1a400505108010300c01c0c85512000000c2040c5c2068a4001300810207240d05541c0040c24903407044092900d030548002070a0142c0d114003901101d502002103036280381c003c10500040c1000001082134050311041024503240d113001a07100360b48103001094400ba46485410403004104483c1c0c299005220541500c515103044c01034081080041240c080d00b28011f0152105440104001c018000008510070003003507009120584546000d44181d000e9900000c0b9000c00c20f040510803188194042e2032801d001d0f4001069000b596110342c02207503400c2d1a41705103070b042b551030b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 119744316 1250 119743066 119743081
    0x20609040c050705100e030a08100b070302070608100311090702010e0f010617030306060304120306030204110712110601051201140a0b010906050c070b090315010609050f090105030307110109080a0308 88
    0x1400c006100c0c5c01003841300d00340f0025550b459100e1050218144080100414841841d404080001c0d000725407103150f4403c3c040c10042d64860b80ca2040c8000a60b200d0009904000c1003152041100d5001c600e4080c142c0b403000412100800090041003103658850354005e00600401200328448002000050f820b0b00b0700604100c1c00301d0a2050038000d600420500ca0207490b02402ca0b5881504614048418805280120041c1c100c0c2e03400694001e01340b200b004004862980240052449100701c1d01c07500254980a4503003007181495812181c20050040026080c40448041b01011100000580b82c038843d82c601c1d40050280d0f6540265641d9280329906541c00100c0d02026040f281030441c00e0603141428181d83e45854000c9032081403001c20862002c0c2c0303081060580c9030350221007140c12507840d50720007040f0780c0151149901c00c80b40107030004290b082c42150f46050351000f4024624102c0c0f5602c0b00c4a0b50140004000d0420045090004a442c1d0520007881114031994131800503040581 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 119745566 1250 119744316 119744323
    0x80c0f0d05010b090f090405030f07020a0b0d0f050106180303080a090602070503090109170316030504030b090c0301060501030207110d081308010501080d0801140f0312180a09090503030f04020609040c050705 91
    0x60310034082c02c86c140500c000308a000055403208801e000c00c480e0303030340d5a92004c510607080343d82c0a620080d40100b4a603c804407182c001c14240c0e600710b101040701daaa540c60840d5400004400202c840541c605e0500120744690041c40d401441c060001c80e16402555075201240e00098003512681c10209203403656603488040c55006042c0d610320000b0760207a81c090680c9074440c41300035445009908a107941058041c00a0b00c00454002c0a40e000c5440c007062840d442d00d078904401886540ba041000c151980207100781c03043d0301d0300302229158194414007840410f00b8019010f441100081c050020041075072902d48001e0301404c00082090751505009900e85041240144240001d0400500c89138287d404818404003048402c1e180d600c1055010034285040038802040e80000000c015000c40460011341c0000c00c2d098075040358460381d81c802c1e4411541703810750082098004101007580100c0c0c94203403030340083c0000c10030342c6040d008400040440380208680004030b1301c04210a0140300051 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 119746816 1250 119745566 119745589
    0x1309060c05040513020702010207030812041a0903040b09030c1f031103160305040218090106210c060c14030304060501060806150a05070609050a03170c0406080c0f0d05010b09 77
    0x1401c00c03904081c00c22000602c0041d060510043c0c0c1075005c1404403d680c0300b08903400056401418096581c090702503075410500c1e04950903190603042062007a060070004180074441c4107024003540c101824800c90141a0744003c0b500ca90512603254a2004c0e0341d510300311400e017003402d079843e10030f6810038810240a968a205000d8480c0c00240100b290310f02d415220792820003810318001450744c0e1948000f40c0d030109a500e485051000c118104520488154040b40590f4110350003c0102d4210101c00180e401c44050020400090b5200800c0900c1c0104100d02d54144a40041c500c0f00486e544c10515682003102e090320b0003529440108032490b00048010341220054a101e28030700b010116006c1c4603c50f0700d264008010b0005450401e11545030322080e603483e0b200c81030b60710086850400819864600d20300c1401801c0c08404200e11010100880c0d04a80d840e894402880d50380c1101511160012304500a80315020450b21000c11401e20810340a0490000050f84038101e0740300b80b04029098 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 119748066 1250 119746816 119746841
    0xb0d140903040503030f0d0f060308040602070803190f12020307020c010f0e010804031b0203010f020703031422021f0908010b010c0b0114030a0f120e010801050d0b040809130906 78
    0x8000c01d228545021048485444a080456944158519181c002005000e9130032145c2361501c800401002145002041111007a5084801c807607100e40c3d000303880348510100040c01d001c0304805a800540a40c01c0c01d45a0062400c111015800200802c03042c2c2e80115409801038000608500c1c0c4d540e0045090403141203d441c00000c00d011001c000b80c6244009400641840031540c81d002240c0b00c1e100510051076400341c000d02c051301e034110360036020303410900e42100482d040c4112200003218581806100d01020004282800d40610803c20440100e04040c0c1e040059103250301c50701258071400c403208913019902d29030424507200c19103084034a05604141040882c420076008038507007042c0c460540743c040e40000001861080028070300505c1240081c000b00d05180c03010184207041201804005803500d86c081b143d0100c0f40119045042406242e621100403040c40380860080ea000e00d50061056070400d14107441900000e81d98902604400c0e08a500e81a0f0700342000070b2030041801101d107 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 119749316 1250 119748066 119748073
    0x40902150904060e070210051f0b03061305090d03180209070806010905030f0706080a0f0e0303070806030a0b04080d0b121f020307021e0a1b080d020703021e04060b0d1409 75
    0xc5c226002901c404814007180e4409072100081140203003180b00115407807408100c0300f0000c9549007010b6506400c11990240b00b004508a982030081441c042c4034071480c00040070300300c16282450b040e402004e1840c07156021480312005000182c84a00c3c82c90700964054580c0011484c107040014100036454020310b001e034000501845c1c00000c0001c1c0f07402924907a0401d40782c1507445c00b4040000740b460041040c002c50070a0071240e145c68001c40110300950f01e90b52406480c1d40c4403400d2654990443c030004081500400004021540d600050001000c4110001c6002004a00041c010348c1c824008004513801902444818030000f461400c41591054010760852410800180d1902180c01c28140b41d490302046090b03065030288a40348045900000e503200407640071604003031a18503401b84254a214900a8a40c124000150300003243e86c01845000e000804400c042c80982c580003d582d0016140c0c50081014000840a002e1000d012440040d0160a2015807280d40341c000d45500d000e0740 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 119750566 1250 119749316 119749321
    0x18050f0a050c0d0816030509010f020c10030203070e030a060b040c03090c0b1606151505090f041109090906060f0a14040203070e060d0903021605010e040b040902150904060e 76
    0x1500410900300c1c50108480440f840343d40c0342400c4809119030703050703661454060740046081540080141c050350500713980301c8155540240d42669a0580300b2207003503210800921281c10144250011540700c00340e46080500f441000001c43d1070010b000d00115403103500c503c800348440c10325110340c07082c0070340c079280902803280b6685604600f00210700401202c05000214102503114101c3c40300b0440f030b84030344100704e642d040020540e49601e2034010f00302c1704d410b0060360440b954441c0c1c050320001130000304840c02d48461007003004005d044840a040c4048000d01541c20716948200c581846060040060107403481d0a108100d6201040d000352442003940340000e010042616070150a40c138005d46005a8030f480301c02e4241d0b4145100c07001244d000c2d10028550580ca042d40d0030a015092083e000c54130300800c1c403a03910030500898002e181c000b407909035203004946030581004441150140000500b602c1c1d40c1c01080e10242e01066001001d40001a10101070800384030752070040c05202a0400c4a0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 119751816 1250 119750566 119750573
    0x30908062a0307020c060c0a0507050907021507030e012f0304030203121e01060f03060e070203090d0204020c0724030216030c1416031b122418050f0a 66
    0x441c0200d2803109000000700c0081e144500800c054043e400c0014003041e256500c4000491340d803089100122054003030702000042d00e05100b407070780303009620540107095410001144080141002416001090f0b1540d4a031111401c082c4074200b0702e207045010b00c460300320005043c50000e0002d0a0300c81a071034001c000f0080030980c080309560b05a29002050645516010600c2400f618400e10030400842681c0000400d00d4004020050b200c900b900d050044580e1600b00c8090a41c003102d41c400560001c0202d90700c6c42c5448228a13012a1005100508001078080d12900c0c0045507001201d90003001c00780981c3c1190555200c00e900e104501c0e0541c500741441c0c03042e11050341c00381401801d100213104040e04009868100108150b00303030b41110f011300c000c0360880e0401c0720a4402500c5405115003c1214103a03401c038400103a4800310104e000e4050156504040c43c031841e83c007140c4481d40002200c0841c095800b45540302d040e01d520000d507015450401500380300516241c03682d10340c888102c02c80003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 119753066 1250 119751816 119751871
    0x140903041401080a1e020a1101050108070b0a091806180506060a0503091c0203340311070b0f13060f1706030106260d0c08040902090f040903090806 65
    0x1d2010070710b004010b0343c4410030004003810040c090209400310700b642106450321180d000c0c02d061000c603a54507440102c2488441e08807071082c0168801d85c4c001003010300c03142101c0300c02421485281d11301b548401d95100100708844007038802d1240c00503241e0604001d8400c901c98201880680e40b00100311508160001980078400d284242082c00400300002c1c20f0500180f021092600300c60040e80165035800e04025241c0d80008044242d00c0c2d84410a80c40044180c500c107030a01180b0300b01000c0240a40d20240c855030314501d107a2145204d003e5011034005951806001d1062030004526140c51590280d00e040302c080380c008404209852a040110607440381244402000901007403000391100c20100740901031503007001c4041440c0586524019002e0701e000520303505800b050b141c5406404004031407a0060703980c060045138040c8014002403000764002c104510004160a03402101e901c08282035402a441c280c010800e252000c12665009002c100e901c04031171204113411060944244a0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 119754316 1250 119753066 119753099
    0x50405090703020706050901150f0b220314030703120b0105030a09020a230f01030c0503040602161e0302060106020105091203091006030c03170306010806120a0803090114090304 78
    0x3082014034041540540240e04540c1c43d1600b00e882403000e8505480e129019000c100c20300b1030f0707040c444400001d42a0030564841c054500c01a41c0900e450042c0c5400f0031083c0c0000d44840c030b1450003640000000728071401c010003100c9128061a00c6c0c014900b0301820108914030304480042c04c02d607901959030303489001c07690700403082c100c005001100c50001c540740c9031f0b158001c0d403000140070082010006040d281400e0310b1000300c402c014241c000d1401107043e60301a04814000c00c40500c0802c00003000c1e900a481c04209a0149080742c00890301c40350b61568008148440c4588552426014541d0510007680580301e240001d0165040098003d40d4650002007d441c1840c800b00c040b17805008103001590f070807000014140040e503201c3c2004403164040d84800c4034004c0c1c0d840d880c40f04003103244055901c64141611420156592042884180120881180001e002d00d0500784001003000300558003404107940001440b58090b04150541036015080c02d0243e80301707120400644000404813031 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 119755566 1250 119754316 119754319
    0x2b080f0a090503030c090312040f0e091606120c020a03090b0a03150b041701050402090a090302010905010c05041401020309100e010504091404061a030601090b010e031504050708030307050405 84
    0x15003991520030000090102040041c22400000f09012220028002500302100c00300c090b03401d61515010380300c201d0301c40c03403091a1700807021100402103018003450301a07002d550f40056940c2d44100e1904d070200f60407039800c0364002c122132580003072a03480d0521400a8010031030009207061b00103624060640700d0a48900c0d403d8190000d21015054400d0700154130560042d009480380d1900c035824103245400c103020b590f44030305040e41d19040c4080140035080c0a17940241000c0c0a64444580e000040c14502d00300346c047d50740701c5040c030001900901c100e000e903440c03641d140c2e0745440c03c3c002c100e5085ea0180152038110740c002e0154043d6940c03441866400c0800c182406003408541c40010b036002c0c0159482003694074548802000e0004d0704184041c07003a4880c1500700030042c2e0b029010342072170854900090f0176901000041c00b03c43c1c4a036001544a0b1414108210071a403850002490010040b00048414805005000c20414100402c9000d0312807500a10700314500288014000c2c011446030b036 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 119756816 1250 119755566 119755591
    0x212010e04230a0203010e0706030e07180c09050607110f0102010905031909031203050a0c0903051e0106050d0c03060506030c0117101505180a080d051305040e2b08 72
    0x451408109129450741d01a00038800d00e10305107d030381e859100c00d10a403030119050608005101d00c020841e081a40d440000c0d054040445540e041d0043c04c00fa10b07100240042c0750710210741c4d07640d81030241c6042c43c0701c0d8250303003586447c15040c4840b000e00c00d507040f4151380c103024004002880201c1550700b01c01c003000c405003501138400011209002c0c150320141800300716a40300b04d840d43c1e15802ca01d2045401401c1800403d219003c2221003504510020301641c0100300d151071140c801242640d07100601038004103002d0b840e10001800600315000488418803450390810402c000f90192036800101180a030840c40c100c4000a00742030402040c100c01c8030880030000d00a82e05202c2c2060152402c07030150140c2022256024016510000d102d035591031040303002008614040c0202402e0341c400c036020780284c0400140540c3e40d5086aa025940981c0400300803541e522684190742c9a1480341008040110090288202150700c0a950000040600e80c5070100b040d0440384058012120141c0c1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 119758066 1250 119756816 119756873
    0x20c0c060f0409020c0d030e0a21021516090902040b03010e0405030c0d0504080c03060106052d0c0a1a04080910020102120a1505030715030c050f030702010212010e04 73
    0x107034681c0d1241e0380024188510102c5d514000280000f2481d031000800d072010400710034105203081d500d12804800411000c640302d6a202d85100320301300080003080c1030040f60700321914480f96900021040300e040d800390900180c00c1c0c41c0319501104003001403c800100714901402c00356000d0310b5200500508112818000102c2c040010800459440290b07000030360b03202c070709800d03001091948588070f480d00911600e400c045031450013040082c1264038a8940c5071a102104007011001c0c0034180e603c1b840e4005803106150a6560000203103203843c0e4202c081c2401203442d180ca0302c031902e03140300b00007091042d40003004001503281e02100c031506030441c0c002e04060403255040f800783c82069603050941072a40e0500c1003d0400f0382044c00c40d24822800800d425031076200b41640c503100d91003085080e80c0a034540b840c01c640242d106d510064514a050307441d040f2400e0b1485000e601c00e80303103200141e42c0020710307903401c01c500e040361400340003980f01c80d8516060a0710303107082040345062031000e4060600403 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 119759316 1250 119758066 119758087
    0x3020f0307030f0309050f0907080f0a090219150207080a030513051c030201050916030605041b0807050f0a080d031d070e041502071a0a1508010203041401020c0c06 72
    0x1c85001035520104600e128034052500403d040c0715849450301854403000e540b1881c0c80d0490701c292191100c0e030741d503d41c29562186e28108a000140072598155950303004880561110722000039100007031441d503904030b0328101c41e8882d000245e0603117000b150001c2c0710034000101e001c50078031405601440c269031500000c240d030340001003044d070001354440e00303816425040560340c02c00030500c0e078041d070000c000d941c5c0da04a62036200d00ea560381000e05205021014400681c0715841150091b000e2203c41c094100308880401c0c0302c992a40103804981c1c00340c3c07802c02191901800c20b00819005440b50704c0300c58500352405680d00400c89848040c542c448200d10100a43c0f126050713031902c218400c4980c80381e40c40d0049100d04c1c00a0702c0a540f098506102e0a0106040303008880c00c0590040d03c20b040d0656182d588080700c04054040031525232501d0408560300c510701d01000240c06420700041e07490405260007140070046c01002d003440d90050120004c41c68011502400305082603e04079640d400f00c80 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 119760566 1250 119759316 119759323
    0x180a090c021e0304090e01090b09070f03170706110403050c030715050c0f01020a030e1009080f0a1206090e0f07080303070509030307020402070606030212070506030106030c020a0515060118050a03020f03 89
    0x801c042c117013034540540104900ca054010300d040500402c049103d80d211034aa0a88850840c06807081c80718103540c007080040c540c000301148503509141e440b0b0801d00c1d65a161700c103841d1b21210f00c4400d5000440c090003401021b2090b440400c40031001000410300e041469014610741c00d1648050040c041241e062a00d003c0c0122280702d02020000c43d07440107036100180003030103a551807524038031801c4902c1d4051020f40c80f500d480d2907040303480d041c1824000c10440c8204e50143c00d443c0b04000302514000480d101502411001d011140340c042002c0b14485190b52030980d103a1164002680241003c20403401c0100440b504411685084d55845626901013880d5100c0d41c00300940051001a4070428084503500040540740308607104441011801070700d540d56091400781135405601000100a41c600079884800a0340c1d4500503600500956140d0904021040c0c407a026250003000c1003026541e0302c0340030444607034a6012110b4400b81420045000503c490000030300508042028030b40694082 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 119761816 1250 119760566 119760569
    0x4030b07032a030e060c0a091211040209030312010b07030806040c08060906030703021908010c0203040e011211090403121b090e0c0415030c020106050d080702130e03180a090c021e0304 81
    0x4c0c0221100d60a003518207030740d15802010800c00081c240303034003c610390341c008000e14410780d007200c4001d04040360345003000f0003580301c0042d4590622007040260591011035600314001c2500944d4642c50300344a0602801c0d04070010541c610481c5824800c042c00c54022507400e0f0000d01c20703070381395442d9034071a00420310b0100d00da08041d520100b02100c02002e01800b803404c0302031305c910400900041c0328504050340e8a000754010508405080001402240c40300310200c03a4807401a000d1041c0a50800042016040f06031801e80c0000e20004203100040d0300c6010301d22405294400d95404002c908a000b80900d4044c010401d404500501080740a0021010b69000d0314a04041068204481a003c0c00800061030b5135005942005c0000400d071401800764071005800035441c0b46064400d600300410204040007180c0000d035600e6105c0355001d03040018085018600c042405ea400c801800c00407000700c160310508075103007850399041400381e003c16003c03408100800c032400303103500c48103101c0d055000c0c5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 119763066 1250 119761816 119761841
    0x9060f050a2124050a320a0b0d0b0a0b0f0f0705030903030c1f060b0306100210020406030c081b042304051510090503070b13050303070804030b07032a03 67
    0x3c600900c0c8480310340d03041e1074129141200d00344540c0d95502411144016030004d542c1e074680083c03030390000a1070304046c0f560715034a00403c031200703090f2038010313a9030182c000301240e16070f0550394980a0300604102030400082d141421645e401d110741c40c502d50b1745900c5101c1e61100310140202d41c00e4108242001990840c2500509480d21039540e151800e5442001001081c2084030b03014070007481d03d03094445c0005850dd40f0b82e03598903550b101c201b0721080460b80b100c01c800b10300c10000c184041003154030240019008036038000c0f904030060103000f0003d01e00948038905000100960021044443d0101d40031100003000d084083c80308400c4050f0a0600503e00540050400d42046098101d800c136151588200712880b82c81d0701607600080b140030056005054155200d41402d1005081d0710340a4110f2181c10700d800ba0130551100c02090540d0031800d8100c4a0a01c08213080c41000005005160f1050f00352a0802c81400c102d0301c284942d8400101c0b0002515030b506444480c28480d41144285080 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 119764316 1250 119763066 119763101
    0x30605060f0702130b0a0501140c0106080105090c18060108041412043201080603010603060219090803030705070803060f0405070f03050703090308061302120709060f050a21 76
    0x86007070009110758840720080f0301c684d500b45a81000b0a51511441690b044041c0001d4240c41c00d0400548680f010300640d444614021300c01031a42604c00d0007600d01500c040340010803641012591185040354041c9000d10a00544104e200e80051502001c0e03441715007442c00e10f81030703215070504002d03030005129414880c1c000d0640031114158048000e20441c1c2080f50120440011902d00004401c0040a41d82e488a80c503101c00c2d00e07940c401c1d8403c40c5c000100a000003400c641d690740d58412a40801c03140020f8000741d0048005240c0c000b202c0c00300506580c4041e40c590300d45500020028450381800600344440400410820340391183c01e0341560380054401c00c40c6040ca0b0b040902410300710711010000038201000519030500c40e018581400b541502d80140c43c1d10394108010383c0c5d6000c030f0030302381080f9401d210420680da06611186c0c01420151544ca0a56003003000c01812299400300c03060510800700502c0c9041c6038071130400c149104c07468031808041004500c10324083c20000310100c03008103 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 119765566 1250 119764316 119764327
    0xa11030a0504050a06080405210c030d0b0906010503010b0d1a040501120b09070602072606040c0810050c070f031403071701050301050702150406060e100323070605070303060506 78
    0x41e00070008200b550700c1281e1a9040c0c81d9540002c0718009001c0b80c0040881e08400918211400107064402510342c00465071030400314215541c1f451900300b002c04000980e11420700b00441d00303182c40d5040d080704007860164510341c14800c41d00100d100760b0001000d8195a0018901031322440c10342c208030b03403100030018010b80d6514000c0300c2094405030801e80301101600042503900c03600084c02c2d4225034050b005003044a141400d01000942c07001d21201007d0340e81001340c0c40381841406454451072062031150700250401c10f28500c1d204d80022990310280c649000c0c8000380c40c0300029103000c0c07a440060b482d01d6201c18a0100c41149045c0d9901c0345015010052000d42c5800039507404200784454103104240c0cae44c410415013650810340c1c032074000d80c01102400c0ca078450101101c40e4003070700aa00c041f030880c6d500e41a1846a100850b25a9140c3e220040c00348104181000c0c0c2d5012111481e8140304c40080a5001903100d01062003002c0501000003600310405000382c00c1103004120052241d40c454 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 119766816 1250 119765566 119765587
    0x117100513050106030b040c09091e05040501060806100e01030f02061e041802030c0a03090804030b041506090b09010b0d0605030a050c0406080703110d030306030b090c01110c0105030c0a1103 84
    0x300b90070701521010a050003a10403450030b05104000b105080b6944a5248070b240024a4004004440200c51072550101d0350920703c01c102d0042c00d016601c10400001c402d072031b0803202800c0c1072015104648210352080300300b108015003c14941943d0b00031f00c258551351240c1c40040c42501ca8480352500c0e640342020220800009407001c1d200303c42c08002070501910380138010004030710045511110444043c8010380342e45110b9131101d00d82910900c1380d11300c0d00741c0300e4581512902044400320f80c44002d83c40101030f0300305140911001030504035020302600ba071000026025107030500442200040101d00360006031600d8110000601001e015221110324500b0a19221000070304460301441c103001002a075100001030725402c498004440d01814031844080203529200034109404150300e4080100c04500340c0100039000c0d0741084002d0841d00e001d98000b40500d16200417042c02a0408925450142d80100450740d00141803046035959140800090b120b08a00c01280c00d614400800c9078410f4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 119768066 1250 119766816 119766821
    0xa0c030515010b13180b0310060302090c0a0203040b09030111040b130e1302040504082502030f0606150d09020411090f0609130f1803110601080307170a020703150f14060117100513 79
    0x1520700984cc0c0e1945540c56004116182c81100a00f00042c2c0c070401c400c024180e004800352140000040002c11442a40701002c6055001504110344940f00014407040e441c0e00c03100110000c2900c7e420340000c2d841c004200c0500c120032030350068000c64888000800b003111074000c99400503100c0780d107110b030000a00c00c00d881c2142074444c100d00038404c1c40c904070801c0900041c03a80c0b04100c01440303043d6030709074618415080d40105c0300c504d99068647c0c8400f0010b82d07482c06a610b0300046021203684030011042080702d01c03a030007110140034081c1040700d0310041d111001580520300071004041860124144000005c01800018440c9a58103000c20020190311501d503561400d04c020807107501e4cd1301d4000c056100d1283d110002d1541f40c0d8490201601001c800c060090511180155003d0303d50301e444500c2d81e00c0c0d5900c84510b0056452080440041051280744a00039032140401e03a40d14151002901d60b0b40b40f806d00032909401c8400140140080c2980e40300175080103891005160072200b4414013 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 119769316 1250 119768066 119768069
    0x13030804090e0c030f1c0201020d06151b021302070c05030312070807030506031009080c1606090602070302090a050c070f030503010501030506010804050d110a0c030515010b13180b031006 82
    0x1030300d0050f5401120305240010302902d001540c0c0000c0c0001000c8903110150340a103215081c41955002d02c01102484c2841c440c950042101d83d441104d0700b0000403006080d81742c5203606480d082ca8800045000d03803925031554070412006100140c0d601c0960800d100c0c0c10303005d41e02090341880000741e43c0c00c1580c103140e1a1802842e0030b843d80c85050300c0c1ea290903426108201d90554155101c40d10014050400d600021291402000040e142040a019803420255100119039488a24150070000b1551102c01da40042c5404d1002d80a120706650000740b1105000d80001100c2d03446001282d40c40c10504122050b4680c0a80c100c06012040c1ca4041d000c2e03007092092a001c02d03d88070010703500354001c55081d0311882c3e21402609010090420590301009807030007603907591007001d800900040342110030740d01850090004103ca012207400200440d18160411500d10005206d002080080071201a00380d031440e0500201b0401e072901030720000c1002110440c2c0c948902e11003104082c000780d000e80c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 119770566 1250 119769316 119769341
    0x3100e0c040e0715050d061205070305120c07031101110604030804210e10030b03032d0a0f0f0e04050a0f0c0e0a030209130b040308160c11061303080409 67
    0x36036071071451490320f07489140b0854810751103005007262068851801400401144031000894503203a031140154556032a40032140c9920020090050000030410603140d0041c000c0d0b0b036894800c1d1904803507103030510391000820340100044030171140c0e070050600510150800084440914041c140117162190076501a9150400d000c06d5454825004520f400d4400043e114100140320032010700103d004618032500c10140e40c0c1c0c12811980d641400102400410f45034110040c07910740403824029000080e00c06582402003201c07911450700301c4040204600103007851495080e0f00c070410741c1d41180102078194050700e014100441607480b5030000410071048102005071000645007a5442c45400c6035059104080c3c080810061821400b004d40c080345902c020682c45000341c6e9600c0618000382c80440c0843d81400801c280320721401070001d245021850545071031201601c6000310781400c5614107000b8080014078610419502c524040150b42c0b0214896070303203545140c281c0040510402c020b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 119771816 1250 119770566 119770571
    0xc1906060b040501050f07021813020414071407051c0f08060405061c0c09050906040b07050310030b0606280306051f0309170412020f030a0c0603020903100e0c04 71
    0x801d210301841d050701c0075a20180c40d518a030501c48001d4401c81c1d0800a412648151144070007540c01c100c10480c10b00a5910740c00200c0da03041c01e44104000d4591003a002c09444144004100000c0d502c9806102080e507400041969003407982411410002c101e4100b240a0007208242c0b40310f2588980004101422903031007500c03e07202d41c400c020940c0d4041e108036900000c542d081c0a22400c103070200c680340621031180445016510605041980e104588074481d0313400c03074001c0000344200c1d0207069034481071b1031500724a5483c2242e001c5104904500002d0b1a00140d000080c00c240c031070000b16a04908101c0140c1e0900c0c241e200705e00c0306105c585a0724800241032107000195800d0045c401d90800700d510000085040c0d0051088000745404581514100fa103824015025000c5030024406001100c0186d101d5403c0341c0103202d05142c00d54042d6000e50301204014000c1048048240107440c580e250159403540504c000915083d001c164403802e42c1d00d805000c1240b9500058114001401954103 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 119773066 1250 119771816 119771819
    0x1205010e060a14090a020a111e07050603010b0d05270a030f02010605031e0a020603010305010501030201081311010c0305130e160509180604060e09060403081005031f020c190606 78
    0x81e000314116070083e440e00400c09030041512222aa0083e020002d4545803100d44603411042903481c04100e10710441c80c03009001540240200d0a008010141c42c00f40c6207145076515002c0c185100340f181850450182c0d50714400f2420107442c030b129115004d0f609080050701c105000502a4503219585401c40c0840e18440204640b14018060003084600080c003803e400807586000d020ba00075008040710980c080e2440c104016a00d00000c2c40c00f860258000182560440c800580f101c00702a0613561048585041100094292281811610070a1a061120001900c0c0c2600c16025110229003e40f0340b05e4408258801007500d00c0d03114860403424001c1c03215002d07005a41501c030b0110602c1e0860401402d050310201180101600210090000100940e9501140b9080303c019a40f84e10346802040a0205142e0300027441c0303400c0304d40009035a1034186004006640c0c0c0204644880411208401980c00e06005a042d44c0b2495028011381d14826004041f034050040b449004540d540d150810 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 119774316 1250 119773066 119773079
    0xc02060a0c0813060515030d051209060c0d0209040603060f090c0f0503120a1206140306070305010f17010209041d0724080c07240f050f01030b04031205010e060a 71
    0x28082c02102c3d00741100d041e0140c191181805008000c0c404155101c2d250120750a9840800240520800d240e8a00703444603400190810782510160041c6d0759035002c1c50174001540300c0700382110003d000c09500140e079010200041805070100354070261416107841c0a0f04288203c64112090191054403030b08211a165142448401c49078000d06406a02842c0d40110031b00e4444d00904801c24503003007a001ca1940507070940160761882d0804400002c4004016407107040420400d9048a00e500f020b00256050003801000c01320349110301d0300d0422030b80c00c0380d4021000a504071000c90002610a220450074800c03461f0005010152040390341c400d001c0009803480000d8000601e556074800c0b0840d46010b004000c035210740000e000d00300c1005041041c1c41c0003e103800000152700b059030001440004da0751640108664140f8140b5441505040800c64a1030041030010f055a5000c05039520540b52390404554010101c04c1802c030340c0b0f00e4440042103000c40c040c6001e1080c4002c0f514061969107450 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 119775566 1250 119774316 119774327
    0x1d0115051201050f15031c09150e030a06110708120402090c0315040b0616060b010809010207030210020a050405030604080c160806400c05180c07050c040c02060a0c 72
    0x1078050f62140d4000c404203c21511741d8101492210b4000c0c215440c0403400c0c0300e40304080c030240381c2040200310821740410114414604d40512600b0606081e41e60b68085404640c41e00002c1c18014480d6540300c140e00d003080191800e84076450741200d003842e105c2001d80d0041441260a803400d1303225200c84400601d8011a070400c0b40d01c5016081e140041d1140ca0380203000281c21001d0340f1076401107051100c0301c0b00d5010178006c081c000780182c5c4046580c540480026052902c094841c0c2c0c46a40104070500100c1e40006100c5500d00900e0f40c01039450700c00440c2240d40d4010b58100c298103024601c14402449140b1010300348464440b0181c1e00034049200d0b50100c1940f451080c41100d80002000406c500d00c1301c154028103410f40e100b403070740d4030303240c081150151003c0d00050844074004030000350511001205640162105031070a014000c040c401141d00480000c0c480000041e00003211010410705101c10150000d0141c01030282d41c005c1403000e03444003800c5500702c020514114440050707a1094 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 119776816 1250 119775566 119775571
    0x5041701051017011b020102030609420a06020f0d0539030c07030c0e07141305030601140108060a0302010807050c1e0d170f0601031d011505120105 65
    0x7002d00da4661400070740101180d602d1071880c116551350840c1c1e00d40c543d003d8078282410f0360141d00040e036034134009017001107a510160a0010000c154608030f01080b0308042100700ea039102c5031040c520520410440c1544800c544066504500000070000d261360300002c4c0c1c02030502900701620070302d6a031448115524003d00c1010306111000f540001d05000e100c4407a041c40034404001d00c210140407081103455039000b14608141941b1400c410024010b10b0f401c42d80c0038062200c00c601d0b1a05003400010a1b0610202c00020741c0340300002c12001482d00c0494120041c0005420b8484543c0e442d0300481c4001d0060b801c4034089081407000540e01c2c13900d4250001601c1d41611454115140ca00046469812410282505121b00003002c03003003560b03501446445081c20801401241181d0400030020001040a08282c034401c0052009004c000c00b1803652105080c600014980b41c0030080a440030300d0281c8001e000c0d4640494070100c0c43d02006514155070007076445282010542244600f00c81e0304 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 119778066 1250 119776816 119776831
    0xc1501081603020402090301020702040908090a0b070812060607061406010305090a020108151507052112060f0607080a020705120d0203040504110705060f06041404050a0201080703110403030504170105 88
    0x4180c1c00c1c03005207480c0e805012444d0001d400141050a1940840c0131a103098206075031800000c11404020714181c0013050260003001d0006040050710341d21a035031070040d140d401214401d0b40000418a48840060ba11116002082405810b00c2d8004040c4100415280c8a000030305020016403201400078800780c08580c1a51042c22541d80c039540b10141200102001d60b004480f0103050b420014450041d110b0203000c1c0c00070304450880410840ca00300000d91001e4219a0140120a90a02000c41165100c441540c0b90801c00c00b21400103039492040c00341c002c10700c00c0c0204421b105030354001048015140241c0c0c00c50440702c00e141c001c60740e400e4044150001603000300b00500084c1455004814284007da245c10300700010342d41d80c0d5080400441e40141c4e403041d13400402003189806e01a495444144148140e43d50806407191074840342d0a01001c0d05004400011854046c442e03840031110101805400e500e5617200c1c03074028802c1e80580701c2c5840300400b41e401c00320149418403c00c2d009188 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 119779316 1250 119778066 119778103
    0x705061908070917031801030501051507030318030e01020f0325020604030803011d0c0307080c03060a030605070509010305090606030706140f0a030f05070804110d14030c150108 78
    0x20403110868181d00c00820b03100c10082206400500190000b0b00384e10000b40c0ca00141d80c40f043d146082020980407251858109400c0800401840e140d0700c0400c10032501c50700342160b44815508003a00501200d114111400d603103004000281a8440c00174814414264280d81c1410002a0100e40d40d004421400b01d0040c09000300403241242c01802c200814409070450f4142540c0e51a0131545410980c010900820403411400c1ca102c94022040d50012190500030305504009070b0003055110020681e500300d500001c01315565076181901940110303423000303050040c4d25107070000500580002c40c41d180803a0030704000c0740c1800303004109a03115810280041810916204040382c55980d01410320f101108204044c6499038210802003450001544012030840d880808010445400030001c5c410003499030244800100c001400b40d44001c8101c0348070003400c8032424880c24280d00d020707a0450910001542c62130002001c40e001f541001c800b2410143ca0703a80c0c0410b5034450808400f03d21400e031 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 119780566 1250 119779316 119779357
    0x10804031b020a03020409050303060a06090b04270c03020d0f0203090a0b060a0305012a0f0807050319050112050606150307050f04080f1609110306060a14120405070506 74
    0x620080c141c819282c00240403c05007960b0307801040c2110031418090350141c20000c200021400c2450f05c1d50b005104030b2401481c0140b0300810b04801b401a4007030039203000182c0d0030110046041250768080500007150800080307014000180085d0301000c40e00c030f81d40e820100800c03010704d094400c4d08d1085050201800303200f07010303030343d041002240142000e522400c3c42c803010000c600300b403145101040034540d4031040780c45480004241e07082031560050801c220300344039030100c82d800540a50480d0b014200552643ca0f040c2134402003034070380003400700703c01d16120000410b50202e50b03860240502032800e540745a106c3c2001e002e8070404c0c1d80a090103c400c1000858200c501c10001801154001107009082ca03844908450505001c0260303800e1640c840b8114040254400c004207004260504080100c00e142c0c03583c20310f06010052500e03109000215440780e140740a00c0011071444081d22606560301e850400000e0b50030070545098800744100c0300041542c2c01c140d001c884030025412040300428 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 119781816 1250 119780566 119780597
    0x70518040c0c050f1b0607030e09070201020912250806040b090a0c0b09031b01120e030918010315090b2d0106090e060910030f050a0213021801080403 66
    0x1805040c2080003089000c502c444046241404941032a03840351000c1d0000e006081040c28210b01603a8040e88035400030410b0200007504100c48003144841940c105049540d80403007a802402002e16658008018602c0c0c40034005000c640c032801101c0300550f0b83d010560f1080210101540b81c06116429031015020034046001100c04035409002d075000c40d0102c0ca0590303036030200d10b022a80300350480000426240e0f503600d42409050b8800c10f50210000c000c5824000003004020750f016405038007581c4850200c03076001c082c0119003000f900581403407450000c403200c0b2080440d091106865404003071240c42da84610600030303100710035000003143c1602d40303407000050741080940c98020500c01140c00c84200741070702c18080034002c1840d038941920b071928080d44200d0710140202030030301c1203500c90204015960284070b003005030f0390802201194550545445490815003220207580320703100c1030402c640858144c00400600e000103050000e241041d000550303c3d580d05840c0180851200190001c22 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 119783066 1250 119781816 119781821
    0x90717150a120305162103020301090c0c11010e03010609020a090315110f03060607141e0c03070902070503040803130f0603050f0a020a121506030c05030907060e0109180501090507051804 82
    0x31b80220881c007101c000b0358900011402d0b02d0000600401d80200040005504034407034401e18110758100251aa006a51241c07002e4107080110f034103200703042c10f51310700c56242540b0020182c0900b804c1190307a0040803001038000306440c44102c4000705003680f00941d0850034011140d080c15502046400d01c0480c007409071443d040182010f400c0076040c0b240310040b80343c0c01c0c5542d5900900d800500440624003800840c0024a4080302d60305a020903409130032a10005003180441e1120100140c58060500c2e02e2800d41c484d903444200e4510004c110300301c3d410f0607170310f0b0081101e0140e41c00e20b0fa0b00d5a02d0f0020780070750b90202c40c100f580c800c9941c00203002c01b10940040510504500d003400b032908034100301c40101c600400c034a021400344e0385014040340b601071048809407155030074030904510306100002e03501d03c000e0280d0345c2000754440300442140d0003084190040c0403d0051500b01c07810310440702c401000300b440344000141c240f074089254a8020302c200c5190707402c0035040000450303101040c07001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 119784172 1106 119783066 119783107
    0x61e060b04030602090609030607110114070507020d021207090e061305030f1612110c010302090303040b1305040e0f06071b02090717150a120305 64
    0x505000100780c400710b0f81e00c0200943d48000c06008901c8078011035010680500c2001c09005500e03802141001c4c5a80542c1d008005c019046071038421419803e8403c40040340e0200460000b60174081c064403038140c0082d00f9000c0c49040340750400c1c40d0010f154022007041da031714000b540d1501070510103540c000c480740c2d0516028500a07191652a4071070603004e441054000503c10310a007038070034140e10409401c040c5196110a19800141c030a240d50818100725009407103074600150302901c20340d19960405001142010709002010350a03601c041d20031400d51207141000205c0d90342c0c50003400d50700000e18025105991010307205500e40341c3c1c05060321082c89140000a6000340a40749078080042e0121003522503500c49003002e43d540c207130700c5401f80c4d9a28541010400319140c0e4444101c0e42c0d280643c0d1a000c003507652924a0b1002009440040016108205082185030004503044 = true := by decide +kernel

theorem cover : BRFrame.Cov 119604316 119784172 := by
  have h0 := BRFrame.cov_init 119604316
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119604316 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 119604316 ≤ n) (h2 : n < 119784172) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
