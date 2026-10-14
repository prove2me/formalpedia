-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0423
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:44:16.922492+00:00
-- url     : https://prove2.me/submissions/944a186b-47bf-47d1-8a17-5ad95f5ea9db

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 75899282 ≤ n < 76079138 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 75900532 1250 75899282 75899297
    0x405090f09010b0a050105090d05030f072405100e0a2007030206011422180b0a18120f1106010603090b0c1c0207060b030601031b050d0c030609081306 66
    0x401000380720340030008500304c40006003140341ca00020810702844000703504c191110400d403404c20501b0000c4035113039092003070043d0701c0740c000b401c1c0754200711103074074020911034401090340700812003602c56284074107003181c600d11030181403800c1c01649240040c0b481408030740e035030100050b078102800015098600000c502d6903c0017986402810550107034004c850b988002c0a0b841525a6490803100301910000103c0d0b0066404000090140110740700f140c07010b0b4001500c101c2448001d8040522a0340480001d201d180010032018901002700072000d001000510303110f80e1060311600c0810b030001c44600d841e00c040f0701900c11090800a0a03407101e404641d842c80d0071403c205c0c6001105610410094a8034101044900140c2004201c4411080710300e900007441d1003040200d50001c698000040c00301c440035038491410011041c0003000d8440401d03040ca200140900d000c8424031030456001400000c00c80c038564904024101c41841210f40840501203000c2012582202c6001011159691b20 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 75901782 1250 75900532 75900541
    0x7020306010e011a16032d05040f080c010f0807020c130b090105010c03120504020a0305011a0102070801021309020a0c1403030f0c0301030201080f06131e150305070b07080405090f 79
    0x6890000c0c0c0c0f5400784280c40b043c03010007400307174290b0781c1c081d0304641605000c0000001c20709520810321000e0080c07507010b4500c400c1e00d0030b203d900c00e02400c10768820a1842082588a14115035100303c2c001e46140040d52003004942d000b44511001500601d15004980c3d01511740000105019225030140c40d0b1243e07184100d0805240000049004200c2801c1c01030071000d05440062051249108120141c0c3e1120007103001c549910b42d40800840e0040007c1104155414004000381d036413403041f03030041c41010800303e25010b040c421504000c810160343c030291485e00503541c1c0650000b20031142030085034002c540c0494005640112481d0010020310b45c1c1e8904030003419085003014203420104c403810f100501c0140d8001c0c00441c0c12a00166840f0203e5a41da8001007694649014120001c0d050200c0e084d80f140c0540041c0b8055601d00000344401c2c1803010580103008682d1001510b01c0d40300c0d407000c10051407108002c101d018040c03886540323440d485601007002c4a4055492480300790780d000811 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 75903032 1250 75901782 75901799
    0x72004090813060903023607050702030f0715030b03030904020c1f14040f230109020906030604080301050904170a090e06040c140c010f0c02060403020d020d05030a020901030207020306010e01 84
    0x19003d01114141800c000b42140c0100300840603004010034041103860548004a10004840c8088288440c050b00c0074588084001c1a0341c2064004074024803c00f848a840e07440c01150010030394074551058410084032500403800303000000c80c00c03900b500040150f0b00c25600da9000800f41008250b000782541ca00345a82d880c001c0e20082c4050103402d00d042515602e06004481c61078200780c00040070106c00c180350508620041c0034807e0105620720b107410803403901c1019000340c5c115a0088501000c550360385c0c0d0a240d1190300403074000705194000c0005108516200d4059130b0401d00801c594203414400750003011455108885032004280d241504120040d012988203034851016201802800001d40c0003424100c0003544402c502000811050341c11002540028000c90390284148241c0c0d40325078010751201400d6070281d0060080084041689000103103103040d1030415514186156502c1c8040c0c0000e40114500a040540030046003001d40d07001c01900d40602201c0600c1c00b440d52510052 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 75904282 1250 75903032 75903067
    0x5060c160e040c05040209011701090c031a0a050114070501110d05060102030909070516050712110a0f0e0a0207050313081b03030904150e0a0e0705010809030720040908 74
    0x1080d8050301a81088009910406550f0441d038054a02580791441400184c600b058100703514070044120100005000c08107030401051482c41361030820081070601002e00d10703559081c00068103d005c0d968100aa948154100841d181213a0440f42c1098004d80c1c4241c2540d80d1000f4013000407002241c010202d00352031150340d03080703107090004515000c1000c0218004201c014009002d000002c00c0d208d61101c503a2001068181d0302c002503405040e264034036a500b41c0004a0151024003020a0069160030704009200649040c801d003c608240341c94400114402c0041c2840c145540900c5984005881000601200300c903065503640703418100714005140071449001a4030540b0420130b03c000319100802103c1c9215400d503008619020500c5107035013040d40d1640030000c000c000304100101010305500040c1640900000e480c01d21f41d44400440d03144034155010741d01600108031560000f0402c0c0c0b0081902913100f40859811452040010103d0b1091308064611840000b00045a0024082c6 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 75905532 1250 75904282 75904289
    0x2030106020c12101a03150907120503071e06020c0c09070302030106170a060302030a03080a0b0618040902040f1107021f02060c0c0a0506070e1306050102101505060c16 74
    0x40002ca0406003c41c45a90f55a020340088601550b40005890840d840320a100e0140c1003e811215019181400122902411118590a03016000c0d0102d844100d20219031181a013101c019414452070340c852a800140000032002038000f681c5030f030320024180740003800041c100180500103400d1508280050168014038560402d48104014404c01c0c0e003111800020b140f404181d161a40c4d64003e90344000d000907000654184210b000c92004c00d54032480542c411030225006120350341c0d400e018002d00e400f070001c08600c0d04940c9a02e000c024100756002003a5180000c00104185426002c0b040444120303a1000030034a40000f51103080d4203100c40110b180c00099000c03404a014000070017511100e01410403801d43c2c1c0001500c41e070862040080c0e0382100d4210341550320324181641c01400d050140c6400c0360182116903400f0f03106034035a100e581700b02c0380d040c0c0290441301a821040001862400d84004410000c0791002c41c564442c0405444441110401003c28a24584400040da9026030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 75906782 1250 75905532 75905539
    0x108010f09021c080c1204170a0201020a02010f03020904050406050106020c06070b06011b061509060512070603020310120506041b0312080a02090405190b0a060e09070c080d02030106020c 82
    0x8080010b89424038031411016014803801c01e65901031070b0440381846842c1701c50445100f140b0f07000f6910f420035030040c81158240e139400041c003903840051586a140d0244007030f002d60854842580503501030306005461183c4c2d8940107181007404e074002402c0300e000352000e5034103558800050250070380400c441001584111a020b003007418603582c43c04503144c0201854100a00305000f2100842030800348070b091031380020180a02d46001801504010076881408074440c20054002554281380e041d0346605107041019000c81803c0c20320560195001a00204003190000c00001d14460182d007540d800ea03100354040c00c81828242048540c8407a00d00300c202080124002c20000100b51000c45400c4201074206030354550343d0704034140f00a014407002d068025040c42c0c20000e020404a162180f9020080c07820003585000d8414445059500c4c0034a401041ca001d04006180c64615026035010f9074a03e040707e83c21110360b895031425046114580030701074020006002494051010b09480b0000340d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 75908032 1250 75906782 75906791
    0x3050613050a02060c1e0c0a0b040806070c05071706040b0109050c04060c03030f09030f110106050a060309020301020904090c0e0c03070c26030709030c05040506060703080705040315050108010f 85
    0x10703207a1a49400c4140d0009205900010312200761080c188420417001c0214440d2008001303007512125110344510202d1440b40c0c0c44010049081c5502e503003507030140c40800008001981d106c4c0000c0e900164261b4054602c0d00c549640058210054920b81d141041c0300e20181c000c0e42080c0c900502e4000040e00f02040322400d0a0802c841103170b201094070204c8495280a07015403100342029802441e0ba400c803585800d0a00324140181078200039024031612141d0f96104a00489580080c02c1b903000e4040c940d0301400c642420080c641c0709400c40d444990005000600d001900000101120f901000480e0001541002045468031100b60158080305440804e0b2462074103c0c2c009000408401008000349070014102d52920030303071075817002c080c0c2c4030340c400b0f999900b044200a441000d1a1200719009880d20070081940d040901a4078028034010340402e04103070150741c0546030707004d00034503850070810113000000105555480c1c0f01810b40702c40d10700046a506054446080d2801c5a00b000d1000e800e0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 75909282 1250 75908032 75908071
    0x241202090f0a060317090306070309031d1201060602010b0a09050f2202090a020310060c02060301060f021903180b07020f0415050d0b01290307080a180c030506 70
    0xa11464952003000048400055620310305020000c010f01c1d04041c1c01c58459035410650244600010006004114222081c83c1da82c000210140d40402c00c00400003401401d0020389a10307805400b2011541c000d20b625030f0121480803140c01c48400c0d50103800181c2d1181070301103e0703060100c00031000e4503a0746000d10003032030102d502c06d29075400644007060303844180c4448282186c00000c81c1743c038150300401003042428026091001717500150750340c2d4518100f05000040da14014002c28170455030180801d8103607881c154060301c405214810350410360080210707c10038481c41d21890590035220703444065582495684081e1880200d82080c0c400381c3c002c10651015903519040304500301c42c1280c0102c1c0b518100000c80700390101c0c0c1e40c02140c0003004200d94100300020f4074082c0d416150400d5554250301100d44501283c410200501410800f042000c50760b194454050a9403200d42d4543c003046500e20403a000c3c1c1042559202900c40702c0082e0340034400c2280c00c0c40b02c103030030602c03040c184500c1261 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 75910532 1250 75909282 75909289
    0x1030308061f0c080f0304030905040506040c02190303060527071d0f030c0301020d060e060d1205030703060b0a08040506101a090f040e0706020d02030307050901030b0310241202 78
    0xa102c220310600c58403404000c02c015800c022501080401c41c8060303128185854013810609181c0034441c4641c1c28070002503d1070910748a20101220035030700030b100c01e42c1011118848040100030039420076440c0c0c4004075007a1150161400d40d480044608804035455401c0d40a104030040d14110070024001d1903881c2c1e2840190040445d2101111400e0030940d1000000e03180c549400c001d00d82650000c10100c90507038130395005200f10780100340c2000850b598081000300409100c10020300103920184590640f92140d4040c540c00703119810300158564a076001c2c601c080c0c004e01003c00004100320704100410009000d01d42d003012132110151817440c140164464050340d2400714aa02e06004110000c10340e407100d1481e03036004400741c010440340122040f4140c494240d4020701015107c1e90416861a91001044910446165560a043c443c480d001107000c1d040343c0c44400d0b814411f00740395040c802980e2143c4030003c0011802404404108011300128686070751000e1520b210310a100b002507203 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 75911782 1250 75910532 75910579
    0x3090a060e1b060a020a0501060b0a030b0907051e04050405040b04030f09060801091e0213030302060f070e0f01020309041416050f040b03130f0609110916200f01050103030806 77
    0x240b0883d007071901c4842401040f481c14011030406071456081c00000504805480001e0058a01d566800c2c0006c2d00c00c5401d014558a00b41c82140009100300801c075000480381544075101d02e07000c0411440d240d5904000380540e20156402d50320032000105100400d40c001c0c00c15241c280e03083c01c1580c0c00e40e00d00500609509014428811050707200c08911703444001400310700440d203a00f450210b40300e80c41a94422030205650000300c0161055a02088070304400c145801e10038480d50380d684c1d85206802052198140c411440740b0b040d4401842038882940ea40d003d035020100614103540d610b4501a010307900d0307949010364800103000f410468040000300c5601114140c0d0032030840c042da00d840c0e4842403448180792a5002c0c11001c500044142040380e035402c49151107010300e030009250f44101c0d0030080404800c0d10111407640c1d080303001418044c040c07415101400c071288c06035401c007070b502c120413814820326a488071000e03592240103008040c0c00c0254aa00010240e030042e02c40e00c4500312289442 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 75913032 1250 75911782 75911833
    0x5060a0b090402090a031a010605040e0703110d021216030902030604061a0315040c05090105030a1410020705010609060803030402030325060f1b030c05090603060604050603090a060e 80
    0x1800006481c0815407901c0e011680103150140408107440e45d41d082500c40ca0031840402e079400b030109000001d402d4807407410758007946c00c00c54500d00c0d0383d2100141a001011b5900c500c050008003440710900c0715006202800e00042d40282580c1039141a100d0801800011400b030010300d443c12000c1c2c1c01503200021840e6116030302400010b0700d0000310f005141c82000c4031226540c036200c1c406090400448a12409000303600c200d02602c1210b07261b504000c016a02401030a400d9400b0010010100c0d54039080321f28000100f0060703603010043c4042500580c0c1c0201c0040d10780d6915400d040002084030b01c6104000e2540318040d600f9410198000b075141d128180c05038501c080c07024070002c4403209111070f641000e41e011204012101d854000c03d030103429412200c2c0c2c5241d25400461441d20b01a010708400e0340000d9030340f2403070040b596040010340d80000e8082a04108144404681522080700950064081d18000c184008040c0b1340001540c074011900c240581040e0100c0741482c84440000c48203 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 75914282 1250 75913032 75913049
    0x120309070e09010902120f0f1902060d24050f0402070c1205010f02030f04140a050d110309062b1104050f1f09060e06070b010501050a1701081e0105060a 67
    0x71a19422141070140c804504040d5009081c5840d206002e80b00103116491509005d0680d002c5040c0140c83e03d8681e0410074010841d103403400050720042c98140010303c0440988180061003880d609007001381c0300f180070200090f220445000b8043c503e000f03048022400c004490035403400390180d4a8952804d460300c00e0103c034007021220203041003000c0d00186100c5012100441d202c0c6400c04011080c0003007590141d0740c8240e442c810304170340280821500d0b5030981200040c0034402c40e04030300306c1c3c061807016215a90b81c0004d2181c025640c1c0d85000501d020445000040b14048000703000c40d10204002c81744407001d5180c640c035035608800d03d505940c201c40c81101e5101c140c0140f00c001c209000014404a4000c0d0789510810384917075004074a03d01940c0c00d84e03a403c0200d00302032040c050b0510803003002800208441d4010002176106030010802351071030b031a02005130600c10200c9641d60a003a00a101641c200c1005440c0c0c80d80c22085403066198080024407050400c1c1010550300041809204503 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 75915532 1250 75914282 75914309
    0x3090604090b0604080109030309020a0503030315010815091608070207030f030c0809040e011509020a05220b0d020d0c0e0d030e150a0201060504050618070c052b0212030907 76
    0x10b555504001c0d90300030f0140c40020f03c2451502c2c44c00030028514014102c2c4242000c410110b034608001064034403032042c946210041101300c10065600c1c280040001c0702c1250240d11088407621034040880c001e103440c00521200940450015005000041080c8210340c070070b440800100361001c14208081e6010f04100d03070403050504100032184980440150082e08009041a404c0300540c401d0351070205045034404019100c0c0003a60a07481402c0c0e100c000244140002c9000605505000c01c20400d80070000c0411a80c81c1d05040454101c451003c1c0940d40c003160054002505011751680b4a170780c0c0c9010001c0c000508002808005a8000035040210a4084480546071504880801d548040c03040c0d44540e5640c00007070181c911800380a00650501c2d001c2111070074140f00c0803912812652041e9116074581500300c55000c0780c010103407002e00c15180c0440c040080c0404078000e0001c5942c110a200c1e081705000780c54400201c1b12080c1040302002000300740b0320042401d0007602c441615103074 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 75916782 1250 75915532 75915551
    0x303090302031314040b01140409020c030d09120201060b040312050a031509090203071202030303061e0409060605030d0c0506060105070c090204080303061504050109060c0302160e090f0309060409 86
    0x3071850050091800192030500070206140001804d444030741c44007140c00340711b840044c8004654900034074800e1104540c007488144a100e0094000d05011450402140d00b042110840300003600c240d5007007644d0084440c203480980c1542806442c015000d14403d9a00d414516561212095085210719080160104800c00c14034400d0304827520103030003004607001090b1a2400d80005240041d0101e2080c03244100010f10758190380860082c140d001000341d810741d981e210070300545004500118180b003d40600e582c403295910b01c64940303064082d140003e442410803052510f0f1411a445402c10300012034403040c005500019141c0d480b03c02031030a03548642c49031404880c2d10000d074002c2009503002003804541e283c4000042d5200746e10072190b20100c03c00360f00c000c071407911490003154001205280d042c40080c0c000d0040c1e1800500c079104840344400310a400594480640c0c202c0c001604030700041c001003010802c112686120b910015500d00102e0900085551041c0d215407012981c640c160f030b6 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 75918032 1250 75916782 75916787
    0x1602010302030604140117010c0306120327120605070516120521060f060c03070605040c090f060501031a030a0b09010212010b03400203030f0406030b040606020a050a03030903 77
    0x200c1211500031007050255849200f9221f011480012041f815840d002c0383c51171051203409007100700d50040080760402d01480d1402c4407240c1d0031541d0392070541400e80100d050180511040d000808070350740f0a500752041850200241c0307601826403800c0000134003c140729420301c4503100301c01c0d5501c109110303206c000e000fa0035140c5001d440c40b40c2401ba07050707071810803031504c5503501c980c0306260444020035038107545420080640150750100145900174004400000d80c1580200d070014003645401142c1c07555401302c0b00c1911825000030405644036682040596054024600f05507862880307608141000c40102e955500004006000c5075151000702c2c1c00c0c250298100c03030b40081c80350344030fa9456864001c00d0707559a000351903000719080c0503020301d1184504021880302e82b0380b0b44809024001544076440110340003000041c0d915001c1040f068030014801d84c018802080c0075180890040c415070100000c0392525449a130554120384440300002d40041020f600441c1c0c5403e0000e480404c50508 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 75919282 1250 75918032 75918041
    0xc210402120d020a0501050f0106080a0b0d0c08030a0e011d0915030303040b040312050103080f0702150d06090e0606010c0215070204150801050a111902010209060a1707051602010302030604 83
    0x4070784180140000000c0040c0d0108902000c503000d00c00034043d6171100f81c80c03000c5d017001c00d21545000030105e5011501120b01d94110307800038040145211800390003901e03031480c036005c581d1040105030310006101e0324403500507008080401090805604075130491050310034005410303803550b10924400000035441c007040410803007020b2002e8104c98403494186898123801d070080c0c40c02d40c0232a40704040c0443d0304085000d00c50580307521145440c14451201031200f00ca03000804100c1c0e2042300710042c980764103004800380c031405c0ca22030004100da0380742002c0c0800310b8002c000c8401c42500007604100180e40c102060b00c031070035070640700c500c1143e2100b441d550540c010410002d41c40360518114103080b0300e90304070440c00d580d00380d0000c214648403115450100c034212500f181c5207850a11000c2c010b414004038810010405000141c40c00071040700103015940301d80441004a10444c3ca07054001c882e10381d440d9400246401e040b890442e244c05031800c1c100d000c0d0802810190000f0014409454030b801 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 75920532 1250 75919282 75919309
    0x6030e0f1204060509012303010e0a05040f02040902010e030d0801060e06070506070e0a0f080102030627040809030703060e0d180f090b040e0a031101052d07020102120a0e060c210402 80
    0x447c001d824016840d1001d07031081c40380041c10280c80010955228091250501550f4060b550380c0f400c60141e82400058140701500f07a040c0140c00d410b098854605000300e001c041074582d5403440b80d60411030040d00d00011008080d000703460900c41000065800910150400a41d00b0900c03041710201000820b21003c035003000703ca05800d03c40014081e81c054014501540c000c4908441d00802e201b885914401c000c01c090486122072070200e804510400700400340f542c805025220010307181e803a484191955540003800c1540f2a0310411041a44444802c405016480598002c3c920340540342800780304038000c0010082c2c2c0c5901008179551207501840103000800b09951900c0740303a0901a11204051458040d154242070010f0116483e200341512842445010070102d01c0488000460302c550040141702599802c00003164103241502c042c52003406c80c2c40001c101140d603640c0040c1015000b500c241c0c0400000d104d04170049115a40183e02c6040c1c5009000e907555844c00011100e9030001c1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 75921782 1250 75920532 75920567
    0x608010905091e0303010602060f09030a0e04110703020f0705060a080703050604060512060403080c0a02030a08040501180c0611010501050109090c0e040213080f190210110706030e0f120406050901 86
    0x801c85460000c0013860494407e42c09441c000d50f076041102c0d1300030000321588200d1b0b810801c0f2103003403507001d02103100b41440080c00000311241c00940c4a0720503401000b0a90143c0c1c0000d1454a84042c00c20504014040a54005042c5105502c001c0d02141c80078003c442815201d500107805a207460b40210010400104503188045501c07041a44072601070b5020760024600c2000035030080d130f0440840d24002450b40c01180340081d80c02b804c0303c541c00701600071a40c554888040e9101d18046843d41c0f640e41d0300514800c2415403a01c003005d000540b10725160003076a41807c0c0100481e03a001762210044508442c404100c2d00401c030340171071b20341d07031034928983d40603201050142d00b071502c1c82008400c1c3d8824108440001011070b8001c3e5850b5400050a413443c440c020000c401810035061200c02e6810034181909100034080016080030b50b00c1d0480030001c3d5451100e00705140b02041100034140c1ca000240121500607603240b55207100d180150000e0002c00200d000c52648100610100c449541c0e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 75923032 1250 75921782 75921823
    0x30c0803040b0a050a09050606100e030604111903020f090c130807090b030f3304080703030605011d061b010e0a0b010602062806031e1b060801090509 66
    0x92601040325002903c0c42c1c881146003d0008201c02c506201e504100d40e000790041242d0356500041000310b8914110380d0080082044e0007203116101000807a009031300c03840803100034490030f000340002c108000c4e05040f0303000c04107141000076841e010070b541b02034039080d00e0311100c40d51160760f540e440e880b4000229900301005000050b10601c007180340700a44900a1092055440724000c0550780e0b800c8080350032007070b005400c0f403080400c0c0650400d010f0390b11050901865455003d408040700c0780c1120706503510b0b14001000010564076200b800040d02d03007400c3c079101200f102e45040c1400c1d924203401c0d03406054001345011100301100d48060310340042c00000c1c0041840120216110100c410044916010420012404500115685108811603130410b69113141400b103140c000c0b4a158040a00b07140c0c0c881010010540714295848990081950f219001c8018906a006d0785074080b20f40e039030300d6041c000501c6030135444081681120720316600401d454483c12041c904080941000d142101040c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 75924282 1250 75923032 75923041
    0x3021803100c020606040207080301230d06020307030f02040602101a0406121209080d1421040b060406060c0615150207180b01090303030203090703170d05060d05030405010c030c0803 80
    0xc1e80c0004105003019801e403070060312048103001c244c0c09007120040092005000510280c62000703042000c09036a02d40171500c401c1d910001c034100c0300d6044001e4907829000410052002c0d01030280c6000380301d4a001c11071410745032610003500c981074001e030800c1c0141c40b00c16403181d540e06107010110030100200200400da6030341d80e2000c1d80b0100e0b41c1c07048640303142c00d104000020b40902c1e044e204032110b0401400d800c1407011821101c08051010304920240140b04040500360520611842e24a459414541c1424213003800c5ca002000104900e10450038090705201c46a80900030181099001d00c01040074221141c030000d034002250066a54040035440410341d15900060000403525500003507200c038070079205208242d42480300003070b0110700b01080810010b8480e500450b4050a84025142c6864503030b920300e900540300c440107103085107000c81c030100382081c00d204031900701c403080700c044006182590b00d898a070b005a01c5aa4103005a4000440905000301001226207500420480d0359151 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 75925532 1250 75924282 75924313
    0x15030209070207080114010602060103030810180501030302010b0906030d030b04140403020312010e010b030412020309030f071508240a0b0a03060f05030321062b020f091603021803 79
    0x202c1c490f5513a150f00300f8171108000701c40d17501d03058103a4030140c0c0074011070784c02d507241551644000350585e440c06141d03201c006200900390360200d40350340b0784103404521545541002425a2a900d510758810009042400219030700040c40c0e4190304403a0601041c4110840006001000340320003000299014004000070550b000c00108800c044490208a42c1d0b41c032400c1c2c82d030350b00388240a00c55040e5420030210300456820100020310341038920469280c669820003090a10a08038440c4149600c412414422240e00740c025403200716140c582606c00c1c0c80c225114101c0d85000c0c180000721480e09007000b40d05a103900985202908100c13480980e6007500000003802005603200382c5201c1c071090781300401c01d45804401c60389480d0451403815007500f801c211130001c81d04068195944070342002c2c3d0403103610412612041c860b02d84401c1f0052040498010b02c4104c195801d5020310403400b61040040d4802000400002c0c0b008925005841e0000c0b00090758503062440d05155240c03081c003480454002c2c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 75926782 1250 75925532 75925543
    0x30706020d11030907030602030a1b09060206070e01020a0f02030c060412110603010602031c1b020a05101515122c011118181f0803040e010306150302090702 69
    0xc0840008210b0040c454081c0142404143c910083d642c00c0704508101003000da802031074110901c1c600010728140c01c09060303901c04800040540124203401303010840c60350180700c00d650000042c20100c00d02144440006e4035184602e04c01400c00345120125420364030b04004080000a000e0311a642e40c0d03071600e43c0548404001c05084550303210b90590260142409015a4101c60164000354201701c104142c011021180d4040e0001150365585003042030007804146200b411174a0300540780c0003000b42010f5081500048203181903c0c02d08140c03040d07043c2d51070404011120041403541120710b00c02411106903000c00984079426003001148001001c601c210a40284500c818443c0c0704400420402d00780c030000002c10007001c4061080c03040700c00c140b2403800c1c072202e000ad2141c826400d80c0454220031140c26242e24406040009198150508640c05000542448002103003030a241c202180c071f01140c14000103005a0315401c2003014100748150580181d6401040e00082d803424860007135999 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 75928032 1250 75926782 75926797
    0xc04030611040509040b0402040e030f0a12060605091e031c1e1413090c050a170c0a110c0406151407020f010e18040b01030308010801050f010603051803070602 70
    0x381d150902101c5035211080403941103034005401a01903907241c1d00c2d400d408110080050340c00949a0b03280801c04441440100741d84110618201d0f00e4040000780242802400100400d2107490207200f8032205810200380e6240781d00880b40c60684004605000d1035000400d0882d503010303c01c0c1480400d600380d00d003070b00040e41d007101d9480702c01c88256014201c50705001d83d000040171840740d6030008a694845002400c5042c50701081c030204503521740000084503082f003a0f90700041c402090481986500c140c81c83d00e00d041c81c00d003822460620800081e1148a801200401e10132000c05400c40031109000041d0038080003001088000e81c2c542c0c1c04c0500b0f400200182d0700050031405201344201200d001d03500340e1900900b200300c250340e8510054440300852180258030400ca6000303004210242c41d001442648200e05040a95155181c007a00d64501072b000303500301c0e074144006c12035007510a55625044682c00c1c030f804226034540300402d00d1303058181550400580000540074003400711a0b0010100e0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 75929282 1250 75928032 75928043
    0x20c0f160608071b03050a02070e010e040b0907230409050d02010c200a08030a091e03020c2b170403230312010603020f0405090109050a050702010b0a050d1a0c0403 72
    0x56599000100c51030968109007013503a010300360100d0040303845280501300b01034281c012942002d80303076000709500700400da00090300b0229030b40c200010032182001e01c64001c9036040c0100000c90401c4184441400c845841820036400840480c813140c0e40c9400003041d40350044199121001c0e074000080c06088079000d0700020070840002e0900d0f000c001060029004005000381881c00400e946808841e440a00b4400c005034654402d500890030000848080c00d54010415541200d14500a4100200250b00c144503c1c00c0d0315841a1a2250710f00c6156410551b20f0010b580401c985481c0c6007541c0c07a980361542c41400401d0110400c59203040d194407850f80f0781340c0c01031000c413a900c0c8195684a402d0fa04401401c041d00100400c6010780c000c1d00c545505549001e0500303072107c0c081901903000740d21907141e05445005000d050841849400c0e0880700600c024000c490350301012800c45c400a102d440d004144441040e01030004100d244010181c0c004140c1d042410300d6448111035420a0109488 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 75930532 1250 75929282 75929297
    0x5030f0f01050d0605040507170708010c050a0905120106030b0c1b0319050a0e030a110f2b11040f060f0605030106020c040c1209030206100b0306090604020c0f1606 72
    0x1006500c00c01240e04945000700007804050f50307941c2d100040c040140c0225164442c030300003c5082241c00749114181d0150700c0042100c81d01d005221801c0d2a0404410b8052213030030882d0940302c81c0c2c044078001c117603103041c4ea10112980d91003d0340790060010b80e1026191808580520440c56640d9004210105038000f03000b0320340380036003281a00c1e88940600e4a4410b5109001400150f010303901400140880d070610f100c05104620100341000c000300021240000300c412000c20328076009144074120035049e90401024580b58130501c12941802c86800ca80142c50b0b4200010440460482000524040d005214114034100580042d100a001d20350102543c804040303802449101500d0484a465000f040d0000c8248140002000d110052004000a1081c044082c28440c000c00710340368400c0e4010613161503c1403d54407010150380004c5000141003042c40040da44a0815a8001740106e8005a44042e10703a0490b150090b182c080360081d019540c8040058007052140720b04807083c1c3d848200 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 75931782 1250 75930532 75930541
    0x10c020102040506090405090f120d0e0307031d040b0a08070e01151b150c020c01031b050301030209130212010614011106181f0504231209150a05030f 66
    0xe007030b03029a02802d600201c1c2400841ea9516144d08070542280d0f07500280c55142120340b801a0802c42e40c102d5070180b04000054140c660754032485a180c45155113000b4604144c02a500204540014a0b5000e041c040031388150750305a5a0794805040042c00800203c8010707a242091901c5511510801c800c0e042d000c0000035043c00b03001e0250100901d00d0f99002d038002200440c16001200c40001a18600c140707960590300795801c1d2040e507008034203a400030480d040402c0300040c140c0307440441c40d8107050b14000f80f03508943d82100540341520b904a036014102c1c0c1d5860000d45060300b107410003035401044400001c0c49884198001020388048070024041d280c0c0c0c0500544441c40c03a9031040d1000c0c0d04c1000060a000d2502d07030490600c1d80b0070026a0700003c600700d08250090010720321701c0303051b40c0e40e075044c042002000580c000004080741098843c40b0082e00703840e03403a8480d20100d12188500007501400e2591651344081c002d9012901c450f0312441d04000062842e08100c411a8041c84242c0205d03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 75933032 1250 75931782 75931787
    0x40f020306010c12051c02030f010501020c0114220605040801060608061807120c18080f1905030c0109060204030b0a0e030406031104050a060c150c020a020d08070b18010c 75
    0x128400c0406868608504086139180ba80c0c02d080a030109003041424003244001c654603440c101c1c020100c0301c00158680c10300203042d420520040e840300b81954004150624166000b10131034400e801001050b0b42c031085800250105620390008481101d4010707007010030742e150031001410950340d5102c003c02105840c0c41041c0c900d1001613a02e02e034020184407404c900d0248070104540e00c2881458410b1602c29554052000c0d1060031181ca4003090700300f85014114a5109411001400c0d000c00802001022000d081d0300c907512410010120042490b81c401030000c10007c0b40c910544140003044841d5203820020000d40050000b11f50082c80d507008140c5001c15400f980c3d0f1a1100c01c006189440d2401c20150004d01c43c10f810300c0c0503070300e013808001030640c0c030746108000800e61a100d03030707900386d0301e07482c003002110b5000f1000094207140031007004803690300052860f4116815180c2a28240941c100004107000340000141807147d035804100158011818100580c031102d0f000b80407030200001c05 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 75934282 1250 75933032 75933037
    0xb070504120803070302070c03050c0f0f100f0c121706010512010b0d060e0f07020d0503010303080712060b03190614010815040e0604030e031005010e06090a020f18040f02 75
    0xc070340c1c080011001540c00716070900c00075074115829040041c90b05406550350300380685254000d6800b034214030b10200040c10100321000c0d40e80f0007250310324120b071641e1000030300300e900c041c0a440400074078460700d9045a009028458580d90007100d030340040150054000c0103410000032200c400744060011540a500680541d0b44000d070070400d01c0c03103e030700305170000c00950020305210001c03603180d40c8001240c410003011b0902601c640b001c160b11900d0485ea0283c9071842250b54427040010400042000c2035001c41c1d000e412920500d0010b00310400d041d401c0000d04099000f12a40d0700c0000305000c485880c180c0d0400f405205074409001c0580e81d2414441504020107105001c207442400050302c0c075410350400d0000b80d40080c000210344026a407180e207464800c41c1c0442c04501ca86c135451041d071a041000c100340c40441101407002d5070604004c0641440098101405040c42101107184504c680d01558294070030400c40c10303242e84200e00d2025011040f9081107008a180181d400d8145041d8000c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 75935532 1250 75934282 75934289
    0x5060603070506030c030a0b01030b04110910050c07271d0c030d120b060c070b03042006070305161220120412050a06060e0402040e490c0b070504 64
    0x20000c2c15562287c1e0200c2c054554004958105a07440c0f940b800c41d41e0f2907202d1003075500744e000d620320f8030741a6403018403400000d007624403070622205003c010155100081c140043e6020b1020003002010b2140c45c151001d070700d000165180c40d0070110540b00c9a1001404015014a003204456156520909141d00c410220310a00000b030080701c268201070425030040000d204024200601e045056841c1030b0400091f0341100125640002c00c0c4002e01194171403030069510000f09036481c2c202541c0025032144240c80740202844008034840511070b11280754a81c1894119844054a102c0300c10020184034505801c03c0c4854010031442d0b043c040002800e590b6800101c0d402440c0c03d0820000440150403200110341078810300c4039050016070702e40140070081c0300c2401c0040c4d40381450300c1040700b903a134050311018140d031040300040224002c0d26010180c000d0f01a0191984084814803c0b10032003408001080d041e102c0201240b4490f40f2103024200c0764010046110307903850307481c0121030600c50b520 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 75936782 1250 75935532 75935551
    0xf03090b06010c0f020d0320010209030a20030708010c0315080601140a090c030524030c040b0f040908030a0510030809011d0405040c05102604030302070b040506060307050603 77
    0x52000d50060a01d0f04810b400740007a00d00010003a800660030380d8a138007085000801c0e10644a03502d20041c0c00502c4440c641c040254100000c00c07010035030fa421030000280000e100d10030080c00f082d5411484a218902c0039050b00c400d951100001c6018025400d0800e00181c2b501e642e6010702100120074506944068000e4002646032070003980b00041c03201c2003580e10002c44800003801c00711510800d61220f01e035450104030b9103008a031807940170070404454110034040c04000001e0b542c0c08a8001d206440403140004c42500800200c0e03903030b0301070f44035564019142000311020321281e0f102842c0714522196052000c3c0d0344090b0412a45c001c68031000388010b000b03110300c90340e0f0341c09803910022014101d0b5034020307580001c2002800380c80c0280c41c1503401004180f0103000a0500e1208000844c24038100b400c14080701c82401016480d40d07081070443d890200011408261080e0119280c040d004150541241424100f180d224503007920380078440e1044407c0007480b414881d094a00c82c00000f13 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 75938032 1250 75936782 75936803
    0x209060d0e0102090d0302010605091006120e030c12070b1003020102030d0203041506030f05101b030b040902150d05070309020d0305031e1617010305030405100e040f0506010f0309 79
    0xd012a405409512510846950244281806900d68004400d401c9020741e0010403102e1030003061080200700542501100001c1c030b0800c1c4185604001c0304212a500244c001462402a506050450080204526a40c050310b2000409807a41401030f24070340703016550442240e00d5440c0c2d100d0807041240710090150f0001c4c00011041022507004d1075000b4000d40c803040100799100c030708500b00c440d2900100c0e02d0081c04440d50051003020841c0321307600004100e041000104456021480303000b8007491208261301c0b00d40709007183d100d40d0021001d55038040d201c2000c0825030668010260020a0f01c12180c6140c44001941705100e40075040c40a074001d07051102c41046070f00c003103a440d4401810364000000b011281d140550440c10842d00c600824000c4039030810704040002c0102007042113030303105220401c00600c042207000c001c4501301c8400b140c4005044440c00800c1c0d42e240ca0081015502615048000b120360415030480c91050300c00344e84100c40d450101405900b101c0f041d200c0504103000303a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 75939282 1250 75938032 75938047
    0x9091903080a06050603040c0806070c0209060f15042607050d0b0414070b091206040c09091505090703060e06042a050d0c030209010509010b071e14060402090703020906 74
    0x1030340500b900035031030000110345030b900d03031010407003c1e44283c0307041b0745540f006a401c12003080144030864110320945050b00e07422941d900042c10256010701207511030104d4034207207400f6030344486488248203107007100a510f9640c0e5030701c082031246000940c020081c0420440c00920b01000c52480e0135154018105241c0c0d08082c4c48903503190700000c2c01110a500c0ca000c0d6010a0281040940001d02d443c5121680d50601340c814454282003805464800d0740c00310091200055000e01e01d403054611200300001e01d140c40d81000c11503440900b803104207a61504003401010030020079500e00b524020b110500800c0741c1da0600316a03d2030211405040821104007003c281503418003158003921014031038481c41c41c1c40d100004c045501000e41128034051005003001103003094407000e40140421a1016138540c03404a02d1070040c03140d00070040c954041000d070041c4004500f42c00c05801030b0458031001d408098010429030b01c50040e10181d1285015000041540788a4022501c0035040034001d02c3c00c280b003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 75940532 1250 75939282 75939287
    0xa020a05100c142d04090203091b060c060627070503040605010608070804060c050c030f0415030501030f110a0f090504030305061f0e030106050d0b07120b0a120201140c01060509091903 81
    0x800b507441c00101c6004000c0080c8511b11400514003450082d006001c4030300d4118014000c2c680d4540c02280203031014404605e00c40004602c4990008080e91700f01c0804e0b180d01441b45007201c0b40c5164480314100030f0300380b0503040d40c440080d500c030341c0c45006c080000f6600e4841c00d541402086500800046408002500080c21034200702000b1603582000c071f0900c150b80d082e85095404c05242c10341801d001141c104010102d0b142440301901e050f060800c420350441e1902001b036450310a000e84200300321a10349502e51601000c0e40010040c2e00c82801c5415250040100501002c0d038082d40003d00b8800400d01615001071005a0b0142803402c400750090320a0f070984145a58403801e075407555a50740001041c0d218100f01104491148942210034075000b200940940c00444503140010f141014081c1c86494681885003642c04c040301204406141d440125001c84000050704034446010a003440c98285c150810b0040d1401101c40c0415991641c4410384c0d902007110500034050501c0c4904004a0f0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 75941782 1250 75940532 75940597
    0x405010e150102161502150f040807050309041d101122080307120207090603030504090b040207050d0509040b06030f0c1309060b09040609051b0a020a05100c14 70
    0x79060054440120300003001d203142c81c165901445010045441003031440e0b5040c00448202c0040c8000e9035030030f00b00702d00a8004400000c000500340d08000415005010b410815109103084c0100180104110700c00016544449003001c00d0303143c851030030341a00e220b07050300501d61400e207145040b030b003801804034480c0300c0b025030010340030003194403d40085602001440288000340c014400404018101c0d0f1009141100b0390f80500f40c21031030910280b0000b54440c04035801c0f02c02c1d810380800c558040b840010002e05c5600c0f4024441e01c01d603078034031500c1da030000d0242c001540d0440f03042001c02084070030310000340f10450701c916960601c840010500510800074110305840904514821a02d5602190403034045800940080c040890041840c5c601800341c1000341c0140340d03043c0164103258061030590001c40e00c80c1c0049940c0460240c0d04144200b00c42080315801c007049a03201540b48550000500c8008403000008241c6440a44a51034210440d42000001d01403450103000d043c05a04588 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 75943032 1250 75941782 75941821
    0x11209110f01050c19120f080106050d020f030f1501050903060a022b020301030606060311070609030302090a030602090a0b0c0d0e18010303030b0301050105040b0a0308130503031204060b0405010e 86
    0x1446261341c09407040000c012a0101441e1824242c8400d0804400d4528500b02020810540740c10204069a00000c1c04d4115944da00785035840711506600c14019002d42510411950008010000354001d00c2d410140990601c440c0b030a41e15460381c004561034895104401c2e015809a00440c50f6041141d00901032180d00000d5505030740d40c0032003090400d2041706072042040740c003c001030045c0050345c4102e00c010089810100048400850600500c0c054050042c0ca041da6500101c01030502a40450314045001440b6007241c58907440c00400075040104840e020382c94180000c1011110f20044440720071400000b0282141c50550031514046002012500004102100100515034900090181d072082d24046030340c0d68600e0600d400c4441c1640700c00c1c412800d2514501c41c82c0c440c0d00d5000c0580303802044c500d0b42c450655154005075495607020541520001403e05200c00e4034004860040e882241d09024130204d500c104000d07940300380942031404922a020510510a481144156 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 75944282 1250 75943032 75943037
    0x312051b032a0106092301080a030c02040207170301060c0302011a210307170c010b0d02060f09010507020d12140f030c07030e0406080105100b0f090f0612100302011209110f01 77
    0x4d0b643c0b542014825036003500800e142c0302c0701755000041714903005142140502010001000e441d00c040d1401030204e0320701c540c0a4041d030f078009010350501184008106111203a240300c0c6035a940d55000c0200b10703c0c9802420740041d480e2a807c0c5204809081d540c40c2100001042009004075941a64032204541c1c000d00c20b01780b0041080341d0014101903185000d5540e020000742d180c0b2401d000030360954201c410030a1040c0f82802e07900006948400a84042031401002c054940400e5001070711036105040f0040d41c0800341c00d44103001c00109110480481300755580340401808859050f1200d401101001d81282000340001244249c0180c050207205010b4a080b024012100700420200d410070741001e02c0b265121030420090988428401c80144079034558585420b00c0940403138500e008002c06030740301d00c0441201d8203075543d0703040c01d482040e520640540810704010507262032040d045e00c800c81c0460a8016545220100b40c400c4842d5550840c00a5501c2c92a006c1000034800f86070b0364442c10b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 75945532 1250 75944282 75944291
    0xe010c0606030602030612011b081008060f0108010c0903030c0318090e0d1b050c040b2205160906170a1107080403020f09090706080903040312051b032a01 68
    0x1140c03140c0901002980100d100590300c0c20141c0503c90780b182000c2c6585407aa0501c00c0d840304801181d5900840b5001c245006c1d810f54403080c41c00e0081c2d68a6500001c101c0c0b00d890180119020303041400f504941c0030358020440110710b1040cd40b5043c26070310003d004102807650340c40100e13000380050300c4c0d0b10351095108111241c4400c4150100d491300c8440d4400c5900c26610f80c1562908102284a0001c43c0b0040a200c400b699454075500d120703042801e40a0341d01c5401400098030360095400b0600e08000203520804c00341114140280001c0703410510b001c0b039800c0c81ca10407d02404581048d110255644a041501007030440303030088000e8803950030660784810184030440f4800141100303600ca0088185d4951641c0100580c12a80c040c045100700074190500c00707001030000f9540200c0c2d00c14109056140d4031a12a141035000710343c005480380e8011400d01318016172040080148102e50003010500100482801d43e81c1d0081c4080e02c0b00d01e4000040641e203865681c80d841c200c40c0390120011a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 75946782 1250 75945532 75945557
    0x606050904060e0d0203090f040209030309100f1806142206090f0902030f0103030c0501020c0303040b01080d080108120c07080a121b02090601050f090301150807081603030e01 77
    0x5142450458040d140243d036048010629502807254043c00080da20095051010300d5001031021a481d901c00c03403050b40c1c0024520004d4805006442074204000e103a0200308211203005402d840042d6007090000c0c801c042030403101074130304030007509441240d540e1000c20101c403600c4c69041e83c00017480564642d440044007a03007804641540d40a0403050b81d4612183d85000495a00c0c1c80468018200d958014030410041c03940780540a411660145071170b184020643c10309500910404c800c84c0401c1c00300104010034061100303841412580304030102c40c80311000d039030100c4480c6c1080c00386001c0ca41015584204c0325031914040d1804010840a4801d510f5650301c1d6035140c001303c55800c84005c190411501d81554100050701800e81d192004031070800000da002a68280c0c006154906201d4041003404000c9100810342d18030410140c0200511440c82c05c1c8070191041384e200381c0c1c10a114070480401c2080340450801d0104032501c1c806400d050550340c00b03403203e46841c03042c54100308429203102d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 75948032 1250 75946782 75946789
    0xa030c0c0c0906060207080105060f1918021c14010e06180f0a0c021212041a0702070305060703060e1b0f04140411040608060d081b16060e030601060804060605 70
    0x10010b000e64940095014a00a006424135019034008851645084200552510740715001c081070001110787c000c01c0300c002000d062003040d6076002000c0c602000740390f0701400d0019074000c154484860070b400001048054041c0f05039010071000b04411000e02004000c15082e04141a8002d10001d111241511150100c11705940084038082d8001c05400240614040750713100d400390080360f41c4080d00390034040c856000345a2103049500c0030745000c0307400040d062151403c00343d140b150003440700b80d9080c117051100950b01c601e18081652180549000304c0c0c0b04a00030300c076034002c40d20081c0c001010fa9540c0701ca8003001080ca0030441400140801500d0a550841c0b801403001e045600d00c00341641c0713071840a1208542c15103900300e001c40010007040c081c01b500700c842268441c03402c0b81e25000661030fa20f0800c08070302503c03400c01e040008800340d0b04048000800c880c22441d40000c4072128417555072034101d86824001007110b8141d048000144802c62241410f01c0c0c2c403a00880c40400c0d0180c0d0356021 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 75949282 1250 75948032 75948053
    0x207062a02120f011107060b060901050319090f0f05060a021e160f03090e24040f14010603020702010e03010209060403030f090e0f0601081605030c0705070e0c04050a0b0c030a030c0c 80
    0x41724a0000c0050003030108107180c815142034840c180c0c0d010342840e422900280c43c52002402420321000f044004d0726040060f504041101e0740e01850203440302e10035103080c03215440c0c119001ca85038080e13100054201d0205200390b0b40e40b5030110400d145141b40401031118160300400c2034a0a5048801100000c0ba4444000014241c03290341c8401e9540d140011480c03c0b01009000310f62140064888004410b0192404210a110032100002c100d010305c0214001402281e080801044910b00000b13002c6070158064003001d8000e0325030300600920901010b00704d210300c0b203406600c64070620052021034403c0c1c102c402260b8450505512407030319286440c2e1303440c2d0304455002200131103904214565910607034894214880301d0150b1244d4070308003c05807240c0002003407030388c8440c0003040031414003204010100003005100c510340d81c207042154841c58a9485402186c2c0500d00101d030004441c20484101c03010380401001842c00c002640c00102d014040803101d00e4100288901d200300400d16010341d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 75950532 1250 75949282 75949301
    0xa06030e0c0613080f060403120507020309120304060201150b03040f02011110020414030c0315070201020403140607030c020307120806060c030d0c110c130c020f06070207062a02120f01 81
    0x42c0a900145021209881c01c85c148005040c036810100c188000280c20a0840040006201d804078580d90707005012071950040b145120742c000e01c0d0081c5802c4a43d00031005100b03070349140e070092001d032484400d20464007006220f503003d041e034200f00080200e41030081d13060034a07205141142600c881e4469852510b600c20510582245e40010104100d000e202d035100c8502c0c205402901350503960500082c0c4421840f11401005241c200019100c03c0c403e41c1118050740c0c2c45101300043d009004002592074104a6603180807904d80030212290130300020958440359880540c910310080e0618003103585940c041c0001d9000036080c40400c00d0382e402440900f105000840c8001010911701400500403040010040c11540050441003150707100e9031000d40c2d00c0f21704e0f110081600601c10108910307002c1030344401500c0d0700030307c010311051076808a803060807920710350b80300c0c040e00c1c0f1045030700c0707d01084005040a03e0440c506440006041441300c19003a401024195a211101c3d0038003d42502c80001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 75951782 1250 75950532 75950557
    0xc01110d0b04060504061d04030509030a030e030708010203010320010309080d0203040c0b04050607020d1109010b0703030608011e0f0902060a05040e0f0601022802030a0f031704020a06030e0c06 85
    0x22003814080c01c041c40f42c0001003a0485003400f202c1d00d410345c1020380e507040d2044810060920b000190516004a08071103200c0c07070180031108072400038100100b552401140d0a8468042d203000040c00c00c1c014026031741a2500a40241c101c03040c00c2e83d20310041d41128081d036061580f200b40100105850601514030403100800c096980d10745850560001007041c0c00104010009100501164550809540c1110f1341611800c02040722424161840c1410b03080250780b00011030004215886858040c0108510a403401d00c00c40b0344507035009081c0c40700e00460094007840340c0c03078002040d121608000c1c54200f001100140d1844039401040250748006041030205000041c02c01115400039801c0707500404112400c0414245800002c0d2141460381c07a000344000030810070038a0308012000c1d441010750040032205c2d41509841e19011901c0c800c10150301041400503a081d22404031510544500c0d80240700603142070070900306078020074001c00c0480b00e91250f440180c1082c5c4849005080403100c1c1d0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 75953032 1250 75951782 75951791
    0x190806100503010b01090303090909060b0307030606050102060a05070e0607060207120509030c06030906040b060310181109040312020c011104170601120b04020402160609030801030b0106090305120c01110d 90
    0x2074145820364002401076030400c562000100b021a90208055058810204022807281d106051a81c040d00c01010810f0389800b40780c0c40003041142c0d80e030040d02124000e03001d40f00e165a400c011042124001c03900d12010601c800c1845c070345131406100400c640d03403044170010b0905001da210140c40201c14804040031910019220304649420003080c4400700b0211482c51035450300c080155107410b40030f0301c0204074400c0c1002246150703130240044014030080070002c000240c041004a00040034281b41030b00c651140054030740c05401c00190305489030341c1507195007000101503903a42009500000c5201841e550f038030481119100e0510041001380640c101a0300321091903808075041c198180e10010561480c2803102d000640166109580180c045900503203501c0301d2444894107007084200100751510b4100c1d42c9007016001071616068902601801c40c01e41c0e01d80805540d1700c180741c0805080360b4000031400b0801324001000b000395101703800011404030340400008481d0307000030444181180c2c89 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 75954282 1250 75953032 75953039
    0x19020313020a120302190c0803270405130b0709090c0e03011d06040f020303040e0103150509120d090609021f0e2d0301060b0d02070b060d0305040519080610 69
    0x2011a00c40075000c151440c001e003c5280d6400f9540c2c80780c02c105411130041141040741400416a1004010720101c0140c80c0ea0344140d01748840c00707411354038410800442c09074000b284c50401c0d00c201d40c410100344d01c0b00407000c03c1c147c07541c1d400302400820340d04c20400c1440010031684128002c501c410070440d100c0d000c0140843d8105030035100d441c02803410440e104100803410440002e00160415007088220303643c1c0e030450000c40d0a61045801c9214402c1a610000003084450b0541c02144400c400c0c0400454480c1c405040d156000720800380000201400179100390425a485100c1d01440303404005801350701c0d0350216145840c56100e185841d0303e01e1441c041c51541200040307810080445100001c9000c0c900c03900c0144520305040d5a1002003805604542d071400d40c0101d0181031411542030b01c0303010010800d03020754800402103a039901a800800c0346410f00700200d0103020b5140c0c44003803c290415050000417603118241600305a10700c180010022004e2103290b01510290280040403400c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 75955532 1250 75954282 75954289
    0x40e0106090c11190206070503040b0307091d01050102030f0c010204030c1d090703020a060c1b030602190c080403020d170c060406060611060a0507110f06040201180311091902031302 80
    0x488100f03103003500b001c180e600b49008104030000210b6411a0815102c4916080031752650050750819040031100105000c6030320b401210700d80c101e84000b811007a80c03074202e01d00c021104d8828030906025034010710004082c814900041d10030f0340410800103041607501d407035100d40740c0f149a01c501c0004801313840740c0c5105440c1c807154652050003880200740d00342c40d42e030104544c0038513441581c04000e9008541e504210411110706151003011900c42d100b503480703040220082d4002403041c1c0960310181411403078036008007400c5e0000c5d60404000d9003401e19640901222a55031001241c0b4070b42c031400f0008201c2c03a820302034801e0000c100000e0009151510f0f00c03000720755098100c5070234003c00401d000c425050000f040c0340c0c031048008002c03520351a202025100c00d400100c4152040c000d07500c0c1c8808030400015058810350003640c8080b1055a409007a40d00c04d58240030145c180150b6a045034070380d0820b100f8694110051a618140c008020108031089810030b131841740c00c2d10003007202c0d28103626 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 75956782 1250 75955532 75955547
    0x80901030b0d050d03020f04120c080d0207211b0e060315010506030a09050c120f06010b030403020d03020a12060806090d020c0607030c110405041208090102090a060806040e0106090c 80
    0x1c0090720384040b000665101c6a03903484410200f14209a000144920850a000d065400030a0351089205000c0b0107440c0911118005009a0880d4840d07400079410092000034400111240a0010150102c4100c42840050b010345c17016540c807034425056007014030b100001800102040c02e100c4000e42450001c05003410201080d1040c50450a401480142c1e03400c0b040b6a0040c802400c002210f0b1080c4c82e0003400d02c182480da091303000851150012040c02c000c56042d240c0d041c40300a85406030303210500c0c1210350205072800350041c2d001400d040301050180e401070200722801e0a00c240d80f084411012420344109420000081e04464280000c1c210108840b405040c400e0018002c43d0001d0000300d0414010f2040c098104202000060244a2003951000d0518005403040c00b251809003081c46c1d29800d014140720001e1804c83c00070312599410310035620003600003130101c002c3d6454054101d032440d20140034240d202d5655010101043c8007480f0b01d0b001040c03206400305510741c40103406003241 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 75958032 1250 75956782 75956801
    0x31312050711090105010e040506040e0316030e15090d0501020d050106030903020d0806090a0b0406090e0606010908070806010e090c03100b010e0109050d03050a020f0708060414010e07050405130c0308090103 91
    0x82d00c0f410014000d0741c2e00803111b803605220940780040c1540c2c801000401501c410000e0a00c18000042c49081026502d02d4802c0c8085c00f0f6111500c0c002861000c6c0b110700b500c564034100b141d02d401d014000040c6450300922082034010b030005810481c0d1050800206e5800ba48030501027591100c800c010180c05101c10491154281040e2000e89044130209050220003800202d40030780c2c0b800c3d420301039600c5500a402500c4400f008015020b480103086136122401c6c2c3c0e103580420038624001481200c002624816a10040c02828440e442c1070380b00385100d0303000b41914146016010401c28541c0702044044070f00c400b01080410b00342c03a03038000900307038a0403800010704124602c142400f01e070321080d4011598a5040c03900540e529041d441c1241050205040f58085002e43c480004060750001911401503004040c6001101845406a8200c030010b00550459800c4600c04110a00c3c4c141e20590344880207103d8455081c5099035005020103e9400861b0408404145c51006507858858000c11 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 75959282 1250 75958032 75958039
    0x1090602010c0801060302130b13140a0b090906010c050307051c0e0619050f040308040e01060302030402100c0c05030d081603090506041203060306050708090c0301051506031312050711 81
    0x144050750b140140f1055050051406061300080d0721134080203a41c2840380140600122551981c00105081c0e400b000749214400d40b1090700344290035207181c0300481c2012203040359901880c00e111001403003450780000700041d0502800c1020200883c2c8284014102107200b54044e0495484a5848110303886441c0014400c000b0b06801440041d00c07171604640c1100380c6010f0391404506465030864079031184420895805030b001c00c0c00402c0105000c090400d0794003e0384140f905e0fa0700c0302000c6040f03002c11500654130982100121070298010081c03410a10301642c0c841e8122a140c00200b480d00380c001c80b0040006030704004108025861003144561041c1610742800030403d2500c496a071810042c001904014281c010285454040d0348808000c540c010720500040c0340090000c1c146520480d000c02c9180134001e80c000951806100f414814a241d034108a6003800090074007485810041140102c00b414440c04008601c84080e040500c400c070703544140e03403085545048103803004010700e031500 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 75960532 1250 75959282 75959291
    0x5300c090a0b031b01050a110c061912110706020a020c061305030105060906010c12031509060503060f0610030c02120c0f0d02010606020304060f020a0633050901060c020a170703020109060201 84
    0x30704d07a0380300781110382e000f201e40717880b85e43d500f4112401400d2200030300b50300350311407000a000140c1003442e143c140c1010b5980e4030344108050000361f42070196081d0651074042100c040214800080305a03001c0c09041c80c1d544100c174001c1c28010049540c42c2d00141c3d045202c01790200c0c04100900d000d00910b07500c060150751201e00c07420400c1c0040d085d13900c4803038000d02c03a5000301c1d880307840244030b40d100280c6811070f900300b400c220796114040b80090507140140341c0030303002c1c5d02c0000b40d25554550101e4000c00d00a4598100c0d00c000013811002002605000d000714050050103040c0d051080c40500000348030340d00540719180c45a030300b6030302c1c0043e0b814400781564140201006100c0d004411f403400c60b07034a401c02c80c00c03440480000b2400c2c075140d44402000d403480c0080000c883d40c003c1d0a2900f4040b0180b140d8680140010043e00482e00f50b44904c1c0d50000600f80144005032040e100715101c00c0c405003600260546070b002d004c1040f00c0d250000b644991100c0c004100355a405180007000740001c1c002040b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 75961782 1250 75960532 75960583
    0x60406061707150305072d110606010c021302120f0604140c09040b0a090c0305070e010311220308120a0b040203130f0c15090f05300c090a0b03 63
    0x10401c010020305107090560318000245401d02602d85103282424148801543c428060051071107007001f4200b0000045100300310915080000074024040e000c140c541075205160781d420484058480690701101e10740a0061212403000c2c07001c101d026020b000104001d0b0701d4104d00f488100c03541c4401c1403000303043c00d00500440c2c001d03410450321004811380f80840d0615010b80403800801e0294400421549414441110507074181c3c0000c1c0030711a103640360114001c002c40110107403102d100800500140801581101c64891090001e10110441034400c00550f291a0525545c000c000301501226a810030041d01902034801e030a10203500320382c114114182b10312a03108007200c0c2680109003454444410040c085410f88800051410b000300200c00b0384d100d0030041c4070b0740d00b610030041401c1080001080c0c6251400d80c9600b6100d6039299014901d0984500c17814154405a01c0c11241c0110300f5505a5500c95640a40c468841c404c008280e04506605041c0b40c80c1ca0008000151480e029260 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 75963032 1250 75961782 75961799
    0x14090d09030b04060908030c1201050a0b040b0c07170601031118070c03030e01050109090c151b1703010605040e09010c020d050702031005040f0b010801020c0a081b060406061707 78
    0x1500d0b084244403099642c2c82c03410900034222440041e003109404005c020481d00d016004003030003000114401a00e981c0c03031080c080000100c4c0039100d030095050000348000388001d0040c00907611403008580109a58007880c485107094034100150301c0d005078006205006803075000390401e4070143c52813140748040102c04000300102400b10400c2003900c05000080c5032180e04140c01107010700000b00503550b514042c3c3c200502c071000d4221805100b6a50010303103041074007158044136025840d07070882c0c5080011403c3e002c05841e03008a0b0030b066100740720750040c0f92400145002c3d01654803120b64640c03c05403401f00000004004c90426810a102c4082d030301e0740801c087c68424000c2c10503d44801080c80040d0a0054540c540e1011528001c01c010a1108441d03c2e00705207030207884c1c59040c690320740c40a28284c3c4a800c000c2e00103907000c021208006080d10300100f040d04a9540c00c80e5440641026182c00c029054034140e40150300c4681c1807045400300c2208080603034004004000061070145070 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 75964282 1250 75963032 75963047
    0x301060203190314090d020c1c020906010c061112090c0a050f0103061701060303140a1403062718030a080a0b030f030f0c06070305040503090d0809030f0114090d 71
    0xb0741940a840560720b545071070080e0808030005040ca1280c5141d40b509004a681d10002c034141e9000601c514a03103282d0300d081a0280340742e02d148a00900010110307030f409102d0240005045541001004244032010a04501c00d1000101800c00c50039500d620610030031070045009401095242c00404402520707548942e280c1046507820342d0035141d60f040c00c1005a004246691010302c0e071440d10001c12140602c19401903054030f01c01d44890741c001d5814040a4a03a0254160322704c0450a0402c4e404102c01c0d8810141d0b50100d00140f10100041d0342c034901a417a10280c40d20040212051014400400403400000c40c030181d00380c00550a0440d44c0000424142c006002429a680d40718480421520244a594040020314040f80c0d9074400003a1035403a0341e8401403000195000701c00c0032802d524800d000300744c081d940120046d41000c3c0c0b0b010410509030040d000031140020204008140c0c2c2e24103000b6503003490505000000c0540800e6020140300324014206c441d076801007140c031099a5088040c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 75965532 1250 75964282 75964297
    0x6010c0b18100b040c0305060a09020d1b020a020a050909031b01020d0e03030a050105090402010c0602090a270501080304050a1e050306040b0a0c0c0b07110c0a03050a0b0c0301060203 80
    0x61030501d4a61026014a418941c210104a80507412a26040b03240540103030300060003c0e5020054021220421011600c05403450fa0748003400450070001c24020760040c04090301005000290006440c652188040d0350075142d00240c1c008010701019840d181c000d00d00208802e494a250f0383c50405112900c901c143c44020700a260261702c03813021042c003503040e40c070208240c1800f007101c0c498491500742d803a042112020700c154100400401d0604204000f0b60049906031511890140c2039604c50f000394014500c7d0796000b602114001503026060741d00726510b0040e103200d0008810001c5582026540b0580100d6241e40c0304100c00c00064561503852812200d10200100824400102101c07080801e81c1c0616858400c18040c04144004403401900072500201d0400030505541c2040d0b80f14400c643c4050b06c1d445040000404c400d00a902c4000200c0a1000356501105203100049071240b00d600251482e60040c01c1c210100820341402ca078220080a00701d40c119131406100035035900c034000703 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 75966782 1250 75965532 75965543
    0xf0702100905030702030706020f1006050f0f0f15250b07050c07030b0c040527010506090402070501020f130e0c040306020a110d0e040c05040b040b03041a090610050906010c 76
    0x41c0d00d03001e101c401d0058441199008080d54403569980c107009543c0e0700e201c0381000040c0100c5002003140f00d002d101d020111030300584081c45a003401401c00907080c0100d000036400c281880801c192550300e0110040c07940d50b8031800c09403244021401c00b016600c0b000401c82c2100448440180801da81c1c0c260107500c6052407400d583d9540150f007160b410210598070041c401503000090202101401024005550703081d9040507003011110802800188580041000742000400600071400d01070014800f201010b0700c054507100b050340d00c441c2217911600540c550008040f469119200c00185420000d00c4400a0844141401e00102c8024821444014030580d4005000a0001d00812085c5615405141a81c0300c8081d0750350302402c0110894102d51040d40b404001d000708502510a540940b6400c1c0e41131070a0a090a03031b00da4080c1c0c40a0f009442a4401c1542140c81c00506015540700d0551400500020300b41035510528010468000620401c102c0d82000030f241d80c0840503581c0c641c0c100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 75968032 1250 75966782 75966791
    0x60c0206070f020d020d110117010b030a240f090b0607050d080406060302090c0901020706050f040b0912010501030f0c080705010f0804020d12020708100216021e04180204050f070210 80
    0x30b200144c0540343c0d40d00020b410141e0100c0c07030014040803d40301da41004003a00c50000c80d90b8807040840641000340511459528140301003440355070158002040f82c0c41d43c009200c2c504804017240c0c003164030b031980905040c4160900c01d02c45403025000c2c90b0a0f1410503030700f243c20000741c0d07512140c03640d011045150421940c0c000090612a85801400c003e68001e0021080e80c1082401c80c5090b0384408580c9026100b10715000a215214004960340d0318461605c0d17505007400c0401a5519038031044000341d0009030f6101e0398182c1e0500f849010700070342c4290b8607402e100225140c80850150254032413409600100d9041085982005440c03511000303600d89180ea543e200d00c000b440726640204003500c580348080d8200c0a25800082e084c00752442001164a801c007068503003000c0e840f0380260480081c0d03c002c002c1c00107040043c4140c540c1c52060b00b00c0405000c55101040458600c815440c2088030a0f001002c10341c2480d01c99290807200e40d1030340b11658a40f01201139074410b070020000108c0b0b40c0c2d4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 75969282 1250 75968032 75968063
    0x1c0b06030f150d030c030314040308011202040609050702160f0602060a0e160b0c011823070801050c04060306050d0f12020a06020f0d0b06030403020a0318050d0606030b01060c020607 80
    0x48942c2c66408014810410740c021400c0040c020700605500b140072910305503081000d5000d0304507191260b40e050f966540c081e82040c603010f90451080c2c0c02260460f0b1202400b20301070b081401002e10941c8a50700410f1503901e030202c521410381c0182d03c03500902c2d2480e081800665400b0500c154052140c400104211207800f0310107184c00043c0c0343d0807c103260660340201d203400034000103085060181c4020321902943c0e440008001240000003007400c641019480920f4580540207120042c0c0c0314286e0703008603580d464a034203464045810f00740400000034140722071030b0503204510240c9010b031600c140021550fa00c1d1240001c14160140200c81e10000c42c1205510802500030500e034480c205540f6200600c0b503021042e0880e4031040442030404441c1d160030f0034504156842160198000c0030800c0d400e403800d8030b5103003004a0012690300c02c00d001040c40d8659402220f05684500c900150051a60030b00c51440c14040c0c2010080050429440001d81c1d01d250968903001d0f0001c98401c01c0500 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 75970532 1250 75969282 75969301
    0xe06090705091903060e0f030306100203070b07021005070813030e031002070303050105041a01020a0303050a1b0206040b06040614010311040306050c0c011107020108010312021609021c0b06030f 85
    0x351003042c990000380104048545200040c0300022079104240600004126881e03407038840300303000c1e00044150310034400030301340d8601064607a000b20007a0054901d009903030303211190600d10032101e4001507801440d022138450118414998402840c2c80c6c8511241011140c3c0280700c0c2e090b50024040040034151401c0540c0c0a201251048210940841d503541980c90b028000e45000d04c00c903441035241102c4401400c910740c1c3c1c1c1c0e64100e04140c1c060042201c040e07800390010321001c0c040c0031009640d0707911001c500a46980c8540c031102640c00901440c50585085020030500500480c01039050450411412440c03d0b900e03280d41c402404e01041011200d8425426405250300c090445400d00092010303400c0b00a0090200b0108403000784100319800d00010407910402100900140c2c501c1c0c010130210324400078007007605120384107031110078810403441d0301031f498a60081042d855000403442d000c03e24a050500c0750803031107141840a18440400200c40e800b0050424241d002d042c1e0014540e0003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 75971782 1250 75970532 75970537
    0xa0905120f06090a021201090203060106050c010e070306240e18010e0313030203070602010203150f041407050a02010605030a02060a200106030305030a0501051903030516020a030521040e06090705 86
    0x850301800c070b480c14a48005181d0b0746861610050780504d0581484402d4924123004031000d440d0003030000c000591030b100702101e8a910107450b510482d5130320100d003c40400c0621900d4011405003070040b0f5001c2408800742c03090341c80c0440002c440b40d11040b0400490180010640d8003815005410030002c078100c04443c0036040500c02d01074140000111082c111202503003a4095a00035000c85403902c1e10354805038201c1c401504e00300740581102071100f0161800c6051140702030030280c8003181600c414448400c1c0e04c1425a03030304011030f04c081910f590066092181d0030060070120001c1008041503000300340e95100f003110541c10402c040400d14820048605440d40c1e440d00c1c00000c01916543c0e0500a141d500f086c0e8240d680300d82032800004582c0390140d01c918440d40c07100f041c07400ba0361456030700b9103803503000c03600107060210310759070880240e40c9403041d0500540c0640040c01d6038032200c44a0281f1140740d01c2205a0a0409000901950400312550b541c000403d440c0c000c201d40b0b0700c40d0241c0c1c050 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 75973032 1250 75971782 75971803
    0xf07050c071a03011509060c11010306080327040b15090a0806040b04030311041d100504090803060a05030a031b02060d060b0d060501032f070501021b10020a090512 72
    0x51982241c00c0b02440b540381d008504a4030144d80721507200d58002c80031a0382e58103910840e0001080c020886011803807458102220480504000a6046d0303075101960864000d00c40b1054210540300006400164640c00a0503c00044a040001e00540000039042651511441214076800304904826440b01030510002d0a009402c6407554640f600c2c0580e11a0800c4034120b00190824900f801c00e1101c0b00b042e9000d030b41c8204240d03608031440c40ca1002000f60700806161180704041000111500c0303501c01e41c070015019031180c607502d10f449000d00c00200d200781c2c00f40d80242d209013940c10109a04c503ca400703160b4001211400c5000c12800011228000d900010341c03214a8070a0004002c9c00040041c801d030b1196181c00e0000940e10401034003102d151500b511814515004a9a041c8070704d403c0301c00850100c2c445031410b04038140c403150b08980141940c1001606541410b12202004100d503d45862210600b0743c17410303050442c000c010080d1842100e0140b0080110030b08003100a01800741c28 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 75974282 1250 75973032 75973049
    0x6020702030a0c1502151e07030b12070302030f210310080d031a2202091302070c03051b0d150e060a050709060801080d0c020d0803040606050a0902030f07050c07 71
    0x441d80ca61413a9100180c0c0d110214000d031040c1269580d0903500c9030740b0741c0c2c45540c1000c41010381d540441c0304035401c000010101d1080540c2c519496038640e0724501200644040d200081c04a1801c40c81450325008441c54501860b0b441004000c2c414400403e8000b050344030404041e0300c94480b20000e40c0707200c106411403001c0c0c0c060030312078610309a07041d40002004030141491b070151103280818002030ba16a89002ca154848a1160b5407046c45aa00140310303001c17000d8440c0c1d400c601d00754040000c0382c001d488205c441445010040080c48003c00c5065a1082d10650301c00405200d5400210901c1d94210002c16541400d281640703900250fa01002c2503030f90220a40d00c01d460220b5175000205801c6070b030384021402c143c4010030280c2c4039801d26416900b945000b0318001d00550400d4031a400d11000407039001d5204900ea1000410711409903000b9407051401107000d5041408202410390303aa000000c040d4814410401680742c160180c6401c07680504110340d0b01d42070040c502d03040440315082800d2 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 75975532 1250 75974282 75974303
    0x105041d04110d150b030a02030a0503040608060603090709051308130e07020c030303011703070c0303081005010516020d061506080610020102031b210c07030201140105030a06020702030a 82
    0xc0d50481a601c91880b950b4542003101c0320400700708030342402a201134042c01100b120f1861100f1544d00104255100808031416510315a00081c600381440314119000d8001207410000c294000076501d4124008460141c218075115402e00e90394a5648156100c4644031030105012015052150a032180c018000f11b81c0d80685415203040d49070b491043c5070b02c400100001402c070a102066030004444014003541c5940d02e46800c4c08440e00c8109150510f40c007041058400003955002d004009601c2603c54101c1490030300074429000381c0307a9001d80e041c40707820000c8400610400100200d0903a0448101c94140301908100d0001c1c0b141044030f007141824005c020513101d80024201d84160007c682d51366000d40c3c140c02c101e085c2e02050f590b00091003054040b20740f5042890010b0b001203c94444002c1c02c082c2980714001c0d0466003601c944044800019030042456428090780c000d0301091100c01007603525140c04a030340d60404040240030140d010a401d01190740502260724000d4010140c0307071 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 75976782 1250 75975532 75975569
    0xc121109150306130e0106051f080714040b0c2107020301110405030616030f0603061b0c050d031503060218090109060302060a03020d090212030904111215010504 71
    0x91644250100ea2080c00804840c03400e01040100700ea100b07041c041e001c4803810a10350080d0001d030a00140c52140d95484a00118042d121000c004d207503040c0403610f540d40c1088820300605542c402411180400803048400ba44405815045908440c551034400d03640f0b411500701c49080c902c01a0143c3e04007500b404520b010113040c4009862418001c40c002c00141c81900301021311403285104807505904040009103002a150001c45c144100504000c20201c01040200c1d0484580b134004072400344c2d4031444c0408000002d1014403030704042d41408141e444054845643d07502c0c42c00001ea040644950000c28040d030340741459001950300100564581e0700000491f50031203110802d41d40101014000043d2540903402241c0490350050402c0d4940f40920800f24060350041c0d0304030041d00e403201440001600c0741322084c0c11451000000e1602d41742002e08000a40740b802c41d002040361010b102c400c2114103201015a00481201c0c41407914807400401640ca9002d16484010b0300554010081d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 75978032 1250 75976782 75976811
    0x405010e06010605041508040203070509090a1a0406050a1a0411130b1e040f0504050c04080a03080103020f060a0e2e0309031e0203031f120f0218190c12 67
    0x20406d5035070160000781e082000500440f0550300840780a94540c1c01901c04020a0070b100c034880c5e42105189064a1841e0f10035164015524000310302610030384071000c200700a0212910440b504513500280900c01e580708030888000d0620f14401881c41540e9603641042107000e2a4102e0340f50940f640c1c0300300f010f030ba46e0310f402080503000f0443c06e81644c3c2254104c3c0340b01c2000c4008840a81d411450080465802c220511000b40002000c4c040c116808101c0402c801c3c80800200e01c00d2803099a82480c1581035106000c20516610043e602840007842941d00880e006444000031210070303503907100640e03450032400d54000010795185a1a0304a855010f40080c0d058001159090180d125407003140c025912104d00010058041c400682061020503034091640c914990240c00c8141542e0303c040d11a4001d21460068203800c070b032885229010f510450400c090381e0640c44011043c0401903142c50401c00041c0840203078a03c001e6556800c4002c5079901542c451450100855801c024a4545641c41c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 75979282 1250 75978032 75978037
    0x9190803040b0105010207050a030303020c210a030b01030e070311040b120d08061e01030f060b0301150305180303010b0705030c1902040e2803090306020706021201060201020a020d05030405010e06010605 89
    0x5851000e40d50300013013241d5000080d05811128050200c1d0788036851904d040380290003095448443c0d0244085070f65040d41c1842241aa40c900c01d074039160340e04003646010381141c00c407040071418142001030440c662103001c50404101c0380c101c46202200d2482200140051000b490340d40d500072000299203690502c0000c440c010071025841e00d160540740c000070060802c82061010803a00e03160301c4d54400e154400d40100601c114400d9011401c640c941100da001380c1c0090b044842070844e4070540161036a8140a465040001c0c80c1c1c21102d201602070b0220389a00c8140921b40003c1d40000d01d14003046400c00442d16840500000d492a2104c0c4e11600218555400c100b81d224500700178043c208140c02007250121340c1c4d081300c40c1d4290720000c00550501c10032640b20503400c0c058600400400b0501c540000e1680358030824005986840e45441414181d0041c1c0000c011603105005601010f41c0009184000407200d0515545940d61490594050718080900803d14010720340002100c6400201 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 75980532 1250 75979282 75979291
    0xf04050102070915031403130803091318020103020a090807151205090a030f09090f02130806090c0613120501050402041a0303030c070c0e0106020d02060109020307050304020909190803 81
    0xa4488550350f0701000c0080e18030406601802d80740202d000c2000034004a144a0105c02c10425641020900c180b015440400c5038004041c03034000050318180b0780b07070100700640c4c0011580002c01285401c400b4004c1c2c910611000281416400100c1c000d4041c01101001d00034405101100c103c6920b40d1074091140b03c40e03100c20800310300609080500700c1c0c0c16005039803017803a40030001c080e030034210380702201d03a8084041128180404ca882c0400d1240140c015220220310f400d2015030794090391110400300d088503a00c0300100e0341080c0d090000310040800c45800c3c0e40ba0071580c040c0c407099240340591799001158401444e150081904608200064003c01d10440c022101040b0302a200c42245031034180400d0000c2d895001040040d01024000001d88480d40c09100700034210f0345c46441001c1c041c203003a041341000d684981c0d880c122580e1704200460240420301000d41c150300b4116000760a0f400b01510007403080c00e1000005441543c00c002c4402845a00c0f440105017a034107003030100a551041e507 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 75981782 1250 75980532 75980537
    0x102070308070f0b130818010e030102040303080f1f09050702031306030f1104050d03120f0e06090105100b0d0b010c061d0610030305071412040b0309010e010c02071401050d020f040501 81
    0x4d0321100080217043c9007150040c00c4980340000304100c001080811002c40d6042c00200d451211064900344080c0c0055842500c45a24508103070842c500c10600060100707880034079490480c07144510709803960007260151800030500b034503080d00c1a4111b0080c0340b00341d0450b0200103800242c0b030364550001082200035910811408105807502c03800ca2040e0300882e90400e82e04070495000a203c0c1840c80a00d42405600180320101459280155882d00e01c4c8440c107030740000c2c20301c00c201c1004c1c4502a0000d070125646841c0b5480c04112044501660710700b000310700e61701d4070105a264040c81007951616030203142000b90700b040c0d860b0391811440e000e044040c0c41c0f103000c000a04168850050070103498154903424142441c960f1044030a28124000103054040c200d500c07a005d0a040c0c0103000a0300009844644030303d05040f03121b0844c2c641c2401380007180c0c1444100720145070007003004001d4401ca0300c2c20002401b40744005903400e101c1d81c011003140610000314190001090700103041540d4099 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 75983032 1250 75981782 75981803
    0x4031e021b012001090507060f080601201e01020301080d030e150903071401050f0708060904020603100f0306090203010b01020706091e030203030a08042a03110102070308070f 77
    0x111040360756420401e1458512420401552030540c000d06107400303040c04003120304412080c640d04460075180d040e5070840d1182d00500060041e56004030300401c10308002d107499101da1404000007494107025007040a12005a02c0620091780790500c108655403440902003260f0301e009100c050300075070003445000c0c0d0311300400c0804e60506129008144200035058010076000000401125007450090400035052000b00304200000d541c042c170036598194039000020b80d915140454000d8000000c00d440100400c89003040503170303a1012022a0016016141d0b55101c3d071740d0140d4244c00703c00603003004010410360303c00001006413507000040003520070344c000d0084204000c01640e65030247e015020226042807403d1001030100100100202100351250300303e140d50390082415a40056400c034002220601004107001c1081020a070075000d10302c444100400030b0351107890980e0035010051802110410a6070701d688204013000c080c5800c03008403690740700d030f51400c3e080000664004603891082c8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 75984282 1250 75983032 75983087
    0x10801020c0606150c060103030c020906040b0303070615090e061006030c02030d02090411031e0c0405060f090a151205130809040c090306020f0a0e040504030e010c0c0306050403 78
    0x1030095503140301035100100100d4541004100780031030001070180c20b0380301c1030003200341c1a4010850103000314025102d00030302c2d6015005100300c04100034109409070317040518080d056100001120381a581042c0f00080c44800522f00c5046607030968402261a8104003001c6051134000c50300301e014800703074005016056510f079000e40c00d031100a14100d0140c0c2007270040c6074950a0ba5001080c01039401000082d504c001190b41c1c102d1504107580b10003030310f11400300c80060b416548402c0c6403c000d0940c1140c1c00c1600e81800581c0ca4821101a0342c1519800308000180f0303102c8802a40150058500c0e060b00e00c80307004001000880503c6c801e0360594101000f1543d0801d00e00101c2c800715420180d1113250016074818000549411020360040000025002000c81d0440c80500b1a21441904d1669100c142e100010800301c50142d09912444c500000e20000035044100c02040640a00341070b4800c1c9071609140b01d0021a41e800600703800c2c03c1c1001c01041580c840001003009040402c1030010500 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 75985532 1250 75984282 75984299
    0x120d0206150a0501050309160b040305160b04060302071103060a0c0206010e0f01051012050702030d0f0b0f0909030f07060b01030c170a02090a0306150806070c0b04060b270f01 77
    0x103080071a0703003080220400744459441a80191b50007146907003141d0301004044e043d00070760841540006010035011902f8000c020044c801440001c0014102800c5282840c0c07960750644524440c2005241c4d0000f0214104803103104061041080101036860501c1c0c40300c1c001d006000c1543e1490014001c400010803811655139800740100607070326030113019a003840b007400841c0201c7c00c1d030b01003841020481c02200740d4060282c580310f070b20680d01450b101c08a0754000029910508100f0420074248840700e00c0685030f0100b4032601810440e807451080e1103f0356134a08511882c1c81c1442c00d080000707100c0051000030341040d00d11034003e0b6010404d0741c030049400c4808200042d01500c50320007020106004000e10340182c21101030041c50009602e50340d030f880b401115094041c03d06051242e2070108129902405500e074441c00d541007030288041590307036024a1101c020401000e05590ba10070000710b40356200c13540b103001c1c0c1c1744003603218400107680500706404e001c4614407840081d40c1e001051848 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 75986782 1250 75985532 75985561
    0x40e0604120305070509100f03150b09040f0905070b0310090e03031306060510080109050912040e091906050603070503030c03090120011b0e150403150605120d0206 72
    0x41e001140d165040d110180220060301c8003624490401109101c840307856920b6000001e01c1e00956200c0c0c030318584208101401b80c42030306191004106007a88200b05188c3c0c800112aa1100100c3d0f000515000d54800c07200100040c0e9000b9009110300040070888940c6040214001c1d0b01d40504880c145a6800400003524159a0001c016402c00d10109071075442a10401c05500c0c4078140204800b51560301103000c50f044501c41c2000208003100400c02041d492180c0b0750410f50003000f4040f0300076100c400440740d02c140c0c8a6004107001000000c0c80c1c40d06c1c244100e915941165010810004c003e0070440c01412003514136511901520170700103002c0c50004200e640502c5924040d504190695005541d40c7c00d1540b1210a45c0e41d1035803c02c2c1ca250000c0c4104100f2844a00c42d0712003001c0d03c200c00815140d01c0346203041c02010218100003031208034209541c02c5a40c04500c400e00b65801c7d802da41701803e00e03a401a600110300a00c1945108000314150000b0301c040d40c01c0f80c55565883c8440780206 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 75988032 1250 75986782 75986791
    0x40206040605090406030803270a050a03051b0105040f0b07020a1110090305100e0714060d0b040f1406011404050d030c020d0c060e091311041d031305040e06 69
    0x904104800c028540c0202c02030407034160020400640280c0d2619041240e900448200248080007404803800000c4044081450405207004042c1c0d1121aaa90f607a19041850054240b0101050f42c4500a19650003055003014036402030116007860702c0c1c9202c0400307014504903160700400700010582407001646030803481e080f0741c0e030040f802c1001080c030120303007003c9e445441009604c40000c00411020400000b50050003000003404d8641d8414443c01c04c0c07007139084042e6003011010180803d59070407050764001310481b40000307800402500020020002c9403001a00d85040864481c0b041072140030403480303501d0a886181d140b520080c4d03200e899110b1800b034164020340f101003d0340420300c100701d01c1c602c0620181052250280c03944403480030241c154803032030005044034410203050520b60303070581e00f0242201100e601c11030b01ba0303502043d080300c08040034015651000c0300c5008031010101320804016000580e0707652501445100343d046518001c441c05103081082d071880b0040000b941c10f12a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 75989282 1250 75988032 75988039
    0x16030309090c03021201090e070b030f0603010606050703080406020a110a0b04051b01140c0c0a03050f0106050907080424090c0e01080a02060d05070c120c03020c0405160c0206120123090402 83
    0x7160701f002070201c000c000712076515071a40308a000c00701e040704021000310b0280e40002e49210344c1c4d03e468130401d1709441d296008801040424000e6a000a0300040099001640041e0250300c501160300f086845103038a125441c0c0170701c242d01c0180e0501090110107405140104103076080f0f4030040c05100c003030043c0c010115000403959604146407540044c0540305060003201541c940389005000651081d80fa07030402c0e52a900b0a08182034004c80920884004001c19108074280f0b03d8014000342c5070079402480501038000710044001030707100c04120301c030041d0080101040104c440d030906a01c0c040d014080c0401407010f240011419210020b480322201764010025460440942c5005000d8074000c3c02c50f009020511140d2000030f6480c2443c4207507400c041c2e8030b614090f412811f000345000045440076000324078100510460484200346111140c0d42420101039564980c80800c065109610b00712621a4441c000403d2500d0303917000352818520703191400c3c5200888241040a0584281d900946c03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 75990532 1250 75989282 75989317
    0x1205060a060f0315020c030f04140306070e060c101109040b060304241104090b0415140f011106070309030f0212090904020d0209100611060103110105030916030309090c0302 76
    0x80e20300e41c42c2200036003911002509000c5072400321b07455508007500c02a8104400324040c007280b815003410145000c0218001d10450030030410281c1045107602810380958000100800220404c00503158203201c030305410842c1c00410803500710380d60404481c1511803418885024150b01d050400d59001e03980100e040d24101954129080c0b03039080881c480c000700c903191458012a49510300162004050010000c02c40e07072105010403086030b14038500030710b90504a8009105d1030090307100c00c0c0040d9000b40c034000003111400005969070b0310980400d05203885268104945c0540c581c00a541e090322039202c03c1c010007000282a0388400c01c0c00b429407990981441952240c0c50209403d40d0406e00240c1071049103001c40c0c0100c0d4080d40c040b43c1150400c02c3c030a0081001682c0482e0000d00207000d800905005d50440d81c880b0145502030302d9081c10840c01101080f01c0c036074248021805100c02100486070242e1b6490302902c1400035120b688543c51521803104c0d11700d030280c001c4072100c4042c1c1140c402d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 75991782 1250 75990532 75990539
    0x6080f0606040e0a0b040b190c020d050d0204030213090308060105191b0609050d020d0c020102070506070804050d050c030c0a050f01110319030b0a08010207080f031506041205060a060f 81
    0x200070052030402400a20560f0000c04c0460b081a059074055401410031346490324181101020791035030380420300c0507070380342011140e20a40c0c0070440710300e0801c0f60b1902c10350303400d4138a103400040d000310b40010b944400305680110580840341d0100b4841e074400d445e0540f01e039550400550742d90184400e001e1503a40300062140200303224800c200c4c0202c022641c140e04140880c1c807010100d401880040300ca0360301001c001c25040b5010003001c0d80540d89490407414502c40e6500003500c544591244c20300404001c81d603601040b03401d0050b10050180500541c0c5281590300340700e955a256241030364005e009070000750110b070a2021280080d100080c1283d41c00c4d03d0010700440300c00380140640703180c900040c0103036a010088034001480d205803035940031075005000801c000c848034030f5038841c64842c1e00c1000f0f180300081c101c400351041c184c2c00f14440c6403030b035454001c4d540b5481c2054100796030040000902240482c0d04030348980300d40b8080c1084034240e40d41d01102d001102d485009981b004681c0c0345040 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 75993032 1250 75991782 75991789
    0xb0d02090307091a12060615031512150f061503040203011b1106060901060225050301020304030f030b0a060918020c0105090d020609150a020f190503090106080f0606 73
    0x426003500c0160484021030754801c00c1c0c0c030860707101c0c00001306260801075085155241002000c84e24035010400f40c13041d800c0c1040050021000900c1c48100f00e1004070001e40c090241c0a00c1a0308103001034040c19a8500074030500d500d40e51004000b4081e928040081015158450005c1d80320711006051046241001d904030390f00f9030030040040b6450f649486606240b08002c2c0440d480c484040c3c0c488104105022050a080440081413030380140b2203400100500d40c1d000586580c01080c0c484203031600050707101a02c50124050304800c1e0550700000c144020140c2c4407848c240c002c0c4080e9001c100e107007495010010102c0b1648520000908400d20502900410f10000c003100714071510700626081580510509640d4121082180b642000310100341c019018042c00340d0041c4144090a55001d900ca18940546800341188502c1c0b41e020030281050600c000886030380d40e10398800c49000b0311100c0e000910691080310041420350030490001440080080c1512045143c00d01a208998070031060 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 75994282 1250 75993032 75993037
    0x30a0201080411120d090801150e0705040308030130020112050c0408010e060103020405070203041208030406020c150103121b0602070c030215180a0503030702090a0e1b0a0b040b0d02 80
    0x584806540740003814450795403c1079015904e01c01c5001d04a60b141c16100900014101d520641459041c4130604081a0307106403d841504d8840315844210340b1812811541030103140c1008204803400000850b055002040d160040a00b0801111010400c0e4455154420460100901080180f008100095200e400444d80404050615403c1c00c0d50f50001310f095903203024007190160001001801035080600490f0303130001c001d00055142a14091030154000794849015043e918044041070404c0740540403240354030400d000315203039040003030404280365900388411610291880f08036604c0c140985460106070303441d001091801c04480e01c486019502c10b0508031100c00c1000720210042e0f071900c0150740442d0800e0300590726000322124035050484107c0000d4811241e9903c10000c81d5000800c48400d183c1c155041c5402c0d84903002c0d458082c2c410450b0949480c044c2840c3c000400c014190465082c0e041142c031285c546640e01840505441140a031130300c241403c0002540d000d049400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 75995532 1250 75994282 75994291
    0x1005061f110f100207060b01031509090503070c090b10090602070b070203010209190905060a03020607030f02011407021510050102061b0903070b0706140919020406081c0807020c030a020108 83
    0x5580010b1640c900c52420110030143c160402076000c1808400d004252083e40001007007800c2c00c02c03001c880d108401c0d0406406110f0340c600c864880c000d0f1700801c50144103a500c0320b5130104010300300036160141c410140881c401098003440c0c55400b60802c040c0704555140480e4013607005080030034109881e0300d403580e000c42020382c0c1540d006c014008083c0c03948003883c00300c00283d00140b22654202141e030001e844010303042c80d204489042e42070000d80d4400088070145a81802c045404087c900001d9015280440115011016100420010a170003041ca010800914213420465507039003112400d2907410b501031180140d00490014444125000d040710854400d440124201071788140001d1070018103800a6014000104501c006c005040c003d120701c10007080021800c924140100e203946404c4d10b00303500c840141400307042040d512035034006005045a2011b69110a5000090520000046442000092220b000103100e0b6102140c008800e00d0000d02500c0080d29980046440c040d0242 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 75996782 1250 75995532 75995567
    0x90212090f370203030a090e0106030614040c030905010c030f0c020303090a080702060705061303030f05160320040e06030c01020d02100218030a0312110a0e0405040f02060c1005061f 80
    0x540c88056502040a0b00c11b1040b15170b68090b85d5810000c03d1802948107901c50300c20b00d414000b0a10ac00740c0e4480d4010b1520070155000101000c84882c22400740261000c003034103a5280c40c0f1010160303945034100100450b4450414080c680742e038401203035a0703c1f0450342c13008640c00104a0400044030310005000c100c2c0020160741c14079625445690a1190540d200940032013503c59040c101031300350080d450712640c0c0d1081004240f078080072002014500b07482036010160384003606040e132a4021100343c10003928410032511580c5034800b0034080b11095801038440c2c07140c520b00e500307290302c0020550030706070744e5902502c8040015510705001e5003058101c103408003010301030002ca0ba10108a901040d5000f691095044000c102048040f5886ca0314030011200c001c00c03525040c1034011b28103001082007950005030690302c0e41810b020328406124000d50003c800a00300d401c5550002e400300110790f40003810015610780c5e00c100140780c0900ca000c6003501e0b1750100c3c040074180c001d285000800c40303280c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 75998032 1250 75996782 75996883
    0x72d051902030c13051012110906150c0c1503060303120c12090307031d030d0c0c03050102030f0901061413020a0908061603050105041104031b090212090f 68
    0x500013551150000d401440030540d90340c100701644030403032801c0b001016506a8544c0c90215a101c810160b1020020726000b89140d4000c50625201c1c0420341aa00800140503130315495014000703600c800c5d81c400c005120300065602034229292980440e80281c0008004624100c4058030050608070000c1100c1900e1b04140170100d020200b90049034801c0307803840041d40e505c140d00d10f03000d8440e0101c654410b070341c2c0325511344c58051600c3c0001c0032030b200000360a001d03624000078585104480e50a4100030b0141d4000f10a000141d02040000703401180c02c1d0000b0310070240c45200798a08600545545a840103140c40940c1a580c4203600402410030540b9048c0c024580303951490b460300b9001e4403c054582c2100b00060740c0268103200c1d5038050282160184040b290003500c0708190b00450101510a00344034420380320203200d4000681c0104038100d810341d2600071500c1415501c030000c50755000340340503071003079010b690380c0118440c440715105201c40310240c5100d441a001505041c40c4440003003500 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 75999282 1250 75998032 75998053
    0x4060c02090a02070807080714070324110c0304031202010213030204052a090f09060303030105011103040e1302010801080312040b06060d0e010905150108032b02072d05190203 77
    0x15500140a601c0c060011f81e5500c6140780703000c4290083da098a6095900400c0f0140005111415010381c03020700d10918500c900201c40c407140040182600824144100103084182902c0110141040381d01400070151140d481c244c060f4241c1c03140c40158529101094010b00c01450103900854201040c070800c0d041000701182c0060b4102035806103002c051030041990122880c19044001800c401561031115505004010940d40d000600659062021080b040a00404100280ca004000340c0600c001c0c2070402038200c409036049081c0036400902c001d4000b05a030a4004100c850f50092499020411398850f01e90070007455000d0111507101d2402c111491155200e4003ca190440b031020000400724800d103040d600c0d0a0b8408400c442074a40d5100400174005c3c04020b80e148055401101c450302581e80310712010038060003818094152011480e0010b11408201e003e50941441c000065016031f01055a030700342880c64402016503200140c08206c002a0030000d60072548054200c4403403500 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 76000532 1250 75999282 75999293
    0xb0c13051818010204081b010c1e03020601090506060703030b0307050301020d020903150c03070507030905060c0d11060c0901050706090204060b030420131e05090c010206060604060c02090a0207 85
    0x2901c19654644007244103001d08660035400882c0500c030700200845c81c1a00d400211529181c1c101c000042c0c03c1040350a12100f64015102c6a291547c8003904643c0c21300d030085104812682042e05400620030540041035400c0b840c13080901494008001d6410200c803903400b1009800854280d9425006640c00010070b40c6090000d00082002e210026031212208018075160440c00c0030101c820a4110041c8144500a07808483d0013032050b19080307546401c0742c241664455040e601c0207401840020794400540408924094000b2140e07503000d0020044090b20f0381d84070010340d0101ea90304030410000042d50f02520040c58140e218100100c0c1c0018607400003000c4462640c000c1740515800410813003000000715200900c3c2c60034000b40c45100d2903242c0420716035045280c92410035655604152150303500101100075030594001c060045207000c8605075268140624a00d015200c7c030710206585184c10000c0e2001d50320030f89d50700c2141c2100c40d02008020343c0017408908299908100c4000801d4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 76001782 1250 76000532 76000549
    0x207060c0b101e0519030b070503040606050d150c0e060f07260702010210020301300203010c020d030c0504030503030f1906030f1a090c0603070e03011a09010501020a0b0c1305 77
    0xf0b6a0030754482414604414410740821080c403003600709184507020320000f100980720715046452440c02d9622a82c2c4c52419034000c0105820007544035520644017820003102d446940003200607050301388003017101e400d41540d0300c180c0304c1100c0d070f844070090282c0000c070521900038002460084010400f4209251b40107812004a401410044c03c00001d1200540d41c0400c00400d1100c1014000c40c955890021181980c120415030b0480101e018402d080b040d05c2c10700310480717080360010000c01c80c2001250000c0d66070f40c0c1416022011905110310112981d01450a44040b01e40080186140d6520f401c0c0f100c002e803034001c01181c40e05c0403000540780205801c2c80f42c03e014611031100300080340001e05202d44140c007184800ca01d00c145400400801c0040410320001d54034007130701e07455141d484014007034030b003114054941d54040d840c00003002d010004001a10703200c0007064a01c091941d8840004a86400e0b50070030141c40030006d40081201c100b82c0d58004c1100e489140c906000d0141c50703100052a40303 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 76003032 1250 76001782 76001819
    0x50306030115030c1a0c0604020d1109190510030201140d180f03090b031e04020109051804020f03010c1b0203030f0301080c01030f20030a0905120403120207060c0b10 73
    0x101013034041400011400d401d030340303014900811801c1c03c0080c401b0301d40d652510b004000038001d24402d204001004040c0e050480e081c00002c00101c018544600c00d82001e14401140c01d07605820540842c0360b04191120300e80603a501a5641900c10a1440e10349d00940c0c0030b031110b646442e81c2e03040c00c0c0041001d804448045640702d4443d00414a0741402d000708099250380024031000d8081041c031081c01e07180220440b005240c03500c0d50941d60f80e6030005031031464540e84025086580a2140e40c4103006501002c0d1060b40301301c07100c411020b011800c1c5400c8541168001d004150200b210780d000140b603611015400b440101164070b00400031200c09400d41082c3c8c040e194960041e4110b00c90340d0b8042c010750424030001c504c200548607040b0020b1010203000500e00e800c0b01000000300d5103102040e0001c6441039042030403103555401294040515500c58441500e0441001c108540c01031b2002c0b40290465003180d4910b00075401c15221034801c400050000155200c60150005001e12032102c4003000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 76004282 1250 76003032 76003043
    0x506120307080a0806090609041202010f050a061a070201080f0406020c031209060708040206041404020d15050a0603060803030a1107050615101e030905030d02161502091005030603011503 82
    0x111416890302130003046000e07040d01d03c2601b081c4108640c0740c4425510f9503100c2e23004410707081c40c0f0a60300820b900402c803c0315400521800c0900f040031b41540d0340c2049080704e000c00d1000c1c002d20403c0388649042e000e51040240015030725004541140800d9524980213030203200700614205001d803000b480c6034459041c001d035001e04035040080401060000c0e6900400354104441c0b145440c0d40010386030320680c0100d098107425040d0b50b6419403115410748200c4141c1110822082d071081a5040d40140c2e03d20500d44648501d0401194130381c440c3c0121001c03a283c1c0d10007141035403110081c80c00540994040d00040403820f100e19404201c0400c5058060310101c00080603000b070440030700c0114843c180501084c014000a080001031045620112000451070000366042c101e217426421807180b05a4040710a001148109000f402648480c0d80c3d10f102d40d030b45121181107080480f05a000d000e2801d40c2c4600074800c0480800c0c014030044d036104400074000aa9400110306410701075810390404e031030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 76005532 1250 76004282 76004287
    0xf06090a0902270306060d0b0a091a04061118060a0e090a0501050a060c0f0210020f030307050a0305100b12150a0803030105040b010302041a070f080a0c020102010f0507050d050612030708 82
    0x5400c07004605650034254160040c05c071a24200020a01c540c0303201e03e000b42902c48000001e1003a014a61001c01007581c0030310f080d50b5800351292149012041910f00b03880301d81c80c1220b02d1607015040c1c403c80f10800c80703100c441c485020000c400c014654101e01c034414184034090701072691036600e2200c0f492164080440c001100e50400d001e10209042680200091241c41076903080481c01072040803541c258111410180c80703500310700072810000c0f60940c1e0500c0b0310020040c0a48150454007a0405c2c40c01070f50100036507a100b4880c2601c03400039200e0f001400008201300390921414100b01c40d80000c05180d203211200c44500483c1e40c00c00306034000c05943d00301000500c2113141c180140d802100d001d00c1c00f98201810846002841101848200b103400c400140100401101e4a40030b50701c55042120b0700c3d12844c0081026100c6442c81070224019403910740b06c6110380c0c4107885458015505642d03000e00301b001c4000c40e08004c00c0301a18041d84050304403203a44241c1401c000074000144240105038 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 76006782 1250 76005532 76005577
    0x601080f0a14010612110301260705030a030203031e01030f111504080f1603080a0f0228030210051b07020102070512070e090303010503030d02090f04060303081f050f06090a0902 78
    0xc1c1110070b000e080380c1d1b141c80300300010800c948030503031403400c1c0300c00b0b83c40303c070010b46001541d043c0f80c00002d5024903054003074100c025042c541c000c00958401c04c04d070180e00340d504c03041c0c40d10200264424040100721000c0280c009000c0b8081900301c400711500506440421240036460203459002035100541d02e0740720404211082e60103003c000d88000f51050801011415551000264082c106110081001085040104510030003004407880c41e00d07481d0203a80c0c5020000001600380c00d400690240c80b40407426200c100c030601c03915210300c40b00002100101c500d9002e404c2607600008090b411442608404161a070300d00c0740701000a80f041d0000d200c81440d1100c80540c04c90f00404800c0150414001044692004011524040880d0340b00503907c03840d180001d610a2408201300713401601e410f1010003010381001005000b4040090307220750080c425003500b081c1d01c0c903600078035401a04480080d442400c00402404507090b0041c44086000d455040c0042203800011804403800d012030a00e6 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 76008032 1250 76006782 76006817
    0xf031a121b01110a030305100b0c0d080705030603070501030b03030f0c0d020601050105070c0501120603060515040e0703210215070207060e013b0604030f050609060601080f0a140106 80
    0x141ca40400a003009000b02036041c81c0d160300d031513611802401307042c0c684001800e07001c0e68600c2440509401007440e900d03140b81c1007103e40c1c1e85a103014001c2c0446d9803240460a03042c0600c0130b891042c45c00a000b0030b00e441c10580114041c0211050880d0144410302c480e46405d414400a052001d00d000010103902c121498002d1401c1ea0683c8890b0604c041000660080340d01c0308240026140b0a0070000c844008014041006010341e6202601903481c02041c0070b07400007900c0385021075520484051150211083c209500d40006200c018018900040031900043d080307080c02400074000d006640e680300c105203043c065035030121000b100580007000c3c240304407034128503802e024100a2800010030a148590007800380c080c542d801c90001250b404030014044003007039103c1280809888192110b1b130700e2428a40007a800442144d0074028030300004d00e000d60002d00c1501c60b850507074807000b03140c803510101c085080015220304900390321001217060a4a0000303640b0300130300c4555a010006009100803 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 76009282 1250 76008032 76008073
    0x612060912140f0903100e0c010807110a03080903130e04050607090e0109050414100b01140c07030b0a061a0304020108070e0a1a1303030302070c0801050103030f031a12 74
    0x9001e010500001020610b241da055400c5031045212003940c2e81200f10029180c0f80080c1148502e060510402c46102d60340811560120a402c0e00c43d600c26071256142504c0c06034200303806407165844032072401c022078412020940c00800788019a8070300501651444050111500080f00403405a028841080310411045c2d030300c500309140410380c01c0c0c201300c014942860103200e4a00c0290b04e0300086001d03c100307000c803020041d0070740080710341800c02604c1c41c40282100c061107a002c1881da07910608000203e10880d05940301c4680a880f074103082d81d8554071805000b505d05824a80d0b20600884d184030303601100c020001c401004d0345e803a450580b000420b403030300007440102044030440490140b911081c6000c0c003503c2c89180ca00340c4a94641d00000040e01a9641c6100e410032000000010306030540c0c000c145a40c000c0b00d0034051241c80701012404e031002807100400260310000390724400340c07190b03220380411141307102400d100c0f5804c5800101c002c211241c1e04012504000d561a101da002c6030302c0e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 76010532 1250 76009282 76009313
    0xb04060b01090b03042003101a0f0a0815251e050c0601050906041103010906090e1b0609130e060f060a0e0f09030c0601030602040905070e0f0409050106120609 70
    0x803030601c4e40c5002d903a0f00c0d40801382a04424104e5412034443c40d103a640a001d030010050b0f41540030411001810403c8012040f00401235004000c0213403078954a091000f4480305880c0c180c0c0c01061050032040e1207404070440200540207500c1c0314180318903402d000304055210700030170344d880c501c5010101805a80c500200c0351600188013003000540400c55021803503504481e403c542030100c03980c800e0f021902278060954429040c172400030002c00e0a5416030300030f0307040d540f14540421004112031925a502c0c0b1595104404007811803114903224a8408c2c000c0c411004040c191035040414440000e050342c04031800000140c000c002001800b20f04c80c02055480301c022a1403c01d91441e0003000d215142d8042c0501489000d114002140c4140401c1200c45d01654001222441c1d80d590401c00001d40003030103400700c15814100031a0019104900c80036154800804c520b0511f0110000c000c002e00c80344808460701d5483d03410000b42000c005440c036003c24003e0320007144030783c40c52270700c090b03020002c40 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 76011782 1250 76010532 76010549
    0x3020301030203060a0911041508160b030a0203040303060905010b030411031b04111207020d090f0509012102100306030c0911070f05011e0911010206220602070b04060b0109 76
    0x1040943e40016039a60030101c2c1d0355000401c010507061a19880d0200c00d00d2580190520040d502c611009015001c12141c082c0150340b070401e40c0450040040860348100a001c00c2e041c40426041b00283e4019500b0605c41d007800200a5070f90860b8005813582640aa1420000441008244a0140c11088a1a1048001d0b020030303145503204040036050030b0000b81c00369540c1d100e01031406c014841101e01400c008052030031580741004000350b664190040c03030000035400e03040c0062610001000c00040d02c000902e00004d6a0030048405030402d2940c4d070f03100c040b062101041c00503854001c450420032410b40c2e03002c1a11070550600107049842c039404000708500e000031141030b01ca00441591074180e8000b004141004440c100f0501602c1c1c03034014148004c82e000384c0c0c150754074000d50003000e560744034080d00c0103030b003a6502c011fa032100000c40b07602d000300120078030800c52041c03110158084980b140d040141031090030307103600070701080440e01141d07050382e61141000e841d038000c03901d80300130f01944 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 76013032 1250 76011782 76011787
    0x50a090b0106052d09010f030605011e020102070614070215061c14030f0729040303050c0c0609010c0206090a0c05190e0702010c0f110312100f03030206060a060302 72
    0x5503610303618950144200b008011000c00c5901c4031094130415101c5001c00b6031400d50400700705111100d115400304030350300c0c007245010b51442040b9019004010440e40146c45488100022068100c6130741c845032131400440d503080018000140c407900c180c800703d020250360321005240c02c0030080d240c050224a4120341100110070000720303907604003c412000080c54414106514589000341e0b002c50325000350301c8180804594080c0305c00d03800015040c1c0754002c0240111900c1d10260200c0c82d07004031804111030f82c5080c000038010a02030781002e0f80003103520a2407032078002e180c91400e00300f0b5400e6907400810f0351114407000e00560304010f0719030000b0705000a04040d04060b500d0010180c00d034440d99014025103050800741403585054400148114402c0344407500e0b01c104002d00a044003d9081d01144442440012251042c1001e40303103241a20001c40c580000c1000d4001141c41c001e020010000605001140d64a540b40d0400c009500c00d4009080908105041106e4004180c20900405206 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 76014282 1250 76013032 76013051
    0x30a02070e0117100b0402040f030b040c0512060402010c0507080a0b01030b090d09061103090904060506090903031306270b1005090402131503020402040b18090705042106050c030109050a 82
    0x2007182d44c2c83d440e051000242480103140032502a0280b50705c5200b03110032132170703000041c8800500400d00c0385116401d190401a01c5804000722020100280245a840000040c0041d409001c1c41221035001e44105d600307031552403ca45240009806084039183c14000c010020880300130081500034000c9006480c00d4141002c00030701a00c400e1190b10b04210000841d400e140e40c2c180100e4801203406442084649071038100300c3d014210545000b4010515040060401e01c0701005981c00b4210300d08070201104419202d500240c41181d0030250502508504400809801910031203618031820042941d0b103400d84c000150b0404075480640184ea042007040016607984c280e48075181d80c420030000307403405511040d0200b100e03140c0009421510006012401d403010341d000d0600383e843e500c0489076100d5000240191803800b80d403644040b5005110601c03540009122842690203040d03150140030300182c0f1150700b6500d00340c540124442d000030051007030304d9070383c0900c55000700040c10a11100d0b69 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 76015532 1250 76014282 76014329
    0x101a03031206151c02190f082805041b060806010c0305070510050a0b190b041401020f0d0f0f020309030a06050a0603080706020d150308070201030902010302070203030a02070e01 78
    0x34012403190003d8504145001158402e440301d0f084d2040040004074a5070a9070002540a8a0500346101c15070540c1c00035203100b02030041c42c100b041c2e41c132604a178a81407408201001d850101200c214072004140c81825002e1003000d00c501d00401c480c87c0d40c440d0b0806010084944c40d0480d404001814040104998100c0d60700340700a58180f8110f6590b03129810650300744007540c503040c2003403400d000034002c040d15183c001040100b41150801501540c0208001d5250498815010b0002041c841001000041800102e2440e01130040d1075481142c40e440c00e00700300c080442c40d004030b4182e4000c1303050164040c500c003005c00309500080d07151081d45000242c2c2e480700b180c00144030549540000c1e4081403031342c0100c40119400180942c65240c01e1038600d001e50420340c0c8201c1c103103242003540740b03485426003403c4c000c594010061a2410105400440280c860800c0c2a0305141d020800440141c80400080020000e60b5010780101c80c01c01801184140c1c0c1a8400080341081da200001c0d10301 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 76016782 1250 76015532 76015567
    0x40504050c0a0c11130c020d080c04051c110604090e190305120601021e0a050f01090201090611010204050901030501050402040507030203060a140a030803090601060809120723101a0303 81
    0x1034000e8040303050a1820000255a011000243c21072203040c06c5400f0340741c640000301c09030b040300c8584401201d913a6402c0b030b030200c1e80a14032801d5405020507040c060100e4a002c01c00c40a20b000710f00c1030325680089400315400740d0099100500541d0744030300904060070300b4421050b110036a28001e01515220351002070503409200296400e141900d40401c11a038000c20680048494035907480b8041c10020b01d4030f0b922044242402d031054007455005c014440c50610805030307040d505850700208030b03060280031114142502e03440d202d159800c00020405584440c4818001c6100d0400861140b0300b078030520045e603030080c00b1402130500500500803a5690b4645031000d0724440000320b00d8078601035000501c40045a0b00c05010b440001081c40216100415403038181d54031074454104540f81e620313210355075907119580b851003200e0a1222200081107c1e0080d2440080540c070200101c0104290b982410076940b0080c55542e074943e56054507003a140c40c080c0c3d54000490182d803c042018060321000d2 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 76018032 1250 76016782 76016807
    0xa030803070810050307060c0204140702070605250c05030114040b011401020304030213050108150103050a0b0603031b0304050103060e060a051c050610030c050915060c0109060908040504050c0a 85
    0x10b0744a00080060665521080c01008010f04882860340c2d0b9103800340c500390175084168000d9091904c001c01e0789041c0e02ca0036001e42d030f4640c0101545840c040302200c0c0d0703401400d131084201c45c801c0498001e07040641e003404080f6010f080c01c401f40d0b6107010101801c4801c02c120280080030000b0800011440460b012070440381288003240300d03420000c004034114401d5400095020060064442011710b01e80c2c006816940390b042100c0007030240c107825001d642c109101c010042c1e44945003140000e0304400c00560000c0c009401c032814005005143d18054000d00d1050710300703901c0410100015a894002c00700100b810302e803844200c0c1040c801043e41c015171802064050300c0040c0960350043d080550034029650072500741e0346c1501306940400044ca49a10003620321844402000c182403803d1036115005a625400461080400c1014010280c02401041055550301d030f0796800441c90310f02a18986510413203040e030352941080300f00011500c01409180450400f8005001c009400200304003c4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 76019282 1250 76018032 76018037
    0x501050901020f0106030f0c050604030b190605060304061a0402090612130807110a090b0904060504032115091e0f090c080109051e0a1401020d0203071d0a03080307 72
    0x8601141006070300d45450b00389243e00f2980b030002c002040c00855003201c101c0c14031642480000329902c1003000b490380600d000c09054449075a0105000c1c2408034083d62140025980100d4550b41d40c500040c3d66070021a410384817240c0ba00c46d07020070040c0c1491448448101101d085040840c00b801003507160003800048928015540003061a407088000c40c110f60561040074250b544480d4a008956011045c1c0308601400c407440000c5482d0515014246420a003d40784c17550542c1d81c3e4403000042c000c0a070050f402d1082101c034010408a02c00004058684800c2000c9600341703c1103590110942654004051145440c1c2d40345585020300d00d511155140c1a440845ca112000c07204a000342031180d0010041a0860b100040e082e1041d013000381040e020348183c95008056403901003000f05049004421600281c9140000842c80e031040717025440090001400c05403540d00c41022a0300941e8108042400649082c0310340e00c091380d110009441c1a074250009518698800c043da010140003d000d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 76020532 1250 76019282 76019287
    0xd21080619030605090f010903091509030803040803060a03021903140309100522030f02010f0c080405010f03090b0703091e0b0703020c010212010e062706090601050c07060203090a140a050105 84
    0x30842e80130824665107180d01c100808c40032840b40707030141500000c0c0c41240b460051020755049114021492402220707004010130313103140c0c1d49550350821944010909940b040d40c5410120143e00c8400d4a0080044c504164140450941c1040c60181102002e41e03107441d80100300003072868132490115040035a075810f040b92510480700080314640f8130000141d014029100d0000240284d0035010100c6038003c0c0c031150030195200404940e60710b0400000350001d00d0400042040354816058607581f08882e140000348002039031748882c1003200503110100000d454520003010b02859041180880402c040100424080c0703a60340d5034400e4004005000707040d804201c80c11984020740449244803002080700c8103941c1c45110b848122242503520764011038190030041d4509549420a402582101c01040b00b40e60751f440801001d00d0300240540d040100a0000c035070aa101002000040c2909401a50720703000000e080c0003146417254000344807001041e200003456121802c1503001c0d20828680240d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 76021782 1250 76020532 76020541
    0x2040503104b0b030a0803070302070f081306020d120c05070b0702010f0b03030c0604060203060a0510091509051c060e0708030405031501081b0d21080619030605 71
    0x612054010101c241c690041010301c0014020004294000111001c00030308050031141e180084a10f003082407901a4000358414010030000c1000d1a401102d6290152901c0c0f415038a01e41c0816601004031031111020031006400c45841e88078002030481807004006016250400406001e07402240c1d0155070b94800c541211280721344111501d4035081407200e0354030709002d08000d008101c106103540c51585449800000c80ca0040104c8079101a00f10040210b030301c80d500c0303460081d40050f203144d9205e008038070300207003a499a00049040443c0c43d1030740703114541740868039401c90005a84090800010003001d11155950f2502c01c001c4d480c0c010b0125282ca952881c010b40200780d090310041440c0b0a894000404460000c01002554030a8042d0b45411240c854680307842030080c000c0c601e16412200d2901c0300580181c1003041c0c1003200401130f4404190503102d42c0d00c0342c00c5180440030040e4280c44001509500b00c80007030b8009800751600f041b52040303400195900005800002c101644400105 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 76023032 1250 76021782 76021811
    0x11107021503070c2d0302030903010621150b030d050d05010e010b07080a0c05030408011512081204030e10081f0b09060703020106031a0105011211030402060703050706062303010204050310 83
    0x3d00c218a517503a84184201c09418080e507203402c1144003900c65820311002140c440d1410161907007800d4403010320290015030ba56141d00e244d2982081c528900d660311040302513030741d00300a031086544041d06c60543d96031803441d80c01e003600c105821112a51211000401140800c41d0845225030f40040708261a140d07030407803c950219030080058902d100216000c1360340301065020512a54003100c242c407110360b94202115284540300317409024a1010702910303500c0f02d4461040e1358414070070724102500100d00000a05ca01042041e800006406e00d82001100c01c000c1d4840c10411068100d44901c480c9010b071120b020303129908005020f20404540501010b00035013007400950b030711011181040c0251003d4070400302d0309105076400200c540103903030b10713000161250110410070030340c5580c03640d43c5d0742c0c00303102069214a604400b084420018000407900c3d174481c080107002424510f45040c80c3c4423050324646c07607600340005e1181e44100000c03c0f49617400528000d422020200c00314640d100c14619 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 76024282 1250 76023032 76023083
    0x20f07060503152d04140112030504080102120106030b01051e0a090806011503051303080103170f0d0e0d03020c0705040f020c06090105160309030f03110903011107021503070c 77
    0x1d154100e069180010701100c4200104c03048124052006150082440100f009403501100b49014000201c0010710030341184c906040c1219009051191620780e913849501d0032070340003216685941c2c1d1081c005011031641801520300d007a009107001400c008003e040300015450842c864091003400003000e89440380501c07500c4000b06654030a03a001980d4804c040e5903c1d601100095000900d0400000c0700700d1030510380400c0041e010f9036038030315981c2507a49a50420b5501303481249401d80500a42100d00c0540b001461180c01e0000003141c4c0e0164814014030303020142e0880000d150042c0524008554005125000c45000701e4010403101d5409140c10024455802d00030610302442c02040451070054000c0c0c1e02650800d03200001884407500210200c4840d240d0060000e40d102610904a611941007510b4034400314038082c0c03174051100c00090071204413070010b04110700046011825407416200fa41c04d00b8111102188ca145400d00b40180081d40402004103120641592040395a208400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 76025532 1250 76024282 76024321
    0x30b120d0e010909060611210a080613050403031a0406080d030f0b1f080c04063c09030311030306010806130e01020f030105032a01030b0f06040b0712020f07060503 72
    0x10410105d070b207411005011043c0048504074034854405109a5448450310401002c10488806070038000e110b00120b69034031000d00306c2548980d8101158a00d6480380c840d07140a03900c0ba482c00a03500004c7c403040c12400f04010355aa10803864030300104800900071410742081a02c13460001b0703114007015000c5008007554202039400036844912420500c030000b440f03a101644640707507075685036107551300d04c0c1052180d40258400660010303443d03100c030020351300180fa015903c1c480341403400e1151584c107580c00000b0040d00340081c0b8443e0b410010f1540000c2c000e099224084080c0d4a14a400000a051418040c020074090f11040d4904005040103601920000c40880d000703550703c2910141e224030903002800789074402e0285074160400390f203422500d08420202c04056a104c015030307000542c010545100c1051f04801e140460b41d0240c1c0c0e900004101402000003980e071030710030b24204812550920240d000640d401100348807240500014204111106440d000d681c030b69a805100407a40007260 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 76026782 1250 76025532 76025549
    0x1109061e1c051f0e0d03050c07140105061002160302090402030a050706020a020109050301140408180a0e10060207060503010b03041505071205060f0607020f0f060d0c030b120d0e0109 80
    0xc0040401101190310f42003d030031585141c2059030b1800b080307070443c1d1000c150302000e0b600880303107084054000d0304020342c01480120514104051034403000305800000000e5420341e50b44004201c17a07407401c041058901161031000303141d40000c07102000c510311591702000e403080c1e4144001404544d010409440c0f100d03884020707104d4080e601c56020b0f40e62140c040c000c0340403441c018070214444c101441083c40442e072904107201249c0f100e40355412140c2c8aa9954240710605070129005500c0d07408030100200036070340d00380125160201c0304211941c09a00040c003150080002004401c0d030240580341900c3d20341e12103503900d0310f4034079265031203030900403d000c0c1c41410f01d070400054a8103d40d0000d85031801101c02d2019a50344030070050101d9422075440d901036409e0003440701500b444030b00c400c181702001d801408113018180c0010400c2d00300610344030070607482c0c600052656902d800750410019040e102400c0700100350210a0711340307542d46c44107400c10205002074081070388074107803060040c440c12 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 76028032 1250 76026782 76026829
    0x305010f140631060924030903050906040b030103020a0b130905060f040e0a0b0a1104060c110d140f0601060e0f0a050a06030207031107032303040905131109061e 71
    0x10f0844000b04164070501012a1400b4000101c00d0070780310040d452001e007035615405d0751241e4581a4001e1140c0c20040d400c000e000d020f0148562a002c0040001c1d02c00c50600700d0b03c1e50b1443c0304110b4200c03080d800140c00904180802d181444500d51804107440100300c000c1900d42d00c0d4000314811850010140e41e1282c00e08100e0045d4000c04541070b090140201c207640850303a0354450b10400c3d0350706890b0000c901d480c208000c01c09035103d03900f03129145210781e0010b800c85000c00c000601c100820070040d61829110306580c01c80000402050918244042c003400440d03241600c050000355089008502803101440c900d4042e0f554180d0712809410024442020280ca4000040085d0001c036000ca011514400d1041e000c500006070000450741c0c02a4410762009044c01c0c8c0c002d03030501031a01400548824440401c021600d401004e106107610f400344440c80340c044c142a0405004211010300800e04242440810b81b0783c1c0809041b01d4640c042651100c50364040480d00c002907460004041da07921 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 76029282 1250 76028032 76028107
    0x516020402040b09040e0d02070501051605060705031006111b120d0f0905030601030b010b0c030d061401030c180306110412120e091608060d021905010305010f1406 72
    0x20001130030300b90f03000ba103081050309880c0b07900580ea041d10130141009a440358400300281e61041c3c005104414018400c020a071640f40c5c1d60381e15290081e44c0800115038080100001400807a1004000f032085142c07290403080400c1032103444040c0324003030021125102200c0e180640302c4000d0b03540484203c01c01c990401080c0400201030f481d401e11074900040100e180000c0a143c0094814140c0781c0000c0d60007126403030403202c80929488040000074070701003445aa0200b12051140c84004c103041400345001070111000102100c1056281806100b0713034910915007000600801d00c1074a03480301002901007c81400036034140503a07400240000340d07080400c0300b08802131002e030440008640740c00f411015940108036013607004880312a1480a013218407114a1711500085030442000740540801e01c10f43d40100d1010002c80014541d528490f010810040d64035110b91030040079090086030380d541c00e2003604c0ca140100300c441e07540702c1e0201044c19072141180800381803020096041d4071003076160 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 76030532 1250 76029282 76029299
    0x60e0406060e01141503040201021507020a230c040c03020d02070303020903011104030f0b0619060804170c03040506090609061308010c050715180219080f1c051602040204 75
    0x200d600a15690030b045800018401c00e5004a05030810b1005004543e01c09442c1d114400340e1300003c0c810390451040500c20414008051f600a000702b201d94050200900340d0304041c0700d00c1d004900703c807010103803900e1086082d140100f50285d401d0802c8030702140c000d4120300301300c01170700505002c0500c503480043c1e02ca01300b5416a0040804940940003070041c1d07134503c40240c5150080e484064510b102014849001410070448650b10801c0180340b504da9040c011030b0844985210b4010902007140b900901060001078540e00c1004165803250f00d00c1d00d240030318181c3d100e005a11500c5e02034171010070055880da48070000d44807000c84c0034100c5c03a2141c80f201c600030340810440c4035800d82da502e0815000c1c1d595106004072088103411454603020b0a1601581400a05101000c84000040c0404550041e41d070f0340010070140b079560301a41000c60500c070300141000380040964441d40e00a110000e44020510f01041c3c8c0b14509007085900d50362001521411642c100100951161002070045603181 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 76031782 1250 76030532 76030541
    0x105070e01020f07030302120c100603080a021614060c010b13020703080114010503010506090301021606020406090503071a09061615110c0a060e100216031e050405090703060e0406 79
    0x909034200c3c1c0004030300c5401c440c0c480c4a030b4000074005030041526140e03007020b031000504d40d10005031b00302c441e10641a10010101c032400d40003110178031800226007140b140c1c108100b44042018001080780c40b0700d01581031620680d07030004070340103030008903040060340801e500016180d0009058110080782d4070708090000e60088030300701e01054201d000032410240a0b81d250030301e560180c40304e81c9103908000401065401c8000625451340d002c011800111003020394005a29104000268695080401c0a00b0f407042d40d4001c24020b601c00c0c60700f004041e8028210707480300c0110103044d80d0b6990b4124081fa90034800d908028a008000d0944070007086120054a10201c00c000005c1140107030316106001d051061410b00c0905500c0414001c0c0480c0d400d0344525220080401180c815802080050080ea000030030030300c4200901c4039451090541001c0b42700254007001550246c6000140006031581c001c03801400d000d070a0800002d8a810700a80c0000f0280c0120f60ba0001b4500c1e0511f0800c4c050b0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 76033032 1250 76031782 76031807
    0x1c0908060c030a060e01080a02010302070204020f16020906060f0f0904060305070b03010602060f060f191a040e0601030e060a050903120108010b03010f1b050d1503030206041109161b05010507 84
    0x3e91506000240751401403035404d060ba900c46026100510340b07070700114065004a44143c5e0b000d80d080010304d103416034600081075070240c102a03100e050304480c0100091204c1c02421103002d498100000304d00c102460301102c1c00420b2079056562039464032404100104282e81000340181709403580402c0c81076035640554122000b640c00c8411964484505002c01c1009a0b105508003500c000329100d54604912450f0240b4400b1141342002c0317680c2c0c4039031014410004d08960b520a4000f4041c00000d8160030070030303400714084c2030a1001c42450044035503644001072803000340039550008580d11410900840e404c0b4001e40d60214901d503140c00d0014028002c080c8030034031940c605155122a0780082c01000a20106181070300c01b81c0303038040c01c01d5490b5800800040c0380e02c0d036100400c114101413002180061802507005280601d400d1178030b982780e12400e42e00c9520038003404e0201f250300e0078000003040e0109036900e07285050b6150f81d210401250388000d80109654206020820a107900c80c4416081 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 76034282 1250 76033032 76033051
    0x10050a1d01050a050f011110020d0e06010909080f03090307020d060501091a130b030f0a030f020d0912030e120d030c2303270601030609031d031c0908060c03 69
    0x1c0e40e88204000161640b4800c0640141d07051000b0255036015494544a03005058207407192030642440c810100e03841003071a0392590f9034801014544201c20000c15014104c01e070b070200000115600d0700c10550050f80c00565041c10000006403a4040a10a9a8855601902280c1c44590502d06000542000d00803c200d041c94490440141c00503220740d0b44c251207020304035909034000f07006040b026119449000350944200b940b10a4401400c00c582d0164500070350b20380031074190700d080090400c800c4000710010800032040c1448000c042e001d06074010350b4581440790b0000911004600700d1105801e01140f0340c041c010015401c50b400d80c0000040d440142c2d0b03000c0e4465625410100740d14440c03506071807914810f000044145411401180300300300100306003101c413002d82403034602d40348003600203c5005e81c95124031400c05400c00e03003041c030200340700c14400c052640601c0865a00e60000c42c02c0c0d144003040d8a108440e00c1d000e50131000140401d501600c005180120030003005500650f0075214 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 76035532 1250 76034282 76034339
    0x15031f0914010207030e0907030b0d2001090b040905070e0904060b1f02060a1d030a0f0206130803070806281401080405070e04081b010903020d0302031b0310050a 71
    0x16035043c800c480c0c080760705032a40100c0d10072440501c81070403c010507802c181a9034545c02000d80e40c40c001403854003441101a5481d0850304001c194a408402c818141400f0400c0c600744032481070b1000350303426902d03180c2002602d07680f11901110700502060f16076801c00041005c2c0003d12840d60800c1d096602d041e40c0410206d403d100c40410000d0840c54180016000700c008194282200c2d0898003079a6104107c40c0c0300c540031200b880f03040d41d010443c0031001c030b110340c401c01d0440d40c0c0500c641944030740300c00410142c5801079240c0f400755201c000d102d07004000113a170000300c0640d28581e015090400318903218081025090031981c0780109402030707d0a040c192201c181241d07101e9481c0c00c0c480c82c2c1c800c0c042c2a46501e00280000303100c9024200703c46a1a041c040440c107040087d0400702903034240000414850000d0801a003464464120002010300401c2040360015030040d901d440d182078038a0341a0f803617581204480308c2401c507030040d5a01c180e04110000d658003080140c03c0003600c4100c401c11 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 76036782 1250 76035532 76035563
    0x20a02010915050d050405010221011502032701030f0f1401120507060c08070206190e0901061e020715030b0108090a050d0e010c050604081c050c0315031f09 69
    0x68103810229100c42c0000d204020280c0d5034002c5400007500729110fa0000760038901c50400cac010302c202101555041006c03e10700108070f4941040d41405161440b400514a88000702481c03898544141e04103042c00ca01a030030008659119034440c0d03281807801c5104115514186e00044050300032501840903642e6444004950071046d40310444503a64018005c1c24584c0c40c121040d00e1300024000b081d11090024040000543ca030304008007108501d00502080c4810019000390120031054109800b601740e40c4010301078a0f4000000c0e104412004d4001d4108a01207602280350001a8118003511b00d8282a00d0030705a40540040380f101000b40c0301d4003200d5540540c007941d00c0444a8010700300b507011001030483c150040b042e02844410601d0130b10004101500c4080c64140c040e901201e240300c0005801c1901c2d01c2c00c031114a0340c040404024400742c00c00c07102a0301d043c00080c18042c50316003911943c4205540400820580000d83c510140618859511100042280e594151105906108080c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 76038032 1250 76036782 76036799
    0x215071d010503270a0b010801061703090a03031b0f14061806040b04080c06090f0616020a080f1903061a040503030a0c02030106090207060515040c080f0403050f0406020a020109 78
    0x1ca02c1030344504030340a0000001c000392440910070444e510514000c1e9052480451032a200c21800b9201140011800510340584801140403c41c50450a604180503c1c1102d07620300c2402803c490b01032405403071111345024180c200c020001c2d0001c08140c005545801000380ca51801e80990000b40b060b965030f03a83d0301810151a1844050b0710b160b0f07400c04000540010711105000e9003080c01208941d043c0000c0085040c0f40c5a815076040d5a04e0748081001c012070b05081101d980d000c07100030507510b0b14480004001c0e40d076484000004085003804201ca01c4a4160102603c8038903001051a103080c1096910280083c2003033b0080403504a145801c0031960744601045400f10780016009500d040c80c916004c030b07204002d109040346d25540360790b40007500407014005880150b00914001409040c1502245103a00c1003540082c01281030580721080e9175042908039078807100c0205010040da80e546021607940c42502c2d03a03a00425004100400e01e01ea0000700b06112074404e03203465807100c3d11014030703 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 76039282 1250 76038032 76038037
    0x206010605030f0702010207120e0a05061303080903100221060a0f051002100e010f06080a020108061c0507030b1905011404090f0203030d0b1306081c0215071d0105 72
    0x81101141c020008540000a501c0469a10203014800181407002030380d54500300010201c2c65a00280800205611911703018242034010102120034500d000d5802011407840f40d454800908400408248d200550300c06014083c41002c900302e00310b564102c0100c218001d61400e51074848011080400207015050528112013943e40382c00280c41c2c02407600c403c00080b820b49481400460188100e0207000f010303507006690042c260341001040610503134000004070356480e880b0200c1a8842461800584d030031845260704104140c3c0c0308a540042c401d0540110005904010014420b2420001c00d20452800351070084004410b5111040a0b4840c14829203a00b03010307810f000c00460001d01140e242503405601d69903c1102d404018541c242c0000c0c0c2550851200720400300e80b81c901038400d5250918080c012506045c804009d041e0034005255a940003108604410300400e800068040303000300112055900c002e014040f25142410000701080380350b4a0030140c602ea81403030040c13950f004005 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 76040532 1250 76039282 76039289
    0x1b0d09020d1b120b060904030509040c0306090b030a020603011203051e07150921030e0303010b0403140a08072009070c0501060609120609060e100b0901050103021c09151d060601020601 81
    0x122003240717840780c00801c111058042c00842c00c0c48020454440b050300d841c01804550349075a20000b035158034040f0a1f2044d640100001f0340f19800199506005903100002d8a05485050f0421a41d034a902c0c541034a051192042d00500291115224010404200001c0048138072401d44601d112540d017a054007a10821940188604007500c0e07e101d130040603400c001c1c00c0c50070303610b4041141e2181404403425540281c1000d2480d41b03000a09005201071092030030038001e107003002004c400c186504c5600c0b090240000061810061804901180c010035100c403403c081e00900c1c51000382400d08002d40591079813113040f0f90139420518000342680c05580a901110000341541500c40030a503240d40040c9201c0b0303001c035822551082c0c0c080c00c02e2020807840c4003140c04d1081c0010886401d03400c02403268416400340d810140104100c09e1400c1a01c00d03003120101c095080401e00c014946000070748119510000d0040307a1030641008c6189400110702c50808980405031496900c8540c01203031544d10902 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 76041782 1250 76040532 76040543
    0x40302101b02010e0f130917040b030106030203040501020904020a0201020717040803040302040e10050c0318160b18031009060501050a0308071b080307080301090507081b0d09020d1b12 81
    0x39884055401800c0504920500030304416070301c0c0c0b010300000c20603280c90315801b18990340d03112500304108054450600700e01c2025a418242071500341030480610050090000f010b801202040400400750181d4140000c01042036446203500d0000078000e410002048d07074040c00c01c03907154040c0c1c4900c2d0112401e50707003103402451509003583c090101a007000d0b0800750041c82800a07144059001d4403550b4090360b08519107503641e060503c49001d103440f00b8207203c00c05402852440c1c11202c0030400f00d000f155507149110761580840303d50114944060f40c5000c0c4c25010710034910103080c0050b4419580680300e01d2080250f640c9410034000340101c107000c001d1501c00108078000c089840d4101000442d60024444034007140c5440040d41160071144049440500100040c0045202030180c2e6034020f4480c81c0041c0903283c510500600c2d45214402080300c0c440c00140d400c20301b4241d800612400e900503004465051076880c203d0200c030061490544520f8404001003001d8182101410706650030a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 76043032 1250 76041782 76041827
    0x3150609330d060e03040302030609060708010608070c050f06060a061409121204030312060501020c0f010f0531151403070309140a021c0c0b0306060f0403050304030210 74
    0x10740400c0c0341180350801e507000100c800b8460014040740035002800c3c082101541c0c540d45984145440d125003d014009075411020400c190150701502850444015150048840d142c2c60fa00307485c1c0a09610006d8820b0244010325810110001401805a841501d101c440305544504c1220700902020581e4400f00c02007203000c0c042d1901c00090700b15681c580060b5268190544407444184d03009910480c08a03400201d1140049241e109150060070280041c000c0001d110001a880d46002c03511a0f0501c101d00110014240c4504140c0d00b40484194201c81119000540034a1241903800c1c4081d02038408440807d00104440340041030440b55100d41c0b004090208031501c1c1600020003000800d951380c180007000c52542e0300703032030203514000014040000050050102061030540e01e0f049a080700c044420008852a00c0f450454881d00d010340d84946800780021102d01c603843c0c0030f1407134200c013003004403c0c00f01c08070003041101d20841d0354102d01c00035407a06440c010b0220362207080d0280c00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 76044282 1250 76043032 76043101
    0x411190305060c13050904051609050411040c030e0703050703050d031b050f070f0b06090f01080d0804110603010e070908071505090112061502070509061c030c0203150609 75
    0x240054100210118103028a45444130041200300c08210b47c2a107042d800a441b884041840c050a5009001200030502c1300e440c01c1d07180d4003040801e10040c1c90083d503980d425141a01e1190740b20354841174115081d00c20040da40c0c00c0c1aa51000386000c207558501568024941d054020b2250b42900b070844849801c1c07803941c01d40295010340000003148002c0000b00402f000007401140c509031031511504550103582058800c1c080d040d2401451b2190580c13411006201c84580010034042c042801d1409858a544a141103c444001d110342c854004202000120350304800d0a80544208007641c0d403810341d50383d580c1d82c0070703a41c0b03000380304400f4a004140c01040100788104014540000103040c4180740f16000081002101c2e216844048601c0c032040d05141c002d5030601001c4002c01e000c0303035232403110300f840360001d40081b000d40700340710444e040003a1040070940280814188940c0007816240c035070031a171081c1c0c03195a10485901c0d1091006a00040c481004e41e60034034a001641c03003415088540 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 76045532 1250 76044282 76044301
    0xc0b060f062706090a1203090b0d0e0f0d02120f04080a030203030711150403031a090a061505091806010207080105040506040c1203020a080309030403020d0c0e070516020f040b03010203041119030506 87
    0x4215009900f00035048d8030100380803048100034080c0e0702004800050416210144604110907410b48a080390404020045199800205880d03000c0321100800d07a00c40c1969040074151113254050303100ca010750b54491003456000302c00b075071044002d91222210030340030705815900d0305509290307603104840d00d01c08103003c00e20035400b8000220039003043c0c0c241400701200003042001e0440303e4081c0c0940743c40d010300c00101c03064914801c11035330382803072420308081c00700181210188581840d11080800005203440c0e00c20030100c40200300309402005035042c541040c40c1c9075070017241c0688124000850011705d8000c403603141551243c00d40d01a20800c44507a440d001c050344041c00b01042c0340b20510010016940c1c0c1c0d010031524030f10502100c00c2062400a0410074007d00a105e001400300034011342c2c1900200020681c0d01d075a041b05c07500000030f422000100240401c1c07420b240c140d0310110800c03081001e0007405c41501001104c000b004881e000407030b00d031417214078080242150031213008251180d8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 76046782 1250 76045532 76045559
    0x80d09060c0f06050f100b0f0706020a02120315100905030a14160602070806011208120702120712030605060f0a08040c050603091b010c02010c0b060f062706090a 71
    0x9102e01c21681e6919065210795003912020741d1800c00c403414000a001069945800d240028580400d00a0504105403440d052034016008040d01d040e80006000e02442e20910107000490301011200da00d178141000c2d09208101c00710303042401010708070701c2600101e00070703140e00046a40080c01030112816a076940c1010748010101500c59102c8c4411421610041e08010000792100340e00910300c048c90905240e1412106030b012213116400d680940c0c02181c0314008440000c80007102c10101d58440380400c03440d020071000c091707034140400701b83c1c1c2040041c2d1800014620748941e03414440f8075181d104000d664802e41e01c0b510340034082008542c0c043c50003000c400d40e209000d114011001070703540c0d000c80e40592007220001d2441e0800c1d81d488001842d00c16040c0101c070800c1c40c0a0030b881e45140e0001c0c08944803240050308200c14000010610364071078100d4038420300302818107a280c008290a0b0720541c1c03142d900e40c3c4400e0f02d0803032a600030350410500752403288a0041c02c0aa441c0d252100692604c03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 76048032 1250 76046782 76046807
    0x231303020f030709020a020309091e0c0310081f0c0207050604091802030610082407030218030d02030c0721060b01110303010e060a1d07140705070902040e01080d0906 73
    0x1401a00b00004503241306101a1100c020310b034010710740c0d4130203141c10041055070003001100e01c4044510036241d800c03c0b8126659100256541ca103680b504c504101e1890398000350701c01001845801d03015006940710810f03041550a03e2942485000a42c40c016038031006140141a04918240000c10050903a41c0098000605a05100c06800c030701b600403a0074100d00f11250703800414003000801c6403500403c103101200c015918030082c60030191b02e411110510240201c02016000700740d0040e10301c20301e48071003600c400c0102103e0348107454260180d180c0c0c0000700050118000c01400083d0074000d00801c0c807141c1688003403141038032900d0350340e280181468241e050400000b40180200c10708100001d42c064613450400c0710152500104025480d609900201c2a80501e00e0340c80d0035585055030025004585400d2041003000359a80140700c50060380800342c00d82c4110040098400032680c003c00c2500c81c1100c00c2d04041c1c1e200ea03c4142d951070845280000100d00d4070041004a01c9040c2e1103a03503 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 76049282 1250 76048032 76048039
    0x50115080406021617070507050603010e13060b061b060105011409040c1b050a02030105070e0310050603160609090501060207030c030b070c0f06020a0e040506010f0e1302030106231303020f 83
    0x200d840d0380c4a50907201080384212101c1917000420600f4000e041002c403004180840b1094038540c1081c1640c480810302400c00d45c00020054041c03800c20103560442e400344a00548070948a00041000304103100c54040000307064000c1d2300000ca0194800e605500703804900002e480d14042032402884010428120088204561405401103040080b404030030064000d0004000d42c100a004050854402500007000d00c0055003074a0440c0c1c0700440d00c0686c00003c4400002c0c50b40c0c80c100407904042c036082c2c1d0340d08003086201c000b0034080d410651150540d0440802007142d40c4c1c8802d410b07603880f462404050121200b10004000141c120007a0f01c0d0700146918000178020300030790b00c035446110300380c004489082c0c0208402c8801540499081e8040004440500003810010006080d6101d00040c1b101001070b144d11051b0355441d42c6210704501c0d21840030455a0350307034a4800130404103100078aa11a4075861028818002d40c54050301d40700c085c02c02510161a103107900300500d104803034030450380 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 76050532 1250 76049282 76049317
    0x40315020903070605040303020c04090b0612010b100c03170906160302160807020301050a060e01150e03030304050c03060a09050d1b060606030f0b030a05030a030b01110105010303050d05011508040602 88
    0x10a61401e03c0000000c0c83d460301d40c1c98440d41149006420000110b00c4140a149001e140c6c1011640c030060158000f030080d02e040c03412501d071400c030b68050320112640a8100c908807405c403044603404040902c0e00d50103507480020315004144008032a0b43c059031440700c19400400071134400c070844070b00d0603420301842c180149440d0010803040391200c40e82c54244c1e1a554041281425824280107107075101071680010000c4c18108a048000b04406000d45c2d040c0404c40c0d2a18410746d4058000c505000000a049a84030314040c07500503075034400c12801d0750082c0107050100c7c1c1007a100e030194115103903124000d480300c10149081100e114001700e050041080c4000d4030400866001d214580140c0403039030f40802e610038041005016140e200d06018000c4d4019030443c0c010030004400d40720500001c0c540401d200c040380c1e00485074502d030440c0c1e11071954600400041010f810170000e05c0350440401c02404180c0c0c1e108502000314030059000408107000c200010009000f40c1c1c000e109802c00d0b0f1b100050b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 76051782 1250 76050532 76050547
    0x203060118060206040c090902011403071205010906080123060d151b0e030d0c1e021302031603020c190611040602030408210a03090501020909240103060b04031502 72
    0x1a10741007280d10071405a040030060000780044800d0201c0940301251050020700300b142c0c002040200c403000c80c01c103103001c044042000c0a104179414603140e80e1549080c0034550b1507480100c01840588209005903103041e5035100e0500350000181c54141d25050303140d0303090351041c0c1407100703d04810030200c9001035011540c0f0708040007481292402c0d80d95003050501c680c0e02401c00ba1000d50f011140b517101c3ea02051440c50b01c0c03075000312030b035902039400420703208070b07155240580000303c4021000940c000c0b90820780044242e5140d020307500c1441840c841e0511000041e200b0743c228400c5580880307180c0c12424803003060311520110745003154498400095070f00f010b001150441e03002030b000710005030000502000500410420a42c0300341250700c2a0481414100041c08035100b550f8110b01410f48400070b140a00c4400e505035413200001038004241c40c80d000c070619a215403819203840204807514401800e0f540300744600000d503088940742a180074210f44401c40642103101c21347c0000c82e002c01019 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 76053032 1250 76051782 76051817
    0x270309090c0e0405060108091002090319120201060905061807020a060606030c0806040507091203170a090b1e0a020f0412050303012405031602030d0515120a0b0a02030601 75
    0x88048000780d9503820510707030b2148100300590360081c00c0103040210260502008410200f114103003203030365800059136440803502080c01c152840c815170046042c2c0e03e22100c01e0104491201d030b0941150341c002c0000580350050301084420070b4400b9508500c940494046c1980c0c6444030b15040081801106d00c1c82c0b50f03035071742c85040d100150810030000381c40315180350f15990002130258010000315014417142c0b40c00f420040041d4081d2041c54900780309401000309144c090040c180d4506090b04041100d86000d900c583c002d4154003004440034249a000035401c81c01c3d203040b64031400c840c0104001503840d8000c48070041e4000c500c054112500400c0005803a5110309400d074481e40c4208040e40c4c4942c5090240e811088040300e031b800350b0151400440b501c00f0b5200003182d1703010056140000c40d826071117038100e29501907624600c4140d403030300f8240282101c00c0c144078228008202c605607070b100c0d09080d4540d00d0358040c00005000f45150800300b03e400089402855001c1010305d081c01b004450300401 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 76054282 1250 76053032 76053041
    0x209011205100510020a02060a0c15050108071701020a020a02270f0a1113030213111305030c01050903031206180a05040b070806010f030c050f0f1c27030909 69
    0xd10b0301442c8070800081c203020a07a070300c0b07980e02e6002a1a1400c1950003280d40c170701c14000305504110965145004200000380d80f040c3c8030300814000c0001e50703100c1200d19170b5907140303009611a2000007124202d9502d014000c4038440031056018001c290140c0d4240051750001000600c040d00010410741c2030700d4942d280040c81015600c02c02d120b117041125000d400c40b040c44c0221903400004101c80003002558110060480741c0c1681c0200344480c0b00810100200804090740600d600c0000d280307007005c1030b002c0d22003095540440a0366404080d2a00550780391060b4140280c251300240800840c040d00411540c0c0d001401800141d80c070355100016612202e0121004011a55501c00380018840480e0520741d001c501410000c801d03041800001e84580c03981300e4080201601c403480c04546512610a1320643d80150000d5138413022100d40c40240c079001240803c12070442e20f0030501c0039500354080c1144044407805503140403101c030200200c5c9a1010b24040c1c00344110b170040007030118464800c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 76055532 1250 76054282 76054291
    0xc091e012312060a0305030a05090409020405150306070504060e090c091f120b090f0603010b090903091203040f180b0306010e0117060105010509130b0d1202060a0603080d0209011205 80
    0x2072042d41c03980d00e20344035825240c024010500030300c460401803001441c000221603000e07810741841074840403400c00160181c030301d1080c000d404c141000d0510401004070b2030306c03108100045051311a5503940303000450f81c5004034450b280018650f518200e0345828005da01c2600008200f44952820a161000c071710550f050b03004045400103030284900da0b1542c00b41c1440030301a00520140300401d015800103504080107032030140102607902c0810420f075400d45c060146160007a00c02401880c1191116440e0f4008610301d5002d036190707800c1c1c4040304802100b02c030b05aa252000424040e814490221010210400200784441ea9500c2c903010507502004143d001304105186c0507282c0d8107010503080400d05498800034640d100300c0051206a82001c180d030306d428002e6a98108060000c5180303005003540c5200e840c0c000d48103200c0c000a002c0344640500c0d0800f601d808684443e140da448000071502603210143c103c031001d01c21501000c0d40d903001400c2304a814540340110181d0034114070203c81c020358 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 76056782 1250 76055532 76055597
    0x70504061812080406080c0c070e18010f0e190c0e04052104060e10090614040909060b12060702070603023103051002090904150204030f03020a03080c091e01 69
    0x36040040d01c0d03000740507540c41566266082e0230291100406a6203001c6800b03404200c29600c0c001944107921009030300300581c82c20780240242000c07502040c0003460300c80541c89503030013803551442001d500c0101c0104042d40c0a0b0000021300e1900c2807003242541e01030011210fa00903000b803007150849a00101800040d0700c2c05060b551407174488081c201e421640b811500912904110ac80c485800400e040c007112002e0405554002c120801c24009209a810240030146440000c00030b109040c0d022013960901550904124035843c048246d03078800864074040144d024000602c2814840d170003801c9000302c0c6c0c20558000c40c00c12040a084018407800b84440000860070800c14040208410411071184440861070220b1420201d072084d2002000501010303d0403e0206c410201941100c1c01182c0026040c104003283e440c0080d1911110f01050740062401004a1040803116040711400440101a1840c8a4946540d40d060071000d1190605000d03d40c0b15008a04d403402c0740c60042e506524 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 76058032 1250 76056782 76056787
    0x3090a140102060106170708071107030b04060509010e0706030c17011d070305011412070305060c0705010c0914010c050a15020a031a030a080705011e06090c0807050406181208 77
    0x2403000a1400d0300580c45071080150b040c03011100009030040407a0403407a145030031105075031000000d480000d801c6070112400c0c4620f510001c01d01c00700a95840c01907103d800d080c401d549805d11210b01380c80070380c004100560482d14040109500a07130101400c200c05051030b8000410010b80000c4c1c9200907031000070001c01800710881110407400a443c0d000000341820402d07035040c089280d00054a1030490342c01408100c42d100445041042040029503010080f14600c1c50328001e090901c3d0480801127032290f081c200130101880c0100c0e043c100350303030150011100700d01102d0300441c2d08072405c0c041a543c9005000d07041c0e0129001c0d1526100c120291040075a54007007031440141260342040050100c200b03c800c001205590200b1504042500218029281e50a0b824001d00502c0d6a50382242c01603085920350f482821a50003000c1103541060307003000682098034042e1580b507021100e07200010010041030014601030340d40300c07044002014007450040d44982c00d401240303017444015107810030003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 76059282 1250 76058032 76058069
    0x9130f03050d0b0a030c15020a080a020f0d02010603030e13020c060a0e0c010e0a09090318030c090501080a0b1f0b03040f0204050105031203160c060213060e0409080909070203090a 79
    0x180c051002580c0e8184e81c0100c140b442c549404251002c14003c450300d405c0b06841720300019208005a556040e00700082d60344c0c40c4400c0301d0181d41c03090300c0c40d11001d460041038094174640d401031007080210798064443d0014211101c00704080183c030458896101076003800305141c40b090802c400d51107801c1b038410004001c2d5150304c0300e51074903010328205410819940c015040e951998030306001250054030003c101d0407014541501c1248502841c0c2111609401d0f000007440112800d101c201c0316100c00400c075590701ca601c515140c0c00104005010114030f02c0c0442d8050446030b0b140c0c0400c003d12198042101c0d141c08201446038010703113040c5d84003410f2641d04010344c503061103402d00620040340240411422558a100c0c07e000040c0341e0907900720405030750011980994500400c15500c903404650340c601074005c800388100b0a00401e0b000a030b500e107100440382801d1244491043c1c11002281c10a07010303e04015002100501c10401c5001c24856103003503496686007031018090f41180110051344 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 76060532 1250 76059282 76059307
    0x1e050f070c05040f0c120e070302150405100503071b050f0106060e090907030b070f0e100c030201060b030606120606090409080406020105130b071808100b030f150609130f0305 77
    0x55080c035130ba162407401c510707920070380d4002c9500368041020303000208801c2d5441d9403e5051160030f81c00650410311400c0281e0442600c45c1c0144181c8000320f50740c141c80a5203290841b0702e40000c83d01d030300200d4076640b00800218008810001f60500c01c07030480c1c18801d0000b0f001402c2d1941035210602181e0f9940340c0d03a0341860400516540524031200070400c451440d01d601101d04005420a8280081c1c0a03044090350b2140020303199645000d48040541e00c0740380402040f401c0159415001946001d0300422000b80319811070340601e0008007845d0612200200d1218103800151445074003440400c04680319403a03030300521800700d00451200d43c41d5858284040d080d104014940e100038002c8120240c00500030090541d0000281d19080c00540c0243c3d50350025915160042d80381ba01c62100307002842d0589030054242030500b6000c1d20000359501142c0703a662a0034900311441880c110001801a0400186459104512020001c580c0540f601c2c0c1b501404842c507416800a800020200c1d01c448 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 76061782 1250 76060532 76060541
    0x1c02040803040311060306010203040501120b060414030f060c030a020d021303080703140301050a03060f09060e0f0c03070f140a0b0d02030601140c0d080601031409150105010207061e050f070c0504 86
    0x30380540c0c85d0384c42c2d0702e800e1300001c0d101c0c0318500405050228014014030f11084503405a00000c1000e0146907982e520780442d080d18040240f5918030a02c2615086581000b0200304140940e20301312040c0d04603244c2e0078004010390420030a1003d029401e010240c011480c1900c1e6000035400be00210f640c0d0310181c20000c04810119030f1910700300804000401003502c072500c030401102c2e085080051025004028000038000107200540340714100104580d25030008981004850400b20031101c602e0981420715498100174411004102030000c0108440f00905002c5240402e004000c010019100c000312400c6401c84040c4c41c10b400d9010003040341c1560040929100745d10b00c1c94141e81450445070f100d0b9070b0b908142c20024100460200441c0859000341c00009401c81d902d5a20800c1d03140074846141e89240700e94603480c0d1151500000260342d400070900200740c50700c45e560301c2c1d41c00e166407164058000d41e000481e400c108040202c0e4a8a4001e079002e44a818070405004400c0b1349804208000c0e02c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 76063032 1250 76061782 76061813
    0x2708030c0d1814060f06040902040204050607030306170109150506041103040c031b030203030d0e01021c0e0106050f0901060c030903060e03130f0501020a110a031707030813171c020408030403 84
    0x140c0c13001c42800f11404002401c0c50380610102d501242da0185031010801a0065170b010702e03082907020503c0010507816070070120a980b408e1101d8a42159454007981c241ca62419026240e00901c2c0102d1414800d15001994403080c09000464200c07103800700c48070581d0044401f0380d2030080f0204244100101e6010704041c1070300f5420010500703403d64001988038031890740201c20b0b40d640c40302c00b180009003c1d01500c1d4460320f600b6800c03107500c00c07012103000904000c1c04010f003d03500e0000081000d181c0000c0019010b080540000c0310b80c5c0c01e048003a507124070303142802da060003030134400000011010f0040640c24070041001e1034030758001540540c0d5500b8160401030440303442207014410b999000500070400e1b900200c4645a01d5220300200303595845641001d0009082d160388080114150030081007007034860b42e034a0f040c1c2d0b030b10200c0007060010400c500908550f00c0c40ca81030141d1640704003503d00404100760201c10310a1440b00c250032a40b103684141c0864001060820a00900464920700b0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 76064282 1250 76063032 76063073
    0x60f08010503070b030109020a021f1a03030a1425030302040302030c030c01050a180503010f050609130f080c16090501050f0406150309080417010207062708030c0d18 73
    0x440d0305100003145035000c1409030b03075511f1b6800b103000c082942c401c021081e0b16030302a0070180b120b880c44c1c0500304054481144c100c41001d45000201c0c0203420300204032000808070380e80c2c20311303c00040340704005ca84d8050011400d20502511510360b0603800440c00d0a0071501c640c130010313600c0d4070f50310515043c11502505580300742c0189412100c1642c226048a4408881c0c0ca0319071a07400414001c80d506550030741000e81c0540c60300d5030340710096007aa4001d42c0900c50481d181d060f42e68032200e1025400c402d04000610f010143d4180348000740340364000e0155504034405030b502c1c5072400441c84081c810154080b125a80d110801001182083c01d02503100740c10030350341070001c18280303815109114842045901095039800541c2c0600025030243e0700544480b001c0080801c0c510f2071158003075044140180e07140b03450045940c40c2d0751582c50b40d42d40758110200e080c0180c9481c07a1200d03c242e0b000280386408100d0104203000c4162100c0c85008885240c01c92811900e4803541012140c20346c618059110 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 76065532 1250 76064282 76064293
    0x18060c0b1302090f0717010e0109060f0b0a0c171c0b0102010c0519111204050a151b02010504090606120b0f0d0f030504090c050a1119030305100807060f08010503 71
    0x1586468125661201c040c01c20a61645c0b01c1a0301260800005000b110a4190507000403c0c10507800401c0d0f0b040780d00c0703480244880c507116407080008a41c0c9229003410040d08200d4040480d0245030003820950103004641c4003000b070583c0104031a804034450300454502d41c2802900c00242d481007001300a030a01c020410700c829044050058441c15401c12002c54810208980d0180708a05200041090100380c03600740b041241c4404440c1c0107030203071030300c0f44c00c20313000104241001004242d5560081d669800714103e8401c10b821415440d0341d41a41004010400450f610556000300001018565a4801d00070001c0391054102e03a0112a403c0c441d5440c000c03500b05030f55490345040c400c160020043c0036042a00c2c82c040c2c1f030f0b80c0f080b03a000382d1070356081c00c0034842c03080d4003d40035110301c000c139480d0f050001042e080b01e40c3c0c885140341d0100b1045030850102c0c1020038030070b5010a50100c440052024000d03191007035149000c0c1c65500c0b0301c00295108003460b02030741d400100e80d40182000e50040c039 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 76066782 1250 76065532 76065571
    0x1a0c0f030301180b060d0c0923060a032a050c1204080d080703020d0501062105010803030a090804090203010e100e040f02060c0a14030d0e070b0702010f18060c0b 71
    0x14150f103521040e218080340c41d4050340d40c0d55981d04088410f41c40000f6800c10404803155030280c10104184207091860071800346910040440d9034112031008001401c0502d40450074009400070901c1c1c0610240d084c031400017810316055000300d0410340100585829440c0c00c000b8201a02c0c04440e220b210541490030f2100300700180000038100303021261402c00600302d83d6180d41c202c00a00468001a4013181800000201a504489145207415861402142c2e42b820249641c090790f41c03c2c0301d481c04992081000401c0324802c2e9004074002840390500c1450159601c2600d410f0fa04207801c40c980b04500c0005100200031143c00751401401c2e02d2a0342100d40c503085d19140101c28110380301030302130300c0f00241306085a081402440032140e4440072415446d03480307401041e9281c0128400711885440c0240c1003440540000c1c2c90011111111400340c03901f402c5c0c5c0c2c01140c0030102512580284843c3c1411074020244c1d07080841c0140205030380b00d0120309128141070401800142c0034030300d00c003030400b00c00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 76068032 1250 76066782 76066799
    0xa2f031b0717070302150a020a030c020102090d0b0601180e06010f020a03021c141c0c05042102010306080d02060709050108040201080f1503010e0109200d060905071a0c0f030301 78
    0x15141c00792402c0d0100c0c0c8404450500f40d04044030040ca1402c8940d00808204d5203481c1f940c00f60070708a1095404010f01a190b480581c00c034803a0031038459008402000f4400000d4203100c01d180d10142c1850032220a21110b00a500440d5181e0801c000d504000c40400c40c6659104841700104030040c8001c2c09148503030740b0080d445002241307034109800c030125940c41c00c46000d9101d01c24030f4940506042d55901c07000a0300c14001c042d00c11046c0b45c8a0801076462030052044094030700b035502d02507260070120344100b1a90300000c200f0030102e052513100c50000070130380300030301000002c4280c58019003514079000c00000d061b803826402060511022405000c00740c3d030700903555580803110201940060302c88020b198003148074011500c1e0705600f00014504240010b4004046892040b100c66034808044403802c0d00203000e100c81260421000386008003c51800d40044180b14080c105980e0100d8079812507004003c4051603440000c01c000030031040d6920700b00403a040e1902c001020318215410b20001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 76069282 1250 76068032 76068053
    0xd1709120a0509040902060409020c0c0a0f09090227011505070b280218010305010506090f09100503010614010809010b03070b07060b0301050f011703090102060a2f031b07 75
    0x21000300a800f00f0301950b00d44a950103003642d141c00401558440d50340350380355000f0354045400040c503801100854074940c1855070040081c0c412101c00340d040301c1d04059400300105900307041681c0c08060500c2c28000100c1141c0f0156040100201c186c1041d8181aa64001001c0007050f03501008020480300001c50b41e003c06141c0c02c03045c054132110a5100c00240c061400088800400c04c852001400748510840811082c03003066007030302e05200aa0381c03401084202d0148103652500725001245245140c500f002109500a10440c0301d60100c41d103850206e401c4440c20b404c41c1c203c0341c80400c035000c119a049580f50b60b0000305030009000d03041426010907141c5103207118101c84100045118400c0041c980c000d200d0705900900208160314007907401c030052100a104580d00c0b611002c1925949841c04070884103240c1042e00100b0b10b07921413282080c01014200c001c1c4410044106038440d40e2001980d4490900e003101036107a80703030f0601c1032041c3d0850b06800407010494508110510008407031000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 76070532 1250 76069282 76069297
    0x10608130c03120e1008060a050105040f15050408060f0f13030c080c030d05090127030203071e08210105010903020f120f0708010e0606090c07020f0a080d170912 71
    0x30f01449802d154105441c502803500d41d6540c042e01c0004c180c03403104d9000d429644658001c58070b0b01c0340703940d96100645e15403017039028014400c04c42c420240f00084242c0c407030700c040103414035003c3d2605996a49441c10722000390b90b0160490303412028800c90a0111100a42103107601000611812860703801900b498a40784005240d20300204215001c0107060003901d001d80c032600d1040c410381c5400c2560b01c2c000d1000d000ca8035001519041752071920408807030003200d00f42c1e0540045140102a03222540244140c8003802601241c038021200001d0540c070250103921410b40d00c62285c1d40b00605800c00e25101600f00b00d0410060140400c00750f40d940200480341d410903074000e01886040c0e41054241504129001b01c5486500c44c0090782a00561110340001c0009007640e5040d20b4020400000c00710a86070304482d40e40910880340540b0380041110001100205003104003503a6901c00d80c2010f41000717003d0003180d580840024030100e412010780e803001c001c10182c40c40100d0428500c02c54000c984 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 76071782 1250 76070532 76070543
    0x6060e06090a0f230f010803030103080d11040f080114010503010e070e0a020c06040311010c050313020105091311090a09020a051611060415020114070f0c020114070506010608130c03 80
    0x10f012400c2400700e6402074126920404a488014002c0405803e28002c1075030800c1c5a0120f40c80001034840002c07040d68180c0798000045840c003480000500058602c504e004000308804002c0001e0034500300d902c40000789501000031801002d00c0c440d510007000168000340c021390401c0040070441c900891408140c40d54000000000d0304c500d00c40c10003c1c001c40c8407500d042c0c86404103120030f06400100d00348415002100034050b400c510074040310b8500055914101000001d0031210042d80960040e1100000181c010814000c2d030a0002007a94200590014a000006000340c40707414a444404040c04091134158508007401038001c00130710403100c00710161602004107804010100c2e00d00820038030028400c58407a0780307500400452001142c054409586040b64500c80c1d5446018100e214410f280c0b20003203000e1020380b06507140c0310410012410000c1160b0103000341d050260180c500c050082004001d2581072820203030501101800c5281c10104400c0d540000540f0401e1041c00c0c0c0b640f19 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 76073032 1250 76071782 76071791
    0x2301080c210405030316030c090501080402120106060807030b0301060503030d0203130515100510170c0405030118050c0105070f0f020105070212100b0a03050714011e090306060e06090a 81
    0x42551004070070100441e00070851654041c0710503c80000041c6020b0842078941204135070b4480700030740031125135180360030109142180804c0950b0283c5030041d40f00f80083d10b6115100075041505084442c0c4d604440f01044108040c07045c59545445010b4032002c06a008000160500001940d2801800082500300b9000800180004004400c0c0413a641e48441116a500e04110606410750400c46040c2c80c0441c1a0800241c0ca10b040200505100e810b030700c829208070150003400030380034401001e0100c80881084009400d86003485003007000c1c4145a990100903100c2e182481c1002e02d406580d9041110a00020303011651220510040b42d0344480c422400100603c01640d8501334400c004e94000300340f6241d000320030000f05400c8440c65200004011520011040145c0c2c1400e0f404090700a40c0304080520101d4002031001404010504104c040c400900c0280350550b403000d03203c00e00044845408000704070307460180310301070407648543d0362892a2440218503031640090540d02040d031913 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 76074282 1250 76073032 76073047
    0x1050303042702120f01060e040605060d0f18050601090e060c030114010905040507080621030703030f0902061b010e010c0c03030f0617030c190b010302011d0901030c2301080c 77
    0x10f0741c1110140b481074010f03600d2500d0a03109840c0c0c0020244110804036400c42d98017142498144501e105503180181801e080c070854403102c0b0000c0003103207041c43c0720699805003480c00c031124000c0b10a580d44107000900d00381d81803e00e00010f6510b24400c01e006603100c8402d0280780c4841c01e06480c1514900030280e2610800c480040703803202d1a40d0721580e0030a01c1c000510102d00c0c4d103c0e42e12441b50005642e001c0a102035551040304041c1d582184600c9a0018450308000034403e820141c0c82c07800d40798022a43c11842d40000310380f68060807070070700d100d0041200c40a02840a000381501c004841000700088441210007170010280c2038801010159504110003203030711158000030107005001c07840c2c1c00b0b0202114505076240e1154402c0c04041c030440200c0500307030302c502c40d40306845a4421403910321a46140d00550b01200907400038000e100800000892a440341c40016009501650b0080d13032007071409445060006221202c289074080341280b4041d181d130080c01264210f402a9030b04c075511987d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 76075532 1250 76074282 76074359
    0x1060923061002120313050c0a0612180203010507050c210301061115150a09060f03110d05101508030c06160c0512040e010605032503110a03050106080105030304 71
    0x104d040b4074202600040309004002c6150040200c03414828400c6451040700c940821000700307118070940002030365616548903906c2ea65003080040c40a001d00b40490b015081d0700003030039180300700c41902c0003031001709066000d81003c120180558070707081545614128030403201d88852205005007418065600c8003240c0c680c01c1040184030301800071213a1b50082c184003201c0c541141800c8222441002000301c04034045803680300745800c81340d1220000c20f82a140d5950034100070281d4191130f902201404001c40410424084500104504140040e10480440640c4400070702030304125244e03130003440080310075000050810f4210581241d54042508003990031162070b584810018058080e0304150b09103401140f000d802500d90b1040b041c0526a00d854081300d01c0d00045590381c00c1c8441142e500401002c41c2a440c200d1180c80780b401003441070025156101641c00128100002655007004020040d07010b5286030140104501031441c051503c02580b00c40801075007a069171030b141503540404c094 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 76076782 1250 76075532 76075543
    0x2010c0c1205070302090a1103010302040908041208040f0b030f1317040902070b07050702180402010e040e0d0908010b0f010315090c0504060906021203040b06010c08030901060923061002 82
    0x8289071014100c0203881ca801c1d510703509540301c128001d01900c00407403540050f5001d00081200c0ca00245402c50307181d9001c010103042c0640f4107542c5600c0400010038034482c444200107240c1d0003074107000e83d1545042e0304a00400320710740c010f1240103001e10501000309002e8a0b20b64100c100c0c86406040884642010145040207071460850601d00080000c0ea01c42c180c1c015281f158050f01000009a842c40001d9400c2e10800138000d42c07040214a0000c1d204011104040d0414010314103035807034115400204040740e0300c0500c283c103181d201d03a6010414951016414015102d01e400070300c101e002e0324000c00c1c2c46a1040703c806048c1a12881c00464500741e00642c503000300341e04841480325480054020b000365000f40100c074009140200045416800040c1c0342c40f110a460310550710715601c0ea11880240d01c009401c160410403546032076401f04401c98051800703403240c44000581e107460f011000c3c00b16150350803c0303420f05101c80c044000d04440c507482c540d4411020b5850050349400700e84100d00b0309 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 76078032 1250 76076782 76076789
    0x110d0c020d052a0a0f0303080402090405010b040504060209130b060d0b0d0510050403080c03090303040803071112040816030506060d02030a0f03020615120619060801020705010c170c040302010c0c 86
    0x250070001000081883d07020000410107580d03201c0400e45401108000c41ca2500024000c40d0744030000c00e0041c140444203590242c080c600000300c511715000000c050320740541d01a41d2a58012500b0450391a11100c214030842285a0803c900d1800c00041602405070301c104050b070541e100038542807500e601494814456005055403030b41103245108800510081d101a00020301c0d0400150804074103808507402000407200460840c0e0740e40d17413208a43d9100030004800c00c0388a1b0103583c0d200383c0820840d501440112400c50f1900e052a05a9103400c0d501100a003a0703840c5144208041000400e000e500154161080e0300681a9400481d141044a85004005626014180c020b01d6408110306005170703600c00c0515007a10714082000a40f19680758080c41a82094021031140c0c400450124005842c5050100e40c6943e134003015030032a040010180c0300f42e5120242c4008c3c0951100300c00074400c5000741c24a8890910011480312030040cbd00009050044004041c002d100f03a580c000b00c011f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 76079138 1106 76078032 76078063
    0x61f0807120f02040b1f02190309180618020c010f02070b0703051503010c02010218030f030706020a0e090106021e0f0a0b040204060806010e07110d0c020d05 69
    0x154241d140300f00c0e413040d5103228030f890507180c420040034007280f003039214002008240c1019003801080e4103001030207a1f40c001444002500881d218003075a8200c80071f103200440117250b0700010030103030700b00c101001c120600d0b00e1909101500200350440e0428001c0c001c402818000340140e000381e04000b00001008000110020b00c6036025a922a4a01d400410001c90b60008079084a90340c0c0385010041c1d40028601030f40d008601c2d81c5889021096004000744698520200d4603802808002003032160002110f0745a80c0c450411002c000d03000401300748940d60342c0d52000c0d41c1c452102c032040002c02c510240340da007940001300b07035061140d803014060180c2202f40d5640d010501d03c020070480e40f060341ca100200342d0110030000d5a01901c5410045030150400c1180941443c41411901d00558800c000b40c10b0956031107894410303181e5040d50406481299442d00d1420b01a090f042101ca = true := by decide +kernel

theorem cover : BRFrame.Cov 75899282 76079138 := by
  have h0 := BRFrame.cov_init 75899282
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75899282 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 75899282 ≤ n) (h2 : n < 76079138) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
