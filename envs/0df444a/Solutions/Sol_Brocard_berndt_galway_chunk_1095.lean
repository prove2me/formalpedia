-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1095
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:13:13.726746+00:00
-- url     : https://prove2.me/submissions/80caa598-f3ba-4ffe-ad2a-e959609ab231

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 196762589 ≤ n < 196942446 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 196763839 1250 196762589 196762591
    0x906090a02120f01110307030c0e031b06130603020c0f030309061803071209151b02010315080a050604020913021011010e011121010308030f100302060d0b150909 71
    0x20340301e0020400e080c201140c041c04499443c8003414001c1c081d2400000c440e24a5600550300840002d18200f400303489544116880f40084000802030a25440300000d5220b200340c02c50f0720f003a441101084503030700c802c3d5240f1b400300040802d624050786808241c0e8090303007495610f440403031003500300300308000380030801240340c030b17804400f607900e450b0a61600421189940907a07407004107000580c030744031000507030000d00000499007082c001d102056007042e802ca070601c105010140e101465108080010341c002c1e0045900c08600202c5013800c40d90301c0d22024600004520b09a0b02074009400780000d42c01d108a11b981d000c41000d00c0120241016800f04240e40707d103807070407010840030600401032001300303402c004200140000203000e402d01900c01c80899034409600d007682d9522070812640d90710f0100c07824504803900030000c5419035454006141c030000004002c0310104006010100060b510103000c0d020304283c0c5100003e800001d4010300107400c0014400d1852040d090140c80e48070f9960071005 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 196765089 1250 196763839 196763843
    0x150b0f031c1b11090a091b0807050303070803011406090a14011706010c02010e0415030c0810111803030f0403080705060105030118030e041409060a15120210020a02150405090906090a 80
    0x584c2d40c0c0c0d16200703104000c00500b10024181c4030200b40c0c25410303110001c2c280d016581c056040d0390380b081d911010142d881c03050328002030583d02c051004101288040300304a2204001800852415502c3c00001c0c80084e03150f001210070b4803400000080b99640308a84508010744100e0b88480e609107100081c28282001c80024100102c80c11605215122a007040c030280c070340c410310008541c1d200d18080c0005003c900854015100f01d28035014115424051182545004c0400a1400d91040c406800380d2074036522880e0903100c100000703a800041040104002c5014030010b50b100d490600d03080d0b06250b01070340507520984c1880c01c48590030b0041c0000412042d03140c200f410b60140b440340400c0207000006030442059081c2810070505030000f00b1290301c18600c44404000390755400503101c01e000d8030f60184180140d044581c00e0018108102c0e000c1c2d100c0100e00465002c81d105900003041c4481070100004018008a010002d17810301a000d44d070029034007130180681b4034089a109540c0d090007080 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 196766339 1250 196765089 196765099
    0xa0f03061d060d060c09030639050f0f04060e0102010b01080c0918181005091914011b0228110604090c0201020a0806010c150b0f031c1b11 61
    0x81400380c1c3c2c03030400003030340503a01150500584c1d00518000d40b0041c0303280b0081e500f42d0304219030a008540ca0441c1c40281000d090a04042d8030311107000c0c002c00e8002890400103000041103048094405040036284901036205404d58503420410010099101c00080c0c50540e0304002603086640c1c5c20100403544020042d103900d4480810000003082c00704203204148841c025441440013044242001c1602e04461204803101c201d01038041000701d0700115012112900040c124016a8041e0304421000074011203650401c03503503555440f800c40da100d00d0110030801100d10519402c54062085400088125814004a00b060014205900d4401e180200b4042407075891003041d641d80c405550262103410b40400c60880b07804030190003540702241d2940862007801c0000e05a41c850408550040d62002d041c00007420910a58070140c040800c40365406450780b40c204025407020400d07060030046038503e8034041044610701600710700100c0d1800c084402065500c00103d01aa41810035030201590 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 196767589 1250 196766339 196766341
    0x50306011202040e060117070c0f020a0e070c06050a0b22020c06070c02040b0409020f0103090c051216080604080f030705090603010b03070306060305240307030602030c0a0f03061d 79
    0x200481d460035000c00548262403020401254859405031228842c1000381c95403114611007803550a50b131041141d02200080d200d05400c0d000841c0d084a05d603000d07101414408440741c41e03d83d80112054112003100008a000c1601401c2c004280502601b0060964040040c030201201090380c041c08201c442000e111021441268101b41d941240c2117149004180c90071824280d2004003004041a0142d200300c2c1010b2154a0a141070300c982c400d0a5802400a0609865035006402810700080f00f6590714040354000111601c032240400c1c0701504140103010111901d9410b0400e240090700400c0d0264051070410000604000803202d8881d0713101070240c0c8035518a802180c07035110b0205d0a0f82c10210200000408041c0302c006140101210380b0140100307074644000706c0c00ca03802281c2c0400040c890481010100c031706226154400c071006000e85c0c00054036600c0d420181da0080d10219081d0700e0010f901c030802030340050f40c0c6040800c60710b404e101141c0f42c00241d00424516013801807917403010780 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 196768839 1250 196767589 196767601
    0xf0603090a0b0702060414010b0f040e010b0a080f0601080106060f0804052b0206090c2409041104030b07110706050c0f0a0624030f03030b22090c0905090c010503 71
    0x84110006503110400070302901d0541d40c025105c83c82550700b02c40741e041d84c44034413201650600864441c0540030b49440c146008000401000e8104195a08669561140095215100c14403520098000d07100200b03621500c0d400c07680d02c0c0080591020400d40d2411b001400020303400304c10091180c990f850301040301c1c0c0f12810800d090040c14020180110815500728000340401021410002c680340c00ba91003030b50380d810a2903204c82913a240286c2c4180100030704042d1512441000380c030320102c850824180440540070608031101c0700407070480f0100108040080180d0300340c80f10303030000052510012881171548a04c6e0340d100c160042405000c000326090100210402a80c0002603d000480b4050010b60034058010940c140c441818013198440e203511009140000504070303071b401901043d21032481d0310118014002000c3c01c6034003034034921840d02c02000b40602101c040340300e42d50024901c5003030300d0302c2306001c80ca40d4441010b1a04007010045130341c001141d01b54080c0402c4c20460780c0d941d946 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 196770089 1250 196768839 196768843
    0x1b0c05060912240c03131722030c0803070b24060a030c02060105030c03370606060f030c020a1106040b0d022d0d020a090909110108150f060309 63
    0x100310403881032094003468804555261041001a400582200c40d142c840d040306450b41c1c441211003011a000b5224000002010000050000c0307580f40c00c15030400c01c1c0000240301c48101140c9140c096164070301c09005001c401c100700c0e40105402002149006180e63b6401040000240039801071a03800340c604401c94090152003100901c01040c0b1aa100344070400900200000c50700e410052041d0740010903e402d0008492a103801c0c02002010b00c1034568001206111103110700f005a242080e8034412118504c0100304041441401d004c1402424030074010480001140004101410b05601518180d0041040b42860381c10000300c084079245c20002c22410b218030b900545000b41d00080a80c0000219400b50281ea2010741c810341c841540b1841c00364103502004901000780804205503050150150300a0802d2401801e0100355a5034580c00302003120a500e0095a030b0383e01303504a50301c05690024200364070054162140d586401030401055445408030320640c010900040818031940b02 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 196771339 1250 196770089 196770109
    0x40f0b0603010605091e07030506030c12030d05042103050f04140f030f07050f070302010503010b280905010e09010e0105010f0e031e06010f030314160501140105011b0c050609 77
    0x800b1708054018240b524880404108050841c802c50848030049902d09200e03024041c042e000080042846030f40c0d090070460541c02508484050303110410030301c210201c140c05002d200360301401c2c0b4080f441d2940d044181c00e1a009a00c1181010302d04410003401c07a84143c0c5003600903030031080b541000d081560915207840803202c0d14030280e2002185c3c01c0381c2e210880340107005c102c0c0300710142c600302601e40e007103140e840c0700500009011403001e00042c0f080855240281c03042c441e4031121151050410702142c41d42c00d1600210780300282030503505003c41c0d40c005001000c20341f07003034512190b190705d850742c0102120380602415040090b11010010380e05c1c4240e0cc107041101004092701c880c052804c40610322200002d40e8503c6902030b4a0001a58001200f944070489806448120108803500c04000e130700c1e1301249461000010b032408040104800344601c0f2039403050040214074a506040000d425143c02c480c440d501c1071401404000000c54094105045917010340c0d0341030315a604c0c00c1c0000c80c0841 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 196772589 1250 196771339 196771349
    0xd0b060d09080c0d080405191a04060f0b030a030e010f0320030403030506031501050d1e12030b0d0510111b010204030618051b0103020f0a03050103021206040f0b06030106 75
    0x1c280754084040c060388100402035a032858048800060410000759001e8108460141081c2c020302042401310b80c1041003100d16900c03400100c0c1d03107240c1040354841024001d65086d200180e40345890400320516104108208030100e000340300c10703003c60754000c1501225080d0241000000141038520754000c0d0041004c01e00d81c206104060140c0c4949980681c004450590029007450041440e80c00c0105400f0b108802c0620030480c00c0c1e00f00000d02403502507003036003160303020354035151440000b51071400300408030700c140c1c0c244080c1000c010303004082c0d03152002800d100b004d072110103000140c4001940b80e19401c1140e8089106d088144642c0a207002d83c80e841c03100700707416403040c0c5a00401076000308181ea108080801c9811443d010704089183e00340401422a4002c4c0342602480e8002c110304400070205250140c034190041e0301381d400c81d8002540391400700b030f2200c0c0144110300e0485000c6041c0030440004100525050f00c030604401c144a1000d0840c0c03007581c1c082101500d082d000800600 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 196773839 1250 196772589 196772591
    0x50c030f070b0106030c050f0a0c061803020c091003060b03030c0307030c0c06080c040e15040f0c12020c0d18050a0e01051f0e011107150c0212010203010b0d0b060d 72
    0x652032048000055011650031038402410310000304065020744113070030b00301055a41d00b0342040c00f903030401515036005072081c00502200740003075000140c15004108150444607404160004c81b0302c0c010703240000c000f4207148107140c81c50030040c051900c07100d901c0850360080c0b00400c1400703605000c00c3c11407081071882c035018000000c0c49d00525420007504a1160b00c0b5200005001e0742c3c5100440f2040710907503000c000c05a00300300c2048100b550700382c0303141c010015040250043c03041a001400b1500c1c400c07603080e0078640301d15100b00c55940211038119041e442030030951510480c190110f0300d504480b0009014810201c82050070341825185240203024003603d080d1000c5e8542c44001c02216091041c24415007545508561150341d0043c41140b07140e003516030381014202030005494540d044010400f080c8504400007809644145500e8101c0c640d90321803800c0000280140644c000c107040048005030300410040104d1000d1104a6141000070392000910001ca4000100540b28182d1304441003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 196775089 1250 196773839 196773847
    0x908040303020706020f010b0d060507120926070b13150203070201050a1d0703020f0f040f0c02011104030b0c07060e010c080105010e18180102040b1215040608060402010c03050c03 79
    0x1d0b400041e44030a580450302150500900c0049282c03c0e101190311070754010f03050001450000300c00703801041e040308041c00c11007028000001d43d141124856030083d90349012034a03c11300440c0350888643c03008102029071525105d120b4842042c9944d014041100440f80d485501042c41f12a040445034086144025552030400e07080003800b8103c152041d5074041d207040c910701e80c2000c1e20f00d82240b81626120140070120700d542c0030080403090f9100c11a0300841c07192210301c9165545e00c144d000c00800588005840c1d2490000282114030b04400303155403180c204020300c08200d00c03a11056001c04040b0030380303940381c800707143c080007410420f9814841c1d582404008000780750440c1100d8140c60003a030f12840c0340300c01501005082110a841c0e2000c0107540008070b40319550041145501c401e082c2c0000d0704c4e040da1f0782c0d14050140c1c00818003200001d81e403000d002d00c81070107000541500000f00c400740031990804030000d4544101800c000c2c14822400c08600c2010702800c19551741c0c07001d8000b502d840d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 196776339 1250 196775089 196775093
    0xb06030709050f060a0c06050a020d0606020a0c050108010f0312020a080a0c0203062d09011104081005010f061e1701080a0302120f1e040b04060905030606030c1f0309080403 76
    0x100300714038011148a4900d8400700d44080c01c007082540e01d12120303a6a038460441c8141c035484001c01020307040d80c0d803646d000c0205034403014807406084020000780c1d00070310038a001070a01d050b40d02e585800c135504101e07541004104030f00c0f8928100c0c058a82000c200c040c07654040100703903e40124680003c001841c00300d48008001d0b0488500001c41f40241c0c2550241e85d10705865504005c0180c1c080150607001119490101400d5020030313601030000000060855145800c0464a420550190a01e40d010740008100c04450b4054140140321991074400c0c01800d203036020300201540d407405c15002c040d01188407031207845440a00b1441d0389003030091219585408489072620790301074068000d88501900244060240d6003129900300000c1c21840c28000701103003101d000c6454413419111358bc4107010110303120614600400080c4450f0711003005651410090609020008040c0e912980203001080703610341366200001c3c41a00542204600301201d41c074241c004040d66503028128010100e80401 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 196777589 1250 196776339 196776347
    0xa02070f0b0703081302031c020709050f160f020712080909070816050310050108040311010509060a1109030d050c0f01050411011106072102040b1602090106020109020604180b060307 80
    0x2c041400f940d034180c1030780d40e40710540c0c540280100009400da401852015280704041d5802d07091000144107076030b00b1552710b40d9034a05542042d500644002418024050458120030108103840b005083c5a1103032044048069140c8080e840740445410114100200f0405620115082402c00802902d60303401e01c00002400c110046070303105130400200c910b40c0021ba000d03805a81c41040c500c0507d45000381030200466000402030011010b01c86c0c43d0141c0c0751144800c0c041e481c890345042004289510b04440c203102980c4502c0280f01000b0410054050551070200e0714621100407401d1007a0360f10708100c01c1a24001445a50700100d52902c01070200300708501c83c400e1b5040c90240d0b20340c1d0715400401c078120b49406040c0c039143d0226444007500006800a584240e58100d000f01c40107003069130307a1140c0c61003a4031401c07003101c0c002c7c4000d00040852503e9103500d07001d00143d03c020440b03418107602140300384c840c5020f02070b0325142540204040000ca5042030b0040e020203031a9170b880c2c0c20720710344c054 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 196778839 1250 196777589 196777597
    0x603120f031109030309060c0a0f030c0302070501090e071d0315042109030f0503040905090f01060902031513060306020708130506070f02190f0b07110409050d050a02070f0b 76
    0x303401c0441c0302c0001202c0c0416104500002005103140043d40010414160710681c00c6801c140a000e42e502c0228281040c00c400460290300c60340c5c00c540c018035009040c0049038004605000e0155020310204505861090b440007030750a002101041c0a00348025265411101c10b52500c42c1c1d01e8006d000300030700b50034a40280d10400354200c40245084000031002d810700100000141d201074204003040900014010f0380f400351080d280307400d440da48120300341c0340112000401a8001070784108900c409214000040c41501411819400c0c0500500001e41e400e0300810720484911145140354206070744008000c65004c41c04668139509460800855080b02c54080c9641c0140e10340060b031030414804035954107510081040070701c0c1c130031382c03c0190021010000381107400c0c03104004203038000401c2d95130000c0c20509000c142c403601d5500c1c05510108101e0340c01d03401641400b248000017100010b104440d004141082612000020030482c075000d5960b0203e0145581802c3c002107401c0420014 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 196780089 1250 196778839 196778867
    0x804052a04110906070209040305040305060f04030e01020a050d0c03170a0603031806080406020304240e0106050a0e01050603070219080904050a05100b181201060617010e01030303020904060312 85
    0x5001d80850b0b030410705801d01401868a41100b0104210001450408803a80d40f05220342840c5040c40e840f501d40f81c1c584030080702c1e8a076100300320809000a060b0030100d0400650800d2004041c1007036203590f01c075101c0004032a581c0621003104031610415019516640c00d290401d8004549031038040b0000000d0b107550300c8154042600d0074603040b1420510b280a8098511580fa882c410f900c9aa0b182d20095000410555000d03c1000d121450802c180450700c503a00201c00d00031600309500001d050031250030307030310041c42003032005c0081002c01d4080307010740d0444004031a8603440b03681e00f89080e428001160080c2c00c0c5480d900000408108a1501070000c5980913582000a60b41300301e941002c481d0141c4844c1040b11440c4810401012490010a00201040f001d200f4400300c81005c04e000c640c2ca07280164150b51901c40034000654003581011070180201784810242d450400c2d00000c60806000240c01c140d000a000d042c5c03034480d03801c100002d5600c000803403200079200d01d00419800f070f40711030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 196781339 1250 196780089 196780091
    0x30901061406310305030a120e0109051e0a0b100f1401120b030c03010c03050a050c0a0807080a110c1e0106050319060603081b071a07030804052a04 65
    0x4840c505040442c00c2c0c0b1528040780f40110842c103a01a0a840b0300714010b0604021007103d10360110000b481440900500c003400e8840303000342c61650a802041e1201c80039028602e80c5407031150b03400300314006031205d02400348014848007201ca03240b60505040440001901580912080c0307c10f241c2074005807000c40300020801400c10ba1283d503844032080000d004507000034a021040b0910103400c0d4000810403074010100c2d8141c14124000c039085da008514201c012030364400c20400b4176111030003402d0b03100c00700008051a02074203500103030a003000a8281340400000c0c000003a00712403a90b00c40030300000308005207910b901400720f01d1942d40310780806190000007942400001d5000500600c2c06840c0c00401502c030031081d400c0c1703043c485501150195480c9440d000c000011420306401840c0800f4030030000740080148a005528001027a03014400104540e004603461400041c16264a40e5241c0740026a9450b1410200d15058a40c90a61108116940c4074900d04d103500108810000040e50 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 196782589 1250 196781339 196781369
    0x1404060e0105010e040803060d060c0201060303020c0a060203030c0d0e15062719021c0209031c12020a030207050d05040512070f0b13080f0a020112090c03080a0e03010203090106 78
    0xc200e40c280c41081c419050510001404500007482c0c000c01b45900000140180c508039031542c54038001d9801300d826a101603552030384240145941484180e2003c4803e50b20b149800380b6003a0029520b01c802420060110300c04248100c0228440e040f0b80440000003040703e00164001079071900e003001c1980c0e524132800504104001c100b1f0502c4180c801c4085144041c0100e90714003005489006015039043e08043d401c0140078458240c006407c80d4188130745c800161222041400d251034018010174010942401d1052481d220b6401031045040c24079110001d81c442c401c485050b4081c1c02004e000400501561240e0b0700b8296102c07001d0400c58208031070912243e008664481d446403414001d040c42c044101006010f614200c400405040c0303079481c0c9104606548140340c0b8100490032010030410307000490060255a4003000c81e40581c50051000c000211650ba28004c03a03200c64030004041001c00f01c2c1c0c000000340102444074031104042c0c020f655a2500c8040e05000786424041d02d264040140 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 196783839 1250 196782589 196782611
    0x121a01060201062c010e0c040e0f04060c1106070c0305090607030309020a050607050a020d0512070602031b0423190905040203060901020306011b021903030513080f0a080f0403020301140406 83
    0xc50406209116162504c56400e143c5800543c0d00c00500c0d03a2003146041000140c0104008103141c407400e0700d070b228250a03040510341401901c000d90109400c11800c03c0d60031007003120108960350000b80d1401c1c0382280d6036103442c09a80500480c460103a100313801240318001d241d0540c000c8507400f4421620001c116868800300003450180c0000507104c2c0d408020000b00501780680c0303e5100324004c000f1601000410b4010003003943c024801114019004014410201a44080051040d105610890409040c203a610060940707100c100c0d41402a680c000d800952220850051954445000310030040e45403000307078000d0081683c04030700a105100001d0142a0103100b960700075841652003054154141594034040041c0f19000c1e41d128454041d00c03850121100e031100000c500c0313070701d1315601c41104801070841c5101071380c46003141da04002015008140040384d0040c0366640114100d459064040c6070040074040ca41009406600c0c219000008404440140307208521075401481048502 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 196785089 1250 196783839 196783889
    0xd03060f0513020c0328020a11040515042d022511060d09030806030d02030307140d0e070f1205060105011b0f0308010f050910121a0106020106 63
    0x19120300301444003454000e1103540352400302d02c40901011800903080012085402c0e0075644009481450080c1998010385404968068800d07040e0f00e900262074423000d81c1c0c40b03503020280c000300c00314851580c070000030310036600c0c441a004107001c010307104125029422031805c0d030003075020721481c0310f6100480c80030081d00074600807604600103008a100703140d0f101c08600302c00844c4044040f142d00045100d00000d0f0b4a8510180104100d00100422240303500d05015050700310241041e802900310420741d862483c4c00008903904600c02d071405010010410031120024014407110305c0400c5e0070160700b2142543d00050f0079056448514071000102d0b41c4103001924818140d600404076040400100515805104a2803520406c25000f401614103961402d000c2c1e005d8800480c082112a001400308040000518000e4202981c40c20080d041022046181c00603601c950302003002c240400a08012606d5441845101d01614400255071180c4000c0e000e403019028032000b0903007611301c1d41c881c0d50700 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 196786339 1250 196785089 196785101
    0xf101401080d03180501111801110c19030f0501050109050105120a080a050706050f0f06040905071703070803090c0906042d06050303040801020d142401090e180d03 72
    0x2074100245410707040c018080c0d01a00700000301c0c02d90100c21426403404a4001e006403240d030220803032103642d180e061400a0014002c40c00010303041005c459540c0208074800a440e41140038102c82c800c1812071400103804c0306180e10f8200400c60000f81e140c1204001e01500b0803416544c4903074052000f03a807030f0b4007030100407080138200804a41c000380c440000701c1d02c504000c140311811890810315000e8180c4404c8195801035a0864000b41520100b06c09a103030f01095940081007101c081c002403e844d20360310f503160300902410210715040f20300c1030712503d003c0007120311150340444102d48a2a08608440e12032a40c003110030701600301100055417a1416100384034508403003e0880940141c150024510380790030124580d50289e03034080101c3d1980e001c0014100920f01c4e10000b590742ca80350100403003a03800015aa101101d803440501084074031b00582001c015604802e41d0304100c11140040310104401d03400750703102840d404144150201c0e013840c8100c4d080920002c495285c01072400c21001c1300c02e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 196787589 1250 196786339 196786349
    0x203030d050c04120818060a05180609030d1e0203090d120309020402180102120f090d11040501090e0d0c0b1b0d020307020a031403010b0a0507050f0f101401 69
    0x400c0340000040d5507030301c5a034110380d03001c400909058544903920030410994000303030f82d402d601042c0308200308880504074181d42019a401c905004000c04050403034012080c1c4240c0018901900c07181c3c6894041c241d07900500018103c4080039103d81015081141c90070407400c2108d00408000f1807103000100f2a0015080a42609240003e58445038011540a00388908050311052800c000d0380d594009003007030440740f19240144032400000039203020000c0c84000900e060600451040181c18826150b81c80002d403044504c0081501e0400b840d1141d0903490b0398041e241500200d072082e4690300031401e94a054044801000300000c003510034107c4540000d181d100b0440026100c894416000031880c00c00c00504d9080901d4000c0c07100585e04100da05a005030b2110302d00ea02415030140640d251401092801441d550401d00940540d12a85044c04c050100002d0814100801000000c0c2701d42c1801065601000380410155180d00300100aa4100e60401c0d003500080e40502c08400e040350 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 196788839 1250 196787589 196787593
    0x1801020c0d0e0d0c030305030709060206190c090f0909030f0507110111030405061b0105060a181a03060f06090702030a1b080724060e060612091c030203040515040203 73
    0x950301e407200700c4260016102241c0c2210140c00064002445401c0e0040510711a891b450b8891502110040001c6c540780d2084007194841e078180b120b8001400d2443c0605400742e40003040740e403210399050b504d08601d5404041c42004a44e00007a803041c5070781c41500007d11960302d015400b18190360841d042d024280b0b0240c00c6d82e20000b07004000c4e42c000c3c0940000c904811041e60700303203642c4400281143e08040f03950f80503455600081c5182540030700c2541d5010008441070f00a03241040c4032080124491480720f401c042d910f9102c04040c40040116882a100c01400c0342c21501d400747c03400b8080c01d400d64030a0b010b03921350350102d4882400030098800700415660b03100540100c0d2020440e82d184000740c1034403010010020782c40855607003544140314030400411001001383c2c802c03001045540d44d074041a4680c030894103222842d51818107c441206e54122125400d88880490a00305035030341c00e03d10ba080001c006e48404983e050b03009148a0b500036015070312040d0952034008060541110003d6043d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 196790089 1250 196788839 196788853
    0xa08220b030f07030e0109030306080706020a030c0303050601050d0912030506010e063702060117070e0109330e0108010b0a060804080903010504241a01030b0f060f031801020c 77
    0x90380c034119443d0f40859140350116080151008a600b1280c0c6400c2c1940002d4a4540074801c6500c108010710003040c40e40700503c030400090b10028002c0320080401800c0580300d41c0480d98903841002601c800300d032640405c01c41c4800500d80894140781501604021038281000550746600420f4440c107220300141181d441c0007401140c007404401d0322030702d9030070420aa40c500c45042006800a42e1401c0d0f5503001800306504040034a0269201c203529054694001c200900101401c680940e044400c4280d02290f208001c0b84101c0c60b441c1c11803100c1e0303440c1002a400c11a081560781c00c0b0f1007112010840c01d0380f181d27218249203080e109074902c2c5c0390f081131040c00304001e043d02c158501d80e4071a0150315440d04102009000a0a4130070580301504c1c4048068402d101c100031408165141001c1000104164a10004140044d0340b014106505050741c503c82d140003a01c0d401c0c002030043d00f00410355607a40e411500c402005800070358043d0a1090329002c08418503034140308865aa800d103400134420 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 196791339 1250 196790089 196790101
    0x20c0108101413020d02070515060604030b1e042f03030708090a180c03050c030f0f07020304030803010b04060e011107050d02040e0f01052202151b0a08220b03 70
    0x1420b950640c1c80e80d0000c3c2c1c10295000b880d0802c0c4040d000d6041c80c1c0e070000d41c0c1c82c0001c0c00c2080c41c103501500c0c001d810400482c14404141d82d00e0045401b2170307134807003801401a42c441d5841e8521402141da40c100c01c0888404207c10802e0700c0b03084209441d825060140d4035040e0180c5100019072009a6030303059402000910042641a805000e0403203009040c00038050b1500c0442c40c0d0072802000c1148016228420030761465050701805038054840007a150031464555081040350201503c3e405c6d00c0300340c1901144807603109004440c0510342181d9561f580356511304c3c040320298001d12940c0c0003e105102e4a90803903104404400c1e04030304d040000d00b000303421311082003c460b01501e01203910a90360680741d0b05440060004804e44030400c00002214a0184e41c4026034540070b0b500d00440e580e400340b180006a94032030b035580403107841175003103522030072880080a00000340b110120350910900880004101d06040140504400c444e28030429090700913580c0b404c01203502500410030340070700c00940 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 196792589 1250 196791339 196791359
    0x5070617040b09031c02090117091e100207140c040204060203030a0f0207020904030309031d0a0603021305031c1205150d020a0306110403020a05100e010513180507020c010810 77
    0x504482d1503c103491410745580040744401440240150b00b43c2c3d00072806082642c4c1041c221b2603c2d000c0c185c5c0c0403c1c0c80ca0129a499140d0141e060130f000030403048605803441d070fa41041020000001c81a04644c1c558007400d01d07500034110380c100c0c14114424042c2018041c1042c1c02a00d080b82c11940041d401c41e124843c030100640b040245086a0b690709006000241c0c0e504080c940c011030090b00d0000d5020918180101102203d01d00d182401c0d851042c0320810f034440d50300a004071a002d143c010b849604140c04400102d2040d0322580d8140b04290800c0410501409615200441c1d0b80b6200940303192103d1560583d0811900d00509100d00e41d024881400e140b044015071903c010000b0b18071503126540d41c011100c030040c1d12a80740350045410300450030b0844c00710003c0e0500b05c60000d80510401001007941000541a80c10482d000c240c1c10326808441c03543c0b00c054054080418200348420300201c0c01000b0840701c06005114440c400e852950044950f103004180d003009815090b41414180a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 196793839 1250 196792589 196792591
    0x80a020321070516050f0d080a0e01090503010204060f08160c11120f060109200a05130902031302010323010603150902030114030f070b03010e070314040f05070617040b 74
    0x41c1051800c100380e800082c0c0520207070118440b0642484074840c200410320094044d0405000d004140f101705040c003040d01c4405842d001351036881c015801070aa0030040317480c140c440c0e01ca16055030001c41c000c20040c1c0c22001844c84041e139540c030010199254454804101e51140d100030129040a1000020510612402d20701d0900908400031212142d800c107803804e0540d814901554000b04014007224015015440c180200c4070048000710341010103a4401c4d104035800b040500800003400200d208c80410220024940c0943c119228134105203402e090103000711080b130029150175401103219511821542c1d540410100b0341846a003804000c0c1c0040422400000c501c01c03041c04001000001c1e800218080c00c03030980d94400044114040c9803428a0006c1c0500807900207103c244520075207441aa03045905c804003800b071a4803014400e1300103080841280c0b04040d500c00401040c0322180711485215031040702100c20340c40e41c4035022540121580c2000890101c0d4002084c0401c006107585 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 196795089 1250 196793839 196793893
    0x31e01030c0b0d1d15090f1009140a06020403060605060c0c0108060f0316051207080a06020d0b0d03031407030c0f0806041b0c03021b060409090302100204090b0307080a0203 76
    0x14607144001561400e503428144608110380c8424005e41ca0300c03040c5d51844d40c00950302001402c03071450048038285c480002980c0c0e26842e580d5202204240003503444907000d1110680186d0b0061021414400d0196005001c2070b541c05040050007d01424175030200e4075062101800b40c16018004401180c1680019101c15804040420203e00c0d580d414850315a00c00d00c54040000103070715183c1800524030f40d0b101400c1441c1c02c1500d041154040106005440355401000160340d1041c240c1c0a4005001c40840a60442e03440340c542d40c10107425a00c84113412192840d01401c0755104a400c605032100344040c0b100059001111141407405421980d4100708000c00215074440d000e0903000801300040c40c41c000040c03d01035403074145601030104062400c100550210503250707000119010f40b15600c10700707500d00e5941b001c00b01458401e105400048e2100103095540e81c1d83c410303103c4c018001089640d0f10134002c540700080e0002001a4600c030856014000c1d20a98013640038000c2c107a650b2480f9 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 196796339 1250 196795089 196795091
    0xc0e10050a0608040f060e1b0405070c02090a0906061517070509061e0a0302070201110109170a11101508070e0a320f07020a0f0b0a02160503031e01030c0b0d 69
    0xc40170004107940240f41c6403031600f0000704080c4d8100700e0116820200811458000d610381010b21410359444003140302d0b015010354007034006d9111401c240b00100718018014180d039140600c040341962407d075000440482c180e4800c0030307501ca41200c0c421103000984080010030b00c1001310950340d0400001408403601c8800c0308100c800c00b040b982c100c60741c3c0302c00f40b510000303640020903008540c0c11050150b5407070350400003040003020356690850b00d40b055640e420030300c003000304007141c1c203c0c0b0540c601c2203580c030f071542500c00030010f921b1118040c0060807171040c100b41d501d100c00318800784001f03460001caa203030b8103d050003a120040c9010007072803a05880003034283e43e0f6550220300c0c00f02059038856405040312011591500942880494901400140454000c00880740108042c0c2038190240d94120007000c00c40d44030000294024840d84800b0784003244610007007030912034040059407050480345440e0829a0a150290b090601309001c01460000064000d0003140403050180c000d2025444c4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 196797589 1250 196796339 196796363
    0x18072003090d12031503110f04020c0d09060201052a07020a0515070b070906080a0506031905010f0c0509010f1d0904080306010f02010c36030c0e10050a060804 70
    0x10500d40305240000343c8003019000d008610380d9502d44079900199420384c2011801a0450380c400014807055000c45104100344400c00f0450f07916070f811030b0407a0b0088030840e8541c0803036900191010010303203e4540554a0107000070743da04370740c461060100ca180c44a4050b0310103c22000b0025410420082c1c2c0c016071004000702d035644440c507840c0c040351014001c4036124089481c1c1003c210710300421410410000a00800440d5000b40d01a6002507c03010042180d5442d04082890002110400d0544001010b403041c240030042d441080c2d2800458410302007d540c551003030380c89201e0740b4101c0d40041da0301d2007000d114a21078204120074120311881500c0d00762007100043e000160555068882c40c1c000001d0001941c0c025205010703410440c0001e105c20491044081c04041d000e030050282107040b400c00d6a80c0300145151081c062111444090b280c6485c1d081444da130f540030380954801503007900041420704081808900c00c544004003c01210390500000712486540580104d0318940058 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 196798839 1250 196797589 196797607
    0xc0b0408060406060b070b04060207050a3809070302101202031905070e0f0402070618051509030301081c0203090a17010b040203100e04080f0a08040218072003 70
    0x600003451034400802450030310b41404421249942d10a54500c642006098000b42643e0b5240d40e2250300000300584039480340c00c00c9814481c1c40d000061100100c00000c129540c070160f103a60301c11541e44a0000c001541304800a00100140d810500d25448a80100018a4110311810942129103007001d5a42494203a05060742c0086d07601180c00784143e070850601e07050902c03c06604c40c2d80303450010f00410703260011039102402d0007402d0307005540003c0c501044c80300c20b42000040004400c1030202c405c207941416500c4900441369103240d03400003004641c0398480003040d2810703140d135600540315038204003648000e02525101990b080d4002801442040d80e05d0340c54420041c151043c41c00d410300c0010781c500d070841d600707071103003d2140d1301c14014802c1c9045810840e9080d039041ca0b00e4048a81c54a0410300c6260145d03241009680d203000540b112030701e030700c007401074021403003905e01ca00c1c4641425540090a24206d40550005440400c2d403500340001300003840e103043c10041540d2a01c2c13191 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 196800089 1250 196798839 196798859
    0xc11010905030a0f1b080c0102040302030610080105010608010e0a1508161e031703060d0f11010206180c0f0105090d05010209100908030a03020307030213060e04050c1e03040c 77
    0x914030540701e6401c0442c9640c8459045460600010541c1c500f1031411914080c1003440ba02101c0c402801c610030128424410203401d50441740034640040407680c02d40f602522080710f49440380164000b40d400c1c10000614140601c841030b05807a102075001c10b540d80c030321507880020406000c05221403600740c203000402c00014889050442d15110401e402d036401c1c003014022038041144004001039070340030f007000071450501c06100e00380c010112442d600e40310040081c0230f044101c2005452a06111840c1d020010b100041044401003038080d61001d070b544003182c511960b06100da403500ca4103c2c00c11090203240c2411401043c50050501c02e007098006808140075050528003140c550394001110442440d240150075620742e554609a03d046050403003203902c0f402151000010b054010020540c1280241c0584420079400e0305120b5a540d602c1100130124003a000305c190245203008041088995010100c0740380011800d800311040528684203000c1c2d501c018000d4071f40c20b8904002081100344 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 196801339 1250 196800089 196800101
    0x50a05061306050f0915030709060f0e1e1002031b0d1205131e02040501141807020c0414040b071e0c02011707030902030f0a03020d0815040e0102220b0d0c1101 70
    0xc007912a0f40c5174a0b21103409880c07011140c00ad6010701174184102d200c1c10303501c8211044804404c0d41e080e4444411668040c0364155451a02036000300c58480c450503666000010704491500300102610100000e5003aa4565504000d00c0002a0780c0d1841684690b0b83c83d000a50003900c8142c03500d590001c035031141805c820060007140318516a03091100190302d0603024541c0900314034224664a103111000082282c1080c82a001aa00394000040c3c0924001e200c1e0300060035001c1c0040c40340c116100d00340082020304071421507408055001181e551403290024964454005144030203506045206813005c92400b0b0302241002050441d41e01c0d403005d032602d614000e22103524003083c2e01016104140c01c000c0c0c1d01c07040c0715607584410ba000002c40d43c0080d5007036000916091803000d58450750241e1158480c4504c10315009401c000181c082c1c84c0c015401010102c01c000c0e82c52800304010f6001210109180c0310380c49865105100ca00340c50841980700c01100310a5040011041624000043c01d60348 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 196802589 1250 196801339 196801369
    0x4110c070303050c011409100504032703120305060a0603020d020409140405150c0301030209060112020a09050102010b0303070b06151201090e010f0e250f0f050a05061306050f09 78
    0x40c2c08912016030420900400c404502c0505201c1d07001d00c0c1451f05240d45020514462503401e0700d44010405240c050240340143c43e6000b6810a0344e04803e0340b200c0714a41c814803003100c5554001007104c6000e4401c1c4940c0d40100f00080c00c8001c2c0f507190403c103c0103234000d190300a03082e5608000006060a440c8650301780525490340b070003414902818400e050004c401044002e0303e01c101c0800103840c0d03691044a064a0341158103150036210400100c5600005200881d9940e00c00608910755076080010703801152000d900030321900b00403809164880c000ca400040500b01c40c40003080322441c0c03500075948909140b01c0c00300d080c00c810b64141443c8030740030390101180c030356100340b00b0340100d000b070081d1451034200c24400d00c05009090307c896590045004c40001444405c2500340300c1c1b00300307101c0240080c144c180904200c1130329092a00300d0700e011446114400c1a12000001d042d04002c415100c40d034410b005440305040c600001900c0c10f41c002942c1010280041101100603620303240c207480c001c1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 196803839 1250 196802589 196802597
    0x120e0a150213031401050105010212040b030c0f0c0a05060709051e0301021603082211010804140d0e0a0f0305150a0605040903200a080405060901050904090b0912090f04110c070303 79
    0x1300d113240e050849406070400e40c1150824010080f0740ca40c0102210100d0b1080455180d8954418021101500600741c0d04018078400040c88031003840300180c1081598000c000740d503c41e44400c041a2940640b030320501c0d0f00101c1900f00c1d051103181d24000300c0140131020700003526100003110910fa80144c060000c4001c203100c0010700101e0a941881d0710460545140d41070700520558448202040c0c0e003581e0350341004001e200180c1040f00c0c0c1e241c20701842e501142203500302252410090115000300c40024020350611a0002c1c1030440c144200c0d08417a007042c080c00108540500c107290045001b4405400c0c0e5480303510001d42030700c0d94881d000e0494040d9035104298101e1100e000e08070328503803150010f907510402a450224801c6030031503088030411607041e5a030342c001d000162100e004201c0183d40c8079140c41c07260002c2c0143c2010040c4515000c000f0389000403c5405500c40354010001c6407500036020102d421075500381640080340d440254000d09080c520038038006440d0520b0707900200c0c002 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 196805089 1250 196803839 196803863
    0x6040303110d0203090d11180109060819020a090903020f06090d0905010f0e04021804050c0a0230070c09020c16050d05030324100c03120e0a15021303 66
    0x40da0051081540302c0c50248091817920f81808001034071401030f50300c064501c644001e814200341c1c0e40e125001018018a42c041c2c925581c0d0347c5030f40e40007001c003885608058040c020886e61004000700c0c030481c1450340240400b01103420b109000b0010030340304000b28198480c182c1c0300c92003170504021062040e0b2011000304403602400200402201d455404035050040c0c040010150300c1c0c106118002c03281040e2001601c400f1240c5008800e8690bc1d0f440c10303005440d000920040a8040c8014424940c2c00c0c0c00315400700600c5424843d41c0325101d401180700e04801c1c10010b00a108101c014500309014200d00c0758a662541400d20499001000d40d000b1540400a6083c000e8003800e1044c0003007500303d403160110045034031600e4680c07000800c81c2281d1542072140c03c1c0d1010159441003107505010780710030340c0781e016541e0240000f481504203401260f865042881d01c18520f01074081007903440ca0281034001c005507501d07000301044c4040c844000d41c090100c01d680000360035420300194020000607a007 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 196806339 1250 196805089 196805117
    0x61d0105040c0f08061b1e09090c030103150902010e1e0109050306011809140106060903140d0c14070305061005090c03060609060703120504060207150c02250506040303 74
    0x100760b00e141c3c80000c1c03030403541508000250003c15025884441d241e00c4040d080e252030081162449491022803100c5180303501501e482000d00b0281492a000b9102c1ca002c549072484944490f010900c002000400858280c2300036180307035048404c17110700c10304065034214103001c0042c0100d0b18030b010900d03440006007803420705036900403080001000d0580251485504101c00114110340c030700d08985410351101500b04c1040603c560b8501c5800414000300512a12400020700d0070045100a60f4064214600c001c8405008201101c0c9071516480d07510700124a983c0710302d0030541841041159001c0c408000020582c2030005600c989144000044070900b000704003c1500070190800ca0803210038010070456441c0d0354110703a050501100c0c41900e070010341c0340c21144820000380c0c2141c030b00d040c2428001008900d8014040c03840c4110310308842071181408450454060205820043e44500e0606502c0d4103201040021081102284c94080d034586001c2600360f03010f40d0045000808010302411 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 196807589 1250 196806339 196806353
    0x6090203040b0a092307030c03050c0a060201020406020601050922031e020c0d0b0606070c120611030708010605090301060305070e0a05090607050f1c1d010c02010c0c0f061d010504 79
    0x40c0c0503445800800109029850390205d015143c0c401010204071260786140041c020440c50000f16030044580c11007940340e1030041d807a100080d00d8203000f01d03450007011480e14010300070340341545c0c80d03980100520b80c030308003c10158000180078071158103400440c0c41d1013003c0410740e040043d4020380f51810202c003008044405210700e00d5644045400c413003803c28071591030711030b0380442070307002206410340d5150340740090418482c13241c00510083c240c80c1e000500c84c03240c6036002074050007a4400c1003c06002c410303070b0f0300b244000c541000001710500c0041c080980603c01411001d44040e00006410380c4035039a4914040c810f40004003041801d00030000701451a0190550112010780039003086d04105001402a0103180c0001107070b80c0000c900b9480110310104281800303144a00d051203482c40000310151140885840300d8419420901c6144800c0d005002c0e40482040d55a1400a1030b00e4986800c480d203c05844200e4845442c0c01030000c504500c503011003a040842d200009079070a261174562 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 196808839 1250 196807589 196807591
    0x60302031606122c16170d050304120804050f070e0f0c04050a030b0a0b0d031101052401030e0a0f080310050a050108040210020705120102070c05030a0c03030c1506090203040b 77
    0x2c442d40703050043c40344140c5130180082c48000318100380c0070105002c002e401810b00c11401016844040e0746040041e40b1200307050400d8400707400d10181c6800f05051141125203200c11200034203440c4c40c0340314005901d0320840b20300303501c280100300313a030740301350290072807908211042d442140004041c03030a11041140c079006240d004603004181905c4c02d442c01c004200092a54800901010756450000701c82181c103400001012a008112080341c2c821480c4c082c240706008081c0c620590b20308400102113805482c04800d03203c024214480c04d41d4070000044025180303600344409680687e003c01c10018909038404025644510049926403030280e68104010055034400703442501c046008200e10390704001c8850308540c0640d01c007051220010404c0c2c2c50a2100c1d48400d0300040358030507240f9000e0041d4003400b01c480c410107001080e80da4502c1010350b0754240f03500113005014a6401000020f0040c08188032940c032900e1041074201800c02403104075110ba910034014503800008120403c40c041c582c0e2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 196810089 1250 196808839 196808867
    0x105060a0509010b0a050708040b030a0b0a060819020d0204060e13050613050405030714010b010e0a050319170a03090605061e0906040b09040501021902030c120d060302031606 77
    0x1246820301c0c080006002e0316040c45155403c05000900c0643c661280c41285d0301c20760424141035071196a208200056030085031400021460b040f4610079a140844403a012503000341d132555455264801d00120345050900c03001e403001e5003042510704403035007800980020302403500c840e41034070302d040705001c904055400b1008038140350004008941c0e40702007500100021500e000106030fa22458050f203184200b48001c1c211600e116041034080c40b05400210080000f0381c0c0d000340811800f803e00a030304185003c2c455158210f0184803180201c104009002a4050400700803030100d201c07189800365009440c040002501c03001014144442d13401903079006030307040c1e400201101c1210040c0152000c904502ea00c941303580c1c80460203c6d544e58104011290004019404c2403c0500d03006000303500400d5000e840b07400c41c1c040c41f800c103400071050f0307915610480094140342c80c400320100980d501400b5241e01c00c99843d007010026072000c100e910600980022555078183c03c242000c2d0007240d0640707003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 196811339 1250 196810089 196810099
    0xc15090203150c1e0403020d0b04140c0105041e1508041b1518080706030207050c0901060203031303140a0c051c0e040b04201e09060a0e03070e18010506 67
    0x74040400c115400312510020f0007440d6a96060050441e03d00905c40caa1019601c0700715240010180272401d40914000da02c9007414414202c07945841c03540300c40d6a000a0750204001384410488144405500d0000480d000085106540c42c1c032034015001c11640c0808000039000c00c200320802003004412421924250b040483e010b1605442d40c1c1c800040d00c10074400c01c40340e0071404801682c4200503a010b80550010741d009940c4409001b0006d4100b00e07000ea03810310913200080014201051010f0580e4a1603014500e199a4580523024121280c0340c01c0f800c1002c00300042540d820704802a1203040e84550311800ba40d2000d082403864401c0900080f03001a828107100c00e01c60381c01105520099106890100c2d500011030300080090199088400460480b10390a0038568444001070140c0504501c64140d03040c00c0d21084030380c0e4050302c101d141d0001001c200494507607008030410b20503840006c0884120035110403c0401c2d904056548110743c210242248201b00700a00800b0b920000c00d940d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 196812589 1250 196811339 196811341
    0x1e0c0c0415030f02030f01020a0c151b110a120f02010b1503070c1103120406080f190f1d0c041a030706141b28021008070c1509020315 59
    0x90070030500c1820310000f010689441c0b850030440d1018030445544031030002c0210340390500c224002d04500506641160803280f0480201c40800c1d00c0d1180c0340840490030084d98100000074400c2c2c0303044a405092850034030a8010800020325807489031201c400055035000540b00d540325000c0d0954198050461241401c032055404503d0100250795010303009251103500810181044281c0b094074200c1560180150003228204100b142e0042048600540d101e0b01280d8a900c2d181e01590740c1541c1c903503506410340c0310003600000c164028000f007a12101d40014400656084c00314000c0500d61300c094560482c1408251600c0c0512400c002083c4200150b00d1031014200002c0d1501510702840303086c00b6141d0043c400040700c64068422528010040c2d119148041030704581e9058601c079901c00125802c010485c01416005111000c180d0290100b40c040c160114103441510000b411034040203003400762000401c03c2c1d0312841c107103039034001c2000851440354010306041c80400b0440503540c0b145a0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 196813839 1250 196812589 196812611
    0x1e0304150608010b091602150a0e06040807031403010b0706020702011205040c17030c0309040f1d0a0506070e010210050406151404060801090c03060b22020a020f120d0902061e0c0c04 80
    0x8030b0448d196405600b100d012640d1903440b00c0005202403100010684a5003042004100850b4010320b0818002c4d01c030398600c000591606030382c0d807100740190400220180054030009260303801030080b09105061000c01400403030740c00c0c401c4038011541500c0802e0b000a0800150194100103d40011800061890a504045010b50324890300740b1711030040d903403180100c000000d40e5005a0384148200324055464000303c0e5810354482c0403400c15241c60180301d0110b500303140100082c2000e054182c000d0800030106521007002807038000c0c816100c0503110118503255400c00c1c1c48200180c10382c3c3c0c540700c17401c00012041c4412600c0e0754010043c3c1d03071715080729034000c130fa40800300d101203170380c0034202092400c292808038105442c007010761448240300d4001010809010707005014003020701e5080343e2100c04214000c1d03a541d42c03d0319500501c0101000124046e10b00c5030060070090b80050011480c00b1800c581d0f004c450541c01017480140301d00841c400d06440410312154261820484061101400d44 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 196815089 1250 196813839 196813843
    0xe0f09010f0b09120a0506070206070215240907050c190c0b030406090602070b0103030e0f0901060302090301060b07120f0c0506070f0c060603050f0c04021e0304150608010b091602 79
    0x94058400c05000103d100d8046130344010042800b420048240d032480001d0b86807882c1c3d260740c16241c5801501400d800541100d20010700b501071241140c0242805803954558103c2c6d0001d59000204092a0071403184d05981b50300c1c40480c021030160751500d80e0303080202c074414100060b1240710960f40c50b414a8110200755100300c000c095488410a9580d41e844629102c170081001c440000c0c802400031443c04180a41d06403500c2c1241d001782c0f40c4c9050122903804104820441800565008040c18018055a446940030340244000600002a43c176218101e40300c45401000d030861301d007074141605160041d84002d10f48504036407420156007030401031f69890b4940c4d10040030102001000c0845854241c890200c2640c01608684100400e0791a81082500d96004152450f840e210781410320703242e07082c1842100c0484000d1080c0305801d0b10300404212103903101900544040e110b0400841c0c05030160302c5048010106000009000c0d070021003400312210300100707040c11003418809407203c1c0b00d0300 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 196816339 1250 196815089 196815119
    0x6240b030f0402010e06220302100309231e030409061707120f0f050106141507021011120d0c0f1e090b0403030e04050f04050d0813060c0e0f0901 64
    0x42420300c5160018000c01140b40750040030300d000d0031400d87d03c16180703290383d500840c8401c0e60300907108407480b9160440243e05442003c000106903000d0803000640e054039407207c1140d801d8140066880e10400b00d0906007442c40054400c40300e40c0c1001a04020088683c03040b03031300030424400310b14803640411600ad500c8080612505404000c8482c54600300500314203682855a4000002c0302221840d0a00e580206021f0040c20880c1c01c1d903185584252030120103014042d07503165015440c244056085c4a40a01003002e14400c1c403100054220725040140036001c05510720880b290380300e2070b881040c0010355060400010034402c010004c1c04441d64441085a455001480c43d1825520f405000701c3d50f4002660000c0b03009580440c4c04000c2540c048103401c0d41400c221001e00840d00c403104200400b0f40282c90060155000c01101002c0c2c6020302803183d402405288414082c41140d180d4200303842c0f00040c800e0000300c000300500003500c0c00040d030250b0303c0025036614400350b0420183c1400144 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 196817589 1250 196816339 196816343
    0x8040b120a181502070c0905040602130e150d0c15110606060a140a210606020106090209030606010804030c0206071112010c120e03040305010603110a080109031d0d06240b030f04 78
    0x90001908800d20038500030301b01c018884240108500e250904180000b504030b00700e40000101484000a58a03503000480d50240e039403500c02c4000c443c805410810070140d900400c4500d4003403031070b0001e0f00054841d00c180d11245c46494030130b28200010006400c2c1b141c01000c041c800c440a110300036403e41d0003082d54011080c03c0540c90358500c4100000e661445441c044090803803510590141e5041e00d0ba00450101d52554000f4003d068941a015090707001e000111a0180c3c002c43c0003176000d6116110143e0064007a040c811000e000c960040b0381c140c2c2c44010142c502190b0586070005500b003c13001500c805a148000f0005d29104043c002c2003500c1001d505450b194441c041400c020109004a40041da070200080248035903907c2c01840302f045c0a0091441207210010008400e00180125a1810b9055607031200c150186200c3e0408014604c00b070b25084017a48a10b5800141c8034030072002400c600300d200b50580240051036540205054104410090042c400d020406070f21030300c0242c0050b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 196818839 1250 196817589 196817591
    0x3021c05060c0304030c0b043e040903180b04030c1d010303030e0c03011b0219112209030c02090601020c09011511070f06090914040f08040b120a1815 66
    0x5266400e00301d80301d206c0380001801428200c03017070104000e06241445010702060401c800d0b038540240c1d8403056000c100a4841465205d030807840707110b20306603100a20051080c2440082c180c207050b04035501d0451500031700c40c00c040c005014805e0041c01910308000340003801000c0420301a036040664409018803004003030588601850300b12400600c440301260002600030002c0d64503a1441c140284907480d0581d0160143d0380c541c0c071006d4074408c0100c00c0146c002c5a0f01c07510b408500d0034080700301c00d401560300a02c1c01c428400295860207000700d44d4224040d546480783c0d0040e034010062002c030040e10b03150556000398100c28482e29902002411205803003028400300055a10a07150030300d03118941480f900403140c000c107074440515500419200b20b0340d135030100b480d210030300401124901000040d61810a200081c0010980100304600f580700f40c00c4d040c240f6944095080aa4100c1252070380103032501c8040140c0046075125940132191707801c81007203000c0c64603282c40f1901c20910b682c6203942 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 196820089 1250 196818839 196818841
    0x2030a0e0303102306090f030f0111070b01080601080303040b0a06031403130902031006080c0c0106120b1006081302040b060a09091103070512040f0c03031139010e060301060903021c05060c03 84
    0x103903814020427888200d218001d01c407400456420715040d0b4031948045612000d4900041001c2100044083c10784801d03200a43c0f80d030b11503807901d11050400130510140140c99210100005211040300c540e440440340095483d107903031354108002700c80e998011000462060081188080d80085030104841050400c40e24644402c51000c04070311506040380c60b1507081c194005240c00c9007044c5252014000d102c4000140c41d031500a01d4000e003944100c1e000110f000000c9528203082a08181c012880140001800c0107440041080e941268502c0004a03c02c0305003007081d42c41a0091940600402c40c889207140703400000505640a4054007a415401940005003081300d1591080c8140c2e400c0900611840d9171707485d008090250800394240a070040500888662030480f00d4084000c1d4000100f04800d1844035a50f0800c0c2c0068610504000741f0024180c0c1036140c95000f98040d111555800b040e05045005000c1c0d40380c840700c20300501300d051089085c080b501c081240c0c0d42040b40d00d02110f40c0e03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 196821339 1250 196820089 196820119
    0x7080a0c0f050d020f0403111804020f04111215120c030304060e0a03050601080109020f0d03020c0603060d06051609050109030b0a1505091f0602070509060402030a0e030310230609 79
    0xa0003041c5c0c01c440300403400940031092141801c9820451031f422240600c4200410321203400404090b60000d41080080d450042c042c90141c004003240c2c00c0030f0044e241040f400d0614101c00d0b90099a002c1090f4070600b88005490801046001502c441c220003081c0c074807200c00110750f49220300e00c205010448082020b00d91a52054141802990400119030140d41c50341c0c1298020b2440301022440355000f0070900c80c443c2440580310700315a40540150001c03500c141e041c0503071070344018100b0b5440b10b448140e02c1c00085140c45054082c16003498001c0c01100840e0001d010b0321170542059041c4a160b0400300002194424a560710400d011000700c0c44620200a103d03030a03141c1e40010364080700d000304001d441034188000c403030b5010040e9110121550788110590b20780d82c190151540295100002808508043e001940c00c24070b042400112540c081d02400c0c1590070984000344411103100003081110134591a030344140c1c0791a0100c800c10744040d40050103d00c940c40925000e15144030030441 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 196822589 1250 196821339 196821341
    0x906040e070315060906021605030a060b1201020d050103050606060f0d020c0a080a02061009021606050907050d12120203280603061e0501080a0203060c160804030303020307080a0c0f050d 82
    0xc04003883e40302449407a9140c2e0000f40036904035000321801441054600f40c0d01d440104051003c84101501404204646499410141804040c602c1e04903841c24044900302074240300034002d64005007400a455419131411906007a4054003042c410356041c0302540c0390003041d2080341c0f509a01d607103006940750380d05400282000085030003d40702400102d40540a80d4002c03511600c04d903c0300380059102515012603a08030b0052000864400382d901201ca400031303005a120a03007144160b8200c445081d607400001d0f010f001800c104803120440103052000164021400e03100300c0e5040c80007135056240c0007900812480140d1000c2d0300d0f80700420756101c4141c4040d80004080c5412401c203004244440402e010440c02e0006942c10f0981382200000d402d0401083e1100810f40c0140030f80001d45a60320308082c81d4000c540311015441c07540e0b0081002524080007080114400d8402580b6850040009404544000c060000c414100b1480020040d0300100030f00103004141002519596014a80c0b0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 196823839 1250 196822589 196822601
    0x1e0507031505010e0a090c0612020705013824070b0a0e07060201090b010614300601020c0a0603020d0e1f05060319020d03140318070b0906040e0703 65
    0x900707040100c1800220000858101038103035501402c898107591160402c01c0110303200c100e80a041c0071880001400b030244114a4505104c0c02c402c800b5051406c940c40313403821111025081001d00f001d21603010b030f902034100d441c0044044158070042c0b2205100001c620094604030032840003240040080c520030b4030403000d440c080d6401c1283c0c10031a20f494001480182485450010f0500c581800003078000d1050203010303001035100e40e24010b11b13440c2280070303110705811403800280300d02c1c28094020036000b410b54201c40020700080100c511013250f03a0441c1c018074094005070440d08005560740403a10364941110848100c0c3c5801a0b507030345d19814180052806040d18416070060f186002c4650035031707139079628040020788030801c56902c48004040d55000150003500c01c01c00b1307894516026140542d81201524040e0030000901000c04d5009412136000b1184107107440c20050400f00d16250070081f0784003a03c0860012071500c2607840c009040c1780113520992008805940c00030b0203d901c05c0d0055 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 196825089 1250 196823839 196823843
    0x3090103051e04110306100b04050607031116050418050303061002100c05120109020a0903030e0f1003150501050a02120d061502030a0f05031006032c030904050109091e050703 77
    0x403000d04141c901041101d04c5203c4c224824865400441d080d4059140b03c90100d641d151b80c00761506113000f0a00c03034150040501a418010384018100d011007042c0940c9a50bc0e150340038001c00d82e0704010400041350000070800d10b02c0c9008034411400034500001702c81d080703002205e00c81c018030001c1200724035250115410920407820103e680d640e07a50410068090b10044050940700d80c0e88070242075040380184184e890004508420410101e4044c010500744c42e41c02400d01c4d4018201350000c2401602d01548600010356149a00703031160841e6040e01c0041d0a092900a140c007030401e600035903607801482c1d4008151400584447c20382c400b40d019030010480c01d500e1003e05182210b02075140c1c1c0040395040d010450480708036072100e01c0360003100d00c1a03c05400fa030500c03c0c10602c3c104e0060800c0350b40d146d03015000c0305003075011040c0c00d1001d2001c420b100c4020b43e50341ea000d4050000383c400c103a0280080340c1c02c107188000003035140c2002003000c000c0c02c801003008002d24200507281c40400c1e400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 196826339 1250 196825089 196825141
    0x12417180d0f02010b04090201020a0305030c0409050c19020c0108180102070606060503090f0a030c080a02030c011e0608060f040809130507050703030518061b130b04090b01050c0309010305 83
    0x462140942c02501242034030b0482d4000304a40a0714600340400c1e218807200007401070b004a584080003a000d18061504401c4e417018550800c1c1d02e6000e110b049031001d0700c262400c030801107a00d241c5000001c0100c80040c2091000e0010400c030880081d20151018010922450803040c3e041d2940d142503050f81c10b0b0070b401c404180005540c1d242e01402da5401520b004030580691103c942c0100c0c0c0028041c0300740c0341d040e9640743c003200403600c0c0c229003908456060b204500041100d0708000e5000d0003454000300200c00b42d0805000c1d85102641140c155520015858100c1000c2081f015004007400740c3c01070308180100e07a669080c40000d0b54210301c5450034044c80e40341c141400326095101016003205072103a141007265440380d000d48009a145104061102e82c00100003c0701114140100c0e9040408060664280b01803003405020f01d0665400003202c8400100d8200040d2075076004180b01170b5820b0070154600240c6109854881c8921019141890303104c002040c011004201c20600d0f551407950 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 196827589 1250 196826339 196826353
    0x3060f060c1718060f0d06080a030f030f0207021215070201060614090414070c05120f090112110d1407050403051e030906070f060b0f030a061805030301030b01241718 73
    0x585d205041d04101940640380b0710340715011819002c00610605c0d0030340c0545503a40800703280581280500980c9407011101e5030203000e4000142c441c503503082440281080580b2001ca455144a03019200c020248021681130000422071984c0203002d02c1c1484100300580d6940340c54800202d0042d0082440c4480c9590480b0200141a540242c450351624464000c0d6010050340075183e0506000300c0b01c6d01101c0110405c03412007290301500070042c0c0d03007103c84004140640c0c0f850b808920381c0c001d4214041e403a510750801212182100c0a4142d201d096405d0a038103040c02d50710b510f5550300400032410f048a100b895042c3d0061400c0082c0c8020241c010040c0759518100e15100b482851800307402c640c80b42c2018615a024034120303802c0200080054001c181c01111070302d442c0080c203034411600c0003040140c0074290100b402400154080c5014050841480d45801003900d000008a0304141c42c40c40040203055200f5406030844103403a10a003400201a290000441c44ca0305402209030403a04c1031103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 196828839 1250 196827589 196827607
    0x41a0c03070207150917011d0307020a0f120206180402040f031505040314090d060e070608010e01050d0b071b1113051905180303040303060f060c171806 67
    0x10000d40c4554070580c00e8441042d616101c403d200245607102d00301040700c44034140003926001404031006d030111000861314441c0302d4100a241c29024029019036000016903200754109102c071707032000342000c40c00c1300949494200021010f15145e800288203501c009010070609849805803185100010411907a8554840c00050744c2d105611084a01c042441c2807402d003042e1522030036210310340541f41e114100100c00c0024030541c0c04100c1c0e9682c810410701c0204042038480c030400c1d124010031801001e01c141420b0010b880160140c0c4641d10564810f07006020946429050b80105544807844030b0780c944416406907212045007800c1a4003503480004403080c0250300040048100095564002c090344407a600d000343d601c200c4894011380f4043c0800b5221507070a87c016a4040784004442c5c010b000705100c00c0d4156441585e0503000603440f01401e004c5182d80e2004000142105c0c100903100c2211940c80c070301546d41c5114030100a22010400291b141ca0540c000310044100404503940c804501c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 196830089 1250 196828839 196828861
    0x6140c0d080103061113032303040308090406080a050d05070303140708100501050901020a0f0f08070606050406090c0c02010f0909020a0215060126040309030204090b0405100c17041a 80
    0x74841500c0950400e840040488284070031202e0300c6d905019400101070030b5844150451a400455100d5449081c403031081c100d0062010f040654071510401d55514105003c2100740c0e185500700d500d598200c0e21164001441c001054015019a41066a100d141c18101074004202032403002d103460f51f0300c03820007030625480301007503102d12250b076030400c00c840d2580b0045031a0700840340c0240c05a803110540c1008144801d1603113014501c00c3d01004005c02d0a9a40c125036604100b0b07003110100e46400090200f450306001d441c0c0509080740741040002010305d4014111225018041d040c480d0700b502d04014244214a6000548202181999245010740009598900409807841078000800208000d0745c803809541801c28603403400404c11f0342c5054680b215078400600101c0500c00d1500001005032140c1c0243c400c07007801469001c0c480e2a16007441e9040400c401d0114034200c1c5400904540c0c9601306c0e030b1070041c1010502d0425455a42c5c0d14001d00b203140100500c4821495a0381041001412 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 196831339 1250 196830089 196830091
    0x32070605070909200d0f06030515090a15021803060907090e0708030703110a0203011b0806010c02030304090b01030b060d0e0d03020f03010b09040b090429090706140c0d08 75
    0x5159140910b45507142c20b00c00c110340781e400d0045011107044001c5803000103000050040d004c2d42d00000907803600041a1407049503103551003220700b50070081f08040c4036510300d084981d0040030710018040904181d40d0301c803c095007090f1031405440c2d01060310031042100540018510401404a82160902003030241ea609000d2080000490078070085218008000c100c1f113080b501508011030510b01c059506075421000c1c000043d030b44e84603049080025a400340220700700d00c040c55200926007061120700414a4000038007145c1802224000d013401031f00c0000407070f1300312b8001e100000340d08980c1c1c1c40101c01408420307003000e500ca100482c0c0c65445000940c400c007003002c2514102c031824a002041039081e40907000c0800e6170340300240010441c401c40c010051480080040c000100307400c0c03030350020b0040c2106440c2500c514204010655800b04074114042e45017607d4038500b0001e14001e0040350b83c0d10759038007500702040944040e80e01065001000e88407501941030030749118000e4088000c00e5158 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 196832589 1250 196831339 196831351
    0x60306020c12091003180c060c0c05010c0203100b040204030b0c04080c030a1a06010e09090601150e0913080405030708010b031603020d020906120d0c0203010b0108010632070605 78
    0x19050b40d41e1040180d600485507041c002500034400c0304075002090b0014a8101500070305401c500450100003010400c210300903001d02d44130364429030b2150400a0382c0b60016044035043c82030401c8140c02507900082c0b100d046541100c0081038907130400b00410040e015550000f442c941000040c0110b5004000140050341d103002c0443d625404e8030790070503603101c0b20b523140a810110304030090202103664042c050382c80441030501d850b1031105103001c41d041060803143c40c91946c00c0349005001d04190500c08140305106403900d65600c0160b90001079480c0c0f000f50480350480100c01c4002c1c1003004d000d007030320000e102c0141a50032082c0d030350b280d10340030740702d1480124440e000e00400310030b048404581450580350003400c0d05441001c40c3d400d00064400c0030740110341c0301c001c81c881e0700e0f0815000c04c402c03600e0384016500c04012913041d1041c1402e460041c2c04590500441400500400b03034004940c0d00f031007000d01e0407594408070815892025100001d41007515008c00a1460b09003d802c0d0401c0e80558 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 196833839 1250 196832589 196832593
    0x303020d05070801050904060203071e0e1509030312060d0c0f08010605040504120309170406090f0503031e0a030f050c0901081f06050702040e07030b01050a0b0f03060121060306020c 80
    0x203550b440c02120215802d0080592240c03840780410b010034603681c003460f4040c40c2418003000c1400f4040d0b5111003411b4140b00c2d840003450b10301d00351250341400c04141840b08035140c00c082c2440034080c0040e8490088919007804d400646000503500e03038550b80d03000201a0400e89800303d1301e803210036030b03d00751620780641921503090120016050410f40700b02ca04c0785030407083c00810b068660504801601074400251600456030b049a2803a03050540140000c0c00302d6154031a4540c50a00d80020050041c1c1c46070703119030018040c61280751240350381c1358a0705c02d1500074699600340307000701900104680d00005103554500402c0180c607000d418018132001000741c0714641959a5801c4440704611458034186d22000f210604200d014040e03c0504103880c8014004aa919904030f11185041c01c1036105035103205034640100003504001c419900500302e68104945028400540054244006002c0d24100b0540001e102205071000d0180a0301130202c01c8288503195490400c48080d4120100c040224 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 196835089 1250 196833839 196833841
    0x221070608060f040507051314040b010201090203030301120c081c1407020f09060105040902280f0804080a140c0106060207050402040503060609040606082e0501120b090102160303020d05 82
    0x1405044514454440200200343c20040700d410710000e0900503102e94184601030280c012131702e1100d013001001d040390708540010b031115070003003100307440303803003000e1815079240c91000c401684010084905490301210032084184183c40c0020950500c2d5105c10200d003d0191002c1d44506001607040200c1c905581d410301007402021b404d00d2a00c00c40a0007903000c0820522803200e820b129580030703804001410100d00301a81c860b209001e130f80c007491014002d8100b10b010420313060030300c0c1010704c4c2d04c08503032401121a5403641d9014140b404050070141c203402001c01e421f02807521070a4400d0b1419220071100d919400701410307080c003070161805103d000d400b6451300800c480c00c1c02d100b0b803400c6400080003090301e46c03076001c140b21002d41e001d081942c0a546892011401c80e8003001314031201450711484245008102c5076644540304140b50700b40d03101c0d00b03140041041d280240002c0404075080103100300340c1d8a44404650080c0314516050100c103104110031001e041d09035024001301e0548210034001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 196836339 1250 196835089 196835099
    0x302030601060f050a03050606040504060906090f020c0604170f04031a060402130b030a021209070f08071512061e030c1712070326011701050c0306100c022107 70
    0x28464005440000131000d00460240d94400d40000c0d0304404050502462302d41c4400104040c1d0303801c1d0300400f8885855404c10411503450344141c0130101c28121007103003004138949442e42c60303510151000d130840c9074428641c180a0018400c91300c017a4501d64400d50749039070f1f9250034080300c00c0070003400100310740c0c2c1000180f076403d1a00840780714a00310030b41c60031024145440c09002d130300054908010310340e00b400a4100940581d420502803a1404000d0003040d1415803201c208081c1030f00a0100c0d41c01001041114106140740d6103090985400c20307120301c6503134807401e000505540d0b2100450804488144410041d003000080580707009604c4c5000503920b60017151000c161001035408658415504400c1c1c030b5641501500c6100e100b0725150f40c40c043d010f1490305003a9003c10603c401c02c07007900c0040020029210300b245480b00800d009010a00e4100340c0c805050000411490003900703059140040c90b407090180d01c100641c002d0019441200110385c0850b8440644416000340c03165100100d1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 196837589 1250 196836339 196836347
    0xd06031202060402030316030938040609030609111003060501030b0d0c1203180b09040606020d020a0605060301060e01080d020d0c051c050c0118021302070213020315030f07030203060106 82
    0x80f02e40e4001d030096107003280703c0c41d1000a44062a4041c0d04000054001050060184503081018240b440700c003084a444100c6250503000784083c40c2c01c611004000420540e80c00c4000a003c40323400520004000c026410314103044007810000702d60000011004440254055200409407502130ba010031000c400c1c0804e0000c00c80007044050300b810203001c02000341c03407240c40c04e44401510906e0807003030790001091080700c40c0100750800c0c0040b10700818454890b04091251b400141410710051503c5104110040c3d10780b0307d803c50141030143c9460000c3c00c030b51405d41003200200f50031402070314a5a0755495590f1600341c6542c100c8014050250404046889051038048842d003000203030040290b9038042c3c0020605403800c040a0000a2004101240080c40b410307048034400ca000010703000c003910400c80300c0524502c140451510600910015807166564250781c50000d210051740c0f40c44542081c016040c91a01045e89481101d41c00d0680c980040f980d14100c0f0700c241c04640300d907600c0d41d02c155 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 196838839 1250 196837589 196837591
    0x1209011802031c0309050607030e0606060a08150a050d03121a06120a0906110703170c1b0102360303030106050702060702010309020a08030a080a02030106020706080a0605060d0603120206 82
    0x7a606a0194006411004000015075641c6a039420300080c448420381c0c030503003881011507c51002c01e071b9645134141084000e2140b03640c81a0b0803101607143c8000444050110040903050b074031a000200c070810038980f030b0382400b00082c0800a00c61840d41c1c80a2400406849040c0d0081980e9402d021003124441c0c25840d4040340600018017640c1405460316040340016001000b5402c6103881d480328202181e514481c0801c1e003200041d42d40d80d12120fa09024050349007102d49038800249140c10060140d00c008103890b040300d0030589401c03682c80041e1080303029000d12042c0300358000c1210000341000f0b1328001d00901d1380740002c40842c0080e1210003010b4072070001b4410840400c004000e00e100614120000304040c030b105040000300122550080360642c1b8142d0840e1074268400a15203840300d81042400307074401e48000041d891503042130740003520750030144901c5045c0107440d0041181c0c21040e410140280002800081d01e40b1861786602014100b00d2000f0384501038035005521015102003401 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 196840089 1250 196838839 196838843
    0x1413050c0903010b0d03050423060a08010302011107060e0607141204170102090d0206030415060b030604181101050a090e0702161d0114010c02041a0901150207060e01050f12090118 79
    0x10312308017481c0284103000e0303c880344d40b4500000c91030041d40030f160360340801038000f540166580c03141542c11840050b0010b180140458140e0713004007001c104841e8080c01c14902030b201560043d44401241c60700d0040c6215072034101c0200c0c05030140c240c1c072054451000c1c00485800c40c1c12410540e001c4c412150813489011403c4d6003096074003c4c06400b5050903002541c1051003410301e10300005c4507035800d00440e040d54214903602100001402058901801007905803100307241aa800201c030b03541c562205a0000c000181030050109103504500d00039210403000f065681846503503840c0c5154000e440c0e00f090b501480540e00000d0001c140c0e0201d000320707540c0e005104c1b03800c15442e90074440c03800d200580604c0841e040100d8500301c280140c94038000e1807035141708070b014181c18070ba03800c08002c1d400d0f4050300004008107141d401001540d40c0010300c0021182d80c0d050000c1c1c60b0403d140102c0d418030808480d00700010000921102d00311080003810711400890008004091000e100c0d002848041c00c40 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 196841339 1250 196840089 196840097
    0x606121a0c030a0c0e0301020c100f02090a050f061b0a0303051b03040f02040204050a0e061c03020613050a0b011805070813022803080304050d0e0a1413050c0903010b0d03 75
    0x70900c3c041940905540d003002c2c00c0c840350480c094030001b03003a84c0c003203404c01c59150440c91807200074044500452400c0901403105508041101e80402c14840f2148a943d00c154405944102e0644840c011112010004103c0c0c200b490102e040259440032002c070114002440c10300007074079548240180311050540500c84501c1c50b100c540b1841d5a8005000050b03178015801c000000c0c5c1680c442d6600c60003005505807107021347c908141008081c0200c50006440b0b8845010480d00003680460140d5020810100c0e40080d80c5503800d003d4034010703a0510050003011010700100700a85040031441074401c400b481884943d5620504484000b01520b005042000e648a034000610b844000844441c07000c1009125900c40310700080c05948107984181c5044070000280001d110003441101c05403105402e00d1800d800924020658020700340c4540c808055500755088240d65880d10120480558500240000d060406001e0050307844800c24510070740c42c004171980341e410100c401510240d05512 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 196842589 1250 196841339 196841341
    0x6070c110105070c0f080c03010f0501080c01180b030c2a03041203110a080c07080c0105090405070309020d0302030a020f0601030b041101050d0609060306050f090a11030a0606121a0c03 81
    0x41d1065080100304884684402d24017207011410404003100a001c00001801c0c00d20a9005140c03c403204c84041006072420200140015500000c1c1c2218425084c40c060b0b51100880d01d400b44e48800c2d0340c01c20340c05800d000042c00700c0c3c440305001030402c541040c611500d078410a114450601000340013074100b280c0050204000c0100c0941c0410f0082c1e000c0e00340704000240ca40d03440790509038500d50496080b8804101c0c00101d03902004030b80040c240d05801000288100c00028000303000d50780c4000d1090303480c2d00000d1501480303a0001100705a000d4804c8103608541c3c580a07469802c010703000350052056001000b0203500c00a040360480360400e0710310140d5161516036606c2049200c8d2001d0500c030341000341c040f18915901c40d040c0189900c0a00041a60851a02c8c0046d210098800602100360505100301c0c984045450503040da4010780445812802c0804682014007aa9010b040903140250001d00c01d004010180780103840f03403550995120505000144000c0e0a41e0441e0001d08180 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 196843839 1250 196842589 196842623
    0x17090d03020c0f150f0f0c0306040c030e100f0e01060b07060b0319050102070303050f22050c12030c0622061503060204090c0e030c240904020a050c06070c 68
    0x36008040c10703444541036610200d0b6103000c0916103a60404d0100101c02c4c0d240c2000045050380021035046001d4003540030b00c0781400011480c0c9400090900e0303219942d02c3c000e80907068029400700d0307501d041c0982943d10840b103811038440140b8184c807024050398104504030084140c18810881501c82120066042510301c0d1185401441c1128205401d84078240540d1050484030908010940c400c0c00050799a0b00c0908d00181076407005001020b50403003c1080c00070444224403110518144805500502c0e1124201207140910081d54140c0201642c09081d01d0324a0101c010705001c812402140d281d0340b40c450030f00e810750108071003941c0d12a400c4198180002d903250420301c000b1a010000c84411501c1c0d4840b03004034be0250b8024441107640349541410150402840741c1402001c401519442642d18086400c59034080d07000b01040d482286482c040e400e5080596071074a8015104644415400b000505681e01c5156219400d10440000444051003010f940c2500c036407001010103048210 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 196845089 1250 196843839 196843841
    0x905130f08070203060c031006090b0301050111070509090a0c050d170315090c0c0114010513110403080a020a02030618030904090f060f1b08040812190e03030717090d03 74
    0x2400c044407600d004009820140c0e070300300a8a0b00a000700d600b015039a0410138034840800e6036035444101404400d032020401d00c0c0c81002540d04450f000c0c01c1103040078402d040620308001e02c3d81c03c95603100e40300f102803008240c4000780500401e8854040e00c075196443d50100005007400c07a10090180584042c030502c4a20140003441d04010420380c268040d1074a20b0008160380c40840d1a00d91803a1b0101d285a0b1031035017405038184140540d00c8a07440344d410a802b00300100451460003080d41e0300d4601498140f202001242d00468010440503142c081111000392124501c031810b9120b481900040750706400400d0219000c0b1400c0170007540380c41d0b5800305000207455118000c0e030f00081c2c8004030001244c1d0b1801130f5141c2035080200082c10040084080b410400e4060520042107600d07020000026056812990340e083d044c0303040a1299511031065884140b000d944e00d5415050951104501d800040074501480c9207440c0c4030822481e414100e0b10440d4202c3d01d101443e030161109449e61402 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 196846339 1250 196845089 196845113
    0x5011a100206011a1c050c1c0b030c0907090305030f04170706020307021c210305090109030c0618020307170705040c020d030504030915020a0b060f0114090a091e06090513 75
    0x2100b40004101443d0065102120811620303503400b04800552118451f200d00c0000c9154215108e040240e400c0c0e04002c07030340c2d45c0701095031140143c03503080c00300380c3c6140500c0308880119404021030b0b54030203003c00c0e0340a0036046481901c1ca000b002e0400040520004180f1409680c0b55600841c02c140c41038007004042403149460070100003030454000049100200c81440d40140325805100381000c520b001001c4841c020400c6641d645000141c03800a45d03c68103a02c0342c1600301401103032800494400440a05500c04000e505106520340080c00300c0e110410030f4480c240c04020b544160b070340d44040c082940e02166500c0c0050b00012742d01d4240c00d010742e115940007802451300414141e21004416008003a0034040000b6038010051801003100446c030066000da401c3d01e5070b1810741d1398540080d21036042e00001300351424000c6000b03440350312800d200000522654500303105569240e540c564150742c9080079210660709020022480003158040d4501580c4643d5040e1402d441c1c0361110000c0f060 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 196847589 1250 196846339 196846357
    0x120d0503040627021e0f04051512060702150c03010605160206040b180a0f0501080c160c0303020d02060907050f1801030c0608150a03120c05011a100206011a 69
    0x980c0714284241d500c00b840340d2201411510345080c032004480e00400440085c0d09004142c0400040440c904035140d11034480707400e020030781c0c0100703031510348124603502890748410007604280c0b03009410f41d5681c000540c26005103940d800f910300d6040c0303a0030003480c081001c032488107501c4001c2004007c240c0c802c00041031081d40a089002d11368001d0360024003994000d52108692040c0851080c10849e6004040e11030003c0458500b5400b501e8031f9a0078806e0b10307452140505100b01d2100095501c0324100496494080303114050704c07040450b00c2c14085494082c00300740d006104207492500458000600d01e800303014050300600d00140b074041000140f81c118050786400000c0c4481910680807a030100c180a1403140441c140710a090010041802c800140a0460802d40300d10704001619000b4140b0306032a00a4941042246404816240d011803880c00811b15803a10140d4a40300c0c5001400d081206002c0760924008510b41000320f0f500c000a010704203020141540208034038007410001c2c00000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 196848839 1250 196847589 196847591
    0x3020f13090203061006030b0303070510230a05070e030c0117070e060d06140a0b0708130305030309070810060e01210503030f0103171603030509010e030d1a120d05030406 75
    0x1220a40c046130408409a43c07500200e000c1c03c20900604d5018055440402030640065040116640302c041c5e4800f01809060b4815660300412485146425240140507203071a40880140c18400e59050091000f216031000080f80b032402042e9910b0082202501c4900580d650004c4400400042416410140601003406800203c070003141e01c40c0c0780604520f00305428009803a80c5400c8040900020038101c2d588101c60b80030083c07044c03151000646252681020f03240382c40e004601e07030688a0030401d401c050043e100110070402d080324006100c0d0141c4010900f540e61100d8002010000d0f0740a44c0140920002e03408c0040c40680c1d64000711035010460303401410200c0300c45441c0c82d0709507031003502c2c5044112802c400601c05e0260003020901550342401d120b030318162901c415542c180c42e103150001c003050346960114081403002d41081e408040c544003078a6903081e00d03030034400040c0300304880030154596240d0031541c3c030b1900021080f003c3c050b410180c070040441c5a02181c0562009104840003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 196850089 1250 196848839 196848851
    0xa0c02071d01080d0c230712060203090106061e0507020d0204060608090601081c050c0a05060109090b15030304050625140f0d0203040603090303020c0105070504031203020403020f13 80
    0x900307811407040000304038840607694100407031541050ba42c1000082801807007031110001800380b00c1c450421503a81c02903240d0070440392035120304080c0b860703100c1601e0214200340881071092581c019401915690000c22516a84141c00c0d0340680d042d00941c01480c00701c00200d800c083c0214000e1410b00d00c02011000304c100d4640c009401c5694582103040000d050800704898030004000d071601502210008001c414141d80701d00502801c95600c2104002c400300d05111a104104114440c1c1c0c5d40c010151441980c403030702c400c001480124015904241c004010070070154504d52206445100500618501403c02c41400b88a90080c180f210841500350984102911200100c0354210b02c21844c02e80d407005410030981c0380a50b0004000400d401c2030110f951031640000488040728001e00b000303c0c820060741415002030052006080c02c80d4244010072607941d0b03100c0d006000b03981c80750891080e401c1c86c02030704804034091070200a400c4134010b480d091591500740011465140740440200b25 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 196851339 1250 196850089 196850099
    0x20706060f060207060201020726090409030509030c010e1305060d0506131a070804030807020102071401060312080702030901031a0d110f100804260705030901090b0703080a0c0207 79
    0x8440d42a44400901d807400d032424401954181300c20300081c9101d00c003e50410200c0d46a5042d40e03494220400075552108c20b00f064003c6005080e00d014000040040000d00d82a0030301500950207001c255100e402000c1240d0980e43c0a08050945034002800c48011800c00c0d0100f14020003015107215401308180c061080003400810a2030b210f91204101840200810308c0c0004412000c9140d90305040505030401c500c4a87c8940720951068240c6000350903629400d030142d00a03c50f41c0c0010340303e6a0000c0030030408840540100003103e00c990048a0b0056440c2d50442d105a415100203005800c1040f804142d58882e8000c1102000c13408003400003015031000040c0b800700040c4d402c598410034290f18030120f240c840700001e1214000c0c0d032a41c08100c24810001c0401000a00c020002d070610151a99400c048181180c40184001e560036559562810015902d40040034281c2c00290340000100ba0405450180d0341e040d0752507115441103889075000715020305055001c5804512a40000040d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 196852589 1250 196851339 196851341
    0x50a081c052709010501050f0304120318060b12010507050d09020a09020307020d18060e01030f091a0f010918150902100905120c090c0a020a020a0608070e04091113020706 75
    0x40c5451504034030b40e0082d5031103400e21540719416400705041c80702c188110380c0480680c900312a03101d5408142d111030b443c2900b07030580c0104950010140403101d028192420444c0d1a442010103001c200c2e9034801c0101d0043c015400ea0b84110b61202c00a0420302616100b00907541010002610051210300d00c2d60702c5001c0c010407604111060401a403064549010300c1e900042c10840302c141078480320000a08280f00684100300440c01541015660204180b45050980c400b2041c10b500600500700145100c0c1007401c0030030160b07140e04210040d0f50000440302801c0c030404284450000f0280101d4141e611485005003004110440d641c0d155400a40103035610208004145210f0720384402003414003051064039405900030403520740c4840d5000041c0e507504940c1a80c04041c0200507560b0316490103040b400c1c501c0440000b900800d041c41d001c104550030a40305407060040b550b031042007010840405c81070b1501800d000c3e0802010b0468180541051401c4000031000c0d42c0d80940b030100107640d104 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 196853839 1250 196852589 196852627
    0x40804030206270d020a211a070807030e19080705161e0e01052715040c1803120e0d0609050607090e1f030813030309050a081c05 57
    0xc140c40303101c2103510500000a40c0da046100f041591a44074a500550124820b0030b058014501100c0c9407949402c0e030360f04c01c002142025a0f07c2800e4414442e03181c411028608803d40342100814501c40001d81010f10a12405101c3c0001000074500d03080c2c1c030991140100b010303000507540f0000c200148404104d0812420700d40d0300490040a0040349001903454a10300c3e00c9044e501000e094203400c0111203c02003606040d00c000715410800580c000c030001401016415a05840c0d0055004001090546105094050205480a1002c17012459040340c071000c03005a03030b5030081040704052000c1034001d1929a4145000d040c80a800c411030000201d41040001d0100d4040d501d030801c400c1000424014990084114100122081d00b8414140b0444e100203002c2c807503850700c4c80070610200f0a40c0d50703c00011500002d004c3c4c2c5ea12603980301001c0d035250394001500807600201000800d81000394091003200d04010140c8040070b0031441001000203000002d1081000030f00561800c0d442c20b032012 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 196855089 1250 196853839 196853857
    0x405011d4c0909051506010c02030604030c060f0603125307090909062702040b09010b1204050c060a1d0604060e0d15110c33040804030206 61
    0x441d41811103048110007401942010030501d0404005400003180004c2d01c43c043c000300d503030a2080b5a00d800048507007841c0180041d5151013400c0c18881895040b4415000150007118180076040d0006030b0700098560320b101c0141400380030340044061610508040030394860a03482c4241000da420100503800c2e0310390040051020202c0e0001c4040d0260400b4440f080200002104c49807501d66805800f0451604c205500b2580701d1b000c4404000c0d060b0300a2a000d040d0522014260000410b000c3d004584010100d004a1801400d16402e01e888041a4120340c0440d4003580703000c02814040c103481401401c1150113100c2c0f0900740d0610341d1400080c0c94020a165120240c0c00001400000319180c90880280125401c000c2031062540c04650000910020f45621481181c58034045c40000344860920304464604100c0d04408a40c0c0002061504a801d08031119401081030300d1028035040050010303c014076411200d08018011449a0b005024007640b605080e070340d13008100c40f50320540720 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 196856339 1250 196855089 196855201
    0x3010b0a0e0405060f06030a0207080f0702040c030e06070c0614040501140106110a020d050f120406111626030c03030406060e04051b040f020f090405011d 68
    0x2944258050009001580102da06001c64101036012481d0f20086610b0903000c0c940000c0001c00c002100e4044038500341d407108100d0390300e50505075a041140c1007404201d1045040108510059100b801507084c4105040050005500d03210401e941448928004a8000307032035540b0f64419038405c11040344120301500000c91008205810300c001000140c01c041c040c04040d06940014a40000f03c5120140c1d040e100341c0c0e540d03180d80c10041c0c9810340c40c1b210b503070840c4202c03068002200f56600103031044401e42d882e04646c40e13140700712864903068001094005201040010008034080c04205812035940c1d0f1030104d90b40c07055900d113030b003140d01c52104080f5070303480001484201f2503a80300380002003001040c000c00600705965503586030907412002022380d20340c10240341d85603919684000b0444c003d0303500856586045221001168104518180c886da1420740001030103456000d12500c0d1448001c49042507a0352a001c19404400078040b0f05880d4a0000d54008856400c107d4440b00c6001103c07 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 196857589 1250 196856339 196856347
    0x7120804050411030c070f0c03022101050c0c06041104180c03020901060e060a03050612030a08090d0806060f0c010902060705010b030d2c18010e0a11070b0402040f1103010b 76
    0x70302c403d80b030001000b5210f44404004203c2482c1c802c0060b141d05076840540c0c00300190650034840c140045640003c1d520440f40650450034949100c031f10501088007000034032560741c44168110107806190002006504044002400202c1c880c900040448009000080d00b5043c00c04007095a51403d00455002042010030b0095150580b40503004100303a00d8155107007684034010407807501880303144509240d00d80000c550241d480c0e0b241c5c1034a80300d0032411281c8070315030b40a00400c040340030342d50800f99001d0300030340c014258810007030b4034450304014000350724204503101115400e91020709200d909569410305800113903a02001406014021400414207500d00c0c1d007010705000b0052544410301c56220812540b20852111500245842c01034101a00240c000480e2851220644503000c00c407184001182210050004a00403a000c80040084c01075240c11071286109a040181c807000484002a00501c1d00760010b9503411000303840454030322030441c4850002c2d0002e82007610400c0c0c01103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 196858839 1250 196857589 196857599
    0x151602010f020a05120405010e1906061401051c0f05101d0601090b0a0908030c070e070e010c081605070b03070e09010e010e1f14180403020606040506010207120804 72
    0x4007501080d50021681145084207103280540f03544a001c0d440c4a0110a19000605008003984403600001070300d404da40d001e00350100c0300c04016096032030407100941b801d44041601c0d070b40c5500402c020107060f19498580714041034001c6da1902419806c958454842c541160107164a00542c0c3c022091000300444280c28022400001c44481000c8154400d410301002480d030392000341041101c01644180340c0e5030121600c00c0310401826082801c0904c40001c8001202030001180411034501e071401215545031400c044503842040d103001400500407c18850103d1032000051040098210483c220f01c65a9500c49062150b16849040d40030004020442034681004942c40808002c03102d008144d81800520908694180150000c883c10703440044c1400104c0c42640300e001c0405580382c3e201a80c0c0349180140701110303250090140c1c1020141144071800740641d1806641d158001d000c9580d6201c1c1408003c1000034031060440c401c0000000d0303161240c1e0385403500103004018880d074480c100 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 196860089 1250 196858839 196858841
    0xe0a030f08070e1c020a411c0b0f0910060503030f032703041404090201050a0311040f0602150106020a0f0b060414070c05010b19140315160201 63
    0x6840306120001007040600d551084040c0402c80341168100c10209084001c2035a0000c00140250800445040032881014096031007500e00d00b06e0f602a04103c0100700b030043c0d140b80b402da00c000f10101c61f85c0c00c003000b45006543c00c403030049022400440c1402e50b482d21440803105a6000c00f94807806e0082c8a05184c0c14051704110099000342444482c0c0b400d4046075480c8105507801d80603940203c04520072aa00309410404c000400741d211429031180040d46880303601c03a1007844a407400000000340c07141814080c564a80740c05840b16820700f5070300481035014040016100e60b03803003002c00000c11705586200701c00b40030b010294000c3c001070000c01c813500d40d51a03040c1c01000a6503c0046101c0002d4506110b0240040c0c1c4a220044140c071002c010a000e090f4040c907815621080d0401c00c100720398482d482e0f508041c0240000d20040f8609400d0002142c2505a200313540130020b08240001c0c0c4444001140c2000d020301207071030076070003921400401f01c4250750307541c401c003203002264114640c2 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 196861339 1250 196860089 196860107
    0x170d020a05180405070504030201030e03090a060203040801051501050403020f15030901060303081008032212060b131103070c140f0f060a0c050a080604020702190501120e0303040f150e0a03 83
    0x20a0f20204214108002d0141003401507100081c101500d60444681c017120910a44c4c1102c0c0d406004151010384070b520107512900217008210940d8600310020341c24265100b141c00c20200c060b1561440e050858081c000ca0340744000c100c1d03401508414410482c003075003100641c890454007000044a0741546002403440c503014101c200c3d600540741060000b068048203e61505450300c3c500f04200c400480c103007a0012980c1d0051030b0016007901d01000b4400f25070046101e441d022218000d026545403025011240020b405500d060760620000d000325010348540362140380548080d8520300c03035188007145032081100b078000d403030741081d20900e11440c02040400c1e00094090403d0184655a58004085024616944082246150110340a42c81e07a50403140e07280d40182030410303210400307105c1c10080c818034070800d400100b00007400062404030307100b034010268600028520710748441e2034401c00c00380000b40603900000700805049547c0c0f05440707500c440d4555840608004000f6040151a03014 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 196862589 1250 196861339 196861387
    0xb04060609060609210c03080f0a0f030203070c20091005010f05071203050c0c15060f01020c13200a0e1c02030c0d06110a0818030f07170d020a05 64
    0x15500c4e130240040004a04100000e400505544580c1c5200c2d0a00c0ca102440542c405416088001200341140c5010b500900c00b001c113075219182203c444010450403880200c0d0148001f5804030980c0c40003450600e04052244d50054002c001785040c50b00040180c841544d1201c01d82001c000c2c20440c550b080103055920080da410200e092104c55100c0200788014100100105603407400050f5100d002030080e02c61040da00021500030400302818014001c2041da82c070380c410015181c0780d0359150320014880314172210250541c0003002c51100300c20064035104e10340e0840503117001c036840e0300b500002010307200402c1150380b20314034401d80300c0601081e4640d0109590881402c80e0008000d600e00103141d542d481382c180c0e07064107201c800d402c250300140007260b12912031040006418810f40c1d40711008a0142d003011094000d00f0503440c004a80e82e10950034001d054a4061025030041885000111085010000360915008041c0e2401c4100d900c14050500490004511208400701e03038084903000c05 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 196863839 1250 196862589 196862597
    0x3040f0e010509010e0714030c0306090609060303040308090406050301020c06040c05011707050d09021e0a050a0602120c0f0303010909231b0604050a080a1703060d030e010c0b040606090606 83
    0xd4182000315004080500440e8024031700c01340403e000c248242c2d083c401c06501107018640700d0134840095401da034020754590340302c0d004d00b6000c1401c034a0121041e0f40a07840c0100113502d01490750f554090150464052194055584d01c4001240e45083c001803040c980c2c0c0d800680304500d4a850001100f42039078005a0400080095032404c2807003003003031243c002d0010f0900c291905281c61020000d401c85080094018280400880e054030080ba001c15454408981986060392190103100354060b1030300c0345e0001a8000907860f407004100b05d00901521082030b09860402ca8120303c65403841d40300b030303025443c2c0c0c581e901a90400e224401718440e0f054990381544a80249115013181d96440b0005001c2d1000260702c00c401145a0b42c60007198010034002d130640c00d1647c1d5460344261190b06104c0140d40041c007242c5200c0f004e2400f10116445014018a000c21400c0251070843d501c001800405043c00000115000440c1c0c2c01c0c10b059114500c21070010448a05141d024415107007030741c1c00750040c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 196865089 1250 196863839 196863841
    0x109030206330d06110309121c0902010203040e0408030f072c06070f060c020f210901050d0e010608070f03020f040e01060302060a02010207020405010e06010f111204060203040f0e 79
    0x1100c003242503240078400c801d0751101c65081840040d1802081a034001d201c14505621044440c40c03070b4028607c5441c0e880c041c5c481180d0965841e8a261041a2840064200ca00c0b201120092142c0c841300c241801881260b06043d15100e41d04490341b13065806170b640303440110030481212030248100707901180711f140c4016800d40e510a1881212030317025030012810002950f405054a88a040c1c848040e0460901790307032192a82000d000400c4071210b45401401000c0b01085060400620744000c1c01c108141101484e14040c0e500382d881c1c003e8000c1504001c020456201c0034082406141c440c00c82c031400026846181180c0b103450081c0e036600c41c0c10310401a03602040903903107031110848a804103840c04218203800b06082401801241c200a500401c041a0344016035415406410080e10039141000300b40d0b03c0704003480740700000b200d5050001d80c09218000c1843d2080440e038400141040482c0d4600a500081c4980c542242c1c02010050788042401c020350380b400401c100040401304c08617100d1b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 196866339 1250 196865089 196865131
    0x150504050904061e0213030204060f030b01060e03120406021f0509071206110403030f0801050906090109021605060114280b0c160b0c010b0f1f020f0604050109030206 73
    0x15444000c0c030280455603a510207404030101244070340c06903913141404659030603040f0003542c0080300714001030340901e140c29004100032040c854000141c0c1e400c00e68038800d0780e207000c80c06c591302c5c3c011f80d5a142d05805400402d1040390302c0500034001a02c07090f00581010b2a101001d0100c80010802010000d41000103003e034412012410409072100404c8040d40004a400c090014080701103c02c0541140080c000050580c42048110042c600780c0d0307940d466903a910108080e100095582a500096002c01081416816401800d5800342c1c06a02c417410446900c0d05420f02200740d00078007107070383c160030a03036050318140550841c22289035003001e9010b00c00559400210f2511701035026880000648c400002800b04035012003203503c100c5041015486604461054100c042004060b600b8280c0c0c4018501e85000b1000c034526000d8800030300f201d900000074401550225084040d0b01407910040c5142c8000c3c0000c42c8628003607400850402d0a52900034074002c0e00600000c1080d06014407220 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 196867589 1250 196866339 196866349
    0xa0b0702180c0409090302070302030d051207020106031208190c0e120f06010308070f080c0705040c0302030439030b1501020f0a0206030a18050d0305090a03140a0e030d0915050405 79
    0x402c1e21040c920004031741c8103130314040c1d1500e829604069454030480b0f03812401d175035000000f0074241d945101060607603162100241d003610310764000209103404220030201079034802c40130303650302000b0000c50703141014194400800300c40d00a0610030002d21001507291103800d040320400da6800c8032400520386007841c541070584586040c000100741b940000b6421091085500180b0340c3e81d50001c1d40075698802c074622203a607031829445070368000c0303003051a00c0f00064000d1003076a116076001710f0034a8030954000ca44c01c80d907058071945145c6410444850000304c008002250014510400e07900f64613013080f0b900c5604000300c1c3e210035811580240e107000c0610001184240c1d10300d07410b842642c0c882c0c07100d500083c042e0000e0400e001d0303942c843d14004400d101000801d600d808841c0e4800700320755241c2c45200c548030782130468040e02203040380b19982c10701c0d4601c80041000020798901000110303034000c0004d09000260400c80f0006926150500030004500e00d4048101a1414484e182625003030102e0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 196868839 1250 196867589 196867597
    0x70b0a020307170f060f060a1d120a060b0a05041112040c091b17060a05190b03100e0105010504030218060409080d02070c09060308090603090c0a0b0702180c 69
    0x1514a940110125240600460818502000d503d1420280b464130803c107500801c0103c440e070744100700512040c941400c0c04802c0f14245000e642c0e6602e0b40e2160041030582e0410621a0182c01c807041811a10b41440c041c0140000244148008900094080e0802621a5454000f0380c840d9145c24412040243c0107000c580081022125a03001540c0b1410041c410b05041e50003010300b50300b4440313030b1980b1030031512442180e07140070349031000b9100c940c44101244440440e0b8860300328003903800512040c6440c510300156500140144513040303461f607802090350380095880d011035081d50417080c06100104889907001d820203107011801c207891a000140e941c0c1e034000910f03044075000303c00b20f40a40c80740e401c00c805050b000320b600c9940f041089001c60080d030003540b00380c1d10284500380201e0480d000303004180484c3e801c518007900f000f40d44820007089500c00780c8481c00610501901c9805a16038044d21001009400c01c040d03207030700c50f9005000c9051264109003289024001c10000900e4601d0251 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 196870089 1250 196868839 196868851
    0x50105030601120e070e16020d020c131e0605030d05030402030a080702040b090103140d170403080c0c0f0a03121416090504020304060608010b03030a020a03050310170c01080c070b 79
    0xa84401e40c0845190300041820b551003400170300039481e0110b42c050144003d00d001e0550030b04100c2d4092030741c41040342c860400003d01300060700b01c1d080300820b0380b0f1f251030b201076048005580001d501c509401411500d0304d2240f0075021058490344100031500c0c1c02c0c4403d20805c2e4007814010300c0c40c0b520b0741c0000d846040282000344400c40101d0018295142d0f07070301460381a100035005800301c6d40c4a081155090780020440d02140c0f0808860002d02c0e0b12420b8020fa036001c14858061071510340c1d5070203464840c4010020f104428091001c2104100100302107850491444043c00310021513060080c00000685c22580400e420090711300342080098900f41d901410380c00c2c511600354240c8608480161490b808540e1050010040c0801c0c4925680b00d281210010710003003111079988824191680030b0036000801582207158a41c0c04240180c004550085034484141e8520f078984803440c4030004201c4004159070302c08401c000803075800c00b800e00c0e0010410700149090610342d0f9030b43c00001d0380c01000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 196871339 1250 196870089 196870097
    0x201020d1106071b0f0506100906030c03080f0c0a0308010f06091410031b0806120706120504031404080f010c09081e0a14030c01060504180f02010c0b09030919050105030601 76
    0x744003286913280c2c061100c240e80c0012645000400c80c14001c0e43d40f0700c1541c2c003800b281c12054000030602091b129080890344c0c0001c402c1c80491442d22400495001109840e2101c2400c00c58017400340c80034058084954404e403641c002c1541081b280c8107140b0b180d5040720040c041c0541090210326140c00f216a00814100c030700c0c0104100d2040300b00c0203002810400c01c007003485202c1c0180203903009540c1920401c2c0c2554028141c6045110460780c40c0380b640305000105030300c1900000d0818440e00a542d2050090801300280080c08030f0145144d17000742d100c110325811204004811110078026a20482d115182409255003081040d0f52960304c0c180c1d14890303e46200c076020700c04042c00e100c0c00c0c420a412800c0500d2451020380181d131203a00c032000f2020702d03501e41403010825161500c83c80c0b0054120182e441c0e00d520b501e6541101c0c00c51081d070b0a81c180188082c580c00003d0308410040c0c8200a503102171074540700086c09200d0502c4c40501e03015a8200500d00902459171300c601902ea001d0424a4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 196872589 1250 196871339 196871357
    0x41403032107020f010c0302090f030313060804060b03122106060301050d050106090207030903030f080f041101120e0309012003250c060807080105060c061611190201020d110607 78
    0x94168035044c03498108020550a000b414003e85800d80d02600206000340c1e09082400a07860416840f40704000e81d0180d0010102030900c0150310070f0300001d501030312aa42c002008001c010010386040b00c060701c52203d041c00012400103511082c0742c500c03c00007106407824964200840002d41a0105000d070360300645240c040001413000c250015001049030b00c2e411941d9000904005060500d03030300080d0080f9080d520240325483c0306e100c4540c0b06004124595466860b43c1e0ba888001a00081807141080401040080c841489100c0d40c02201c41b40402560346002550015001c04811584516030901200622401c044003108444c015502ca81496080c44040306402da03504890000c09008030703a46000101da11a042a0460300503c0c0940345c20409030b07680e404000171442043c01f80e100710307049000401c1418942c0d81c1000c034464581d0500b421681d900c8802d032442c0c08206039000c0c1030706c0d064075504015540c0500001d4001a200c0c548521030320410215039980d244050002810004018 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 196873839 1250 196872589 196872601
    0x304050c040e07090603050601090c050408060109090212150a050709060206040f0512030c0c0c0402090f0d0501020d0e010b12010b100e061605011e0b0a0509060a05150414030321 78
    0x406443c0c09483c9103202000845d441e8240307150340703003000d005e04e40d5081e00d4048003500c65802841a10116010f40000308134076070904c01e1540240c18202801c98111030050501c41050703000303119400c003608071100c0042c12843e01d0a03030300c0c0903101301402140a11001403c10301080740c2c0468031070ba005400154154000035185045860890783c164000007046010003400070600340030300201911885034003201d000c0e60209082104910404440d25402000c44c0500c64041c20074280744440503006070001414074680c0030015007642c0c03000704004001d95440500036030300e1620074000c0300803040040003081030603143c00125407450740001d448030600400d6100050711384c0e614000c1710943d00c81d46a0844139000e80380360240c041e0550b90601d082100001000d609100340d01d1040990000f401406c9520151401e0b0600401160190455402c50543d03003000c541d68460300c030350740340d40b41c500c00c03c80d5039440c500499079140d0110b220040c0c3c4241c00c2081400a0300c440040d0210000c0b0b600007000e02039071208 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 196875089 1250 196873839 196873843
    0x15060203090111070314151b0703081806090f010f020702060301051507060c031b0e011e02010905010e0a0c0b0f04090f0b0301090605010609120503120405030708040b0307030e01020304050c040e 85
    0x1648001c12244000c00901d0341c0101c080f41862400680d02601e4109841e509800d50ba491510082c40c2c42d0308d101030000b0000b281c441c12145d500042010b40078604c84c1d00481e003003810058212000c161546c40b40007001c1c02c80c00244921100c444d2144c40450409184d5030018515220600c1031900c12034890b40c090421000d05400c5980140d403000c01041185032011001d0090a28404414046440039102c6d8240d680604451502c0c1c41050f50344802528400c00960700702c210144040702159614160200020740c2485402c0220702c2c86001031502000c4d82c641041da01270140c0060103244010300c9240da40304c5154003601e040e641741202c0402c540c620080080c00802d001d00b40580c2c103609010103007041c80095402907043e1002682c8000d07999840b06400405580480c100402c6517208204804404640854490b001481403065915002494945082e0350f0429040214001030000c01d1124954142c441c51001962040080d411442c0c59201c060f01c0f0042400792a0003a502c4081c00c80e900001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 196876339 1250 196875089 196875103
    0x16081009020f12070c0c09021e0d060e0915131a0a0207060203040c0e160509240403030203040602010b0a140906060405040606021018051906090c090e0115060203090111 74
    0x710180301c983c44c4c070b081c64008001c9002844141c2c0d09840f28100890f104416008035504080c0c40341b030b402c1c124511540c10814540c441740304138010640d01c840110784c1c0a01c6002e194000d8591000820080252000460050b003002d1f000c4003408011091400c0083c00c03041d041c0480b01d901c07414101490344d40a1202e4083e00c504440203103903d200004200402002ea440380c2c06079440311109201ca039480c0c010242644105410100101c0c1c4180404010742c0350400940d200b06550710700144104400d0175010085800941085015800102c0c05002c031590904c03951080240c03c58090a80524241080d0742c0800e0781c00445004c2c001040009010f900c4607000c8600038030002e0320410100b07035540002034541c4001035920726160f041202c482140d05007503c2c00c450003074200c0007500788204100120004407903030bc2400c50b01e95071149518001700b046908014010104d400e000301d008452846524212110115004070409d8000d82c00c0c00760325400825207025000a007404004da41305001e140c0d140180c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 196877589 1250 196876339 196876357
    0x9090204060c030921060b030c06070b01090e06010b030a0213080d0c0b01140f0904061806140a060b03060105090f04090609021509011b0f020a0e16081009020f 70
    0x1000103000114640d02440000105020307070303504241030351980702140d02d0705030105a8403881c41c0403001141c04039503a13a006001c9020020100d428207150b91012666a4011400598908100400401854401c0d00854034148070450141c1525814441245050302010b4403044010f0350100728598800d400070f00300d030007602d400021a0710013824000000d0486440740d00440d00040804000034a035811100380004503c0024044811001c10009008242800500c00d440b05911602c4c81030303c19110418800d4024007510002c14046a00210b0110880014006011040c030b810820000d51105d0b0050300e410070b8003484d101d503661510000240c4d001c01e803c01f00070340c85407904014804110f05540031900b045e2080e55242c4080404400050490140e00d1090f4046180000344070500081c5402e03c030070307051140340b081002c281c3c6a0042840554a604030898255868040c402861412909128480031510b02440d45103401c604020018282e8451001c01640100c1c8a01c004651141500c100103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 196878839 1250 196877589 196877591
    0x201060b0a0e180103060c14041505030702030706151409040203060601031a150903070f06020607080601110a111306060e0904050138060702220b04020409051503010c08070305070909 80
    0x56140e0804400030300d60841c500003c01c0300d040202122340b0a40e01a101180c84030244503401c0d00e00c0c240c06440325480202a5002c60104010510010b030461050400408041c42800c40d11400c140c0d034444074100c03174103046200300890820040140e80009403664800420319001c22540849901807200d051540c100c20742c4000180240340b002c00b00310020700354280c0110200e40016a0b5183c014450100354052000103802031400035a180c1e00a08040c0e4000906150640e002c03500302040798201451020215441150030a00e03000a25000c03d40740d020352110102000003a183c6840900444200705085008200550004003800b00070360103c0a6160b032207101c01c51608400031603400e01a0414090314010440c48802c0c0c085013420000d880301e1540c0038008100d640c20080140003e164516484010345481e941030703803419211800500b00510803d840414642009202c00b007120907800001d50090b803400600c51280c40e4083c0701d0035001071050600150340d8440413802c884441443c1c01c282a42 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 196880089 1250 196878839 196878841
    0x304050319020f09060306010303030b030a0f03050a03060e09031c0b03060f01030b0124032004060306050109050d020108060d03122310300512030103120201060b0a0e18 74
    0x381c5550100552280c401c5405101da00c0c15042040b6000c40c00380c500d660182d2003e4010310009000754004218030310000d085809400340c4d036480b07880001c049032085001510203c2c0c400c140a800d40107003030190082d031100307203001c0c50981903240c1d481c0152400c4c030784203050002d141845410b056001101030700c0c014042e9100d515146000000d40300c0300784021904203c001000007440c0001202c0c0303001c905580468080c0c52040b0a004502030011800350444100c0301c180224182000310f001040113102c030752004500d8500e0203001408640e0720b5803009004106813000d910060303900c03043c60b0b5840001207511107030078845810201c441d26500203d46000e03c0c80d00f01d10501030b200c91a0128411249d803001008540d6401e070010000500320700c500c1485500c220106505600d6801081009010004000b554980305031103c510b07008108283c1500720600100520501c1030707180107598090030b0383c002400190700d0420003208a100b40f00c02901002445200c80c80203a46081c41000c0c031440c4103020100b1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 196881339 1250 196880089 196880113
    0xb040b04050f010b09160e09151e1507031407060501030618020108070e010309060f02071e2006070515060108070c021c080405090403090806013503040503 68
    0x10140c80c203803640e02c036000e030b441081407050040c95600d08025114055903102c00020407404d0304803603100000c0c402c2541242d00180c466a8080e8400c04000401058201616044c080c00c8520300c1c8a0028211011109903201e480d80ca0b4030240540c414644540d64003403c2c2130880e003440c0d4182d0703d50080d10b40010804240102c0f60880c1d17041c0e9011704010449003248a81c4491504440c2000a010410000001d401c1c24010103c8451100041c180030540b080b0302c0e034403241160120003031405943e901007510301c1400200f0340b0000c1d5146081100000064464030780c1c64400211030b08030708625050002031201030301c5000540b108a50302004964004403440a8000d454008580e036034002000c800c00110082c0c800c051135070016030050401c4c0e00b000c0c401c1c0c92150300454520b0307054031210410000050961180c0c2c4006224074080c0d0303100156641003c1d041c42c101081a8444003441ea90002c1d041003140801e2060380b80030345503503400c07404040c043c04850300714000e40c1d20143e40350140d2491000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 196882589 1250 196881339 196881353
    0x3050102030406050f16110c0a0609030c05041112060d12021b090c0f03060a0e010611060106030b090a0b01020c04020a05091305040506040318260c01030603020622030b04 75
    0x2c01940704890500c880d07510590001881c070012901600107850b40c010386030b07400e03001c2d25402c40102d036000e0986120411a1000c14000c1109500000005022101c10424495098021809007008490a1100c22070041c0e94480d81c0c045c07803680350b0440c0d8590021510b140d407007034240c0d90115440000c00d4107078198001e01944805280b08012003412403800c1080303480c80c1a64166108001101a050800d0a804415001030b00028161b039080021900301040d41c010003400c2600030142aa24409100c2d005100d0ba41040c2c1d040e03000d4414941007500d41d01321552281c40e101d61000d007260340056010440d800403854000a0100c1540241c0b0000e204524160300500030100d003101030b00d0f0140c2c100b4603880e20720100c41c01110041d2070380d00002c000c540024070903400603100d40320101c000b181950715a0040c04403000b070360a03500b0205481c41c10807040c100d4240250701440c4400d0904201080c40c40e00402c450384030b41c00400700c0030101e83c12184107403142c0e1008500a10f4102c908220140b4261600030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 196883839 1250 196882589 196882591
    0x5061b040e190c1e170703180206031315140c0c01090605070801091406330d0c08130f02090a150305010b030609120f0a030e010f05010e090703080f0c03130305010203 73
    0x2590f4541c0890301440d84e40074281001d0100d01040d03d10742d46a4581004500810b20160001d5084000c2c4c1d2007500940d0706c070000b03580203d4400020715a140d0031454032030700308480000c0c01035606081412640b40c0070910881160f00484880c2e5443c0d4a0300d4ad984c1340760060140c13000050a491400c801c1c00b00b1182c0c00b641a9041c0e4951980c100846400e55a1815210808403140c0b03521030441c100d000d4045400c410002c0f922207542001c1c01c07901c3c0e0390201d038641d0b50300484011040702c0c4d91503d2408066604c601080e4020464050100d000c00c80303500e40c03c0d10340300d9405010380a408134901281103207141c0d0340300500b0270140c000c00d10310842d16468041e01800070694094881c0c46a817010885034107000c42c17244050010300b19000c2c80c190110740e0720360458000396441700902d40d99498009000000303008004061456820002d4990b06150141c0030500c4098100610355100040610000300c03100100c0d21082001e161554440c10b02854091540c8100358401450002c071f4000003040010540140d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 196885089 1250 196883839 196883867
    0x2180a0506010f020f1209010c02090408070218011805100f03080c0607030b030d031104210c0e070f03020c0a0c27050709350a05061b040e190c 63
    0x648054520541280c0d124081d01e0345c1174581e040902141040b5192070020300b500712060400b028210501e400040900404035070039038041100150020861501412144005c180840c0a0b4902c1d41003241c0424006000b204810b0101e80d2500411031078180c8440d02c40c002d21340e03031416081c5140c40e0310300f8403159008280c070340d0014454a000700b101c0034001e0040c0540844007030010401c0751084901180605004856144200c1c402c20020036903588a20803a024001c00300740703100d03c845c010700e451510441940d0007041080e41690500c444150710041d5540301160910340984c07250340301008a8240003034880b00810035500c0f66000201d9003005482800018403400d11514800300f0800c01c0d200344d54003210700c48002803400ea800e2240c0480b070030400c0b03104601a54201413500301c041c3c0030300c03060351104014003460384a800300c001000410400c190340082e41c2c0c140400c5c0d10102d54204403044c095070007081d86503070907400011000c0e50351081c0c51a401c40a580c040c0501c03049001d01070110f445003200 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 196886339 1250 196885089 196885097
    0x60503011103010608041b08100e0d0c0506011202041103040506040b01080a02030604080f160503040807061704060b030a0b0f01090b180f090a06060b12011208070f02180a050601 78
    0x20620700752103280980f4120b4416031200080c2d0b55507136684001e410700e10391086032100b50895011840041c01c0049a60400400000060a0047c4900c1610b45402440000204407209000da40011004500b080c111915103050000c203025510004020f024030204010782d2410120400c8284400041c20b41d0041e0302441004417280d80b80d0180c1a200c2c0129100a074250340700c6801302e000038a2140c000e0211002e211282d5040420106c071600c511707081c07100166030a0b480803c05000c000820300c0f05000030300d1141081600d200d140c54a03440002c82c0100082d0500303a80e1007642c85039450502a401503e0b0307100038040003d2400421180d0714410a020b4021003a10b405601d4006040c0b20741025040207490560310041d94500c10351422480e0000c01f50000e07801001035210001c1d0b031600030070340a008540e03402c0ea105d01d0040c2030249605c6050344171601c08440081c1c10000708010a00711228981c1040402202a41500201d00c180c3c004100e1510101400e03001c00c0209841640132500070f1800b666 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 196887589 1250 196886339 196886351
    0x15051c06140903040b031504050709030302012d2003040f0b07050304030e09061c0b0f0a06060903031107050d0f03020d05093304080709150b04030b04030e120106050301 74
    0x1c0440980e000031100072074141d20401c020300030203e19401035a4807295844003800c120380a24049800d0303540a82d1744a01090000100707004060702800f401144490406000d044080000104d042c51904400112210b41e540c103901c4010000c0040c00c000c00f006c1c00c545003552800c1528104c0d0488103d50740984500000d0004540058869403c503406a9015074840d0f508061182c100000b6201c0640116070008004030313444110b00003c1c226402450240c03d0346080391400000e00c07444850b0003006d03849017034604501404800e0304401024180d903003610b03041b00c2d04652009001e1901303040b908943e07442011807440508001c0d40c0ba54001c001c500ca41c0c00d43c1c400e07494000c8181c800340101400d907684800110700259104240c001c0350b56840d202410348102c00c81d071444000380705074865000303600280c004a000f400401110f028001110030b48190482141e40f401e602500d00c1c1c055404000c200f04201e10205007810700c034517805c088800c002440c8010348690750780824001e048a104060080d42854 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 196888839 1250 196887589 196887611
    0x100b070f0b0c041a070206091207030b1302040e010e070b030c0c0a110112151703040e040c06020f03040605030f06040e100b04110708040303030b011101020307020d1b1515051c06 78
    0xb41a03030300179075000e0003450600350150200801c64551040b603108600c608100080032a0a034507130f050080303826001c3c000c7c1c5c1c00700c41e005110555400b801910382c20303810880b4204040100040c003600312190065800e8894840300c00c6683e00348140c084001580c850f15094a05201d800a0301401006003600c032140c2c0303882c0c0d40c220350f02034601c1056602c801ca11649020007c400d43c0c60117580303d080300e6a09491619441d0740e00c2d00040e98041d601902c2c02041050300740103064040010b83c1c00041400000d6080902d4160010b202d032000400740100e0349000408141c144c1c036150844401c1d001004282c0b5403000b01400400c0052460b100c100780310b54105019410f001c1200000c6813a42c5400c558094600307415500c040e0040d00f00b1048032030421141c0030380002c02c440c0a2000d140181c2080d4042c00446500403c01001d03824142051441d27002c400e00f60000261103000240f000006044010034a44044111902c0700c95080c0c0c41507805c071441d44103c5070369004200d89100ea6034411441007121007002 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 196890089 1250 196888839 196888889
    0x708070306090510030201050a050706090804031a0c25230606040204051305090c06030f0105010f03020c100c02070b070317090c01020304030f02041509140708100b070f0b0c04 77
    0x4e0354501a03034440502c0c2803000d54495030080510700c440b4144685000e50655502d0104c650081c4281c1c2c54841c0400c0510401000814058150310040309165841c02c04408001c0240300d8080380e00561100020511082850b907040242c540307400c042c0010300c100302801c0f41e0b0742e019402c91007010070340288000203034146820310a4405540d03001d042c1c049058900329a22004001c041d00041c0c5500c81c500c240c4503250b440000451041d030340b100001c05154548000500101a403030311503001d01d40103228144540b2000502c0e86940c03c017142021a00d4151120240d0034140580c1021418100000b41d120a150700082c81075055403203000c819803184d0304c01001c55210103400f081d081c0142c204002c20004564240b0003003e4460000780005000800d01c0c044606211884c0c0c4400b4203e902d940442c0c4808480203d000c0e0b203c2c180341400c800368500030440a0580c010380c00f8030380c40c00380c0c0800c02905105060501600007a48041047c5843c244401480a2030b082442030443c00b0b06104400c242c45602 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 196891339 1250 196890089 196890091
    0x9050306010605160501020d050c0d0c020106140907090302060c03070b0f07020706050c070b040f08010f05270a02062a0d0f0305060117040b06010306141c030c0b07080703060905 78
    0x1240e844038242558110b80d00204044c410003a80e0310b6400340441c001c0380d607240c4a118051003d40d2740d101da8030f848102d4100f003510821030502d401e69240000030801c0c0d120360422946031800071030b8901090756070f0003803e80e07091100b034002a4103c4800300f81040302d06400001050406c0c02000c0b0354640d5a5400403215070720204980e520016000940704121b510f000c1c6c0c000d0704200e400302d41603903800c5454042185003138005500010b01c0401002042140000c28803540008a042e240240018035280381e022000e44a15586003615242100c0700c9654101705021190030158010046076070380c905000030f00f500030400c4030b400107003840795452060340b81c10000311603040c41581c0c1c0b24941d101d45109401e5000701002000181800200d5a0021101420a803040e00c00c502c20001103101d800c1c400d000408586032500500305141e901102003070540d64039803111240e0071000c13403d02d80001c150700d401c841c4c2d00e0f55914001e007600c0b11031f17080c04490740c1c01440082c490700b00c50741e08011460350380d41101d0035110 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 196892589 1250 196891339 196891349
    0x60908250203100504021804150c020604020a0303050307030b0a12020102071706061e0d150615170a111c0f1b0c2f1002030c030a030b130e01020a0905030601 69
    0x1014a51200f0344070540e410180c1d201e80000e20050418690504040b5410b000700c0b0f003215441d1050131409540800b600c108010800f0501c010113035840e16901048030220b0900001e018054040b00168029220360400450018007821100c201c95413401000c02040c041c010890150080e90404103808074011024030000c14800001d0545484e00014040d05140c0c01c40d005440724281c0b441000b468451b0380024203030503c44ca0080346074205540040d422106a41c0150b2083c92440303800402e402c0c0d110f8a218051041e100d4860640e0315030300d441c8402801d480f03220000f5604041001c44c01211501110300302c8440160040c44120a10800030701110540440c0c06804028004d003486124071810038103441c18465100c1c428068100000a030001d0030946000404242c056051204d41c00c080d440100b030803807130707000440c01c00e00040c0d0350a4a0b4000c18240504246d55208100a543c0e40c5d41c0f907585100c0c2c400c49080091050090456010390b005511031404108010030000d10341c00c0000c3c0d2030b170480d4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 196893839 1250 196892589 196892593
    0xc070305070509060f0a0918080c0c01021501120b09030702040903080a0605090c0406031805060a0e0f060702212b051602030405040b0103061d010602160506091c060908250203 77
    0x280c04c01c40321400420100f5070104240a40c5a0000009849d510042490000f000010700160884034002854417610042c00064810035000401c060401c0002c541d0b026035201b680e14000b41c0c0d5441ca81c074a14060004041d51142c1005d0005090580108519001c0d440782c103014003040703071124103004c1200340a440310b10030105c00700300070040c81d803103907000d00c137103402004190300400b14903102d55150070400d442609500350798086c0348815941c104001c0c0c040705505d601a04c1e0034603001d6406500c440c4000c43c940041c00e1b1441305e4543c0310300c2e0b810444080c911343d0721f140890201840201c4a2041c502d10944e02100e2414002c12100c0c2d01204014040200c203600079031a144c2824240000350094041e0f143c14035480d00c41c0401c09503218921a5807542481120080661400d080240390544142000d104890110400d01c04e68607140103e03240303004140c0d0102400e01880c0000480089180e8019101c985032920003000c000c503035401041c50310054074001541c14024012001885001d1200035855 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 196895089 1250 196893839 196893859
    0xb030414160b0703030f05091f0b06090f011209110f010e03070303030c03140a020d051e073b0a050301020a0e0d020a080a0308060103060909050d12020c070305070509060f 75
    0x206214000400d0f4441c030a2501007010030781c40f03404200781c0f17809945126107508860113410514401070003101862404032030611800800c1c002242d007512551819a00a461810038002a40d00901a0411480c00c9440802070b0100a007403000007500703d2a01c1074441c0c1d00c0b0400d604200c1d0301c120001405118000c0207800e84130300d1503409a0040602c04054000d15494030903d2003d0941c00e00c4c00341c41600f441d9000f580d6481c1d12404c03c4222280103001c010880280210545858105806554804518180304403072100440840480b4405a02a1a85041302c0d0f020922462040d82d000029000c0a58541500503140c1d003c1500341e000745544880024154030303200744545071000b001180903001074000c6102d036446907100c07420041c04c2c20040c3c010580740d0040c032105580c103109080060102d0402003040c01210b42e991900d401558010404100300c1914041042100364110390340900a0800c40301c82556901c0c20645031542880f03103520404001d4000348103420011101440c8500080c410052 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 196896339 1250 196895089 196895099
    0x901090308100518091e030403020901170601030b090a080712140c0d1b170307090503010209090604150509011e080f070501051308070608010819080f0c0114010b03041416 75
    0x40070038001c242000d588254007000f074030240100702908001c45106d014694807801e50051151400c03060b0f1005420301488a04c142908002040484c1903a40c8403280725216260a16410301c1c0046444020317000041c006030400c100103a00001c4104c03134845444046180c0f1901d0300c5111180900300d8400c103540c00c540c0c20070804030321840d80e14514210100740040382800f10b46414001800d08030150604805c0001131101041e00541d040c80148070480c025841c01c0b000c8804100150000303002107019075215400c40304962103c10114000c2c04001d40070455070360396070709510240d104c8500c501668840802c00802c10500102c0d1018400c480c0c00001c001540c508001104c19522071440400100d01505020800e40018408400240b10035950504107504212040742020305880c0407008681060f0b10356800100040140c0c2c44003450340800545488040701c189024280701900d400441c01c414002007a0a050080918080d5004a4007030410031402501581d513109066014020f181c00c0c80f10400c4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 196897589 1250 196896339 196896379
    0x30c1f0c0201050d0630050d08060d02103603110109081911030f0d0e0a03050a080a180303021f021b0a120e0f06090409050609010903081005 62
    0x25610700c1071520074504000a921501112115044003903444960800314902c0081e0180101211180c0d00c48030300c086034195241c0ba034070441c04580704140141040024075035500c07a10988541600500442d28808100e54020001d0100907800407002e541c48500842e0210281c900304800c94020403c040c0050560711089040b000415203681080784147c2d0209803858140300182450418810040e0010f80742e01c0c00324000762041e00c010f8042d0380004070045120304001051104104503060140751860080003003418650907410103481440354038203000c00c000d2900014a200b908968030083d01540070612182d0035502880060300607404440d00840d840341e610354884810320040780c0180b50030b500300e1600d044928140d0691601e81c201b02d100301d0a02c01e04d074152101055a42c0f4000c0d100c0308420380003910081e14a20580d0007644086002ca030035888580c05a00400c0d009000c0722014580b0750f2070075010380b10b4100100d0000b04034401240c04d07404102010b80c15241c005200c4414403c0c1e0f004015 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 196898839 1250 196897589 196897607
    0x70f060f0207080705060610030e1c090b0c0a0b0609011d07031b0206180102040f090213080a0804140913082107021e0604080f030a020d0204090b030c1f 67
    0xa540d19400c000000015040400074000c0340e1150b00035124030310f0000100602030110303800b2030381410b041140c28074561402007800040c0d00604544001b48a00f42403044550300754a4000c4d007841480040c01d0102c100c400a46120424400c80440c00e40e540c41d48140000c444003880f41c103aa00c1d281402ea00303180c2404c1d6500660100d2146070006415500d5403e9460f030040014002c0e0260300200c05100d200c111020000210b00d08000c000c1d031038646810369807000760f4624070442c0c190580c0400c414500310307a41c010040040c40890308036544c1e200c1a040200c8a6031041c81110b040400c030691420f0142000c0c3c215900c100c0c2100c507580c0b5400195190004250b004030b03014011503041030080058164407004140c0100540d5005114002c615903000c4980000302000c0e599541c0708108020000f4405c40448220540c0041c040c0d03102d0310f840813003001030302030307040d0a0100c14008200458005481e52056986d1a0100e00301d6000d0004581800200000300b0140d200c4519150540da4403507000304220 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 196900089 1250 196898839 196898861
    0x605120309150d020c07030303060608060a0e060d05241f0501020703031d0a060f170105030c0628050901031b080a0c05120a0c0e120619060b070309080d05070f06 71
    0x5841d0143c441402c5e81005c1c1c607504103c0c0441e584040620804d40c1c02090941c1c040010744501003070780c0c1480e01c0035160075002048a4819480d03041410100002403240c802e0503818503140c0284800c640300101001c1c00110740c410208045e02500c140a0b0003030807020012180107070007820505042d074800307c609000d00701521100045943c2c2111064962022102c02003005a85040001681903c001c000031404c804124041408000602c0550340200b03107541c1084048420b030303035a031044014510980c00070403004d620000070130617100d1900b9000001441c1041e026070741081248038500c0c1c01c20b1400025440c40300010250750001e155018150701c0f001d8182c4107400d08906200000200740d640d00400c551094401d03483d050fa0184d15504040881901901120b9820b010080800425503424000b04614a0314000503156440c06072213502480290403200ba07002c2d038840d010304002c0c0c14441144521841d601c03c281407418014440e0b41914142a0701000d601d410b0f0f4415120240900501520 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 196901339 1250 196900089 196900091
    0x510020328111c030b0604050102190c0f0f050907050307020c043605060a0902010c03120603150219030213170c1f02060903030601050904051005090a0605120309150d 73
    0x860ba6451000300603035606a1841c0890404a6840c40ca0082c140ca9000e1221070249100340000d200d66a00417070780000d007464040b03110800b41d640b410728103188002c13980705801840180d040403030710b264a684103005840e000d9030351190640364602c040352030340310450700c000060f001041000031501d0305401409402620380c0440d004850310150054101303251a401d52201164541d03850704010303080c02425403020003882c08000e458807940002e8010411034200400300650603150555090a035030003000a10740020507150551400d5160b01300a50000c0203e107071424221300c01c02e210030702c03a008440d03144803500c1d0700340103042c50403441364140501c09904115600411b00d264102c0e45076440003a1f50100740303052420100d202001c0c06800d1100180100649401c1081040450398226044444a010580707000500b540e40140554107224182c01150f4864168020b110585406410001c01c0e20320448901400c3c0d000c844401d6600e102e901001a00301c1c0d440707a6204030115401014100c00004540 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 196902589 1250 196901339 196901357
    0x6010303080c1c060f06030b120c060d141314010e0c120106080d020715030603031704050307050f030306030c01050c1203100b0d060e0109180b0615030a060510020328 73
    0x2c208411350760540c100c43c0039452128401c00800381c2c0741c0100040c0c1142521010b404003202003030103480380e0443c512107000c0c900c0000c400c18006d400f42c1c00780c41200b03140013411203e820402c0188117400001d0406588401d0170b1080404444810f1041c040c1502d110002032100c43c861205200c0c00a16203880100d0039542c1e1180000e0108040c4018042c110141d406851400d0826820303850a1541509040405282003070904c000f82d0030007190b08900504512005180d90396103010703031452080c42801050303030007407000c1000c0e20320000000d5801000128140c4040c171940070011038040c02078100101060b4401056000c1c890107080046402c00c8401540a046640711001c070306d419440341118000c0381d030380c0700c20170050507000000c89800351400d41802d00600407035480c0fa84010500e888040c1c4613402101c0460340c80d80c0d44552030200000c400c25003d490703141004078a8002c003e0b131300c00d07075000f8038000039401d4516202000321421800c2d121006125813410035504503004000ca0030300c0c000c0c007500070 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 196903839 1250 196902589 196902637
    0x90607092d0b070204150e060103113001090e0c0f0f0a0609030510181101030f15080708030313030f0c0b040b100b0406050d020d02070f030c030e0306010303080c 71
    0x1400c0000d402c000c0300c400e942d480303503106000886800007418030a242c0006010300c0b030000c6440f03089410440921b001b189203944180840c1c414440d030525903040c144131101c46081d03201101c50650800360f0006240c6126a81e921040050720199414505203400c0b42100d08107924000d4401e015640000d8440c040080c50840410801001c60308101c01040e0302550070002c20404101e011580c64044030140509124504070755070680c003182c40140100c0162540c81e2040c1d100c1e500c101c591041d031000a0100c0000c1180f00c0341c40d017019000741280e82c0074588000c141c00d5130000880f0b028002100700050310440ca910101c171401e0451842004002c1a807880da00800c3c048039182d40507500811000000d4100220340c080041c00ba944290340c0070800b80f0040000d5a0008140c0700940ca40c880050394507418141e82c04000d102d82d81006101c48007026801082c1030b400604005014441d4480c1c0300e82011040400d540c0328001d1100400203165440000e10f1005600c003e4007003644020001080c0700c0f0b2203 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 196905089 1250 196903839 196903919
    0x2130b0a06180b04081b15090405041a1915140d06020c03030412020c0f10030c1e020609160b0306120a1208150604030c09020f04090e0a0b09060709 65
    0x80e1780300c0071540c1e01126045002803503042a034070401d8030803601c0b958000034181c2080802d01440c2c0740c480c419035035000081c00740824a000906100c00d884020001458100d0b00c0c40c0001c0c030010ba0341d89090349002c03070ba02c50710a5200300d0801030ba90741c28a8500310621100c100f101c07500c12003c003201c1c5c440d002d00540f842c046081000c1c41c0201c1c45000020201c25100c42d0081c0391404000d0805e104102d400c0c0c1c0f08407103032100101d240007001301d407a02296285200340c1c00e941813614440740c98102100720741d1103002541d01161842c015a43d06080c2d42d01d02d44810400c3c00c40c81d80e507004640c900e070005c001003410b61512003200c5403022512015141c42c50301c40d4030391500b060b5a298810000c603440c407003008000385880089128030142200c60710304060842d1601420b0075941d0140821076640010000403580081d01918010b1440328010b0125030004d62906840d80c030603190840740030901c0b201040d075841c0c011407802e1080e10380c1d82d1003005c00d62500052510100403a0b000398070000400441d1001a110 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 196906339 1250 196905089 196905097
    0x190903060614130b15131205060901050f1b03070903060528020a05090d030216080706030f09030f08060a081207110612041113021602130b0a06180b 65
    0x4464401001c0400501440140744511900038429861300b001e0440e103a0304ca40344041d00641800d90940c540701c400305207280c00003803900541c0740301c51744101c68030400000142d4580b0816810f4000c0c0000d4850a5003481c024400765542c1303840420040e4115506e902c01e1004c2c0d5400034032403400800c0d01c1d035a5101d82c4100c60051b03030101454071070f4241c000049007403014014419562010210315201e0740c0340c001083c0d805a071403210b21a20600c81d18209040c03080014130807810b007500c003900c181541c0341c0306182d035042584205070110741060080300750342a1500c140c02116800d921502809280944211404d40f0b0040c50154840c480c1540807420b50000c10900d0304200b00e017011103682d80c0190612002650b2080c10003803117668100b09158844074011a155085980006600011000c3c54009100f410741c100100301c800e840840c100c000200e80302c0c6580c55013402039954125811081c00c040e4241d901842c150340d0040c0e401c542c10040c0512031030b410b43c40401c0303004282c3c0c0d9075500c07164101c1660388 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 196907589 1250 196906339 196906349
    0x70305040f090e12090d0807080d0c020601090507021212060102070906060507021c080906031b07061e0921020f0a0302011e02040602060f0a090203010e0d030606080c1909030606 78
    0x83c0d511443c1103e21400c02102c1000909203075041d0600400d01c002512400c0c500d1001000d01c000402c01c402000803000541e40c0001d0f88403018003101d404188020f42d9035100740708200019040501082d1464000b040440840d0b81c2600902d14221180b00c140c2c800600280041c0c2c1180704846000481500500c00c030006444c45564003992f90380300e401000131300c440d00894180480001c06100300010700c60000c6071503061054660540721703544c0300d01c0d8075004602994021880440043c1c04010089164031803510480490492460f58015003500c208842c1c1069000740303c80140704000304400390581c4030100b030040500c1103c0010926070344035030501400303040c1200580c0d1510b0910101c44c4103840d400e102040c41180071820145014402540d42001130404583c0c0c859600224241c40225000513030700c26005002402640d0160060940e81d0304001c45004c0040e10700720000c525180700c1c04400b07005521103070440b0b08040007007595005040c02c800b900000d0091600700000065424064080184 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 196908839 1250 196907589 196907591
    0x11b080c01240303080702030417010606030507030e0c120705130c0912080f1b0123070c050a0809180109020c010b0d0206030403030f020f0706150f1208070305040f09 73
    0x1482404a9a00750750300c03070880080c00b41c9601c00004201a012204008498040c50004510348609809038214030464203c0030b00704110480c81d1100d00015001102107504943d010481c0e5a00d401044040710040c0c070416502d0f410820303000300f135850a044012980500c2c8402d07240303119914130000e6007111a091601c403065840c0c160040f65241c111956400800c0c1d0080410b0302101e11740e0701c0080034400d10303080c80c0030b403030011a0041c404d68050440c06039501207a0001c00080414280101e4100305810180c101d81d00c0c5a00000d002c107204101ca4800030394070000501d00d5650303e6030340056a400421000e9042801000032a900c036000d10040e600030003042d500160b80700300c0c0c011240e003990015001d442c050b0281c18820030060725084212540709403d032030000b40000000108001031f1085582c04086080082440700038031007181e010701202141c031040c461030b2a940e200718001c00a41c3e8403501c50b4002c0b4a894100100b00b021000300b007018271030700d059841d00d5160844000c118081c0d1708500301027 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 196910089 1250 196908839 196908847
    0x30219030c020a120b0109112703101109120c0301090c08060f1504020d141504050901050f1f1a0307170c0a11010b03010207030314180c010c02011b08 66
    0x50f0508482001c0903000b10302542c0c00d14042c0c1d48a0f0401a00180306004c0341030341c2e404900b80c044051806503413409140f07186c50407411501c0320540041101c142c207183c1c424080c024290007104805d100d070640030400c0c800c800d03080454500c200f000721020500880c0c0c1314050090028034a5600b0310a403090301e40314008500350b41c0e04001800c0d15220000340009080d0902c80c1c10300c10410400c0b407489a640300e0441d805039440d24081c60300400f414109004074100d154003c00c0c803aa01606c240b880980c69010381d000c209603540d140c4074600380d40c019968000401c80800100392581c1484031b000b1603114400d034039811103035501d210159600c0411078040351501404814441855481605200360401c0034403086801c0c102813440028510030b00e034103e801d00840c422200a86003081d0032030f0384283c000038001c540314401070602401905082c070814900b00003413800100301e100900201c0d440b0040c4180280405260725006551282d42c00700c003641840480c1004000e4031044000e03400d5a9441220b0003915 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 196911339 1250 196910089 196910093
    0xe010303080a05040f0b090c0a030809030d09120305070c0f030605041401021806031801020c0a021009080709020d0b030322051005030c0d060b03010303030605031506060313030219030c 81
    0x2141c600036054101860510041c800480c450080140f6000d030000a82840e82d250a01480d10b0031403403d58881e001596000300000f40040c2402030022000194142d0b03206a01405046492400a00511800034404440c00c0b0101e8401c1000d011014403483c5102d0b5441d8950310007903a2082c1c0340d441140c1c4544c48200700010000203810998808082000075411311940030300c14a8504901130806014103804800596240c01c0e58104100e0340140c80001c42d0b4800c50400301546400c10801d09030301420f1423801e407002c2e241c801d0b501c05080b03558481c0604511414030800101a41c040800540c6e400e403507a4150000c2c2d5400c2c00240006000300c40e044001018506243e200016650f00c0540319280385600416001d401c501200e03409080c42511030303500c02007514603600510780c0343c012402040f8040004000c01d50981c1c010b1068490480c2154403520b00000804103004003140c8040d0040014408500b10300009074001c50060321034019038641d199202800c10442007100d2054001902104591003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 196912589 1250 196911339 196911347
    0x304050d05101107021008041104060303020f0f0d0f0302070503040b0409090c050603070905090405010204030b010b040806010b091c03021c050d0513030806100e1804050f0601030210030b01020a0c0e010303 90
    0x90301d030f000c00038100d0030328140b0340004481c00c40301c411280a1040900c002410401c154050a107034000c010800c002044d20b904000350345000f0107003200c3d036900c80c8030314940b1104000161400d43c452241c2d105c40c5d4a51009108a001c1e400080c4100d98170322003400041418628240070f48082d0408010005000b0940c0c00c00071080314941d03011500901041050041301d95000c07034142c00b030f80d10948403800386450b145850b500a100d1507001a244214180000c140ca0309418020400c840c0054211042a601ca40104ca410b20585504d02d034000411a40f0f030001c130b1001151001514040c1c01a1141c100a1003820441e81402c0d142d85400901e000518005408861085607040640303440f0040c10a89c0301da40c003824502015040f58810400c1c900c06800c00782c4a00070644c0d400b000985042c16411441480038842e800076601202c0300d0090b0203070504240e5000501d40d048940062020740000040b817025070040820481c800e0440c00303501640000300b50003005000003080f086240b4076180d859810010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 196913839 1250 196912589 196912601
    0x102c03010c0e0604050d0c030204020f030928020d03120606030219030501050a0e090a0f0807061d100c050903010608100b0102060c0403120c021002060f1506030f090304050d0510 78
    0x4280541529142c42a4070792a05131000c4ea03905581c014000101410410320704039090744001d40c494000280d101f00d00407108080c40c010311501d130440e544210460800c031040134070000c00401e0b081840c074403000546482c5261501b00d9000e420040c454003002ca003d101940c031181c104074046500012001c002d00700c0010301402d070501c0c6180400165040400150101038180b1542010141f02e03070104940201c00d101030241c1562244404000da003a42c9010f40254002c0c50302501c00902c0c0c519440142483c45144800655451014000c129000e00c80310000b000041559400c010051205a00c641c4091050300050600c80c0000d00700180508142c0342542c201c48511411900300c1410320402040e26015101034951080e1050000c000c1c0700001c684c40300c10581c010754444041c0030301c9445580c01040340d0b40035040d400c23600c1c21150340f50310040800740086145190404001c100140006030094074040d00034107a00103803803070942e8600c0001c100d40d10140040e40c0c03d4005140d000c080038502d01c208 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 196915089 1250 196913839 196913861
    0x20c091608180c060d06090b0d1208071107030c0e0c0a0c17070618060b0102030f070204050a1107050601150e01170910021611040902090105102c0301 66
    0x10340c502024280c40108039403009065500701030810b490074024110240500c3c00e69280190169803903081c2011058040c20146c032408912601d0403000768154101070244d00070b0345401000d00000c2000c1d0355811036502d080101071904100c0c64480a50821000303000c035200950140c520500d0b040d0404141a080501c080c0050000110030043c0e0621140c000003100c01203038004140100b400b0500100c00480c1c03040d000020500c0c0c0ca0043c0a00d02d4201040e01611001d0280c1c0082215040510040e0b90300d205009242d00d07040003d00100006184c1904496448000400b02040b08000340207544099085008121a2904094018020f8010f00d644000c0d140c101031400f512000724007800a0310b443e07104003612070340000e501c0c00206030400c108018800440e00a50456845120000d1141d04014007803040f258040800341e595010b00d824000c41350091340051004101da446c040410280c141c0d480040410300200050091249820004103009841d19800a121540b491010075007120948214 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 196916339 1250 196915089 196915111
    0xb0a11030702100f030e10020418050f0c070501090503040602030909090705060301030605151306210c05060304140d08060f030313090b010e030f0a060b09040b15011707020c09 77
    0x600560f4400c040403105490506065102018410048000d0540400000803520402c1100d030518100d69008004a131788a581c401d5000e8170003000c3c4d505685064928840050011010503401800314005103503d500c200000034048859603101810341d0415401030300076800202d240c18060410b80e402551108488003d07000c403d00303110005510f0300044c0000f422159413040082c4601d8040c2d031030041303042002011700d1122042810004090f0a0a011b00080c0750008104072400759845445603080c02c4e07001e0400c07002d441c10881032110b0760b003000304191556050003990100d5150140000348000c50203031342c0c1d9011803610340305018982d602080e40c0381c02507004000d20900c5940064554065502c859004280c0329002c000417924030301803400082c0e16000e2004410010080090503c18082c818982480446600300401c51002c10803100913141030003800000301601c04903411403510a00505001014551441940c10900b400712000000344e13120795980c9142d4500800080e0f0300c0520901 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 196917589 1250 196916339 196916347
    0x906060b180a031a13020409140f0f0703110a0509070503060f0a030807020409030e031002030115020303040c12030917031314010e012a0c15031506050d0e06010b0a1103 74
    0xc0c40001802c0c804401c1158030744d20758046000141c46543e0307a41400e4000384144500c1c900d0381072a00d031503038907902c1c00740d882d1151001c0003044aa020a1000044d07070700d0409000900c4c03840d241d69034203104000d446640b005260001040e140d031080c4d901e0f402900740d5910540c0380d190400038008003051103088035114054043c4204006511f0720b0441c0c000701d82c140c0703000ca00d04c4e015240c165a4519082905949805a0082c40340d521000340d01960480d1030030002c0750071200f00c02d40181d8481c03200356009044c0905d0341c1d03400e102050809007050101440f905c2d215070016a140514500398182e408005010b40002555079440000d0791041030191480203c280c80c5144040d0000c0e00e80c40048507100d060010040f1180380380d1010781c0420084504200b1000b82c2d03d0b01600e481000d4820901516a8818142080800d0360344288200440000318195a0700aa03042c01e41c240e6503a00100150441c85840e1540c44107d9074040c0072140c0200380c0407078100d4484c0c0c48040090103802c0c0308a0100da040d44184 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 196918839 1250 196917589 196917593
    0xc1b0607150e0109050304090c080a050115050705070b04090606020624120a05010c0906020f030405030a150b220c030b0f010311070b01030b0f01080a240906060b180a03 74
    0x31000440198041000481e241e2800c1802c0c00351005140242c11400301181c00189002350381c00600c11001940d45140e9641d88404c2e08504540c030070301514011600d204000002d060140c0010400580208116083d0580c3c51079100c0c102d91064015035880c07134503507808010050301002410380060340484a403030701c1074a05210000101402008074410020400d14030405e40c1c081c0301094103150810004e0004058265019203040501d2165400611501c40c0c025840533010040d41c066030300050240143d211103444660321049584000c00c0480e946040308003503641d80002c1e000881d9913000301c0d980342c0c02040311060101d5807402c3d100000c4c5800c00c0c48003560f580e200201c80000c007909003800a2444251110580a0b0003400d10081c0300069582c008024032a00d410b103180b25215003040706000d60380380d5210549510703d00d07030001e100ba02e9610780504400c1d1502c410f04e0030360004150000365889a0348405003512050b502c02c4800c03100010305807074480030a590180c084101a158075603014074603 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 196920089 1250 196918839 196918853
    0xc0a1e0e060f09130e0601080d020a0308071b0f14160506130e0c1c020c0d030b0f0a0611010b030a080f0702010c151407080912030604110c1b0607 64
    0x222480d84a800c0005190701e402c650041034500c625805800020003030090162034000703000410580c211840380c44000540000000741c402c0d420490b550250081035181c0d54241d4140d940985507909011b045101044800309900c1c14221150242070b600f5151256414201c44640c950038024400e5081316200030240300540710707020b085490607641c4a5946031200e41311040540e294004028010003541440f800340389500150803130f0740c4180e51641100a0a034088000c0b8401c0340c0f6980003a4000a06103941c590080d802007540b4600a010403000c2201040003ea18011a401050201c3c00032504c03003036881405d114200342c1440680062800140a072500101d0380118211b0104142c000644103086900c90804c801155038072148070060f129562039604040d201e220700500c44c00c2c00000c0082c05003481100c9a9004910b25805020071499200d840348290340001c05040e08903490343c510114001c0c2c4403004105042100b0050004101d030b81c0c4001c0d0ba80c88400d0b6038a440f41c4400d202c40380104e484 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 196921339 1250 196920089 196920107
    0xf0213060b0f0304140601300c140310020309030406031803170703090f0f020102060f04081903020f040e040c09091505130c0e0a0608070b03070e0111060c0a1e 70
    0x85442c0c0c0c1c5035136803860244184065600d42d0308681c0503200002410040940307040701ca81180c10444100b54040181e11340c80510f441002910b88030815408001c00030012410048040000d4155200031540a48240c03da900658003000309601c0007600300803459062183d005408144080c1500340c10071510010500e600740b051165070040f400020aa00702d000e035000f100b0b00c030743c01002034a00c20003d007403404020060300426805801040001554001c2ca8040a0320a590104080f4207201101c0c0705030003039000c201c9005041c0740e420000b0300b010020f000058801003500e550401c41c0b500e401e25288951f0b03d0254400d00d01e0300e04100c0cac00c400150b66041166041071401800041c15640e104c80d00294007282c0c0b00240c5a8108540c1c0440c1c100c81c64100c0507c500d0015400b03011981d0758010780c83d82c0700c040d8442c1c0e040615051001c9290b0a11418665031982814982075001551a41540c0d0030890203071a14121000001503001020b40c1240c490054100e40000b005003a10280001800f0442 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 196922589 1250 196921339 196921357
    0xb030303190b1206010b0406080919060b011205010e01050f030d050304060b0d080a080919030507060902060c190b0f06031e10110301211203020906160f0213060b 71
    0x140380c1103a100203440f0342018807902c803915000c60b00c545d65121101c1c0350079806801210002040100002d414410003d0800d50100804546000c0d8180d66282d08000b49803500e0460304001c500481021303494064040c0c20301900002c0c7d81d0b403446516003000c00c9a58102c0441d902e00076003043d90083c40498002003501c1d4406c4d00108041000071a00380022443c0f00100b9004028a4000c241c40185070f40c40103985115150300c40481c0c2016224101d1280f210004e048000d000032410001240010440d030425010a8400380055041c2980f0b407501038181211500c000c6401103200c4150f50520015020303942e004148121180450b05100340441d4036014058410501d5402d070003099540184200300c100300302a1456410800030703800600c842c08070390081c0b140b00642d654041e0b51800301c4a0980c121030110342e000001e840903408408041c3c0c06500451841503000e8014000d4030702069041c0440c18006201e205540c4c0c0c21021481000310102e106100c0741d03c281d1500e40c05100070a04842190b080031 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 196923839 1250 196922589 196922591
    0x5070e0105010c081b0328090e06060a11010209060c0d080a110d0509100e0c1305150904050c0901090605210d050904060f030b06120c0607030f020a1b090b03030319 72
    0xc407000c4401851880384040340d4000142c1c1ca00710001f480043c0d140d098030b0151a9451841207655540b00c0c00d0103440c15900c2c1a40a1000c00850803028041c040044540b1000c40015003000c1c584d030000740e0356401c40c0360340c0d000c40c1d00700e68010b08115500025150380468070540c1082061390458085126001d0400c1214031503607183c001c24100203040101407400303000e11038280001014a02c0c0d071030301d0740100011036009208290010f5000081405114822141d0080070051404080104002d070300d40075109844501607428480e40c0ea03143d9503c09406082c0070003002c10418a42001c0c01215203113013041c03242c0314180503581c0450031000720b00f20700e2900c1d19140c11602e495420000600400361640304100c0200c9000000041001000200d4030540041391011071104c0810300c0140c460148100040c1e000344200102c100090240c1c0316101c107075100d03204031071203500c00b42d0761384229070080e42102c48248240e540c10012240c0b0380c010041c2c203401c150007170b504500380180282c04040507684032150311 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 196925089 1250 196923839 196923877
    0xc020a06020a1808010218090f04060908071b05090705090a0501030f0e010911010f1d2115090c03070e060d080c0a03080403020c0904021315080a05070e0105010c08 72
    0x284a1140780c3d110000e524030325210282d546954074000d603c00c0b000c10f0f5085a5041d1815030314036291000a22442240b100b411709650307035940350401418490001ca66003401804044017044440041c808601c101c0504410f002c1d051000304034580600419080c1006020003c10300b154445e400b8040444c1e4080c00d0101d880711002030090301034100b020300045a580b03440726000904c413110014101d6a14280c8601c00c0c8615043e42c1101c004244c81c441903d80b25102c4410f800c2820300d06940090188032070103406d0f4040745091301c107050044800303044071034a00000600002002c2804a01c0348490220001d01e81a486e2001100d2500c1c4020240c0b8810000d03010346030140f02c2440c0c01c84070b0000c0744c10203640b00f008071490f01030407080041e203060700103200e1540c0002072410000c04140c043c0da002000840d1034440202d12801500c020060006001010321001441c0102000202110340c03250f800340c1141070611140c14904641680198104813400300c003000412004000c40b9540d0b100020a9030756 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 196926339 1250 196925089 196925107
    0x12030518040b060706020304024014160905100e0603040813060801030312051003111207080d080c040609060507050304120b01090e06190216020d050609060a0c020a0602 74
    0xe002c419401900402e001030000b00701310640d03005600c280d1003281c00c400d0091911058001c2110040c80b2410182c080c16104155500d41001c0d401540c581c20303170080380c032071140e00400812007410703a10480c000d41825203210030b05800000000117054140c50201005244100c014000c0c0f000d0f0301d00e070b406810000082014000c216045883c3c1c90fa140c1c600c10040e50740d035000204046824441500082c101500758200410036000300303806522440f80d17201000e800c2d500c4107080c2d08140d003c06548080c45c0c0e000040300c407000f8480c080040440e14040c00390b541340707260044e2007400e0041c07044044c3c130400c0005016880d00490003106481103440c150f522400075160403440e51003287c00040b0001d280030041d50400103420401416550503000a100646616034616596035041c0c4015514401221036004840c81542c0540410155111203410032340203a004180503060300c0c1c2050340c064004d1700400c40501c1341042401d400c08040341c410001c8907000076009450b1410280700601c469000070b59208 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 196927589 1250 196926339 196926341
    0x2120606090a2003010b040824040605070309151a0a03020907140d020d15120309051c06050411040b090903041e1809050607051303080a0309080a0215011203051804 72
    0x4007003500b440b00305a41756103500c2002829001842155a1840342c442e4400000401c0c03007e4150301002c1c114a400c181d00d90342c1c4d601018007802050346081591714400d140100e200d2074259a2140f0200e080090701050070b60b04100c20b40c003000d030703a1400742e80c2e0a20f0401c0141c40c1c41070110f5005801e441d14020808803c5682074043c4a10503c0603c45400801c40400c2e04105501c21500341c01032120f040d403002d649802c0d421070500749100140219034010801c109504020f40c05900000d0800709051507881a0390783c0100300d802c1528203981c14030070340240d240303d4100ba10a002c03000d01c017115500030b14540f0314056683c80c840c84c003585200302c074410180540c100c0604c111602920b144924145003120a000d07001c0200301e0307000251114070036000800d2203940110226500540d4200440d8961801c0d92500540c4d0303131246112404050740c6032031110202d2281d0000d000c502030242e010706070b6400c40b20304252004a040c2c01950403040c0e0300c003103100020f400c00122000000300d42c024405540507800010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 196928839 1250 196927589 196927631
    0x215030a0b0d05060118060303210608190209090c0303220302040c170c1303030c05070902040e0f07050f071112030f0c010501090603030903151808030402120606090a 73
    0x10307000b0142005440030000c0118509050352150940740e07425402e02003030001a01c0c214400540840c3c100c41919240d041c4001c8031002c403040403000460784d0342d0358001503031810064012a190707205c107d11080b411407410390368243d0060400001081c5a03401301c40001c1e107078070070310350284d0603a501e000e04010740340032040c0034100540c0c006100b00601c07025100c0252141d26251700750f5005000007000220103200d18000d03600007007030018207141424115a41a111400c01007820b0302c8a00c00c6444c0010494110700084c405030a00c02441102c40c10044008140c011001c2c0c051000e0000c28001d00c0c2410740b82c070702912000794125201028441d00c28001c584200c2c40128a07001e03d0000017104291051010002c3c4150749d4020000c01503680d0701e0940b80100c4210380030003000206401e20410108a003401034104108110780d00003800700d507606c40c20941845055040328580e4012041005500d81841c2c10703852122281c0181a140c81d01100180c48080b0003400814032543c0c801da4480900c101c62204 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 196930089 1250 196928839 196928861
    0xb0f1603030605130903030c2f1213080f0a030518220b0307050a050a0501030e1002030a06030218041502031003021806090c040605040b1c0f06030204050c070215030a 73
    0xf080701344004071201c00c00741030030030802d50100e4102520400344900c169540000c501e16020380207600808030101140701d100d0842d00c440c0c2d6114600d107501107040004000c280e07502800891103513036403504010701c0c02d12020b921250115001803c4020110782c00c18215801d10620840092800c110800050305c04000c2034840a50340c00c410f001156068510303030003d22881000c5084400071a551000c104075552680101508401040d404005d2035009410800c5982000741c03d54039003c1620121000326001120355180c02512040b0420943c03c003070000070410a080c01c0e001c0c44030319254aa201c1080b2000f0340b103026140e0b0010000c2c03050000765404501440d4010030400891003881640040400140c8005115015210108000c0854042100c088501c69100d490a03e80f401d020300d95690003245802c4655a0b181401ca1118038481c426568540c1c2e180d10000750890440c018001143d600a0803003030080c1c020064400560b41e0005080c1c0c52001c2c001c0c0b9107980340d440382c1200300038000c0402d003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 196931339 1250 196930089 196930099
    0x150d06060b12010302130c021005040302330a020f16023d020703051c03060302090a05090606030d0207120203030d05040506041106090901030f0c030c15090b0f1603030605 75
    0x11507402c0880c25007001d4101c900032101c81c0c941401844508045882c81c80190000d6401019204455800c0d1381089500501070700648141c002c0303010441c80024144a101040ca0000d1194103809800c0c038140b09c4d80240e845070341141000140e001d84c100520800320790307000317039103600e41090115951610840e80d9280c840c0000610490710526030368000441c40c0c240104031191007249507101d48000354480450360008000d1006c9590009200351207211802c81004040e1a110040050380707a126032240100502c0400040b145003024616003000070203440144a0f4000ca40004021a8000342000a5880f02d600d4520806120720000345140304510503084424204001c000a1042c04500244218001c0100110100000d4104500e601c00d905005034040ba03124014800b0403004111245800e106900d0030700182c0c0c42e92516844080d6540c0401c4040300d0200d845011554803090305e600074103c14510608204511007641a00e0040e40240b0414034800580c02051510a8000740020300e00030380 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 196932589 1250 196931339 196931347
    0x14120c03090a051f110c0634080609070201090201050318010e160501020616050f0309150a06080705120312090a060e01020d110306030c01081807090b030d08150d06060b 74
    0x4943d14011034080d00e0900f100d840c5c03044040101c0d1485040340d01000e4120054541981c03829441c7c00341c0b500e41c1284261178840c00300e03031180074440700000804080b480d444415007440e1400c2040500f20005100d8802c5905040b01800140d8001050b00c1c1c11645044030102c1c02111400c0e040c1c010800c0610001c904d20559041d85056004005e11005031361007a401c2e0781056031a480211510b2100c0348912001550800c080900182c070768001e9508210480c054031048041400c1040c0c030706100b070702c541c10201d50300c4404102c031107000c0128900519060b00ca849100301036480c2d298490040d10301d9900820030540008107112001e0180c20070203540408100420424400058003e401c00c422000350149412040900b10b000102924130a0900030024003141d604040111754400d00681410081600c43d10700e2202031300c4c04d00c81307a006402c50080000c2e1500001040501e032031921110031003401410002d0040c01203040c0b101003a440002e8400d03503d407030f00c0c80c5041d4004050903840b00f081508081 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 196933839 1250 196932589 196932613
    0xc040203130b01030f060c05041215020c0307110901050f1c0c030503030c040f050402071e150915141003030c05030910120e03092409040903080714120c03090a05 71
    0x214117224403401103804101d2001c8000d13040d41c181c40355005641021944244030f0001802ca6800c900003008101c40c003504142c0000001d503e15048401c00301c40707413086801d0403075050410340c950600612089030205054200321002c5008910007450030860a605550300d0001d0100c0102e6082c0215070002c103c03a600e1601b001d82c100d0b03540040c06940803070421003900113074928060082d508404e8120340400380c80c1c081c0816403000d456136a00c01312482c03d070348000010203000d94410f841e00e41d80504c0d0b500d100201c600c111801211164404240d200c1128010701940880002c02c1c4415654035040031103240b03180b403c12074654040c903140140e000300205010030090364080c4170380e00140d9601c03000b800981010398550743c690107004400c40d0041e400304800a03160441d1020842d0040ca00b400305440c0c607007480046001e4a00516082d000704810905011200f0341c4082124200f0b0303541c0701c010303040c0320a040e800c0c03902c240040c20a10301d506d0b011010820940040c458116000d6000d412645a0b00b1301c8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 196935089 1250 196933839 196933853
    0x13510050d050a12031104052119050f03071a0a060503060403121d030307051303050102040902130605070c1a0910020607020c030f0601060305091f0f06090209030c040203130b0103 79
    0x900c50031111000c6104c0900382140c028007600c07000103005002d44d42010f04007002c0c004c00c4008601490300d2007a110700d1001c5410014810100b0341002e054801a20399981c0c1012450040c5941512109500403c40a4049100600140030007a00016501500d41320781c0c20540103007403035800580e03250007404140000c00d6088003132184a039813440700620690440080304c2041100c2040324440d541c10800001e2200b0b0302c20001042501010b180307051206841e5120340e402ca800130381010103030340c1d4006041da40c000c204c40f0a11004016a1402d20324241c1250307205035025042c1e01c01c403081c020044030004024a07228054a52401c8047c0c12198100d00b4100020b50342d45c2c042d1225409405004c0c80c1c170405080214070400d104940034001d20040e4a0004220010400100098014000d0f00c4281c0000d800d4814110b10035000d08a000c510f02e00100380403411510168010302c0e016104005003102614042600b104180048500617140d5942148820030802c01003402000d009003030b0001f00c00c001c86 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 196936339 1250 196935089 196935103
    0xc060804060f051e1003050f01020403031704030504052413060e01020f15060105130b030613060e04170f04060320070c03110105040b0315013510050d05 67
    0x24801404411140c0152500f00c440030303554000c816800d0410041d01e0500b0600050300320182458903400550344c1d880c0c803401c0183d0304c490351009940014041040c5a800804039420200d9105010f201e07091a5401034100c0c0b2851080d14000e60f01924004001d4044070303a440000d080c142c04031551110b00c800c2d510307414a401d0290002052103442010f1080d4030004921018a000388001c1012900445480d83c07118001054141004410821030324001c1c0302d003811000070320680c40b0b21a141d00344441008084101021441d403560300d803000c20000e550051040075002500124a808100d0800907910410b20278110038084442002400041c015403503403048039241d0107040c503444412107400c00c211451180382e00280c24030040b480e060000c070b60b403100381d6072044d20141001032620390707111040c1a450300100c030b100d002000c0958480ca07003540c1101000c50608020f83c0c9072403071000b414480910010984a40400b036143c0400041c600c2100c840e08403000d00001090001c3e405080e00c0c1241e62040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 196937589 1250 196936339 196936343
    0x10f020715050a0b0a18110f040807050312070b07021c0c0b060909030a051c06060c020906031c030c030e01020d0203060120070501050a020a0605010807050307240c03020304030c060804 81
    0x40b80c0340010303404034804d1240100202c4010b003113481c12840c00c030f10142105400e1003072991440c2c0e6403040c0500d40c0a07050040407c1c0460151903601c945c0741c41d810700d0803c40c40b0b600090203600100b07410244030064a04039252203a0015480c005610b400004918250406030b41c1d50101510560050700c50740c0140640c10079501c103400d201a41d594101c10f00940703020a883c2c402c0c0c151300a00600107400e0140b0054062890425040d03840c08440e00792080c10759280d81d004102007148451b088083d03042200d2182c0d80700e80241e00803c0c003d46849869094030f521108140f04040d665021030070034501c40e030012550303c5903020080d511010041d1030100254001d0304c0e51400308490340600212080d50807408003800d02c0a2f03015100b140d14050064607542e004d01448030460148030240f00004d08603106041c064800100113001460070001810f1405880f60040000c900300110041c484110f50404850140c840d450490351041e450719059256000302d40008144043d00d01d40425071a41c01288903100e24 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 196938839 1250 196937589 196937591
    0x10e131109150d0c26030a050a14041202090a0b030a17040305060108010f1b020303060402030c040905040b06030f0102091c030c15050402010e0105040e0a150911070507080d080a0509010f020715 85
    0x281900c0341d0030402e0005c07003218081c5800a20010120714000c2c005005008924200062140640c071000e512650058001d00703402c4805181040030740c2000044280d0106200504205401d044070001e50350781c0d0925001807880c82d81740c81084526403d03c00740c8000b1a0300208640340c6584401059001c2c0041e2050803c10034641803201044014545c4880410f100340e802840c40c0d07443d008280806035000a00c400f072600002c0000068030403862155074410780c021002d000103030034a0020181040c101c0f0210b1a00c603030040c002c204040d03443c51034013030600d040c00158046049403440c065801e4114103038082c20b09a0b01c110fa40c90007400503008144114400d036034201c4005441401920980942e010f4080d48140100c0018058500343e449055000c0c0c10072103009843e503564046805903900c480f0600300e09000410000d080210805c50704014010b1403018141040b9408801402004010406102292120302158202c0c40a5009103400c2d00000c905541c0c64a881c00e00c2c0554281c06203050a6031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 196940089 1250 196938839 196938869
    0x320010e15060901090b1903150b0a0815130b010e040b0f04080d0923010204050109050307030203061609030b0c0702031608120f04090f05010e131109150d0c 69
    0x941c1003030300c12522514000303041640d16420408103100900919510f59004024000c0c030842000d441580107000714444c40400001c0694912031406990403101824011055450140220311000c1035100e20045a2909043e1980d5a079074103ca98202500c80540b40050200011410550200400713100b14021081809a6181c0c80d0110303200c51822200904800c106000c06980d031241500715150a5014521580380d24900344111fa040c0120005401c1d002da40c00a4100581c0d6080080f14005103400c401403c0c8591544d0007103510348074001d01c401032428051a1189605028220901c05036070421003581e1540b0f001c0c201c000040d4803180781a131213032017180d503000c54a146400881c01581d0300d101c0905201000400003541d070383c1050f142c00342c40d00000d11000c241003a940c801d6801041132120046125450f003042000740d1030f80078100302c540c004c00b45464004a140c00403080c2c42650182c4102c02c060fa65000400c4200c60f80712000b981c822104040d08051020060888080ea44550901c0901c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 196941339 1250 196940089 196940113
    0x22e0507020a061d04050901020a12090f0807080c0a050a02090a0c1d04060305030c0d140309120f0c030d0f0501120c120501060503120703030b0a030b130320010e 71
    0x190301a086009500680c0d540d401d00185100314101d40c080d030702a4000b076800c0f594050009007030790002c40380b003a5540c1d40420b55403100b40e880501748501028203d0f0401600c1071a855014030607410a802a020010002c0e02004002c9101d08a03031a041c05c5a059a40c0711050746000354943e115441c0986c460240003021411400c1e46107e00c120301c10b00c0703488900381110005d003408080700b2008041a032140e80c403000000130582c180300411490340508054142031001d4000900000340103000951119014000c10490110010b500c003191400d04804c162102d12402602c0c0c600d101c1c81c4d104101074003011070030200f1440c03da000385d82c28070f12541051210343e881e070f1401b1441e06401e800c050b02c84400024208000392035006c84480050056001140c0e454440340402c3c030b0702045c05018885c00b031000540105056061048260a0a0840350307460b4040c03840e15402e1040802501150f00d0444840e03c2d181018010140005680c0340c2d03405400c2e0455221040c2c60080c000800401c1c400d0041e2101c0d220 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 196942446 1107 196941339 196941347
    0x1081c03110a090f17060705090316180605030606030a0b13020d030c03120506010f030c0210050c071523090c060403081803010515120a022e 62
    0x241c49a280c002864101c050700c2d031000820401c00810000302c0710303006c0f944c1e6810540c6450308548a41d0b2250002e030905e030311070040d5002e0149884000610400507007400f00c84082020041210729070790010b140c0c9850f0101c49055051700a00c202c0c00c0001c202c00215500f11311608804500c00352258040762901c002c0c0401038010a140f58003100c101940804c01c1c0d0b5280300424001c0c0a58200fa50010306181c40008240d8207050b01e412640d40828803c0040040e21340081e2006d000c5810511810801c50b40320103829101c0d100d603040921a102864014003409403e034111b05c0100e124440d03011841203001400095550107410b4201d0140e0b0349120141c00958040d010740780d562064010107000242024800f075019904040400801003074840d032490215a0075141c15541c40e15170310b0014204040c0c51070095000d00c8000c1184200559040f00c0000c104a030025611048641681030b1 = true := by decide +kernel

theorem cover : BRFrame.Cov 196762589 196942446 := by
  have h0 := BRFrame.cov_init 196762589
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196762589 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 196762589 ≤ n) (h2 : n < 196942446) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
