-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0737
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:30:23.073897+00:00
-- url     : https://prove2.me/submissions/12e3dc54-d08c-401c-a2eb-825f0d9132b0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 132374100 ≤ n < 132553956 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 132375350 1250 132374100 132374107
    0xe01060312020d08420402030f04030206010905010605040e10090501150306080304030503040614090d0f1a06010e0d02010c170301030209070801050105071101030905060108010e3c070e090604020a0803 88
    0x280000c42580a0110301c00f580190143d0b0701800505e0980b614442c0d00c0300800642d40ca15100004451150054400324003501c104030000c50308401d503000f402c0c140d0b002540e44900303246ca00380c440d884945018249003504c640d02c46c008541c10845000381380c080c1841e0581000004480708004046601c994010800c1d03800c1480184002407000c0102c40c12207042c3d141402240007001100c1c0f06c0307031040c0310301e0640c09614034079a90700300310321b46c0b042ea030741e06001d90700d22240307076035440ca1600c0c40c910211000d0b80007554007140c401a41c602003408424080c0185130000d42115070b60f50350600d83c11409054451810301200400441c5020b0560384c2d4002514a0002115490040040c000340141e0200905100303a50050300266482544a4442107400c01c040314680e503901c464090081c50342c2c005a450347c0c092903205090800382001005001c016045613207901103a03901c0554103000c426402400c03d4002e02c800002c2191f4048100703405a1840c10103012541003502c1000f9038005141d0040038541c0040c0b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 132376600 1250 132375350 132375391
    0x1020c100207082a0307060b1201180221070e04170a0503070804020f090a09151e1d03071202190201170a022703060f0105090a0e01060312020d08 64
    0x11030a42d5840b80b038036100304c0030b131864031040180a03e00d2586541120b200c0030885000384401da41002c1010300054901000a408182c0d080b400d840c50103412060f40a41001d01000600f8a20a444020a000c45481044040821a990804603d40c0c03002242c45000c10904c014044505a004a909028004145000130321480035209006c001c00c5401030224400010b015501c1d00e48440e405500010040d51652130500c0b444401401d03200303030659003a1660003d01c44134112600c612035403e99441d03914251301d541601260050803005030b800202640680304400e07a4581003001e032509500c03a20b024240000d070100020f01d0700c1c0c0204400c8416080d81c00d091000360b40c0201c03002040802401e841680c3c3c0e0b56000100780a4450b003a04188280703608030701e0406800d8481c04940650030304400381c1d005a210144c440d1080082070003103941c8460400c0218008040c1580101140034081d03001040d80340e80c0703407034a40910702087c4020000d038008114a0241c140d20000807903100c205c01c103e0100c1d8402c2c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 132377850 1250 132376600 132376613
    0xb010504053c0406020703080108010605030c120f061009110405060703050c071e0305010b04111c060e0106081e01031101030906140c0403031103121302010e0307060201020c100207 79
    0x300c10341d4600150b403442d0008080501c0001040c0d03018400c4650350301d00c0c1880d240030802540260800d800140f1b000c0000b096a0340d06001d03200c11510001c00800d401361100041110207107140540510a22640c01c40c0c01c00400103001c02889081049400b140c1c5915200d90b039810b8410081c40410110400c0000348030554070b0384240d0b0b801540503e4203a4039100c2d16141d1600d00304054105410000c5d1050038900702a100007455401c1e82d202d0b1000303101c441c00540c00c0c08150b03440900d403070f14602c0003800b518007010110402e06e2003500981e1000308080d80c0e1420700c1e8118071400e0300580009003c9408204070440000020000011100c85450040d859074941161f418500c0c3e0300365041640761f1614a06101c855048001002011494907003107040009182489600c03603c800c402107101c4890800c040c0c080441510900d08502000200540e6100301102d0f5005845c0d9089045c8801c080c4c0c1141c054030101703c840068002c2e5000141c0c1c07203403041861854200c0b048800141d50f40100003500c00600c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 132379100 1250 132377850 132377881
    0x32e050108060112080c01060e01061404050a0501051e0f0901030605180f10050303180a06020a03050306090703090506040506040201020c03030c12090d020d050c0f040b0f120f0d0c0b01050405 84
    0x80070703d40c0c0f4100301010302c0d110b0128400d1b54a165015030920101080d1424a500028101c5180341c036005102e040212140e84140190302c0b42c603a000b44000010002d65008a00410f80c0e88054007d140040e8102c208060701608158112900d00b400415403052079601842208054401102c021400742003880d41920058002080548900030003804108017401804292010f00801000d59031111080c80211001e0304c06e0018a07445207e540d00e000614a001040001030290140c0d21704d45076990309014051807110103481d150800d42d440c01044082001444003901540c42a005804107040500009185c0308501070720501c681c1080040c01602c10002520f4000005240422920f4000a000240003d079000c4000303500f022100081d50204480814240c50038441191001000e91440c0c01303000c12030b0310b1702c07038242d8004420918407070080c40e243d0640c44010980008580808450507191030405039126100c1002c510750031541020003110701403050140c80c2c1500d0400ca203161012a0b604c0010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 132380350 1250 132379100 132379109
    0x12012c1909021908060907141014090402160c09060b250b0c0d0c031a0103151e060305090c01020307120203070f242018032e0501080601 60
    0xa960703803440c50454a4046070750300c501050544540f1100e58445880e40c03955000c807241000f50240d4500810780426201c1200003140c2c000e08a03135100c3c010030320150390b4000711641840341120240070403c1300f650340e40001c02d580710358060840d103440301d5480e110203046450382054001500704007041c0b0030044c2000964102c4110b03402071143d0044020f5040640c00740d0179001404940301c400400c0408400070b401080ea9184907202003000c210f852004804075001030280742050a680405214030390305c171303802c103000105080d190302c100340d82d90f123100400c0115404071603072907000c48000c10448203415108076070b800030b0108043c00a1240110000752240310f03070800200f8850031507141c1c1d2000f81c400c005a51110342c1c03244449011001c0d5040039094505880362000319031913000c294403080e82d05806520584080400d000724000c0000c40311b508a50802c403180c09036028443da2402c500da40411000342c86486018000b50b042c14840c040b00c0150b802c055000d003590b030508004004054000a000741100d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 132381600 1250 132380350 132380401
    0x14d12090120010204090213060201050403390606060215010308090d170a0c061a01120e03091903030305131110030e0105040308060a05010f050f030c12012c 69
    0x84151203803030a402e00d040a9440942c0302013000f084848942d401044080c0c0c0c3d82201700166a45c480c0100c1c242c5034102c6000b0009819107951660300154241c0b0110340b6850003c1a200307510000f0445407059502d803000740d540d2070326400100402501484040d240d48840302050358952b0454850210354400c40e43d505010348401213001080c0651030764288111405140c0440e0b482092950080001d41d6581040d60b05170301c2d094400f035980c210b07140c01003251b43c010b84a1b90b4010790302d480304030000c281003140001240001c1112074101c0e5505010075001e04559048000c4050440c00c00a0071124010010038140301c60081000210300c81e500c81c0c0020102c115480089103444410407400344c031003048660040e41c00c15041c40200751300100235601c00c20080c5d0320000955a0f03000115441035104502e038012440411042c15078000f08001154000002c3c00700e1450202e4000b03c441c84000d090f0310601d004002d008810061001b00c040e07042c041c40002000e030b0160b00706001a80c1c8000c002e10802e0004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 132382850 1250 132381600 132381617
    0x5070e09011a041e050303071b05060a120902011b0302031308010c020a08030a180b040b0604020901050409150312110d0201090308060603070c0b0c1e030106020c014d120901 76
    0x200c0c01d15045413409440c001d82642d440705894503103506100a00100001c41200c00b050100d1f450070020113441620000355580d6440f070301001501d000406c844042a0f0402c0326400401ca098240142d82d5100d0501c04d80c0110740d1058806504100040c00c1d07048085141d06000407803006907070014484140346e81026180350390351254940c00d001012254110300401c00804144400d008808008034851790145c1001c201c0b55486800304012031260f0081d40740031803020301003444000c404d42e0010218541d081c5450000c01c1d2691034028091254000120009850b40003101500300144844a45000346000a00c109025540c015126400041500e03011f40d4010000039030191044640d410816003005009042e1b0a000e03000c242280e108001f40c1120712010804960104202c0e0100d174100c5181e54007130f228026944004442d28a4a0000412065024a18050744c0098815181c00407075000c0810f4550518007900c10484650310b155024003a001003010740c0c403004100c000c5130310350842440c02002c3d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 132384100 1250 132382850 132382889
    0xb0a020115050303190e04050408091e09010b0a200c180708040b19060b0a030b0a080703020409020102030d0e060105120105070801090f06180501050103060f0303050703031104030605070e09011a04 86
    0x45d003170041406c40d03502a0600f410310003403084100092882080a030381c4e544610341940c40b28254415007411041c2c000b0304204c010841d4000c50b50207070000c4030680c940a8640c048810941540598202c00c24980e604078958450a504c0c2c14410b0b0080e40011044504044c5040400a840b82500401c081e214043c600d0010324643e1080d0500c201061101608021041d201c59141015801468980c03021a02e0240300b42240e203091844241110115001801c00314210703424040600b0720248128158803091200c41d480c142c2600030006001c0c0d21100905c0150714000400c61090002e64003400715916007030901880741e500016147c15035030420000300c1c11110f140403001c0100f945600c8407102600d05980c0004059680e000a4101c81003642d0074846251200700c0e50400b04450712006020920030406d260000c1d0098000011444403040240c5c1407170350325203030401610070407204480080d00405c50040c0c1841c10066480c003400e0802e403000100752010883e8426071049018100e00070320181007254 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 132385350 1250 132384100 132384107
    0x1b03100314060109061421070308030901050f0105040c08040212120c03180103021213030e0901121b0614090301020403050706081b120703050604150b0a02011505030319 74
    0x24011a0722401803090744141d0003141e529000e0a00480720018144500000c0d641c1c000600e82070000401010083d20442c070120300b4001034802c040c1c0d83e095018009000000c2801c510180d44500504030022a00c1d24001013421000c1205800081c462464602441c680503802079102d640240d0555240702024890154181f6124986903401d01d501c0300018540c04d8544080040d04a0603440440c84a135490b8440040d0f0aa02075100d000f004007100000013a04504c810151181d4540241000348118003000007050310320409802c851074242d101c504000c100512400001c07410090603446069980c00c007040141400001c0303000b0940c101020844240e555000e5044600555000040311700c190342d180320240c0b07015000c881441c0c10840004802440102602c119403656502a40000d1243d07030701074050300109800303001c41d0381042d69114a0404ca14100200102404902218645070b01e0303045002401d40f0703d00e030418515075016400400550300d000083d0740640100d0703c00c0d600c0411040808a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 132386600 1250 132385350 132385381
    0x60801063603050102130519150518060417060a0b060d0e0114150108011508011814091f18060203130f030918050603060a0c050705030f04090b091b03 66
    0x50f1007540b00080c0d40b011042d142c1c05d01c2c400c490003034554039000240c080f00020100c0003441040c601c012500c8416216a10400007060f1401036880401800d4214401113551604960010440c01c000c0b00b01e14119040200b1141d07904c801901c500b4090800e014010464078000c6030540303103015840d800e00b031000c03005c29040450b5000365078104082d1440c00e00300d0200844410401180401c40c10000170501089100c0800207001e01c1c0d807180541c90340f9120380c900b80340c0c1d000b11440c82c1c02607880081d898a2000c09803601d02804900c0b0003080b004083c0c10302c1c00c1c06022140b04000c5124540b0001c40381d03c07000201944801c0390018001070f241d075101224480049811000100f1000140340c1d20010142c02000100544054021440130300304000302d40000c0b110123a030802e038541c0c411400541c1000040d0081084440e180c94900e0500c7c1e462340e120b5103160400c4441221043d000320741070084901a1140da850740c00201c0d10403642c1e042182010301d0114400110700c4041d1400000981c802d1590540d4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 132387850 1250 132386600 132386603
    0x30106050409060204060806060a0203040302010f050c01090506011502030403020109030206091216080105130308041104020c0d08150103020a09060806030316050a0b06030c0307061206120c060801063603 89
    0x42c0310164080c60007000950141c0900c9020a803c0e5022400d1801c10304181c07001c8003199002145000d007182c0054070750706403090100c02000000c10812072215820f0040309605031242c00200495414004281010070103c03201c0307000c543c010310040000d82e038032002c12012640c0546042d1303640c1a858001c0341d0808400c00c0000706034410a803800c005034445175440822206000000c00103526404681c540003265618041d00040c03a8001040125482da10341840410009100600d8100c0004903942060005405180881d0f208800c1005940c95000b41440c820001d280840c40c001140d030021704244264003e80041068800000391551820000c44481400320324500d60100650f16041c0d540e051003040440701c5c10704a0300070460314200004e81000c80d44004000d840301c0e905240d8100c3c0d1440d01d07940050243c46d181c0e4000100e98282440320900305000c9e4400301901401c0c031a01800001c01070740700d2030421191003080c00c9030320307002c9451201c003205504d4401c4110312488400000003119420 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 132389100 1250 132387850 132387859
    0x1020408030a0c03030614060307030209030a0b01090c090504020c1e121611040c020d110106050d05070e0c03010e04030e0105070b18070e0c0318071e18020a020a06020903010605 78
    0x4400b400741e5042040c1c030015a201e40e13410300900703848109014480483c00300e0f030780c2c001c9414408210000d000c0d8014003a0040040d048031a8101ea544513078148000c00e07400b03004d90742c0d52154443c500c190300c03416a00140c041a54154642000f41c007416541d55400720580c1c100752081601c124a0000078001d921803100c42c10b540980318044030442c01c080c0a07601c0003c8544160300280d500540c1800d000f0b0069850f003070380240010910140b000d5480901074050149255641d900214055650070041805a4000c8009100d00b41c1809898401000040c1003070b01540428001086044100e125081e84035504d1b10300380d00c0400620f401a02ea0340a00200102900140d00400203100000090214070305e0404044850703641d920300d2000070300103013036840140110741000000c0e0080d485001034040206041c040300d1340340351340d004400b03218070740070a8101800c205550100320900303807100321021000750000118074206e0801d90180d5070305040d40c0700074a20364001c246c40c03000b0360f42940a0801040083c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 132390350 1250 132389100 132389107
    0x1d0607021504180209010806010315140105130308030618040b01050f0d0b0a050603120a050d021b0d11010f050c07030f0210090609120903020d080310180b04060527090102040803 78
    0x44020b00070750000c046860001f10403200150b11980302e4000c0e940300700300001c01c0d001007038208140340000c0301d0100440c905000741000103080c00c3c40b420098000450141c0b401d9a100c0c1425402c00200d00c0b080c03c160200080d0703507014080810340d0034100d941100c0701228803000002048010030907000c940300010b000c902080040000302c40b102e81260344101c1c3d045060b940708508040781240c80d40030300e100190004000340545030b0300840b650b00900070034101400042080a090900500d40b4520030704040014925039030b203408504c024003658400c0d41040d82e00b4089444c08004054180c018100080c0410510000c6040c0041c02484540c4d01c20507010700030301501016060500241c40c00320411520601e10a909000e128441c03400c14044d45c0d4020103101c20080d00c0c0e11240041d81000e04002c2c84a9259100003c05465000c0c0007914407046d6500800c0000881042108071080da510440c0182e029182070305141c0d01da200314690b40e0034010b40c800f10301d40311461007500a0286400c002d04510000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 132391600 1250 132390350 132390389
    0x11122d1207200d020c0321070809220e010513020d03090e010f060815010f140f030103032705060a1d13020c1e0a0609020f041b1d0607021504 62
    0x400c0400d01183c2540032600c031007950109040d901e1102c2c0100c000c1c400e84016103492404074403402484041e0190381418200301440340051006840d803001040a0354800c8a20000300300f03d4043c03401803a00b200020480c1e4540011450414083c40000a110760f039015210002c260190340c9102c060f01d84981c4414480da152043c0e400309400901810010502d003000043d04104014950281650180d4840203a0030401e0003e480c40c2e51a03900a0220314400c0c040160041c4e01280039500070360295a07440d66030560144401c640030140024040540304009052081da140c00041740d20000c15803400c48850f803180310758059109648000305a0000050006100203482d42d00544110700f0b1210680e01541c903000c031502c4469003c0701e0a01e0300f80e00078440b945d010803020751000c141180064079401118001c0310015007103030101031507558501900c00d03005402070f40c4101d002000d14403036901450320003140c40c006125400b5804009100309004001390401400d880d0548006040009440c031401205 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 132392850 1250 132391600 132391603
    0x40c0c0b0903030106020f0604120f02030705030c07030210031a06030901060f151107030b0402150c030a09030506070203070b04060903020f0a03080a1a06031611122d120720 76
    0x2c0c13041d03c0051184c1d1021032226100440c2300c90281d81c2c0700d10000c85c019406030b000d940d00001c2e8941a41980010300c240c10102e82c050004059076890070003d8030f401421441081000d51401e030700d401c2098900164021158100d66084920342c070b045072410740366a9107003601030141c0115001081c04400b07800000a040001d180d00d90000c151940f070340440100711b10799085d81d44150b07200240400010202050142c140102e103040e2041000443e00c1ca0114400b40b05403450340000054800298400020010300805100c0d0380e41210651003e189803139080d44440c498020b024001900341c6540b0b148980815000700041006040b214040d90043c3ca01801c02a10302070013201e18208080c1000b8813a2000c4540c20002d21031100c0c01040c00341561920b0346a40f8011400ea100901405080b83c0110100d42d000c04c099161040c405800da07a54000a100c0c3d2082d10780c1003120044030080d402401c550303400491054904542c030004c90350400d580c0c1c6140c01c03500c04c83c40302c038140d802c80541124030070314080 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 132394100 1250 132392850 132392857
    0x30709060801140f0f040308042f1f0e0f03031306170f070f0806030a0c09060f0e040215070804050a0e070314060609010f1806020d0207080c0f040c0c0b0903 69
    0x703020b451000f0a9841040d0550880411600021070f844160300083c0068020700d81903400c0790040440031150300024101c0094040414481c0d11744040c50750081c0000e1904990038020000e070303065444070b21409044080c29440ea0007001b81e05c28949110b05007002d0310100103070707625000481e0540e521540d03507a1020f1710041c80f07010840350000d403840015054800c90f01d8940c3c0110210741e5400b00002c3c000008560700c410141000e5494000c401c20700010503007104240010b804002c400107021480c1c490440780d031840581c403260307c0318442c40400000d40d440581500e685215a0340e5079a83d8940b601e00358603184a00d0300110b92081c8100f130301003651042400392510400144c4c4040102c41010480c100007001c1c22a40590b1246081018000c1e031352080b403500c0005001405c201d20151161820910105060341085c0e00507400180300f03101d040c1d07041000074010840c0c0b40141c168030110310045506054490388480c0103c2c2c441c541e154456115200e2001c4954000502503041c0c01d000320801d860381c0c0f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 132395350 1250 132394100 132394121
    0x7020111030a0918060513111303030305070e04050907290706090b010819060b040b03030c010506180403021b01050f0c0c04060f0b040306050405010b060d0615090b030f06030709060801 81
    0x19030f41c44e02822510316200700c00036070710024417112142454511b00c10141c4020500310308240300130312490440710400013000000e0362080d1400700300e0b0700c0c00401c0102880070342203117140f1403030078841406100d000114056060340c440e0a003d00d600d401e41710003c3e05004c96410a5200a40700203a400309124480d409050b2251092403416179a0b680c840025981d150080781c403d0014a4800c940c5000814561224545000160011506640a1000078259000305408800c140d4403401004503500d420000d50110303020000803035540d4100798900950b42d14105e01d410480103182242240140c0c09001a5803400002100413903990014040e49a141c0103009540c50040d8100440455803410001c03c0388260744a9034440d5080515503244c030805030001810036207541d56035844e09207aa0700d0f1240100381c0d13400301e6403010480c146016a61980440007585000811404000900c84115110100c035004100580c06003c289c80303640003c1d0800d0b0f0340c0c0c1c2c0510901c27441c01000240c9401c040d0000d40310031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 132396600 1250 132395350 132395369
    0x2012003030f0a020408030d1509020a0e0f090f0f090c060708070302010c050f070224070503370f12050a0e010f0b01021510090504030903050c121207020111030a09 72
    0xb0780720a0f02071020780c007540c0101c0d003180d0818008220002916880b800440d0b402125000e0002d680c1d070608412a071142c840310000489450300c416541c14111103180d0000801e0740e07070700007615041d00c08000e0400c010308034030f40c801d02c3c0402262504030200901403030240001d007100c0c1d48480e580ba011a4542c8541c1c030172000755003001c0316952900d010b4000e0700c50344080b1001091518450f40e003003151044010404000034900c1c00101800566240c02415205d071041004542d01e029422b0710030060420010461490598661100c0c5189190b141c024608561401c00c0c00c110300340000c00b070310013001290410300c5032441c20b400c0007a003010035000341d0009280a0000c00248149940110649080140d02c6000d03134040c0318406105082110003d603c1310160448480445d25454075409841d4280c03425000181c045c8400d0cc1800028000060f0001d0101c40d40b0300844003035100140c6462103500100703d81480880c0840035139001d040c15481c21658071007600e540d007804c4800078282c40c100b070140e224003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 132397850 1250 132396600 132396631
    0x14190c0203300c0f0109030e0102100c231b0102030601030b0303040305060f10030f05070608060111120f0f030a06140111100507051603090501390201200303 69
    0x252481d820200b16411403002c525100c540d980725401d0180d0301ca0440303c601c51003550020040c00c0303c00e10811400714441e40d5998a8800200b000a18107403100c060044e48a180058401138190003044400390701c1c1716194030852040350030340301c240b8074042c020600112a203078000da000c16940c19070085102d440300b42c03000c0104500d80b03c00d141d502d0195000c000d000b540081c0100d44180003281d841e6611100000b02c80202546030780e140900c4a10b00d5200b11596801594180318060704070004940c03140081c0b90841071065a440c003190344040907126005c01910008980f60103210032002c4a421f41c07aa0070003940d50741041c07150100142854480c4110031221480c1e03d01096109881144501c00003100030301c640d141203600b40c0300070b040152031503003400346c100182210800740d6441258481d029440c0c0050702850f080000d40b403404003552094052007071410020151600802d4000c2d191088080198800308c0ca02c01a108161094030181c02400381d44580c00103540e0020086120b02a440d030000c51 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 132399100 1250 132397850 132397873
    0xf060906050117031b070503030a03090309170d0e0103021b0c04050105030a03020706031107060f020901020d11070b0304080d02040b0d0e070501080609070c0b13170301050603010614190c0203 84
    0x1ca804148443c4041d0010480c1c421880c10101504828420440030345200503602c00c002880d42c0d004445405c0405c1d05d42d8202404d0680201500000300318401d0010801e03510002c81d1602c03614050450b4060156003580d061059101390b0540e8480f60400c0311a101c075540780340c0020358801c5e40140d124480d034200000440d00c3d00300032a03542e603055890740040100d036081035000e502400c0b208203d0303020f054040c8480f40202d6114020072103002215a8016600c070f46400009080c00320314000e440a000210700c5100a14400041003402c03178003014201501d0781c4031441c00c5001031040099201d480b50011401003560b1804600a29040306202d00402c014007140c1c04c12501c03660b161141e1408605618001440d5050094245030b000301e00e49854015450656070707003c05070905541e180410b5042c545c0310340402c0201040d046089800250580c29581b50100249aa00c81409a0303401c0100142c815480e48a0034030030744a40745107000c0e414460b0042c0b10801000d80e9640030307080c0c0c400c1c03140601629 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 132400350 1250 132399100 132399119
    0x30518040c2109030509090a110d0f0b010f050d0b0409050a03180905010b041809050604110a0905010b090f150f0a03060e10050f0310060e07020607090f03021005070f0609060501 78
    0x410135419143c590034104000108401d0040c0204041650764450710071214a11100e4006e01035804064000101c030304038503074044100c91480d00c595040c030a1b06106540103e801005440d0407070000c1401007a50100140803c000d03000c00c4074010314034464961503404240c1c001c0e030229085200e00b501d240032660b59489450542e1230030320031845d000340100400e002c101042200c44000421068010030003241c1d542e0390b545012001c58054941403001501e0340824501a441c0d6001005d40d194140104d50400103184942d124455840f44600c4010503030f40e86985500c2da007003011003968644030340c031000c0e03011402845a10407420301d80000e18155001c114411400c408074007400d40041601c000d41d04100234400c80c0811807041c554103225024805a50744c20381c3c01040050012525001c03542e0405101c01392030300c0c4000e010002030100743c0300180a00300c0ba2002000440e07404a58604484690007410386003881030000203040003014036007a0040c0b203030300c0c0c028130800d40c440c14081102d6079840c1d0062 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 132401600 1250 132400350 132400361
    0xc0c0606030d0c060b0f06180906060a020c0d2f090c190309110a08070302130e0d26010603050402030c04051605070203070b0309060f060a0f03030518040c21 69
    0x40002c03851150003c40407400a51049009a101800034017924107020700103481c40c2c00c8448041c95500d1100200d41240c02c06900b01c540154081d82c84074282040d840c000380d21940c21021090240211000f03510910281022841d03040c062411400c141c2d444d0841c4c01a0142c107801003640c06414008041200040203804696507510742d00310b221940c0c860000c0c00c030064803119005030b6525001940043c4155128088000101500e0b40127124203403842c414001c0548410752011081854903144034a9520007190031000160145800c8041c00301c00148058030803072105d108074404d1801c1d000428429056445103008500841c100c54110144404000969004503031950b0000c55500c01c1082ca0340c0550050320103544004c0555607a640c903a5060a0303943c2040f9018a403580c0020f0502c6940c04020800b150040c6090f181c503032b01d46040c41d48150a6440601c17004081150000c0c00003509172541030341c1d6151800091090101c08a0800010003502001c24100200784511100b18944011442131 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 132402850 1250 132401600 132401623
    0x31e0301031e0b04030f02071502011e0b0604030b04030c050d03140906070912020102031c0504140a031e1101060303050309100204050a09020705070801060914060928140c0c060603 79
    0x3041ca0f44d40c49990456454540d090042d0641c0b141c0803010481000e04074600c1100d025580c00081e070308410420402504d901c2d11a03858a41d441c1501d441c100341c490404403020303a50400c82d8081075480e20f180031a40a0240b100107890b40c0504001c0c5000198187c0184141921a107411030781502c401c14003030303120a000d444503030100301004010050b03c080c00c0c8000075540c0c01401036070704100591080c058441d2401c104c841e1056602c900300410000010a1401c000d41a80020041c0b503409580142464604146210704489000c1968180078821000c404110012000030f00c0010b40c0d07807402070004d810564610303107a805240f8040141d5411413081c1e0b4201d0f00002c000e600c000345402e2a10780290f00c800400d6680c0c2c001c41c8408503001901f401140c0090100a40016060340d140c091000640c5002c0d01e080e11400b030410a100d86902a50010901c81c04000a901c0c1c505940c0400a0010300b481003c401400c1c80c41c0003003280c010010805440424a00020b42e0350b160303151801c050322001445039 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 132404100 1250 132402850 132402863
    0x605010e090a0b01110a0602030108071706010608150409050105070807031404080306120d05090a061706040510050a080f010e0f0d1103120a020a030b0a1206020705031e0301031e 78
    0x110350700710700e40080380e1419041c14144400317032104526504148503d081900c3d002c1d000801041022401c204c0c00c0002c000520006500c00b00d02000e146c2c0300e030011702c03a4900f0010014003045003018400340809042c40028030410821000d480c19502074501200c3c100b001c590b2600010381d0070740c06405506644000b8603003065403075031156a9841e084c1c0014240907082841c13068000d9a40c10108110400c02e0840d807545074440039028200310703112025400000420042103000c1c0002c240c407c20107904030208660105031543e4042c00a0382c0100150b0050340d00c0843c000d00010703c66008601c0205e00c1381c0c450028040d0600c509510740d9200040d40309002554071101403072a4240c4900a003a641180e2030302940c0c44c006980b600c01c5000c1d00141c5030404883d0f03001800020094040c821410404c20540d40544500d181c4100540848110080580307280e0f000241c080030030806004881c240d0145e4508074080000c210303207081481d002408100c51a4159201c2148501c401100c907a8040307500c5413 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 132405350 1250 132404100 132404119
    0x8010509060d020d0503070c3c0e0a0906020f0702010305160c0b07021015150206070206010605071a0c070b010902040b070206090103090c03030f021005061503061c080d0605010e 78
    0x50a2107610313020b000c1d080d42da40c0014000c010009a0405182d0009d00e03403086540c2074260b49140103046d02100c0c14800740c43d22381251403003010987c44054a011500b00540302090703580c030700b050000038088003000180a1840041c410301c2c0c0710b08d88030140007214000c0c3d07002c01c096036070640b086071903005159160001c170700c5a01c80310300010005074005038420003a05c142c070b10000c4440350741c00948150300c404000880030181c0500990340031724440840c0c0d80d443e10080c08541459600030352642010b010349810000001910000e0011101ca8a4100c0c01082107040303a525007004224000c3c2c0000c00203c4814880c14000148200b02c3e001750740c01d8480303141c6002d14040d669802c00403140d1208600e28181620340c504200440c07201c0f010040210701a845501da00120400c000341003901c000c0407018901d24050911490361205a0303134812031050604040c0d581e44804000413074002043c00c0da00440e140006070a02002010006400300d01481c282c1030003400e449500549500740700d1001580c2015051 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 132406600 1250 132405350 132405353
    0xb0d0b0103060902010c0804080105010e0c07020d1115030c130609030515040606050904051006050312040e0403030209060a020c01090608060105120c0c0a1a10080318040f020c0a0308010509060d 85
    0x3d500002019205041ca005d011085545000b080d42080d031004000d42d5449004120000c0a0312070076500540d01606103280403400d40c0041e60070a11028040c001c041d00d1a1010216181e00e608561018010b18420340c5a140034145e2381003650103004c0c0a83e0307140040900082c22409042c0100907039a11001804545101d07442c02c07200c0080090003940c04684544c400603841d03c1c2d0004440c0101d01850103440e00382071049030a408c2e5241603212500a50241d11070881c000640d200f92303015100b0110380034044d5203035814210043c0c040c50600b6540500002510080c2c0c0c0d80004641c08890000e03240c00740010343ea1700d03098501141c00c944d03443c08540c00304171071404e0040200a095200144103030703007410019560a014a8034200880c00c40b8503500b5200d0719440c00203040041e96002c0c583d401841303200b40c01c2821883d140e00940d5080c1c02c81c02e2140320300b0748407179030b4070340003c100c8400d5140115102c80c2c0c41c030310301039542c0e803440002c0e400f06119400120ba0360520b60207840c414140504010f20900e0f06 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 132407850 1250 132406600 132406613
    0xc03050c03010608030d1a0907020a020a0e01050a0303030b060c0d020607180b0f13081b0301050c0304031b030e03100204060e0f060f07030c020a1d0901180303091104050f07030b0d0b0103 82
    0x848252500e01010203030000c4050348d95158190182c0c503d903005000b4000c00c0c0c414024824a1500500070600c0807800400c4565910700d440829a5410b16010804c0b847d1803010903200c1c0954070394000640105001d0000003a80040c2c0140700d400103540d4900150000c11405020300d61600074030a0303451080100b058040c038564001c0c40c00048103c0c2e4800903c0d6124500360401200141950402d801d041c070740e003214034090060a401140c50303800c091540c1441d50300580f054030b40380c18201c3c018a0302e100702e10515026400460344e101c0041c00361907164104407584030080d8020f0145e5004207903415605042814074503d8403c210b5400b810032840c0c030000400403105a00700d024124104000410204010b0301c0d0602804000c000490703500ea84000e4991111021040003852414541e140012802d440c5039503850720089243c05080000d080700380b40c240602d41541844c0340541141c2000d09100d04030b400c802c42c9611401c81668104420020301c800c120b9038900808010301070111040051012031507 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 132409100 1250 132407850 132407861
    0xc030b0702031b0303100e010e06090606070606060f110109030f080a020f0706060e01080d09150c0f0b01080105100501020303041b18151d040b061306030c03050c03010608030d 77
    0x216401224205401c0c042103845203c50080301c846150004814001d040d030003088401c001d020806040503256061000c003010030040102214030071003556000c5102515103008035540e5a4002c0360510043c0d4860f070000e0140040c00b4001c1c2d00046821140ca400c0120610482c1441c50f0b050707440104807045110300700c1c0c503060090b0034002203a50030051a1008042c0800408400784241d2020592034178101400c4005070301688401c0058001c8502101007541c406001c2058442c1075101e59080070070b05d103048804041c0b0a400501540c0d40001400034000782c1c0e0003481c1292640e0009100c40d0b0344480e03500705041040c2c828180507070700500101d000079550111900840450014a001b100c1d074500c0f45048050f54204030540095880d03061f0760040c09c850321f46c2d4014144001031341d6640490050b4200d92400001c00c0a0001c4440d000030964035562203245c118500c0d11007000740401509c1341003101c2d40751410300c0226814880c03442c1d00a620705040c002c484c01c0b40c1a52000d142041d10101448001d0700 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 132410350 1250 132409100 132409111
    0x3030307030b0103023a021c02071113052a0a030f14100f0905060609041a1e010314060117130c1d060d0209130309050901030b160302070c030b 63
    0x5400b813141007a900303145003602031240403035030b1b042d000c018503a100860007060b400300c4c0b4800c541c010425a00e9100c0845861a0541060500107035035108600b4854403a002c031207020350703000d900180c100c940c04449400040c060700d503904281002e032116115070381e03004140f00d0105258038014003402103c06e0003507018280fa4800c601c00480c84c00c103100411811241c00301c840e2400c03182500c0c800d0240700c0c4c00c0040e030f03c054110355600300098100040058113600031030034044e100e562140c0c03e00c282c411802e054845d01400c043d00306640f542d007126407140040325078000349000a2030100c2d8032200800300c1c9801402404103840c0da0100e14010f42000b40f00003c01002c502103660500a280c0006400c0d146680040c4071900845207511112540340c210201c025040307911420b5148108809640d81020141e000030103001c50500e40e56444c5400c0c1c40007105980b06541c464450800013060141c4545598410348840582c292071441c0c40c80160200c3c0295180544011070201c428000107158035010354128 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 132411600 1250 132410350 132410357
    0x20a17030415020d0215040203070302040f180c080c0105130905100b12070f02030c0715090302060409150506040e1512030d0e0c040c0203030a0f0e06010b09180603030307030b01 78
    0x546940948180b02c01d107100342c2e0016440000498061a814014a16003240c4008030325001e0034140c000a6403008180006889503513200e200011040e880d030f00c50640e0040003040c25080c1091824850a00c402c14440d50790940102840d02c403066205404582c942101c00305c1d007405440c00d20035100001e03d002801a40b10ba00403407001b10702020400090405a10821803140c4c03203290220004080722990900c170401e5610521000801c604007181c480d0a5401c441d518103105c4120607400c079140b404651000e904403000003400708010f4125085075040040d01c00012407240d5444045c0324280c483c500c00d44591055444c04a004842c011440d9002010014141004036151b403036020709541c06150100c40981e61107040c0401d804040c0302060141034101c604101c42c00c2070300c0c006516440020104224070b80d8030080c0a01d00c0310306611150801c010f06007140d99540c0c41c0c10315201d15500c491066440f44071580d9084603d080c0b0191050711806001e00070b981152640f000c02c0c1c0290041c03c00e4141030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 132412850 1250 132411600 132411607
    0x2030106080d141809040f0218040302150703060b040b04090b0102031908070e040614030f031602090c04080703030203130f03110f010e0306090109140105060f01051c052e03020a1703 80
    0x45e039284d00c0d040d400317580108a0030101c0601841040302c588065150016164084402c21000c81d4004c07803a6511230489d05441c0d5034507580e50008034010f1440350004809c09034045004606640320328003030300c00d96005240402504807503200590340d07801000300302d4800c085450315103082c891244800c0c542040c00c40c1800000010418001010780e0150b8100d602010030a02010b0110b16081002540c00303681c000c043d51410002521615201c0c6910f400640242149000709105507100b4046030001c28000064a401a0700c0e490020b440b64040c1c9402080341303003421008540d074160828440c003169401049012015104400c0c40305110120400905200201109011a490a104c0f10b4030400700e401c0005a503424a291100c0c03d2503408009d002c1300ea03d89402c01003203440c0c0f501701c1d89000b0402d00f010394840743c0040c4068502c0d18404119a44a030070281800208104041c000c010700d40c400050340c05c0c802c401000703c04003103030728800a03601c88005401080b1120000d006010140760560030b4919 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 132414100 1250 132412850 132412897
    0x5010c0c09050114090a05070509120316080301030b070801050102061b13082802090406051305030a021b010c12030f06030813050a0e160509010306030b0f0402030106080d14 76
    0x11640240d019244224812120004e03500d0051011944603d130600d04200c10b041020004069000700146c16010305500710038255425001c02c01d884640c81440704132111380440d460140e85641007072100300e984255250115540c28050b11a4a041c0c0e1030681c01084103a071001c01c042e4100410203a0b2100c150410010440040c64a145c25000350050500038180008261010880b5000080100c107004ca00141c40800603961030321a80e40040c0c0080b00402e994661000c0005180f80e48200101203100c0040c1c0341e0049500400c6946414140e003c440211091510042d100d0008102c0001d000d2045594114100c902a030320103c00c5501500b400030300f00d9280d0340d491426034007100840d07111102da0113007089035103886042d01d0081c05031055400c0b00350420342421014031951050342002e100003c140040d0b940d106e07a0040c1c0045420042250403420102c1062000d94026075040c4c0c029402e110001c11a03002c00141b074140440c066039040d5090707140c10603400d030790b8105842d100c0003005c00220321b08 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 132415350 1250 132414100 132414119
    0x3210b1002010606020705030f0c1002190c0501020606040e2d0d03020c0c0d03050403120e1e010f1b020d0212010606051306080c04031e050303090313050a0b0405010c0c 74
    0x3080602900001461424041d0280c0ba00c80c9560010f80320368401600550ba051010492021109041c0d6504000806e480000d9003489084210303104081421001c00060041c17104054080700c5007a025a5090388500003480151400b1008a05e9198802c2448041502c1c02920300c0b240b00310329800080c508921030041504001b0700440400000e034010401d50b440c190305200c60550005c044400001c1803e071982d0182c004d0007244409801c0e10088507604000364010590440c0d01c100003040404011514540c0003507000603251510f00040a54007c030002034082d00c103003219000c07400950060010568204450144816800c980000c1c40c1010007034118003d0240d680604400c0c0c80701a2151514514480440d1141e400701e420000c5400500000003640340484040c0d0b41c01008000e40700000c0066051603240c0280001c020340700001c20000e003d4404400342695218202a00221540c0ca4040001006c0240518400303082c0030041000650300403802c50507014403901800260554407802ca0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 132416600 1250 132415350 132415369
    0x411030c060a0c0506060904020a06121b0804030e120309040906021201080a140304031a040602210613020910050306031e0d1403131205070c030f0506090a03210b 71
    0x40126003c000701c2c408008091152030340c821003ea41d09441c503e480d400003072040c00c0354031881c020b110307060f04030103d8000d141e0050f030010810352425104984600b2401001708008440590002e4050340b1035107254503000e0a94078009090900560902c3c1c0d403581040000c00ba030ba502202d0199007004410340e0304002d41d001c18004e00c00400030b000f10203190700f065041c1c1004031114424580080100b8000100c08002400840ca0103c1c60030305581d4031031510308002d00ca01d24904d840104150354008145505021807840707500140c491401e0310144103103440c140e0080303101a130350001442031007010103032041c4055988044000c08540407040b580341003410500c0c8981c0c0508803600b204d50608010b40e04419404c1101d491102c1031440d501c4c220146001d00f80c41d0a074000d03c1804910a9130034400d200d18182ca42040e000407441020780c0d13580c940300d0840500c40744115583d0107010b0010701c0b661004100c0592464054440015081700700b5010039200c09044001c9103220b0b03403552045120789039407000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 132417850 1250 132416600 132416617
    0x604030b040506100b0f03011a0405120f0c0f1f18030b0f06100c2a0602030304110604030c1202060d18050f0105161107091b030f140411030c06 63
    0x54103d074100b18800000d91615a0032010440908000141c1c201c00c051040740e04484601080b03003040f104103480c1842910896000c26070003031a0b68604403008102003469020f06c2180b1085916003d1003d00780b1069118501c3d2081d80070f8078519040d2904810446044100f02852911a28034003644d400c01b025400b0030340046d9543c0d40140100062181d00040342600701c0300c12203c0117040e04000e00700070301d20005141c0091801d134411312900c0e8100070300c0c0301c4100180e441d0650300659a488150080d525041158160f070140d003446403442c0942441400c41d02500c0c3c10040d05440b15050000e0701c41d00c51390307103441242c1088040181a543c030229102d58021281d240c5040580c252a03070512a00e03084d00820a014564035040611a007402e210050f201c2e14406130801c0744a04120110043c2050481c9d4056034440d420008030600f101005805903801d24840d03142041074840e012480003c54040d0304075640c45500c5600420041010380380000420f42004040b02c40d0340d00c160000c2201504079549 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 132419100 1250 132417850 132417853
    0x6060908100603020d0602090d080301060c02010207050a030c05120f0a0303020304140f0705041113030803010e07090b090d141510060507080a110712080325090b090604030b0405 78
    0xc0c01000418040a140d44520360024070a00d411500042d880b01c080120041c1b4940d40010820215103030302800859460b0001b440a07103035070351b0712409043c1820750788040f130040c028004045040e10300300510310262500405820000c905000600100c4544211211241c4c80b07482804a0082400c0110109030740c413982d40542c40e814107241116906ca1144100503181d00404d80c0c40c1c111940018101c0c0131290700702e41c086500341002c00f0030030070b6100e904110321030301385000c0021090040800003503040302c140040800c540d81e1390382ca08132481400c0b4019002300300d1003002906c90624145ca85008058041d104030243c07200c0c1e6103d854902054842c0c1c3d00c04008081c41045810311260710b2100c010002401d000d46070511640d035000c1d2601c10100f2102c14000d0300c84125194600030000c4101805680c84254104a404d0070013480540007100c945c3c03c000308100518144509140280078030100c15140d20120700e0401c1d40f2107000707402c1030300a41e41040b000c3c0000404145441c0303180c2e005500650 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 132420350 1250 132419100 132419117
    0x5010504030f0f050901170a1103100608071d010e010302040803190f031107080705070509090109020a06111915020f0409050c0306010503130c0b07120201240303030b030309040606 79
    0x1000d041d44440001c2e43c018071009001084c0c850342c01a4120707070304000032054014180c0d5642030840081103000303440009940b020040000c1460300d90b1340e80341640c07840e498900c5c081c1d640030f10880307002015190800b0020552040f07498694003500c0c001e04c5051050501500f400e0f00c400c00c00f40741da00104440501e10400c0700040010300d800c0410784040c00e0051a040c030100000c0840791140740704066000344420000100c50007800750034803144016003001008030045003072500c1e0050207029010b000342d200c1c0d0300342c44000503c1030080c1e0406008410020240c0003070030061303604800002560106842ca60501010002080b0251000b071503491140301c241510f0702e0522440c3d078203c0780014051800400100300340712040e0b030860b040c2ca030302001515020842c1d403c18602499401240d0384426800980030829508010080b480002903800da64000c00c814011341caa0030f111140c3c504501c40c000c800e001814000700c2d2003508516038030200075003100e20300010407005c503003190740a611201c001013815 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 132421600 1250 132420350 132420377
    0xc120c12010203010803120c0f040303050307030b060915070c1a120901051b0a030e070b07020909010606080601030f1d03030709060201060609050907020c0d0803060a0605270d0501050403 82
    0x140403541600c0d003500214255030403c09501c0e40e80c445d480c00c04e009651480d00040c0c0b0100048120390458100f8140b060722580c0d00d1074041d0413a0015100ca20210f800d0a80b01540b505014013551012a0001d180350a41107504980781075940c0012419603c40d5100c45000c0340d101d00414404814109074402a07a40b010b4040c089540302c4009000c1c0020780c0d04240500c4007424440c100e610150030082e14503665401c0084054004020800f5414038600403040e0014030f020f4200080c0040500a407810185d65803044180c5089070340c91b00441000c54801004035081d544641d01001924402c008002100c044061682d8540703250041d01c070101c2c0d07000204010120340c0c02144480182002c2c0003c0c4052400c1000281c055a024080d0b40e0284102c2400a41840d200b0407561103118009040c0351805201c904040406130f100b180e0766405401000750025800348034101721039001100a1501e1a03d0140005600d40300110124135a03005a413200074401041003032107590300840c4251510740040018 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 132422850 1250 132421600 132421609
    0x1306080f011401030c1a0c19060e19060506040209040608030c0106060c0503040612110c0109050f0c0a090b03152e05060a0e031e0303061507080a050702030c120c 71
    0x1c2e1815059802d46100420000d07010f00420400e68031494011040403c0c00200c00c0b10038061a01140401c3c03040005c807203410010348a002d004240181004d000b07103400303c1c21082e0386000380450306203203600200f10030001c00c441d07500060700100010310161034a0440c60004060f50801c0c2c2120f4001c0d000081c026600030001d206079030040c4010f0804922040e0103407902602e9006d148245005e2024590202c180300106620410b141d403031030040d0740e0301c0703d9038500712034002c2038102e42c1191244604940036a0046c80059440c4091a00400701e00d4004e0402c110341028004102a00d601441402c0a50704090311820800d88624244100c2070003000444041e003140c00102c0c0c0f84458070646084080c40951a8082140d46001e10780c00c081003100914808a8a4209101d03081d50b5100c9818102c0714074404044000c42c000d501c1164520b00f40b00d030040c0410b035030380300e0000700404601080112080d4a8003c201601d2068001400e40350300040e90004141107200a80302d0f2032070b68208028150300e5180 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 132424100 1250 132422850 132422861
    0x50301020d051e06150703090512030a18182304210c0201050d020a02160b07060e0c010509130b0a03060c0f11060112050f030703090e011a040b03061306080f01 70
    0x4a03012103140604094000c6545c2c0425121751680714035001980109050103044020300510015144601182c8020119130b126040381c5a0b10300080d105100d4805426031802ca03840c1501c0c0e900e840c607180700f41c1c8846400002d107039440748140d144122404c0401042c0500888510980c09001500412504050204c030344125448449043c44140000100035036407000c01d840e070b880c85451005a4640d14003c041e0725180c640220310aa4490302c00700480e002d800400030340a603522510003803105042d0b0034010b680b0f840809580a00069080c0415062440c029181148901e203180d80001ca2a21503c082034a01c8180d400a650f00c1d034441c00b1024000d5480f0b1a480c600c1c800501d8a071220342520104203840362410700c100d400201c0000303042e0041c4941408460355070b080f04011617690310b0207858090440760380b17481041264500c00e0000182910010310400d1031400d06040d40e4600b41c1003001641304c41d0006000c042d00403142c2c0000315124050303803181e440600741d000f00500385c041590f8042c40c2540c4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 132425350 1250 132424100 132424141
    0x712051c0207060f020a0c03031d090109020a03140f1303110102270d0b0c0c07090510090506030a030c03050a050c03071104110403050a0809063013030e010309050304050301020d05 79
    0x6001d1a208008564494126012340340d061401c0c1c0420741c400480c02080c0c3c610041841d85c400c15080000035008215801040601a1500c0c20312105a40368800b01c1000d100301e4040100ba03880e5000908040491061094094032909201c03c4140e0b010005a00720781100e032100844030360415800310b5088003011540c00740303002154511030015031565005c0b20610040c0c00d44400843c04516510b82c0841400600302512030314030101314925201036074511450152041c40481860800403a20905002c1140c1140c2ca426803901c051705ea451303560481c1c040d0300100d4a401040b1060221403002c0405000606c2c01900983c0f000441084140c1003100f200d203c4801c0c282c00740c1003080300700000798000c031707c40c203400da04040119140e00300035000c41d2803481800c03502c001d540c00600550444200f0500d01c4603d442000c010501656611a03184007081000345010b004241202444907480d0b100b504007001041c458001d5030305195403a40400e0998001468090f4040d40310341c100a80300b0252225002c01745c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 132426600 1250 132425350 132425353
    0x11a1e0c070e070e0d1e0305070b0108030316050705070e0408030405100c1202090414041406070c0818010903080309030405011101110306190503100e01051003050712051c0207060f02 80
    0x2410003c002900f050825480c06008807882c219a4080c0300c01100803003079510340110148601c0c000c91400070621f610035101122254640d0001040e05600001640d20480486e92402842c0038400010f0b6050303040600d080310745108081d0041090380c10100b80c03a010b035100c0c40800f6240d00305031901c542400100310003c0d14031841c280000800c1688504800c65010b4001700040c0d803140024041405420055014803160882c0000c1c0420002d0312040d01c840c00d4403000980d0503903151018200e500d0303410403901070310100d01800000740b102c0503000380c05d9034030f80141070142806a9964403602e00703800840e680c40304d1307800100b41040156000041203154120210003004020a44492120a8000500124003401d00086c060281c800202030000c040d0100500320340e0303c509100b00c1e01d03020301031160101c0c4a5500340b0f00800c050309007110780c65090300da010b4003418400341130007040310401c40041c10a544900c80c00103c0390b0280200a0303210064011580070380b5416080c074030003034202010300603541d046 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 132427850 1250 132426600 132426629
    0xf4401021902010b09060f0d05011404031701060305010b07150f050702100606080613020c0f1005070e0402182202030114030712120507021305070c06051e011a1e0c07 73
    0x2d0313039103615001b1400c59040710201c0b11801d08c1d0800ba070040100d400c041149c480d0f0b5400340000e05811202290405699420760012682c030341a045055603402c1c4501030320a2003d200c1d82000480041509c0b000140d6583c002468400a00b003035020b0301d9017504d410000d0f8201d10f03440e0821084900607480504180d00f0300030317240c0c203017603020902d10180805e907440350b10740c00302e03150105000a010480605014000710341c0705019440801005010540301c45c0003140840e900304007142407034002d0300d1a4817203902521141c3c1440d0414030070109a201909102640d03242d0300c00c190400c49201842c060418540b9080e2910301074014985020f00d550890514901800d01d22400104605903003020503060746441d5449007082e101156180640340f1223860300038144010040300d81c2e44141456074481c007808080c40310f03071501c2034580d062484002c0c649000d485000010b005040c0607507640d04d0508100d8070580d01d0704c110072482e0400030040c0020b40301c0f10280010b40465141d010031481c4050302061190002 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 132429100 1250 132427850 132427861
    0x90213061a030a0b03030c030309160302010c0f05210702121501030f080712050306030d03060b250b04030903210816030f0609060f4401021902010b09 66
    0xc808680d80d15906032071400400245643c8850f08030040d13058001d012070780c07200801905952250000c84080213940315030000c01c0404217450a15404980c4c0685030070300d081c0c0c0141c44442d0310040d100c000741d070305110700541080d00e103002903003c4066041c60051961204003510400c14818190200f24107a603100003000901e03519011080390442e5403100202200302114a072104c80707401a030402130080d210101058103a2900400110303c0703281c048041d40e0840c041c0700b000340e00f200c04d01e008143c2101e405000b00c0415440501e03d0007403c2000d03c0b0000404070303240d690008240c108440c11000240600020410008e02d030b00c41c04180214104c2d0000c4103140054010229240103200c843c0034140b464440c0020b83c0a50701c843c41d0034145e50810b1000a440d42d105402411080c41010001c05854100003605240503e0842014445008802d48586803440c0905460a110220000f1010741083c080001000344014820105d002c85d03845d05000b40d1010190858000c410340038010443d140c00c015 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 132430350 1250 132429100 132429119
    0x40501090b0301142101021803060615190903060608010209010212120c0702130c02010e0c090412140d0f0605040e0f0c090a0e010e03220602030306010f1704030309021306 75
    0x100000646042c5c50910340c40701202e000a0011200034815480010001d055070540300c0721450800040c1e046690540f2990144107407071407070300083c46d50a4010b1044280001c070712412081c880b03695207051160907460351200d03411144161b10072803e81e9800a0340b84680e507014040848140107076005e80d410017028040980034039800510301e04200800040c400110b50303480140035917800c0d110008004040e01010081c0c028060024611400d200b1100c42001501e455440c0c0ca00c500d520081401d84000700203400c1e200c83d030703440441070700d103035814803581d007030708250344161060800b49401c0411600c1c680b9090000f2500c0c000100f078016080117900c8006018001a030310340d888400d0710405030503030f108031f042c0f03000305442803d591840d400c00e0880e03240310400002401e20039214100b000d0907041f502c000c0c0341c000030141c411403025070010300000b9240e40c0121102e03164940603007000ca050391501070360480307402c808032411000700b50756070840c20942c1040d41d04000c0018848008012450400c401617 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 132431600 1250 132430350 132430379
    0x5100207031806090b0d110310031509150b0607140705040c0903020f090601051909030506180a080c160618080c0105040302060c0f0703200906010f1d06040605040501090b0301 77
    0x100d800c1c5001940850300b8643ea44440400b02200d00389582324104100d101c1c10441d01444160307544c0102c48003d00580e0002e1040f08481580000c0104401e00242a43c0f0082d181c0c64041d103601200500c03018000c13a9004406c40d105441c06000382100300d042408000032242e0010040003002180c0d0300510060b103030160307106071411003121882ca65542d0100122920700c0303612495842c4000d849420028603402c1100c240649114400f511025603a0340c20310b0541c185075907502e0109a00403860180030440e000300402244e09000c0c02d86070130101b88840f214054180c1c1c0d00040010317040784000b03c25080019410005014024090081c0084640009025004500001e0300c0f8070740024801413080010400b07d40308600c200d0580b00c00c00d076203060501e403800d034010400188100300d0034070403e18585880c085214103016102d0000250000b18106c4100003018000c40c42500140141240c55079040090402840107684807541c03035092170b000400401055100c418071010510051020402d0321034103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 132432850 1250 132431600 132431609
    0x1110a080f13081305040c090e0c070b06090a02070803012d060504060e01120608060f0c040f0311060c070b0c16080d050a18030c0f0b0a08070e030a0510020703180609 73
    0x1c213032150003900300c0e1085112164003141c0d01514040750600600e4000f001d0381e044400d001902a110303a42d04080d220a441400320003010501c05030001030491525660b0113400042480700141001900c0d5280059540281c20207540200f6101c0c108140080c1841090f50b0038001c008491728403442c28030040d21340d00440c0500018023501c1100701e0070907482290701c07c0c820108440e06001c800d61f20901607880d000183e0320035036003280030400141110000422681107030080711205001e1803858a417100e5481040b800154444c40400c12000c8401c0c0400150010300f030074230742c403d42d5060751070145407410341c81c1c02e11640c01c0c01c0c03181c904005013080030a415000c140d490070240c0e40e074644040304941e040204070200d0321205240f0004024000e00042000c2640e100e103081e1050700d48c075004035040c80d009540040f00050704c124001000184111054299010302900301c1e44006641e584890404188401101101e030340480c080d03003810352000100c19843c03801c6c0761941c0f04030700b4840001c2c02584903025 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 132434100 1250 132432850 132432863
    0x50d020f010e03100f051519060e01030b060304030e0108061008010e091e0d0923011d0a0e06100309030203030103080f0f030a0b030606010201060b0403110a0801110a080f13 76
    0x400e0070180c0f01440b540301d2100010004000300d1401d4084040101030079030313126401f501506845030b60b500382058a00c3e6143c0510300c6050025281103001c54220228080e800c0c10107441d4180c04140d0303140d190255018520030348840c140c0345000d00004060b07000051100f80318400404030040800e80240705a0305440300f843c1040513a039180c1d41c40d146880100d501000b968100e40b05c0245850710045210710224507160746a03607466590307079501206030b03c44010f041100b03c480b03803a0080e551f008007030b01101c070030001c03215502031080d040029400d00d505501c01c9000386081010030110349402e40b0260024442800c00b00811155030314029a02d01050000074a02403000840350050340b104415140c08a10800c4540d64074901481c603440900141c0b0700c41e6000703105220100e00c1a40c01801030b00240c0e50000305040c2003525685818443d101c91074071290304004c8150022505c0700e000c0c043d8108440d520000c2c9551460030003001002c1a000400c052850702c146018040603820140f0640380082c5c100c3c2 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 132435350 1250 132434100 132434117
    0x3082808012603130f0e01090c09090c0c06050a060906080111030714070210050901120501080d2006010b27010f08041a1006120509030a0302030c131e050d020f01 71
    0x1000b107450341c442c568003480924401c010003c0c08013000510780c400e4034000c11220400380d0341c49000e2015a00c419640c2c0001c90a020b009000360f03e065808050060018600700c61030720641c2e02c4c0c2400700e4106032041018603850700818030411095014990003090400020040c034205d0450400d01400043e0052003003140c3c5d00031500b1012402829281c8140d0020b1084100503801d08019029078005d2001601080c0080500d226a90461091a0480704498090140703101003c1d0b04032210120300030301c822040d81d601d4448083d5501001041c0c003070044c0e540740503916502942110710b541e0809510840c01c0d90007007120342041c1d0b03005a02034000b10081c1003d8415031500d14004680201d803444540e1410f00c03100030030009100c030810341c5040700c00c00d0b00d4621402c2c130081151000d542c8200c0f0190707802d40c0100000c0c51102d1185c0d00642d8081e250141c52401c0100300c5594000121407540640e070401c000c900464004040c000c0f0200080104030303503402d00001a40e002c200c0030714072074034071906101556 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 132436600 1250 132435350 132435419
    0xc0a0209060a03050105070503010315090c14011116080c0d0f08090409060f050a0c0c020114030901060e070302090a06030203220201030b031009120503101502070308280801 76
    0x10b07000006507078480001e008528040c1d030010035030340091109448054104040418540f0f00340706888056402042d003041c140d00301211400c0c072503001c850035410086444c81620310000103002c030b5040c4c944440c2c580c141c80782ca80914075142c00030500d4201c2c4100d0206082c40001110b0140c000341441d44010026103501c0c0d0040020700400603810060082810314000082c5004036501a501c02c04103108200071052409404941000d007800009002c551021107415810300c00001030f680c4000341100200d070858485050640c407007000d56103900865008141c150251604c0000007001d09501d02e400c609600c2c103e03001c802180201c0c1c10a0b50941c02c1200c101d0250b900c80c0c3c0200f1801140901103a11428480b54150300401a1382010303100300510860312043d00e8400da040303e00890380303e10800c44036810060060340f0450085031090540c0b03d69030002001400e101d02411030041106c0c1421103000806104420480110b08850704201e1080014000380820329540c0542a00403034580421481e81b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 132437850 1250 132436600 132436609
    0x1703072106050a0909020111010501050a1403030903010c0c030807020c0d02040b0d05061014030a11100c0c0308220b0a05090a050901170f01051504111603020106080c01050c0a020906 80
    0x10382200f60003481003803012540e51a903030001444907100303a9504109034001100c10f8200e80080c0203003580300e11103080c10005840b1059054086800007000d4070710b812030400000742140c8142c924200030821000c1c1010516410171403540c3e0081040c0050000f0748111800940c0c0900d001070024401ca42c2c0702d001926545076058050100365110701121030900b080c499270402c0164610540d480e0000b0003c4130446818042820480240e2010b08803d8604500b8100500b00c4000081e0340104910103d41d14003040c0c860301d1200c003c42c05040703017559401d0380344440030702c18040415010a8a0440c1810003440300290101c4c0c0c1c001036503207421501c030000b620016288003402ea0080381c1c00341c10130001281e007554007070200b0000d90010040310024111520340500740d5608031019a150100803020a9450801e50040507440c01c040800382d00e0807500201801e200a2900415070040c0e545010502c403050041100115012007424900e0610a41004096807540070000090088820f000480c11a071103 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 132439100 1250 132437850 132437861
    0xf050309011506180906030b0c030613020315040e0105061f11061602010b0102121c0b03010203070903050d050903070b0f070507090b01030606140d0504021f0c17030721 74
    0x824603906803d503980f1008141a0a8910443c2e8010035480d00140c2070465104240441c2e40c040004d80440e520504001c0320381c0c00c000d06042e04a5940c091507a42a031161004600c607808010301500604000070500084071110041b8400503898101400010382e101590426401e070710071a8004200118402210440c1d12945062024400d604c01d0200030005403000d4000f245d01540200952003da400480e42ca4071200715038450800c0030441c20600d060040c24410701040e4202d0b02103060741d10301000c40d0899100300e42440c002038110009108118003030195016040c001c1c501207040c102070900080c0c0761100c031321a20719010340004d110800c00c41c2c4001500c0445030030034103803414a99202800740152924440e104c4c0000c3c9040382c08a1554010140343d8a0711442428550501c3c0100002c440200000740007a64030280d0400f4040c03103945184002c20180f03c0c00c0d61003040001d500c1c03420449140450a1000e001709040c000c100d1441c0e8081c0924414200c200501c0b10254450381d1070302d00400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 132440350 1250 132439100 132439121
    0x20318030309040c110f03090108070302090402041503090c0509091b040605030304030308102102060c1023010e060f0118080318120a0203100f06080f010b10020a030f05030901 77
    0x500341280441c0d516005405c4410b000084800e40d181550455900c50b02c0344140c81e015408142c14001040405200794040c107680400900018541619035a80d0280707050b04401c0000002d481710b440300100808080307003400419040c2c403c40c0d40390a1210689840314400c3c42c0f510110104101c5078069a0381d6034001c10000d08004e800c0c0e83c1c0e119140d0400502d408005c4804094950b03100c140011615540329071440042320103901042c224866500300720099000074510f4805100700c1050040421540c85412030080c40310908a44070280d010080700e404e40c05030f0110041d0082c010801c103003030b02c420680c0414103801b440c042220405085070a12140f4242d04a501c0a10000c1844c8400c40c918010400c1c1c4003904860741c12030003c0c01e540155488903e4803000b50550044001c0344085000c0c2c1e01f0500aa04c0c071914007081071601d81010510345189406020361aa454007031819681c180341c0c01000000203280f0142c03020740400d480241a9441c5c500c8000c0030458000005003059000390321031b01050 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 132441600 1250 132440350 132440359
    0x40605090a09110909010c091202030a0201030504031106070914060301030f02040903051b030a08060603061503090a051006060305010e01030809010e040b0409050d3510050a03200402030106020318030309 89
    0x900f03090b140c5e18020f190042c005804a0400c01021507a0400c0810074410503600400900d14000d00354011005018040e1044091041801c0700d040051014000640700e04c00b00d6603400300c603e02e00180350b4007080c0c18407002e9004090400041c004900074440d41400305030140c90106100d00286030450700303485200100b041e002220030000b0b0030040c010000f03000f0344880d5910350001c0d4449400304841d5200941d100340d40405281792100e14161488017465002c8246800d5450700340301c0303480d00341c14465540b040e484525514401401040c0d01842198054030a018101a10b0760444d52483d0291089080240c144841c0c800e00865503681c0e50021004220045c0040c00015040d04d040b1b81d585d811512040045680b078052840348142d0b00e008041c40840c562112060800c20859880c401e08010b880c030f801c0081514004240c0b40c560202000082d0700c60902c0030140640402c404800c480440c544500c92401000100b0507640e0001c00d03100282c16480b00030070701c0d40104000900d503104606001d41c10 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 132442850 1250 132441600 132441619
    0x6081b120d0c0c0b09030303070f02011107080309070608090d03091b0b1b01020a0504030611070203030c03030a05011203080f0601030f0e010e0f0a0f03050309010f29040605090a0911 80
    0x1040da00125100314248a1443d214a107502d0740e4410b1082e01444403100c0d0140e10034000a6a07403031007881801301c009110b000004000c01461410070566000007025601c00d0000014401d0308802041031000410440c80c0200507030a02611142c0ca8140308030000c0d08040e00c5000ba5418401c0c44000042801d02440d0342152190f5251044007558100e041c104140852000f003561030084180211144250280e980616050450b56880d0082000e18424600448184010001610200000c020311190343e8004c68503490b180b000744055032030580005020244540507500081d40105400f508440f604000d426541e640500480040c042000d1644d240d508150001804a02c1940030480740314040e0f003500c40c000c01e1140095500c04003034000030701103a107045103c0007203032091015507002900000007013080c010482040040d60814585a0000350186950300c0320303044001040c40444038141c80034842d0528041c0000c43c8084000c00c440d015580301c50045040102d2500448191800140000300 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 132444100 1250 132442850 132442873
    0xf0f04050d0f11030606150d0204050d0b01051e0307170a050a08041404110304060903020a050328082a0405030307083402010c030e0405040b071206081b12 68
    0x44a00500700143c40208001000c049282004500079101d6030024100903c8030303450504000720340c1e20842094103029070900011443d40c3e1110340d23107841180151412515541000c08001186041054940ea8075503441d0308035150740c4002c100c2c2c8003124040311064100c41403c03407610303042c0b4a003541b004002d8081c001010080043c0031000d401551007803080e500c1710003981810b10080342c0218000e00110b034014800540090ba10350800d4050078464030656464012981e20303280765401c81007d400640c0c8070280e80813560315012003402c0001c65140303401800ca050540c03d1851820100c03080390b40001100418403404282003003160001e0a020b400c0720740d2140746045c00f491a40103880c202070a12008034100c03070046e110280c8044650300058100034140001d90040d02c0c81c0c07070041c0b403c80c103000c00d41d1034120303140e6078a11409110754000d4040c11100d10f010390006003001e026900c0004000d00d000300c14400c01e100020000d40012015000d00c28007100c4000003800001c8103801d0a800d031150740840300 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 132445350 1250 132444100 132444113
    0xa030b163608010c020a060c17010f030b06010e2d060a11060a0e1c0306090507021510060c020d0203010f020c030d14040f2a06020109020f030604080f0f04050d 70
    0xa0701140c0141150001c15124034250b402d07070b40007a2140340160700c0070601350081001c5500600792260641004060090300b8a100890420309034406542c1565200c0c0820034020074030800d66100500740fa00300d45203804000007510100840e10010710b42900105116408004e0083e10007840c000145525101c048503000200030b42c01118030100b103401400b000c14440303402400341400807010280500348000b1a900e007039030341c105440107510801d0345804002421040c0761086600030b5200e50301a010100100340391200200e0090401031030b40041410070400380780e0103441900c04540c100c0c0d04a92100b021300000380501140e04c4004070151001400114007000000100300d824051a410300404480c0580711042d0300042741c024060180202020001582525041761140100804220703802081e45140354602c9283d004080540c0d943e0143d20158035101d140d5a0b500d0000320018002c5281a540d0002d19008142c034520510401003030700341c0b000c0c00240c29a0042e11000d01621030341505802d140 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 132446600 1250 132445350 132445427
    0x5090102072307030813180c020d0903051c030e01050f090d020307150513060920040513020d150c08010317090a18020f030c09030c0a030b16 62
    0x1160450044407014180c070220100b90020711010310302a1000528640b1150321a50068008400e600349880d80440d1914a0404c070300b1800d0162440000c40c4241c0780006840e050f030f04039042c400c0c0304c001a003c2000030300020743c0034040b9070b6200d6040c5401804590580142594a1081d007a9500b400100101010901c0c5018440c885050031038802d1954204240d03128400d40801400e80d10301e0300505803400302c482d0800c81e003000c04210b0b0f0150701d04203912140211501d54a08540309c00071482c40301414881d001e4007244c0450200d4080040e400c00301c503a0034209085010080c052140c0c6000d00051107031500948070b065035890002e0289001c1c549000301468000d010460b13200d42d817140c030300040380c864100b41d03840d0301400f4103064003050034400b02251500c2003045030841c0a408203c4445011520f038081c50040070400001600e68403008101405c1011032442c40340140d190380410008a03016400f141e4112601d46c07910308404c08940c00446260800744200b81c0c00d41d405c04e000c6101c0d1142d60400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 132447850 1250 132446600 132446603
    0x30307020705060c030304120c0f0b01140a0e011802040b070311010516020c0f06041503020405100201090b0109020309012702040b040501064508010609200702130509010207 76
    0x251007000d5110010400c01c2d0088519143c1154001e100150006440c02c140c0006c04141c1d0030644007041c0b0503a11820b464850100c00c88440d100b01c0c00400c4034a81c140350f1403000440881c3c081620781c3c1024281c01181d101442000609100d0f613460941946040e41250080c041c6e240c101940c88100707040c080c00c040d20b09220203440b9843c000000b500860242911001ca070150f60240c034004c40b00b4002c00003100c100a2180e54440410400015520ba00f00500408102d981c2c40c05600d4038502400c000240207280000410369040c0041346c00012400420701d410b480d00f1440c01a01c1c0d480f55644140148000e03400b81c2811106401c00071032200c0d402d0041001c6510884060282284010600045d20070038424100428514001a140c00a030900c20b404401c180b0047c4100896160524003c603041000704080c0b54108400140000350083c0194409464000400c0c046206004609941080b0489059949841c00b050b10402c5607600a440701321526480811303c03480c2400320b50f59000f075111010 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 132449100 1250 132447850 132447853
    0x306050f030d32180f0f1e0307080a02090a05071e021c0305061215280c110d0504180f02090904060605030d020a12050306031203040503340305090402160503030702 72
    0x44c500f50314034052a0b4200560300c090155035901144405000180c0036000034200300100c400100d01a60f20308100c1940141811002400903020900512042c0c40000c2e1071810402d0800c400c205000350011620800b03840345600c3d0481488018500701d08010140c0f589105d00201c01c500d503440140c1c183c1049005100c11036135810740030346902c1d01702c0d40c403440006271409540d000b0740000d841c90761001035100c1e440b500c0c04a1440b1000d011510a0480e05402c881300003240803e20820000c4404000103142e13588142044e51409080c044048072030b46c0e00101c0130f9555038070354100c2803000009030181c40710038a001e0825800d5080a02c0c16101528103800f90301d01130301c507001030401000c2c800140004241e802c2040380904800b48002101c10b5400107002540510409014075030b4200c00d8001076100d207008202440d1500c50303040d00310815009519a9060b56210008941158000104400303400c40d89402c0c42d42e03031410303500701240c007a0288421691021882080c07160a2280101c01180304824590 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 132450350 1250 132449100 132449137
    0x13060e06090a0b030a120905090412030b01020d080613060806070f020d020106060905060d18142a040905010b03070306090c0617010909060b09070f0306050f030d32 72
    0xc2c01201c01084180358180d000526003800300300130281c168824081c5140100320540c807070b408607003a40403c1d54200c0b908910458000550f0780c1c141b2071811240000d1002d8184e2800d4100c00500d556005081030344522500821020250741941c40700006003400c805442c03007852324a07000740c104195140148054010714492601c040c1c03040c4199415192280c03215525a800c1038180f2505820546600100540ea141d40b06660700300c4035401802c1c280700781522168141c0c00c0b070f81c90341400d14910209017040d424040340c101c544c91080392054440001d4400086841c0d240c00c05501428244070402c2d0180038804010040c8040c1d60000740c031040c0249000c55449039207030340c1140c01240c845a500301801d0312100500030741d1403641184c244030b8000e40000c6601b980e58000907010100541b210404291107141107014140c01d406080c000b400110b0340040040c480c0d0011940f500841081d0380c0c1002040102078502200da2854205901020b981e0554001c4c0042e84ca000d0079445860496003900510 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 132451600 1250 132450350 132450361
    0x40c080f010b04060906050309240712020a05030402040e160602030912070806041b09020d050a050901090b0a0b120708010c080a0605030309100e1203041511030702010e13060e0609 79
    0x2c2c044404031021942c5a4820515101c8116440c0c3c1000d0194401030041c6c0c0c0302080302a200c0c1e10300078501c0f800c03803240c0c440600741402c0140113551101100300c1e03024014442000381c1d5401c030b000e0303a51164050310007040003465407140c582007112030804001c000300d1105000c0b5003264000050507406005442a0441c5107111294640d00c1e0614030600940354842c1000030001420040342044084061f00380c000f056403a14540c80c281d070088104450316590348d008000d860041030143c0350300000c1b1000208403001c0c031743e141c49542000052184090640320b40c1040141e40300c0c1e41c1032002010703074981580e1341c2c40e80780c0d60014060710002c00303828000b030000808a0112802481528122040107008524006640040c882c1c42e43c001c1e40403505101444081402c0c54a130000c1c456440000e080185a0304c1c0c2c109909800c282d00040084020802c030341078071201c00700e40001101c1c031582d024205501d881225a000501c1e046200d410202c5480c100000094040741102c81c0c203008500460301021542e0300c6 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 132452850 1250 132451600 132451619
    0xa06020d1205160c39170d0e06090909030c01050f090a0b0a02040b03070306031514010905040503160b0109050105011103180f04090305040807050609100f0e040c080f01 74
    0x760340005034000c00e00d200d030024078040d204003001544201d480515001715403941081c1d0783c00c00724800c1c40c040c2078200d8441c410005541c4d214081d00002e422000c9540d20401d0107a80c1c0c403c1c1000603028880c0755901c05c1740390b80c0c0c1c002c2941c2d00e10307000a0030480e152034211030075901d1f138201000f6001990f080401084c50b404036880360500c6501194010141122541c890252070701d00a04400d24041d400c10012a00081c218003c51041704941c070023140051846c500765000889204980c07210b82d141450308a5204450503e090455201c50400301b00c9444600300a81944907000100180d5420388070007038100801035482c241200d00f40f5008018607030fa24001965020803060300810107400c100036240e189920194000d0000101910048045c02c4200200d41100c06842094010400100b400c0203900c00400900c0e000d0712064800b0390400040030041002070f40142e0010007401100081640581d2050b03040c6207814500030f105128035018290003900740c50023540c189150141400020501905 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 132454100 1250 132452850 132452861
    0xc03051e0909060f01170a0603060c0807080c0a050708180901170c0d02012a02060a051e0406050a32120a090210031a12010b0a061110090f020a06020d12 67
    0x410307151901b03c58202065103950703003030040846100d981c5e40c860100114090307100e01d08800125841e030b6125414464400303891510001d0441404423002c010420589500009840485502a92250300c8411001d8401e400843c0c1405030740e00000b10000000d070031041d0300c00103940182c407402644e50200503a010300c640301a1900000e808203d0000c547c3c04400000003501d01c5412880c5500c0300604172541c00503001d0384c001c0103c9030004030003003180603110400c0160200c4401c2130844851605181501c00b900c140540180c007014410a0455083c0440c445480e40c3c02c03034100c0003241c1c0301656001d18090090341004d071862520922100c001685200c4a10411035140d03002040c882c2d095510403800c0700600b0140034800c403031072421000e4600e10380342d12402d02c01f11106440042003021900041c8010b0b030a4907800041046480c191541c3c00701e0001c03d03540842040da040220301d1103182d0074800750240c5100c0c1c0c000d4001010400010ba91540031500c4001c0c01c0090b5106507510030f060141c801600d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 132455350 1250 132454100 132454129
    0xf05030103030c02120a020301090b071205010f03020402030c0c10061805190b01090302040e0106060305060306010b0706200705060415142703070605100e09030306010c03051e090906 80
    0x4400c10f944001501c0c1009a80c03a0580c2c000046130001a4540e01113804e43d601640100c645650410900062a80160441c1c0120420500c10031056140152000c9520034503c0041c2c0540d41c004003003458540000c0031500402c617548125440c1c03829581000d802400d140c400c4803021a8040d40b034401c0c41142c1c0c041e05009000703d40d18508500c1d000c4d94041c0c0203141c3d4500c0281800b00000c8000700503100d0f402200c2c0840308000000800a140c220701400351040240302d140710382c000c84010f10801038080203560080b038004078009030548000c0e01c910041400d0349000c04e4801004610201000b030b000903002c0c800e521801440c00580349010021047d5200c4140a543c40c084070000a15880108142034110a62804403500001c0b51644c3c1c6900303651100b04191103007611842004066407021062500030309858205120b43e10300520040d480740006080a41040700703000d5401e041c54030410943d4007080322039041d00340004d1001080d443d07583c451030450b03016041c1c0100003541c17894aa810080100b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 132456600 1250 132455350 132455357
    0xc050c030a1419030f0506040501031a0a090827040612030305090a080f040e01080313120302070e10090b04020903070303051303060f02030702061005151309140402010f0503010303 79
    0x800406040e03441d082c4500b2500c81520082c40240d400da504000c400b03a1031800c540700080d000c20301802050030f541005214a000e142403900410020300d152280c0488080c8007503c2414035181c05007600302078111080080c00c021404200e140205000081c0c5040e1002c0a0132805c0e07019448400780000d40f040c9100f9010785440c0d003144400401d000c2d420a60340316803c14280c40f04a0b2032544c0d55210764111084034600a03101050601038651640071440c050302c0707564000d5040c9101c005c00462421420301411410415a0300304200701402041440050421644510400e01d810303140800024020f1003288025030a0600102c09410701d0300c216440404040d024040160a548044d00c141d40f03e4080c540314080e00350300000209000344550301b90604c00351070242e40e80c2010000286843d80291502105556110042040d562400d00b00c2001017100c0000715203e201c84c840c824509d0f90349034401917409082c54448102003100f01005440380e0300c01d03201c40744017401c002e0741160503020074000140803 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 132457850 1250 132456600 132456607
    0x10212031e01090b0f010c020f150906030109060806010e010e01030f061e270c03030e12010603060504031202030f0f0c0c0307060e150405150406060312020c01090512060c16020901030c03060c050c03 87
    0x403402e01d620009030312100c2b140c0340380ca070007488000b1030303419802680444201641d4510074465484240021801440c02c144040400d5041c02c0d851030641c6018800144141d0442d080941040781c0d5402802c0c1c1da035100184c040008120088200107000407800ca0240c0f0005100d44511032605403030144002600074001c000c40342e00f5585c003500c1e5068002c0321254085404020800001c40902802000d5407040b43d01250504040c0340180000c1100034060314428014401c0005038400c800002d98091140d000720851a00d074424040014030450142d480c06d030200107030000031320405810a40c0c40c1410101200c00d2518401030a0151602c2642d0041858000049a04444030b0050400c0d404c40d01850340001e000f9502d540e210341c101c010400080150700042c203101a95a000807002000f00b4003520100b075613843e000c5006858403001480800f080748080f401000a0307641141050320190f001d030400c14203584030b0030708481ccc2c980036200480300e0504101408002522075401d0300c59401c80d11009500f03 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 132459100 1250 132457850 132457879
    0x218030d2a020a080a031107050108130303050411060d0212010503060408030714040f08010e0606150d050408090405042102030702360a06140402040302010212031e01090b0f010c02 79
    0x1080c03941a0300b66408030a488020400d0300301803006149951107a15846400961110030a042c100d80d5800a8140b01205007003042c0221648552507144c2d50600e00018a95100e28001440343c0380d600426801c0701d004946000b20702d0342d0380d00600c40c0c41680006403240342e0b6074004059075060100d500400072101400810030190041d41b5021180b000c0d06000c50400f6100c0301d05401103100e950220b1740981d182d00a0103071500c0f0034050303035401c80d40c181c41404c1c40f491241c501d4032480c03003a0410001920354500001c2d0030300a4072429141c40c504024418804d900300341c10840c00c10704086098400410144034604a0b1600020841e0072450b40617000008048841510414174140c4603c5040341a080d42010b5159040311419548200d400090001d955402c141d511250001c80d2000140610302c108030030f00160b0b80004004a0b4007820801c1c10743e0b2551508100b800e60900014070303910701075480e0008902c040050300b04c1600224240c0d8a10a0740e405e45004458030508610041c1d0000c00948080e00d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 132460350 1250 132459100 132459167
    0xb0409050f280f02030f060117010803180a08030a0503041b080d030902030a05010f051812090f0310090309050f090f010303030506031e07060207060f050301140d05010218030d 77
    0x196544003042c000ba202c01c1d00c03003242d000c0c1d0340f045600090700154001000f05541c1c222034096100520340c0001807403036042c00801c0ba80c0340305002c0c00021400180148254654a440c00000a400f51000796510b0741e41d0940068550b800680c1d045a44040068900711100142803081d000c4410754802031910a040c190305034006e12218205136050300800b03400002140d024044c003014006001c0d00007487c0c2c40c007901804109180c035607171410203030005030380300e189440c544081d508088400c0301e079040142c80400c00a454480010401d08056080c1000e01e820f00d50440030400440c3d005842c0d1140c0c0088070070402000c0307542107825005000e400f40050002c06d100354003207a03010001504481e40050002d8450980303480300a10040e00d46d11808041c0040341d814041c0d5401015903051406018040708400b40060005021f0444164113200402c042543c80c0303a41e5a045603042002195144455811290301e103a0410210b4040d12801c0c3e11000b542e0700c43c1510342c51002110181c41c40d010180c0c0302d01e5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 132461600 1250 132460350 132460411
    0xd0f03030209060723100b0619020f060103060501090606030902011e050f1206041404120809070902030109020a0e01020c01210b0402190e100e06031e010b0409050f 72
    0x26a0441014813a500000340014014021743c0c105005101d0200c110ba01c00a00c0c00c4624596000001d0900401082d03644030300c026500192071a1000c0180d0401c405801c92a000d000c045014051081000010038482c5560240d81a1042860113000b0961030317a60a40035568110802800114020850811200c075202007540b00410352405518115550700301000c0c94010506040380501c80c401840700c1880c081c070a05804141d0000b401d0103a10745074880710032070101a24800284151100010749580040c80300c88083d011249045480756140d0005400070b420a400800c041841c42d29022140e60001680050580b81651040001c0c0c581a07003401207040c149040344521030301c0300120003440e41e8600103032100b08500c111400c00b1140240c0003c3c0f25018082c4c0040c05003c4182031400e8042d4860320340c90020109564555032a116450800100001944e100c105142c40c4000400c0345600880180111000e84006114684038984040c0b40c5000030780d00f2840b03956009000242046145255 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 132462850 1250 132461600 132461617
    0x7080709080706030c031d0712030e03070303090e130b0a090305120103030221030105060304020d1b0b0307093002120109030512160804060b1c0501020a0206060d0f030302 75
    0x100c038100e0394034000c052502200f6044100030a40b1000c01d0b645040d458490030580450385412032405000c00385101c1e480b580710f40600041c10070030400250034035019032008680110068101c1c6c1d803041e43d03410001e20100c04c502030b031691045d001c400302e4444404d1071140001282c02045c1e008042c0c0307520003240e0090205c4c0310100e080c048144030141c03034001f01c3d04c1c00600a50180d000b074004111391b401c0401c2242c20a0140c0b50503004240014003190300e600741643c1c0d0180e415036405004495078100228030034280c00c0034583d01340070800c010441c00452006035001303011640301c0c40112030b202e85484295500300c00b0740c0d035010f183c0c07499850851603010325848082030026021002c022074041059083d2500c00500b500800c01c000f40c03841d5110303034049016034002c4203000c464412041d80d90b401048510b024201a012544401d45002e55949421f0218200c0e0b07140300f1030314202c00315440d041d80030350090401003000d8014030001030b0f42400c00001000c41154403541c506906171a658007a4025040b50701c5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 132464100 1250 132462850 132462857
    0x6030c08040506060922080d050603070315020f0c030705010b01121808070201031e021905040501020d0305101d0609090111030406150b0f0903010c030b180417031305070501020d08070807 82
    0x21b010710001c0c4194003000784074000d482e501d980d90410041e95040d14806040c89000364421402000445e040c40085042000042030160ba07030b03658000c0c1d00790180240745407034000303020008a032020014154086548000d0a0b00c400c00350340d0464816004841541c401004c030701c060402030200080c019801481505d02c141030020b1102c003248290a0071218543c085070100703034005900c4030f82c05100c0040b0107001c0c1903450600e02c1d007030400000039282d0008000c902c0c2031545a40205103100520915240500806421181d00c440c10440b14101908203640da2405000a84040307048000f060003010725004600304030300e00e1511aa40d503480109001c000750b2030f002d49128808204841500000d0040025140886440b4503022080600710b4000004001c14540380401c4042142c60701400d90003100649d40080900342d0352801c0c84980d024410340000074554000007000380c0b080a8264159985014000302c0d01620b88581c01640d9686106030444007250700075001401862040500c903034001400c0c038 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 132465350 1250 132464100 132464131
    0x13090b040f0204030c030b10030c0b0d0e0f0c0a050a1413060e0f010302031006060f110102070206030403030203090609011a120c0904141504020a150c0804030c06030c080405060609 79
    0x240301c2022600a50812100d80c40407400400a1110304001d140e0801203d000003192686150758800c12400706200d42c0e91000e4011078245030400e101d41c4450740c0d074440d01040c0c17003400300f1055081d13485510300c03500310348521440340b4007103401c0c01c3c4100380c901507a401840c0322556080702c40811800ca103413005a10259038540c440031070102141030040740a08070141d00301d105035045104041c149480304415284583c5054130400869070b04c141c0b80d0030480c0c807a00309250a00400d01d410b071301901c00c400010f50020030010a12040541c59070007581320740184e4099509944036000c200e801c4c2e800715104141461828074003491580303808140040303c2c0c000682184c041c0c846550200e00710b0b00c3d0440b41900d58607041c1004481040040c000b011401d000c9011200051505030b000440c40b91450003021242103126105200c8940070300c1520b0f50320f80d000201561150760303a280410b0101c2caa409480000390510811849040c02940c0c85401994004060100c969506081c4100c3c400b000b012611300b05e4210 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 132466600 1250 132465350 132465371
    0x30a020702150c060403030c0507050a02060f0c061005011e051210081c080709030b1914010b0903070b070b130c05040e0f06100305060703020f090a06020a060b0613090b04 75
    0xc10061010114030300103401c452400c6c0c20050b00f11803040300d0003810320204118210004a001c50130140565044903036984445484241c12178034003c0311030300095845242d040c07120036031080d040501200c809a031038a036012185035841a0900400a404012590511100d80203510a0031841c0c1e00800c0000c1e03101c60f17640d0b10001546840d4642c0c58594068468655100d400c0ba48030141c564000d90908203c0702c1a40744d6a285420450000c0508101080000300304d13640c2c0c000c0340c226a014030394031014001c040d40c545a60008540c01482c030755201e8403440c240041e0710000380c8143e079199034000e42481c1107503441c48001030030340100f440c0880f203041002070046050344c2c40e803040d8011003004070000c144000450f020341e07280a002400c109040e00c00c0170b00c1040003400c0058600d60001d120328004d602e5100050042c110f03400b0300d03405140d00c407407201e101181c01c0d0b5002403e819424005c480a000c80d207280028410b142c40f5481c0b42440000703c50324103020b9403c45800400d161032002d0700c0000e900540 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 132467850 1250 132466600 132466639
    0x1360212010603090c080d090504150305060403090e0a05130303020c01090501060f1409250c1505150108070e0d0201350a0b090403110307020907030e10020f030a020702 74
    0x342c20060120740e40c1d074421001d10400c0792040000d0106800100500c07031501d000540148454030556115a4603000340c01c10019488210400031360b03200048500c98106854041c16001c0c0c54002d64985044640c001074400541e4000e0034080c06041c02141d0880180391000c4000c0e6000181d0745610f9174030b883c51a03000400920860000301310b00f02d480d1704120300f00402d101050421403000e921400340c031b0090152081d4209599082c2d030781e00c03020710140100c0c131000580c0c0140304040702914003407100c0f0780700440b0b02c3ca0781c0003940702d0f00e0312101026030f45200200645e0b001c1000c1c0c6070071002501004050417141464001031083c14014107000a0030126004030101b0700c0841a0429140d200080c88501c142a8842c411600616441400c6c8605460000031134070458004101900308010303031030381901c608020b0007100c000ea81c018041340014505031034094090b025201d8542c4651040c1c2c4001d8a03501050f10913035922442011085145031110f00101c00a504580f43c00e03a8088142e0450641c01c140 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 132469100 1250 132467850 132467887
    0x1a0703020f0d05030601020c0109050f01180e1e090a1a0702120708040302030c0102060c070b070c0b10030b06010f0203070b060a0f03110405150319061b0c0b013602 72
    0x110350fa210340c1c0345415400203081410709051581882216481031002da51410100c0d0a0500c086c0b80c0a090b59450182c520600c0c440c40d8082401400b201c424008100e000b00c03074401c640e0050003550103583c0c82d6001926690800210080e00c1c0301281588120b04803420006150001d015104544400c3c03210f4007101250b0340480d60031141c0755000507042085040074402c40061035000d002502036032411501d460703043e00c6036180080c0144a2100040e0001d4046c400d001c46980c3c00c0003003002c29181c55460324605d0f400d180020784140d02a40d001a00d07035849400c400d1002d54607980a5418020146d48040740a98050035142c0d10410b1000e0202e00c00c800641c50400070360181c010102044150341c02e000484802825842e910b45040c401447c0584000840c07086c45106003c20700c45281450500c4401402c1a0170b100b03048640300101558100c0c0e200c81001d05282c0a2a000c0e03095903039071012424003030300e00c2d98200c110300c401d043c1132500d07640b0805200034026110b00340545012800000b0318813004 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 132470350 1250 132469100 132469123
    0x6040b100207050427030e0d0c030b060310021c050a0e1c0906020105040f020d060b0a1203021905060720070b040e0a06140d030c021005040e101a0703020f 68
    0x3484680208000c0c580343c083c5266411a2107030305c461440f10814880c4004291810103170030f200c00002c00405540ba44c01003c14903603003000c20b0084803601d89c50a0303060400300740d806610921402503407030b421070124800c0303440c0000048504115591400418009000010038424040d44d580e800518901c80600240d80840004042c0100070441d00101400525041c0c2021046a24080030000054628024201e41c01c0c4c04440c001004402d514091010301608111107400810303203200003070710500c0f0f00041c4024610030380030b42c1c040c91040c882d0781192104680001d801a8003120100707048600812580d0000350002c140f4014240c82d40c0c29551030040594803800e1403140004042120800e4140c2030b42d0000365800c07081c85250720300005045040106c0320702c83d1056201c0c00d843c10030540141140300c41c1541c05003d800380050110000391090b00540714034400d0f01c00120004520001400200054070f6250b1240c3c0c1d50795a4076205000a9001160308405600c07507107110a1030184100580d154a2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 132471600 1250 132470350 132470353
    0x80102030f04120f05030c03041509030f020c06030606041203020f0a03050909011202031506060d0f05010f05090112080906091906021c021903020705060f03041719030506040b1002 79
    0x1070420345484040040000d40d00700c01c006500c0d64000941758804222074020b420700d018aa12a00d442c01c08410591300010fa19811916042c411010140c004100541e00002a001da440511208041c0200c40c40120741c8990310920421091003804491100211168041d03c102d841c62500508020f203481a00c0c40250f02041003c01c94443c00e04c0e011002a0140c0b80c0a41e00e0038415080f07a000c03998034100306451099400d10301e00000d500d0303250030007921030f14185508180411904040c900000701006c0c00703014a099071511010820b41048425503040b40c501d09103446499680e42c8640c9000d40101c021650300420400103101199240000218a0480a4580c0d40705503c3c16902a02d40466900104403618401003408103168000c0b80d00d01240c840c80d48042001703a01441c0c03c90a004041d000310b54861004190b00062a007854041d501c82c6105203050000c41031000300b04c1c95940180101855105103084801c03280b944280c2109400000244c00411120603410000d01c020b0300b030503013001c0107 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 132472850 1250 132471600 132471631
    0x40c02070515040e010501090303050d09032102072607111503040803060a090e03090118030804080d110a080306010c0f080c010e0127080a110105010b0306030d020d200708010203 78
    0x110504d1900042c01041c013420072104252030b5a43c0034140780290240c10380001e42c0c6226410905009010103980d060840e030903400c0e0b030701d50200c2d010020b411102c2c055407070001102e14641d0707482542c1100700c0302d007a21a007052700b880001c0d40c1d0102c880005c60303091500a00b1008400024911040240d8091442960360b03644918011042c4a140450350b4003405c0c1070f90425140d40b103685804422500b40c5542807800710752040e1600b10078900846140c1c002803011800180000300c8400104008551031b80654560075200600020b00390f54100410002d4004801000410110344c01a01c010110601c202c1303030343c0f503505c40f642c86071021034214591280700c03079440d11003210580d00f087c0310701c40d00f13516040f2040880b00d1003100300d141400e070840c17001004d01000003031000e01c46002d403c0b00d400cde50401d540203000030747e100c002952140c1c1068405500901c5452644c48a560010030b03619042043c3d613a47d5a25600007200281c100b44410036141d905020f02c40021401c504203000551041801d0121000c4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 132474100 1250 132472850 132472859
    0x613020102100908030610110a060b120303060117060409020d0b1902210c07060203070c0b0603030a020c040b1306080717030412020423070e0301111305040c0207051504 74
    0x3020802c1280c44410b40c5490180b10001e001602030329003000c804c0d510301034050100a42510034043c4400c00d0005841070281d01000c100b030980044e0368040081c0c2d0796101e400e4807842c03469076038042581c007580800c040814030700380c84004049045d407019000300049540c481c0c6e40c02103421046000001d030780c42c00695003040106082c2c0341d00d1407100200d60700d00b1481d205031001e0601400c210001440b51028a00c000b0800b062181c50942e079030207400100440d941e04000e40007900ca920082070490328051040005600340c0740100660300b220045401500b42c4900c40d400700300080c4004075003d54072642096182c075100342e0611810002e44a90801465128104204903805602d2030166030a150310400081c8811003042030a0b010069050320089190004541246402e403180e810f4003210118410812204590000c020041c059045d00200460100d030070800b9810f101e0b000342c1d05004540f09500b00803600306944000c8500320a441504c041d0358031a80042d13503012910300c00d0006248042424407 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 132475350 1250 132474100 132474103
    0xb010609080703080403080703020115090b040b09130204092405090c0d0c120f0b04200f01020a110a0e0907060f0804020a260d0c2f09070905030613020102 68
    0x40c001000042160b145165a40e801c40e01c610b0000a000e904003280f0282018000d402c0540c002c021026507040c1035888084150091400c40c48083c0300781d0801a15410398180400c03680d0003a9020188600300c50310603000e00026190340c840880c0c050300e030088110395201c80046000a105d02002c0302282500701401c11510742050302c02e9041c85141489101ca000030258141401211034030300c82d10b0307043c545a00b010030002c8170ba00c1000c1d1617007000c5020001002003d51803000c0081c40d018020b81102c43c1c0c8018800310840f0340e00d68501690000030380b840071445148811aa41030001d252045a6440e03500e1180664400c0c0c0702c00ea4654042081808602d4000d090031003040c105180082280c946500001c041520500c508640d65224503144944911078a40301d07405000c00720308440c411206030800078560588000152011001c0c0c03241040b030380300c54203518501408040d250444070958207003001302c190005003491042c00080480002d0340d071414040544181e003c40b14100e074100050001a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 132476600 1250 132475350 132475367
    0x615030415150302030c0a151b02040f05061306030c41090901050405120c0c090906011e08070504020f070b011202120d020a06020904090602030c0910050a0e040b011b0b0106 76
    0x114800c0b00720721414440030b24074402d4410501002d1605410700441401d80c09d850108000d40a9009820002d840c40110025000540100b00550f0142c030168400079844c0b00b1a40b060000900d1101c03070313070010490144994400b00d00103c4480102501b41102c200c0351900e44140548500b80702801da0001c0308520b006035800d03a002c00c0780c90003840740703185c00e5031820740b114020a420017000c4408100c100c00404104404644024003070451200c5040046100d075550409120350b130350290350b0607920091100ad000d04035003100c1a110040030442c8c00c1408002c06074001c00d90b02e48429900b44601d00c007051014203028000c1085500141c101001401841607007006800350143d154022809141c0056000400d03c40058101d5401030300c0f10702400004029001010020b04158008401e201403050b5290081400643c00c451440744521600d100352128000c0f440c8500c00b040c2e00d8003c218290401b90403031011a48145030014804641c8441c0000301c1049110070350340b2034108001030003244c0d00314260 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 132477850 1250 132476600 132476623
    0xf041d040c0501021204030209101e0f0f0305120f070203030307030e0c042a300c08060109032604060806040e2d0c03010c0f03050609061503041515030203 68
    0xb6001700744c0122011070a0744035600c0000d01904030013000840e200000c0c00f2541c0a441800c0078000500740000d44d081ca9102c140c00380c90500104807400240140c48280d21008980c0c0c8900a4184180440d018155640080b00e420040005c20000d40700103a409000070343c802e51642d10000f8070502549400303841c00b100b0ba0403d50240e442c2044685c074050080c0701d84003a00350020412001941c009078202c80103400711a0110801046083e0b440c0300c20f48200e4441d1801000d40002c0211790380142d001c030350b1600305070713451408216610424030104c0e03003c00c01d4a10000066003c83c0044851810124640d4031a81c84880040e10610620a43e80341c90f0040c0c441d41e101060040c0001103036070401a261026100ea8403a070706d01c0a007001c0405410070300c0030307690a15000303008016100c88407070301030907941205098400103450000010740034a01018401d01804024119807032840d0050540034080e8406441034070a49020800000f50400d1402408901c02c0c0300c1001401d4a07242d403041c9882c04072544070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 132479100 1250 132477850 132477853
    0x2270103050112061d0102210a0501031e0c1d07081503070b0901110f0706020d08090706140d060609090c03090803040204050417040f1a090f04020f041d040c050102 72
    0x40114004070503c1c00c140581000c4000342403d400302c6094202d10b07900303029200550003c5401c86038004220076400d001c100b4203140e01040d60354482403030205c40c800d020045c00108421241c44100d600100c95a100d1b40c41030f81da5202141e203400006014108012540614a40d40c0c020040001da0290344950452032212b40380841c0f00d54100025159000c40c0121413484002107410042d680c0300c2d100081c411881c0d8400c0d1000c40900c40e829603124480b038045c40d4054803947e10f540120074454000340e440b8818500141540b00c0c1800300860f0351045039446480030400c24032071100644500e1140100400050725002d0034145080441c00c00e03102d54070003020606207000e10100201c0c01050451390b00541c11180065240e65601d45030350044099a610401d5a00100e000300f034804103c94003030142c0f42c0840600d141914652203190700e5100304003865800c00050406900d0501301500a0880603411410360782c24540c442000c1824142c030703c8800b007040840c000c240024801413202c80f0b00640380038070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 132480350 1250 132479100 132479111
    0x5101202060f040b0414100e01080703020909100302040e030a0e0616080c01060f080a0b01090e07030b010308070219050303070f050c040f150f030201081614031e01050901180b06090402270103 84
    0x7c0c0207401e0202880c01349040c05602800182058070950468601003001011150b05040c82100c8181c0711076103000c02c900452a041d071003042c000000040e10010621a90303802e6040c5412000d201d1650410105541e5902101038440e0000b400720015092220388400002520381c070340b041880c0d038446198800002070308801204808104070801181c15107944602c0030a03164000e1523000d103404950351025016040070400442008201c000415805000312800c40034401c07007124039604400c00340b00e22541544108550b500003103643c0e40189a00d401a030541e00c40110362401700b0292050f480d40c4d030130b0550340d59402401d100c1100c0c4041010300003411140f40a80e00310341c0040d040041c0036100303c42c01c011120018042070320503c0300c2007a0400600080c1d4590500d40800d140007951500320419964009001103400d00f082007e50b4104c0700703801d41f120000b241700700783e80e001046803010310358008804000740200b07501d0303d000500d40c1c400640c000745512008110880c0b1540b04401005d4101401d16 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 132481600 1250 132480350 132480379
    0xf07050a05040b07020d0210090f09020f040504050403021c0e0103050c041202060705030c16080c03010522020102070b03010e090714010c0201030e150c0d0f05101202060f040b0414 79
    0x70668059500d40300d540b681c0e40b01c05000041540d44030500082d8407070031003074010080030b902115140450f22024081c030111915010072605900440412110100043c40100120303d4183c101c41d41180c0030f4015a0481c512048051044035a920384503000f00c0e07544d000083c501d503407510846502001030014941054202101010240d0240c200070740700d580c0100d240f0050001c14011204040940e400b2203200c80d5115103005070485007032003144060b000b54044288281818003c02e0301c00d0050a010560031032050348a0450b48003003410a0f03046205503200405d032010301d0001503020b012090000c030300074a4030920700d80c03074183c0c0c41d041a21100c0325101b41c01c0060341c0005c0090f203d40d509080101c2d2092a6a104610f046004c00c2c201e100942c0c800140220000d00400418005d91025018080d15004440000665605441a0400d05a0700a081000b50188070016240c0741c03000f040c0c14901100c00641d5842c60b0420380140b83d0026002408210050010080ea0f42e82d0300c040d01e600b101203448 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 132482850 1250 132481600 132481607
    0xe030a020312030405031b01051506090a05042403060b0406060c0b0f0403140703030c0807020a0c03061104030f050f3d060504060303080a0b06070224070602040e0f07050a 75
    0x410720b009061010011404001060007078032101401800d40100080c0d2410316103002e42400d9440d11180c0d0790800c843ca086040c000c1c1181c0b04140098013902c1541e14210070300009100440810b502d05c0b902e54641030110b444605c030140114001c03200400c0100c1244100f004a0302e441d8055410b000c0304000c03080005503940c0b1090343c082c19055110b01c0503542ca0500390341c1d5041400640f80321b0080003071068201501036214002d03410190795641e500350b80c1c10f04182d03540c3c40200070180500d440c40c1010070000c3c02c48d40100c44514003a500c49800c00340d503951100c220030b10002c801c07101508512071003c40c00c20108030265080204201441188141e02884003041c1550404402c00600082d00c0c13517000d448a800540041c10081c20401c40a0340d44c1c200103001110039145140d0381400d00302e04010514084099446040d00102000c0e1400140c0e0048910500a03036107082d0b041c80300f0320610004c43c4c600d20151008010700704100d0001d2400f080c00703c0801c68010551f1041c00bc06104103107425a1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 132484100 1250 132482850 132482863
    0xe270604050f040c0e0403020c0405070c06050906070c06020f09090c0309150f0411040e030d02180a14010507030207030615050306070c0c12020a031401020c0f030c06070e01030e0114070e030a0203 86
    0xa001d08600c0c8a0780362401e040341004032400c9c4032038100d42040107114941790b100c140078004078045e2034100a01e86410307010b16116103003907424000141350610b412002c204164001e2041d090800f01292810304100702007101010b0859865042c2e0300c0c04400c200c0306003070500c0813581c07041d404140740b04a454000d403000054a00a003001c3e00c10302c164880e1409a480386d90084203609088403c0300d07101c100c0a1241c00196000b0b102c01e1a01c024a89000300c000d0401d0f402e2042510f51b2000e8001008450100448103500020002c0d01103200d140c00c001b0104a541c8616105190125402c0380054144014146400300c00303000d8404004550701a0300100c3c410501140903101d940440401300070450001500718041900080d080c00705d0903454044c104415401058603001d03100c1681c00c94400030891685038041c019102145800c03241c00683c105100d404000b04d080814140052105105501a800c46030741001720001c0041c0c44081c23016103500070302200080c0604070001c00d0110290350110b0f45400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 132485350 1250 132484100 132484109
    0x1020307030c0204020c0a05010c0f080402060301090c090e010b040609080312041202031b07030204060608010b0d0203061c050c03070b0f04180902120a0b0105060a0f0e270604050f040c 81
    0x701c1c00c0b42d64011580d69030116902c884480c02101c849102c2818414002c00e011840c25000c28580104180c08900614003184034580042c100d44c1941c0c80c040903100504800d00e581400c02174080d60204440001c1041d0318003070012000641d4456081c0100500000c21a07080f402c82a0f1003407103c2e0600f841c54010041e03000341c5c40201d5074a03a0b81d00d10b00030ba00d54007801c0c0800b5a1a60414802050540009480411a8000c850500805507507410544807100203001e0300c20850420000d191201540b6001190000005042c99080741d401c1c0f80f0040100340b48a20072185500300b80e09400d61450208401405410710420391458800c20004c3d4820501c50340c841c40004c18244d2012854200055100140b080d4014007000c509050111160b80c40d220a48800c50f07042e07407810000b003050f0070034900b070350526100754445407156042502e096400740b17050400b080e40040c541c13111000c1d00c00c0c44e1020255030403c2e042c81e051281000420041950b0380102040e410006410402c030224111450010468 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 132486600 1250 132485350 132485357
    0x14040e041103010e0102070609151416090b030f09101a010c020a0b0f040602120a091202131a13020a0c02060d021e040620070b130e070c030f0903020102030703 70
    0x11941c1011070702400c031207030b030400c41d0b94404a0040d0078420030760040c0360b0380c80c81030a0b40e1850100b6040b840c4112103a01025000e4060080300141c0e5401c55140da03681c040d0081c0c03c12200207a502c0d030603611254002c481c8080c10003009014003580c2d039420010380343d401040d610240002e00d4545403461a0040c0350880740c0c104041502c090043d9115027401c84054801c1c0c0c5001c0e0360703540f0240f400c1c50407039000740314950052050003030560f40080310f10241d0f10001400e65400728101e107041080203180040340810380e07100c10540c0103141c50289500c44c603c0800d0000d2900c2c20a19840e0b020054a00e00820284400038010000c4c0715145502081110310340e03a0440c2c0241d210083c5011400c024020341d501c2c02d11101050703440c88096100030003d003088412644d200301140320482c4041c4000700d01e1081098a40d03001c800180108090315016202c081d0346c0001101e4215034910030000e08410643c0d0180220b13412030002d00a26500c1100110306c03814500306130303041a01d1580000c0d501d00c100240038080 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 132487850 1250 132486600 132486623
    0x50306041e061e060f09030f03110607030b0a060c02030601150c1a0a0b04140a18050307060501150807140906070218070318020102030f03060307050d0b060114040e04 73
    0x40101150324440500801c0340c20440d0355107948014440107081e01e035010803000441800642903201c0e61900c580c0310f843d607403100c0b255440d503075410301c114030b4050089080c440c0b10b02e071503070720241c0800209118042d155004101e0900001c14450885410740113a0200290a03202c1c4001da2000121581101c41c9200b80c48452400013800321402044000d00500c0e10790410b08091914146440c0180038500c84607042280010b0304e0100011102c14a1440607180e0b506030000d02d6020080c5c0c02030030602c250300c00c02036109203d5582d0a0960b800518211955960b07030005018100c4100388a0701c03040c956081560440c20b01d4040508000b9002143c000380081c0010707440d03541d403220400c0c1e0f10300903409041e540150201581840da214411644000002c2c58024000c5050003000384c0c42d44180c2e0103030007940c54840c814103a1041c030340c4028801d40d05403180000004076034949440d414840e6000e400070030305900b805000100418090b0b810150340080c140018007100c0b202004040d00254001d620150 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 132489100 1250 132487850 132487871
    0x916020c0a06081603090203100e0304091e06082d030d0f051501020721020f0607080409050a090c170703050d0903141c050c0a12030c08061005030604 66
    0x3502091805454220303218600004150f900281c19a00500c02425964542c8804600440c210760703603494040d500d0350045d42c403c4141d010a034008807582c00380c401564035150721181c070721007135440d1021804c840340c014880440c04503065100764800b400e5001c2c050001e4651403040581011040801c840c4136201d010b04079a0000e00c10011600c14a4281d0014040c481c4680d000b100284800c549503401c5410042e8500e046601c0403a02000740c4c0c501c00b507100046002c0002280802c100350070100d8014500000508060383c5030000b4101c4a40714445d0741e548e407400d0645180030707100c0103032442500b141001d040c8000140d1546241d401e86e150702045000c00c2004841321445c0c070900e0b90002c2c0c040d000307d545c40440203500c241542d081c2e070701810751003061f08a0602c106607201c940c2d0003000c600d0191640c0003101c9074420b0000b000c40c102c410088a02e0311440380c80702610070800302c0c0301e0400f007940ca8216a44080d000801c96038008411103808800b058000303809401840010a098410343d503d940a10 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 132490350 1250 132489100 132489103
    0xb091e090103021320070203010c0e01080c090319050304031b0b0904050a0b041d210307110a0507060203040513020901170901092103061a07020d081210051509091602 73
    0x941501c060381e05c100b40d01c2c0500075408815401540107900039402e02c15030180950207100d184648540603901c1151507a281d0300c920300b058100135a0190305021700c010910503100c08060201031640100e010307580d40c030302e10f00d008180244500b0741e540b14843d0f0000100f1841303451401b500c4001c1c2c000e135008140c654484401030000c207104284580e01ca0300e002131b096240e142d917840b000d4130501090200d074280c0780f0b166400041319501d00b0010742d08072410000034540314270404120040380c0e01c20040f551031034401da0b01c05040111340c0d0001e0f0010f80c4040b504010b189001d20044415174041c1908520741034039080020800a49000a003d02010305004905108e909600951403607801900d01070060b0034000c49101d01d15050802e400000381011400306101410380381c00c1511920a60303219180c400301307078240201070500510907690000f09002104801a0010071144912001560000d5003800c281c100003c07950f15010100c0004000d0242459584038608101d03041541180c040595016a0208070b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 132491600 1250 132490350 132490361
    0x12070605070e1207080705011106150607050607050307030606090303020a02041e060303020106081209011b02010c06020313031e050711060c010c02060f130807030c1103070b091e0901030213 83
    0x4a40043c000e00200e5880b050100780070042e5011107055800c0302c1da1390001101e035560045188074042e0000d001081845501d59682c1c0c0c11494041d00c1c85062240c1030320f4180c10517600300c0707500d00482d000204000301d1039414840d80010308070508082c02824190b0700c1c000c1d40c402d00703840024012640c480301e001002c250020180344548850600742300c929101e2500a004e09400d01c944409031180e1854103d11400c50720a540340110b069450851950721844042131104522000341d050001030030980000c02c2450008600c40c1c0700c0002c50341ca020342c007880c0003442e541403035210107070b140d0500940e04180e65000307003107400302078001d40d41c01e08148090000411912610954049542c0b90580198640380c0200780a482401c00d8894640c0507902c006841d1034030700314080010039a450802961b40083d0042445000f1640030301080c3ea074500e01c1001091074003550b40c0200c5841100860013014624140400c00011811002007042560b4a0b2000c2115140c060200030311840000005004034103066015 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 132492850 1250 132491600 132491627
    0x3040c0e1e0a1b0903030e0904080a0503040f020405010e011508040803130203190506101502100c051b07080d0203040f030f050a1a0121020d030f0c0203030316020f1207060507 77
    0x20f04a80540c800c400341c40d9403041e01c4110040344024907502c2903860314010403071083c1c0d0000e076103e240140701d40741190720703a00c014021140078401580a13000758545201d2503000e0814540108203950401c1d61429000c80c1340321400c400c010120741000006060f8606507038000119101c903107c2e0714035910002e401c00c8140360f18600109003096100f41030050003d0401c2c02488802d030965481a110701d001400c0303079400d072408405640140800032a2156a03404480c3c01000352a1440c1010055008600250381054840c0c0c0903a020030014402e450b01804104045c903401c4c0001c52400389841096442c03050f1501c8080d04d80c1c0c0e5040e50700014800709025580c646503203c0f49411046502400c6008030310003c0c0034094a018141122100034003010342e99503680c035002021003011450030354003114424610300306042085400c0258200503142000554069001c00c458107070328041010000b464400c100c1420b080741e60003228060b025009003411a500e00c2c0d00008082010b5446d0503007a5040f40c1c08418 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 132494100 1250 132492850 132492881
    0x4050c01180503012f0c0d0c020d140a0501110a2012030109020301140409020618030f030a030b040f0b2101021303050c040509030f0405190302030a0803040c0e1e0a 72
    0x1030f501755541200141c81108500c4d024038440c3c03800000c400702d00b0741c05903000c4500720f90302c45044020007602600c025000c9030700c01040450600000c2d0351303c80303044002110b1142142d02a0000c2820040203011b40741048119a4a29081401c0e040e0010701d006030480026440071010700303440070301600a01030380840048601e605581c2c0c1d69102d00c000001d600034031a500d1982c5469680c02d10030f18060041d0480c40c0d400404e850305204e0f080203035100c205140520540d00d4820098042049039042c0050301480200740c40026012175544140015a0104d0795160b000c2c51900780c0303070320b03140e0f42d199a0070711800124542c1024008c01c8003101402845901411410348a003510000100710000172104180142540c0510850f01e40000b6039990b40a500056090004280030030701c540d082103c09025040e40d00c201c2c2c0c0766401d03980d130007180c1000c01c021410b40c3c0d014400401c06c018010740c4401c0500034924164140300074600b0f841628407000d591010303000c3d403140250204002c0c481503001034440221002 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 132495350 1250 132494100 132494111
    0x906050106021b04060e010918150b0a150215090a0501050423010501050a17030409090b010816050d0807060b10080912070f06020f070f080304060501080604050c0118050301 76
    0x4080d56600d600c8148400c400c1103004140348a0a05020349011100d064559034011f0742810160380240ca20119a400ca0042c461010030108003c02901c2ca03481c2c545001c0042c102c00500140101e40c1e849401809448803000019441b4a41c0011035208030300105190083ca501c80d10203060400c24030413009040c075070803d0140814004e4200c4070010031200300108c0112041c40c51303c40b80c01d03100c0074882c2c1944010010b41c2000030030100311140c000900d00da4140d0b49825110408042102c0300c00000387d4402c06450010311006e00d0400000e00004000e09518010903e00000034924451046004150806c0400e1450401c5040d411003e05482e00902c072014049589100900e20441180e22691520800c19002001c407152011690740d25006040200850f10743d48078a806540030b42c48056022a0422040011840f442e2140300f150344503c86061366820141000f4040d10010303000f12020341c22160a10000400008445100b04000e0030000d10350103480c461190022540c2d405240c00d9400d10307 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 132496600 1250 132495350 132495359
    0x3080c03030f0a0504030c12030f06090506040b0303130504021c020a02060613060608160203040b0415090f0e13060b04020c070317040b03070e040b0d0818011107060305040609060501 80
    0x440590311400e140158440c40d96144190f2070240c03402070354045c011594441c1c00300007140c80c103006032184d02c2c86418049440d11002507910202c945075408280c0c21595902413090914003070060ba55440c0c0e0480045041a41d0940c00100f44881481481d00c16940011b100e10145540c40808031044c120540841d20742c8510a40603445170011102144100300000130810b01180c2407080b1001c4ea0041c0d540c44006540b5200040318000c01c00c1100c0013035200600c80010b090f40c4020040c000b07411200d040700c0d00511880406861640140c0140c1c0400c03011600c1031042150030761a0950210030074150100440503030500304010504400d07030b5034109000169044100500195490842e0301c0b41802520103210311a00962a014038003941e285150204046000d19100c0ea040f01d5000c14000d000096070403000d000184407105150302145c5081012819001030391507844060400d0345c086c20a0b1840c07034464000300c2d4690146008010a06550780082024018a5800740d620103030300090030002035846 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 132497850 1250 132496600 132496603
    0x3150d03020d080a05010b070b09070305010510080d08011206180c060e0f060a020d0809150a1a040b0a05060c12040b0c120702030304140105090a090f0614032503080c 73
    0x4850389802050f103000101d56030b02c00c070b480b07081e040b02c1c200a0440d003070141039600d04104a9001d00343c024548a00b035404004103000780b01d03080c0110a13110403100340306e1910b10054100322030a4070304424080d1540040041c503100000b07055170258025000140c1e07400c00304090072404170207000070f8141c078015035011a5550b000501d505a440c1d085504403035944c44601000380511405d40d508005810020444500078040c8100b0b5421181040550f40003000c2d1031207414040104440403116603403200b48070840c3c01030b14820130742142e1f01610305200c40400d060103d030601906108840c0114000684056017040074414144402d070300400f182e40d00c81c2e07a0003040c045500403c818203014010a4195049400b064085501090740031b000385040c186440a00400d003108002c465043c0310040020058980d80d801016018001c801d40000700245140b460000310327582508044840e40501ea10500d090340d00148480c4413050f00000c440a120400300d880c7c03d0b50500f6480181000743c00b182c07594101c0030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 132499100 1250 132497850 132497863
    0x1110c0106050d0c0303141204030302090405070809060c1308100e011103040c05040f06050d060911060a021f0e0d0302040602190b130314130509160504090203150d0302 74
    0x20020003805900e40300c01c10407004005900300100001904a030800000e8083d141800108402d03503241414082c00e06890112044102da0840010751300282e100c0c1a13140a100742078024005280c801410b140c804009650b070940540803006140c070114040310008104c2c00090301801c80c0c039041e66030541c07000c140000640f207900c0b2450b40950a00c441001400c0c201070950b03108540081c081d030100d074274001c00c2c0401000301c0300b003ea071f03010344507500810b03140c41d412a0304412a200d400c000800e0007460400d0740140c001c4280840c816072040101e0f00a0700e900181490043c00c486d4911070b810745c00310b12001c005082e80e240c1c0e00070b14000c000025140341d4241d0b010f80200c0b42140c0075142d00712800e080c82041c3c0140f09100801c030560000c042001c0501000500500c81e110b401c180c561008072480701c41054010001c038104096045405000c2c80c01d0600900b40c1241605845205254001101811a0155005240b81698044001420700b125044c1c0811000000703071071908103c095040c000e45a00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 132500350 1250 132499100 132499117
    0x602030c0d030513080a12021206040c031e050a180305040911070206190c230c18040b0712140726060d0303060b12011d0403020712020409050111 64
    0x510040070100034001e0141038480c4c3c640060b54003814110b6503070103403a03800040c0c0d48020807640c440c4c01300b055038007880100071241c9040310b030f0b80252401d442040155011003d0500406040454111403540c4102e203c644800c1c0020004ca008c1e901e5080400003000342281c40800351111140301424160400000c1040e6418541d09020301344403100009224400d00700020341110042000240c0c5003d85590074402084074036007203c11a0494035085000c0c040039554400200500a160013502001c025014601c201a08c000c43c06158840d281e0505110041001d41203110390b00010741e904d84a0180c0502c542400c00e401c11640861a0700d410b48504111880b0000c240e4103401c500000c0c9a00c408030040003100c920f03680071542c48205000d10a800340e10110145912008045a601d22090207031103018075180380d840040d8504841008071004070034000021003100e10902004c607502003001010f8400c00124100c81c3c50076807020030000c00c8031000c064065480d116944078021100780c010f04000303 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 132501600 1250 132500350 132500353
    0x5010513050f060c03010b0721120608071d060d061a040b0906150c031b0604030f09080a0201050318030c010b100207060203030f06010201150801090b0f0108060f0c04050a0602030c 79
    0x2203440410b12540d45400f680c0c010300c881414001006a803032020000c1c104644503583d103040e60035101c40454012481c1c4c0301d00e000400d41c0c10307100c01d80326003c521601c8020502500246001c0e450a45103865041d04002c110780f104440d500010075a4544040c0b0540b62a84401d04015000c914500b10882c0d01c0982610ba00c9a41401f030751214a140452403980140380080150400e0030b444400d1009030b03030280307100804901040c01007004c440702104611003200c0c003050241032185042e140040c1950a007405000a0044c90801401500c0d0300241c41c0503941c0e8282800c650f252605560808141d06034a80c0036582d1000150390030300701ea07064100d500c40800030303126020490660340c03040e41c039040c2a004180c0144e00034000208018003007080310f5042103040c0000201c40508003407107501a10260407401460791607280301c804000036004903941c0300000c00b89814031541000003450700c900024080ca0800e0000e04041070000c2c0d1400d084030001c0400034440310741150f4900010b9240c0e000300c500340105 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 132502850 1250 132501600 132501613
    0xd140106030212070809070b0d1d03130308090114030406020c01050622050408070c1d01120b01060309020f060d0e0c0d0203070b030405031215030f071401030f02070501051305 77
    0xc1030003030080c0c07405014060310002e1144d0350800b040781c01c1c036001000d01d04540304860001418106c260002c22031841d4505000c10031109505036207201d42400c00083d1129801081200b1a074040c0c030170194180c2e03602880003542e030820f010040312404055242c0404c17054000080c8020080d659004114212049009000341e42d2070300200031100d1905030300c82510840d0300e108119001400c1c0c0c450382d8414802c00203a0700304141503d801c60b081105801884411b6140401c50084100641906004042006e550b001d02d02950340e400c0c200d288180329610901d91111176040c00c56072040c4008507000c4018185586640c3c01412001c041c1c1000d8503441e0450140240405450a1556065407400d40250080215070314001c41c8442a501c01401583d03540000e200941d100b052002c80280521404401c80c41d24403d9603042500b44400b505410764103038808402000141420714154a85003000d003000990008280060000392050b10740080c115441c083c01c00c691100e00e001691a502e02410490300e8 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 132504100 1250 132502850 132502859
    0xc061801051006091214060c1e0403031e031808030601121112220501050105010e010309050c01030e010609020c031b0303040b0a02030403090503010905060117010204050f0d06110d1401 81
    0xb2031041501400d00065044841440a00e0a155070399400350301c66440c20508690141d81c803420310101f40c07480100340b08006401312078130005032600069a11100b40544c0350615599020b0050080d003100707128040100302242c0d401d580a68840000002c1c251503c803002c1e0840e140110f4a0f0344100c0c0e0303050210700740c132400340e241100381d12900d409c5820711410286055040c040590100c0002400200e101e298020a60400800c400f00703802100e00c10000480c5550401c4000b514010841c0c0407070b410107191010281c0132a00005041480c0d41e0282070008020ba401d1481c24090b1a2a400001800d4000107005c11007071030000040071419104507040b1510b21040c441f86c1d450f1310040c1d6024005151000101e60540c04a03801141c225210341040b404103580c90380801c0c2520304c884419204d6030400b0004000d21101881640020103c038002103140070704280010b0507203010300102c1801140d8a00c1c250040080640c00a00c0445050303504d6511000701c800868007078900f0085004450140000008 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 132505350 1250 132504100 132504121
    0xa02100509070302011b111507060501120b0f09160e0f060402120c0906070606090903080a0621021504080706020705060708040302010e040615020a0b01050a06020c10050c06180105 79
    0x10950313a0507910f07600c0c152125441c2d00d840c07201b40c40c0c090b540340e05c21031010b00340b0b6690401240401c0400d00901501e84c9104c1c24802c0c11240305038090070710320000c00c10101c00954060403855118171803100d600c81c6a1185041546015a035114211014480d008085000516201c48920a11280c4c1c0c2200712503549c0720500090b40100c0d1010040041c00c280458201903c00c0050501445d0142c491420041141c4a44056036910745c001040c46a0303d1001388241548a0341440d8003019800c401e1203114500314030188001d034004030700759520040300389850865460b6610f4a078105c0741c07554003d880f5501e4224107074480390a44580005031141401c001018208601078482c850703004041075042c42c0c41d6800640d84100e0003034030107901590300d440116040b81c141150311420707001a4028041d04450740742a22681c941a0000341c85030901c5c00041140d25030000723881841005c240c60036080c0c01c1004806492502428103004418050002040070f0041c40d403e0642482d480c41c402271200761213a091341e0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 132506600 1250 132505350 132505363
    0x115080a02090c0f0f0a030603030f0314070e041b030b0306100e0114040b0a0801020d11131203092318060a051212030a09020f150901031d030a02100509 67
    0x9400002d1200080d05103071003180604034903e140786a00c0d24010341441c28401543c0542090008244c0e500c1c014414554440001c211010403410308100d8020001540c03031000d40014203c0b000c224100c1a0491103448a410180390301c602500781020180a903031010f005010b080440ca40a07129240002d05c0c03e20044082c54119404c0314032a04803642084c1240302446402c50350700e60441d0701c54042100030380703d00c2c1c0e007800140b5100000503203c400800900060301c1628049010b003420501c01c07191084c241c3c041d01b10840d807041a4440c1411010302d800c1c1d40f03a1f6426401900a9000c0e40d03c00000309480751055000c50320100c81180089420a040ca40300f180113070382d91030b00320781d504000348110b05141101440400542e41110414010a00145041d0740101c440310b9100d601c1d50480b60450070840d10184035030104842c45500d15041c111645058040e000071141010f45900d0610f42200504c00000541b603040b0050b01d544201e2200043d6490131000113044403a0f02d0080024869000810407 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 132507850 1250 132506600 132506603
    0x311030903120912070215040302030607030609060b0909130f120e090c070b070e0102100606020c03010f06030302030f0f04030206120915011505071406070c050f030906030412090b0c0115080a 84
    0x79135007803002c40d400348a43c00d500c01d64031440d400410880840036903000c00c001446a00a80e402117a41c40c20070a401055642d00d43c011400c0c01800c0c48510a59030790f00040701c1c0d0200080d07010701c1c101d140a080c02c8135802035450016225480914840c01d4080d80232801c00a42d210a844000030350b01c07248150303009480303140c8000c0c00e08100200841e0f0854442c002c241d410503014070403034102840628424003110b820782c0c40342c00540d002010514280c1428000c080ca40d41d801c100810a00d4659100a0f44a215030013035030309a80000501134117051041025100595009005070b5100d0364183e12070380448406941040e110b10801070100c614008803090107059840c442c040a411a00038602541c070b40d00001000c5481c49010105004440c00c02c2040383d00c1259255501c049038031440c1022411700900e5422200950003c10000c0b80a4032a4401c072900150311480e00c00145900e110100e8140b0740c5900310040c07024001401e0080880150411508085600001c0c50040d0395030307110a07507803110a0b40 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 132509100 1250 132507850 132507883
    0x207020409211e20030a0f020705060705060f0703020c1204030204050907051309110d03090501091e0b1605011505030c0a1202091f080607030b01020a110402090103110309031209 78
    0x1907003c202e440340e500c4108500100180021071030380c40003075908642003100d13100000380c8026126141d080d410040c0000030f0600340da101d07140c1441a00c0d0103488410043c5400282c00103007011881d40c41c07003a41203d65034180c400940327502e2801030110121a034010f22059225604280c08240c0b048404980c0c074040741d400038445100504410300281c0500661041a203806421000d001c0c05038541184e940303035051099460341081410003002405c044419008615505289814918003e40e2000318405030743c0c1d1070b46100d1b21803024203101020003100c0c3c03900510b2542402c0e51034841c40d0740c2030071076801c0d80d000701c042d5481e0010303107810300451401610840120130800542a40542440102940c002c1c00280098120840080e0310b00c488030002c0d881a84240e00600030420440d07410b2150082ca01c2c8248043d001007546619001e0010340c1c5c441000784220750004800c449030f80290b000d40a403554060200d51685041030303820f1780704e411283d504a0211000c0c0d001861084010480703001d601c10108 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 132510350 1250 132509100 132509147
    0x130b0a0f030c030b0a080a17070f020d170c06010801060503010902031e15040308040302060708010b03160e030106030303060f05010e01170603010207020603040f0210020d0f080604020702040921 85
    0xc0c012000340440300b85107000e150307031005508025151304d0b2908025000280092918040a01e803070b62130180e2202d400a545007044c04000c00003400c0c2ca01c20799050b9011101100001d01703600748280c00742040002c685409200041c400303805000880e40314102e0300b103503008000b016503581c141426241d00c000001e50541001302200141d40c0b0006071002c2d405014800c84000000d00044103844070000c1c2e500b580400c3c0d200c41008201030f410890141d0018ad1450039414030351429142c0545404003600c0415920b00e42810b015907c2d03c40c64819008800080082c05600c1d83ca00700580140301d14021402c00003604140410b05502810b03405c04e04802c182c0d541e0071001014625072544c0500a4000c9500d0f54081182c2c10148e50b502d00a1805540200010303440e4603071034810402c81040d150050419034024210900241da008030210000c0403150400308040da80c1e0a0000b0020b10820000940c0140381c80c640070103001c141030072081094440410340e450312407242c0d0300b9a80ca01d0038440c2c01e0903034290903 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 132511600 1250 132510350 132510377
    0x705060418181205041e05060a110a0506181605010516030203090303070809120f0c01180806010902030417040302030318130e03031b0304150903090801060b130b0a 72
    0x60384800109a044028010700d50880c0d076903100c601c01c108552000107000803801b03000c01c816581c00d401507031042c0407090001ca442d110100d00d40303001d030409103000e01080703441c40400700d40144150b510b600d40c88425a449440c0088038840d448a12104100342c038403030806111040c01801031000240d81058480300d0516800801040420b25029001c9086010520150300152420000703401c0c140e114070040e80d11480c6520501007011580300f41180981c4c04540d021801e0000070035403140c5074900b0300c0d0205880484031150b2059484a6000c002c0a104500c000107181c4642c1c0d000e54000d61044000c0400d11000b40d00040715070080340401782d895001080364a2864846207404002207030040c2c81c420312481100b240b01c0480340e25082040075074000200700103010800310700a041d1300040350b030403a04600b895202d100400c040b001844a40303640d20075640b010f1500503094a4002c04100c0c00078860582c441000220b1500010401c3e250b940b6581c7e0045124981c2500351020603c640e951004040c40c007 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 132512850 1250 132511600 132511649
    0xc0f1d090403140307030902040b04051512070b0301080a020103060e07140a120903031a0312040e0a090206070620160615080a030c0b060f03061801020f0a030e07050604 74
    0x1d0411024081d00340041016003d03554080c40c8141d200e900e0003d03010629006000944060a44441c41145401e040200c07045080c0d07900450303103c05403885040071444051461800e0250303004016500300120000901c840000796109005100fa43c05020541c0d458510080c0e410007a00d010b004221010700c00c000c40ca62850207040700d0b5840e4980360000754009440d000499843c001d0980010361104424481c000f83e030850300308116001e500034031903c807000069418601840c00780410f4841d9140115055045075040703032008540060005949030b16902d0a0401804180003009000040340500241f000e105820341b001c1040b000417451900e1000c0d9154001824150104922072846200100b8483c10421172144070030301c81e40750307503000345a5801d09035207606008010078482c48842c00000c40c00c5c0c5004c10f0b000c1c0c1040d000c02140f00d14000c4c0c401d0751800f80c040d0741700c80858208081941303140260715400c0b460001c4845c8099540f65174a4406004580c0306a0284011a8808001080c080082c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 132514100 1250 132512850 132512869
    0x10501090e070203070204050903070b072a05010603020a0e0f0105010c0f02040f090503040611060901051006080901060b1305010807020c1c0203030c032b0b030703030c0303021306030c0f1d 83
    0x5244113032860101e4950004080301c8081d41c0307a051030351003c20303004200490001080d4202c1134034200300d80800920a502190840c0c0c48100740001030402050500b001000d4100b180a542d0040400040e80e0326124507003140002100d110000b13110400c0000740c194010360000351410b400c21114070341092990207001c05001d51510318840259500301c2007001c2002800900701610700b80c0e0750103101d45405020280303004000b800400d01a4504020301c4010302020010008849890601c15996961020709c1801803180707510185840000141c07031040d1640494504094540c243c99002c0d0588030040c040707070340781c0740b12000b145c001c42e83c80101040000769040c0c84203224401011039240903000c500b51030850304406001c90500d450b50110301080341c85519003880429210070104010301d81403000a03500c40c254030000e4280710081e00318a0906200750100c8410706d403580300c0c1c80c40f0103588000c0200280304612070540040c00c2402072a98152049032406d00031419a103038001011101d030200b000e2042d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 132515350 1250 132514100 132514111
    0x816080106050a03240b09010f0e03030d200d02040611011a04020c03090312070611130e13020303070b060306010f140618120609061b030a050408040f0909021206010501090e 76
    0x21400e0411a041c2c1706034014503000d484140d2500da21010760714005005110b124040030184184d00514503452f440c000b09640000400d428003190b245104460318034001380d8455040030003540095102000501500204121080c40d034031680d0f2806101074070307402c0300d400b404a0107440003800c15942c0e5a02d099005070105d900c0250580c0e2a140c801800030b803420707440d40d102d02603240c00400c00f201404a42c1c425040401060645185001c4500812240c6011640102c8038180c4160000c00d680b030649940440c0420389c0682100d03030390b03a281c1c2401c0c0346014040f1981032084c480c02c4008900324840003004c00c21501e00946101c4400a060304000f11074100c41c1c4444a0601540701620f043d54865400000c00c940d10b10140080d410583d00f41c50a01100420714102e680100c94501c220400c5030007120792044800300b0001e02900c4c8c0c2d01d442c0d0000e00c583c0e84200407001046801140041059100d02031182c42228031031101c01c030301c40c4000c0e1a86824890b60f404107141940400c407012403144400c0d44078 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 132516600 1250 132515350 132515381
    0x90b0102420105040509010905060f1b03041506060306080a11040f0204030c03030e090601080a180b0a0c0206010f0302150a23040501030c0306080d0e0a030506070816080106050a03 79
    0x107424000754035806528000c400040c0c0e10050740100602c3c00d00b0b12856411410820080c4003c07011510f620342e03141d5014100100f81003904c4002400c8202e910341e400d22024080103025034a00301420004440c0204a0301e0501c041e00d401c40003c0c041e400ba00c2003038202c4902001a0103100615154858080d001c0110706800603100c40703a4400080003880180040d52044950312241411400c6c000d08403044820000c0c011040ca5003405040c3c1e030000065980b043d1b00150101d2000a0505020302d5403a245200034072004014040c44011700d4140c0080c8940c9081d40c1c03c9540d20fa1303a41d90304017034440441c40302039042190f43c0211840078200e40018514881e240c02c2490011035410b003a0a000075074100411a1030001160510841da49401620440c107001e10701413040078103101c08691103e003040740090500040d41140001919004000c10046421800390b03001803130300c59000382080000300c600640c2a001c0b0064402482d000b00d02e468181c4000d55141d60030300215200540007000c0341130910308407 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 132517850 1250 132516600 132516673
    0x10801150315030503300c0c0c100203040515161704030f060c030c0e030615030f070806040b090d020304050103050a110a090f0906030503270a140109090b0102 70
    0x2d4005124100551041c1c0045130b41b00408036050800c002025094440100032020440c035a050031881c682d00111780340c4900d6922491b54080300d250000b40e102c410b400542c0304210222142c3c02201400071508180d4904c000030740e000d00c8890b524442c3c048402d18440102ca44000440d10300095080d00068000620346003a032a5129901c0c0c030002d11504450040c1c980484c00e080c140d00d8000c40c01500500d0402c0385503482500c00194450300f00070603900340c0a00f00351320401140d40400400c0d41d1080c442c0c06441d00d658584121a86541d800c640c140c03482d0640001041d210707800081c0d1a040121a03134040c6091501345001180130b084007510012984c0d03101e13411407800b41c141030000e20302d0000b2074407940182490030040c54a8543c165110039400c40c5491410000b0541c0441101c0b01080c4402d80e88042d140c0001050800b1209000d85a41051200c0170100e1218030340c0000078960b02003601c40104e01942d40f004141a10700300d4848a0040c0c00c003d070a51340d0540b0540000b000b0740091004c0291 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 132519100 1250 132517850 132517871
    0x1209050d05010f0b06030402012705060f0304020f010507050703120c0606090509073002040608030705151510050306011e0302091c0302070302010804111509090a09020108011503 78
    0x81180900d0603111655103520b2000856441e04c13404200072002c1e0b401500307501d030940018100405052140402c0412000c581843c40404000000a01001004245c45031305007002c50b00b541d0001c0340c0c103e0007090011190080c9600400c1542c403119030080c01840c006045558026092144034003403028005980082d100007002070040c000646501d000c001550318003e4203051500c1199800203520070141c0c21505000c8a10303a01d462880b0107821a98070806110380b000c90000c12656000741c919000128880081000c00300b185858041c9580e040f40c40354485002c42150202c2403030506501ca1801c0c10b40100f02809000955030040d41410a60030418070b900ca40000910030461400010ba800603240d50300703240000d4015110500108031300c04c0716000780c0e4065a1007085000190600c650100001c00700f005202000c01880005881164140c01082100d041600940f200702e204100041c00504444114400c3e06441501695048060307440d004400c400514061450303010903032500811034 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 132520350 1250 132519100 132519109
    0x1507140304150512060108010609060e01141803120c07030f080c01090308070207061409010c170403051006140109060806030c033a080a2a1d040c0804120905 69
    0x100340d4010784901e50748a55010307440107003104c000d0545042c01600c41c0107020701540000032070140e03049414a00e000350303007440069401101a20b007002e1446000140c05a0401000940c0c0c0f40005090301114103041c10350b001c5d11094002d4429465583c1e110100410210b0405146d070244107000c0c03c41540307080408402c05082d5001c48406030040b40d00c141c10302210030b50421400c801822140340590580c2c982100700c100d0340c0b0540d030510f17041051811507a42481030f1100c40c403403480705c2088016680c0356a4505191200d82c0741c030003481c0d294038109000904001850030b6000130f00c0140d48800100d42030030010341d002c0401400c1981c00d032186008544840d2010450614005604540440b42020450310122612050482100c12001001046000c1d80c1c2003110701d038021040f08804105402c0c5240321014a80c07040080c1d0074441c0102e20040c43c13a03900b0406400d050b0708520141030b039180b65030b0b0510090350380107600c94001403041d43c00200410300c0b40c2a0b80708070004629110710225a03860004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 132521600 1250 132520350 132520379
    0x60b060c0105090705010c030905090612100c031b120507030f020f093f24070e011103040506090301380d150504050c04050702030403111507140304 65
    0x44003903a56900a000c00c5110400924000b0102481c1000700041e140e94003c01c03201e4030740300303850040340c1040104805c0d50300c0580003d46e00194404445191410070302030780190060525182c00f00f031a140b24540b00780a106000d0701501d0454890101000c8030032403075401810001d22000415956003044078200c020b5000070111903c0d007441e1241c50ba01a80100996001004103d18201d000700c50602c1c54015055000380002c840e04441c94115068164244d040880c0340f000000360380d444c0914007009407070701060603020303824607505e08540e001c400300107440c09075201d1103400a952040c0000c000301e1901100500d00300401400224901024507403100b1444220b100c403444208207840794440c50750148a6217288540708070b410b085564030350303150345000002090707030900c1060320ba5002805224080040800c03c49029104000c80c0c80c11000003500c80c1c0090008561414a03800d400319207141601721103101001c11100d25107012007a9481700d00f03508140341e00201600046c840094140d540002c003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 132522850 1250 132521600 132521617
    0x7080d05040f12050a08071b121a01080613020a0b030411130216060b12331005010f09090203040602190c03020d030e0a020901150206010e15010804060b06 68
    0x800d5140d508044002d0068200380d00f010038000c01e0500070101041c0c0004a98540036005a40c15540d810681440341c14101444440050004418400204034102c01c00a06c08103000b0031075100684040c85c400a0b1060081c0324040c074903172110001c0307001040d0b56007800c009248000c100c0c142e20b41d980d88207103c4c0ca41003201c064507005114482c4501c01c3c02d1a10300c1c4071018a049104510700f03542e90b10251840144610080c20f0039550740c0802d281c0b0f440f00e6008004d484401740031a4440380d40c0c0410802c1980702a81e089030507034814242440740e141c1ea41c41c000c0c06020700f4000c00c483c2c641884011140031400c0030b003240c00c0114800000444071840c1c030080d40518041e080c0940d0b9504030a0303003d03143d80c449408590030058183c95160200b580421500c20914003441e000c02c10942151030249040501d08019611000700d0000154400103182184040700c29502502d03243c1c1c1e41d42c50404da10040443d20042c0c15000004207090562203441a50740c00391094500060010a18000c250190803a121 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 132524100 1250 132522850 132522857
    0x150f060c011b230f090604080a0f030311040821120f06030c011b0303050a0e030a050d0506040e0d0c03090b0703020d0e030316150e010c02480307080d 66
    0x24550b01d00c1d07014500103d201c00380e00ea481c40340809038a0030f5069224001e95a05840d8000c562a040c56840d00c08a038001e003420f1084403144140c1c2d042c4005644c161020880100345811110410203800d8811b80301240c090001802941c0d004803411034061324603049031103000008103e1030214103078541d0175074010800c0d10916403003842c00d80203240c07404c1012501d260500100b00c4004040402d0085851081036151801041c26110741c4400c0e405000c205c0c2801c1d06034000811100201d40c2c0c41409016941d015000500c9240c8801085c84101d031001b82060b403441d008199820f50b000d0242441e000071030310a01c1c0c10f00f94940d6a00b6111401d4003c6881100180c10000046460302d600110001030488101c01852074804041c415814003240c040d03005003841900d140501314440d0a40c0603103038401c1048001c0c40b40c000d5a0400940b41c42d02042d450346107448800982140c40c82c082c0c0740140405900b409004009218002081581ca80e4400075605108424000c40d5040e801e014046d442015603c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 132525350 1250 132524100 132524141
    0x2032707080d03020403120f11010606020d03060f0602030306060a230306010f020f060a0c0224010509090105150603060d020a08060a0c0c0c12020102070f0f030605070503150f060c01 80
    0x1041d0030708145200c090482018010301052020070501702c5550420301c03050900030b02d620381407142550403104150219141e540380036800034540d034011820102c4980950741c100041619011078280500480c040c4400592040c00010300c2d40c1040c8009041000e00c034109407810080000000900034010750b20454a540003100303000a0303507000043c0c01507101ca60300161844498109001d5a00c0c00e0080421a145407100040d007402ca0084c080940c80009000214190340300c0010290041807080c0701e228080d0307074003500249006006114a500070f441000300071541c03442c0c01040100755040a4582e035400050b198001005960b41c44910b80102400b2000d0001450130200120031503400c00c07000014000032070225000a66425030190079904222108485040b6600040380b82035516004803000f90f031b20349408110350131180e80101c00c0700e2003106c0c148a550f4850200311140e00050f910b40303100a440040800040c07428203030390038164402428041c10300c68056030107425141100040c001c03015002 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 132526600 1250 132525350 132525359
    0xc05030c030414180403050d1d010c0915090b031e04060f0c09060c0602030c0412050c240d0c12180203152401030b0607141005010b0403020402032707 66
    0x2d43d0400b40010212100d5410b550094585015008000c10007400c001c070004e02d078020780800394131401000c04082002c0f01905000d0f06241d00812910380c40e280400c4901000103071440080d404190020342d15510000300c10300e13013411510241c00180440c0038854002c11045520302c40720502d503100f0ba00800000c61000b20941d254011108540d1241c02003005144c0c00740059600050402c1d40164001d0300107945c1d03507600c001074842e8000d81e005400b2081200d0342200038041c00141c41d8aa8400448400a8480219450000c18540c0036140e1011080a1103510001c402c9030384154402c0f01c041c20984070300b1440300b0011080b10204802d00184250f050104815400c0800039403103e010801140303080b606000c40480382e1903c1e0f23120041c6400203c40142070301d992080d0410f42d10b442002d41440e8852800c0c1c90901c0a0b0100d074001180b0a10411171007010700d280e02e0103181d0481c5c4080038582e15050442d000e1002079400101038103040500742d12035801c20380c025811800580c500710301820465090 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 132527850 1250 132526600 132526619
    0x70302030f06120c090406060801050f0103050d081005040903020106090f0204080601090e15071806120506010c0c05150403020d06050612011523030604080910020304031509030c05030c0304 83
    0x6000940101c0d40c2c1c0301e1440f0032400c00200c40d9000380048840b030515941e0ba2900c180a0202604010515400d0500f4130151506011a49040c2c0e88a9004e8907078001414404844551048031240c0b2041038100c01008241055800018024040e2001041040d100c01c583c0f41a603404207108210194005001c2041010070b01074036000d41840302d0140310a64040c1c9000d03648008400203666070000c89008150780a0080d14421500d42d5221120f07804107584410260050314802c1d001852281050b00240c1c10350b10400c880280075178450701c1120042d0030a410311040c4c0c111048070502d00300040101001507960b44c40c01c0381460348200300204040c50b12100780581d032044408510156130420070b15030f1054805140680c1a03842e40c495440200c12000506921034402030907054040c0100401d10090121040050a2003c01034030002d82a61028504076034034400c52001420b4042000d400c203122021980110013914001e04d051500c0400a0300c0e06415503001c0008061183d10002e42042490301703 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 132529100 1250 132527850 132527881
    0x7061109041118120a050604210806031c02010e120a0216060e040506040902090709440102130b030406050705030103050d0806040e1b13060303020d0c020d080307030203 74
    0x40b1428504181841e4403c04141c0070301040c451040382e400c894510704407420001883c1c02508442107881c5414a420305a44480c6508001e01b90010507414154101c1d0156584078000d20000e0000d10708091216190700304034010001c90b8085548a081801c0401000c01c040c080607894001c58a035074135550080a40b4100201154005656101d0410041e6036004800d40307103044400c0d10041030030307036a45000400414642000a5102c0c9030103040c0010a42d00c600700209448130740900310750300d4074600d1488100690580c591140e8035040c140c1c9108142101340040381015a0f0f40000d0301f40300c1800704914060107150041c0003404000f10420003808524000c0c0303170b0400f1041c1041481d65045858098444925164440a20034498042001c0c0d4030303258031840d07945c480c00045da4030901003045100340303070400c0c809010301c1072004000544800300c0754402c0f54101c0f641174000703000358601c00034182c030020960001030340c2c09581c0d03071540404100c02c14001c0d031103104603540050381ca00c5d101142049010 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 132530350 1250 132529100 132529121
    0x301090503030604140f0103060207020d060f09020306240d020a1d0405060c0a05040e04020316090911030c0a0e0415110421020603010605130b0a05120916050d0204020706110904 78
    0x2a14803040c401641241b4011a0660b600444050b0b43c401c454004100c500c1a00d010007002c151030f05a808000740075661140d25200e100f00c09440498540c00400c4840340301d103044181c0c219504414030011481c040741003112103440900500801ca03a1080300840134a11012030390248010300c1c00b00000c010b001d1000f594030801c402941c80c140780780d41c0da00500a00540c042c10100036022004a410b65a04105103100518140d50040c0050b444005120217002c0d04401119488800d112055a9241c040342a0410a101800d044170042c40c000c0711044a88000e41700303448001c907103400c4c100b8080c001e00400900e2402a540566102d180c1258600c110025202032074140406d0300c1058010394409041b00c0c1100c005240103915900411400c040e0f0701741542c4a0381044000042046509410101800c0250b1444210702c610341d0b2814030301c40d1100341000074440758050180040c40301d80b0381200d103000348500180006040100c50360b981c4003180c40c0744118400d07000c004921440c0c1d1f40b0301801580300c0003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 132531600 1250 132530350 132530381
    0x906020601080316030e15040801060f032001050c0d0207170a0c03080903030d020403060c020114100b070f02030d110d03020c07090b030a0b07030902010e04020a020307060c0302090301090503030604 87
    0x1d624000440b9103d0094440c0c3d00300c00c00703d05400f0301c1414070031452004c46030002030118801c20000041e40c1c0c030540c0700740310340070301c40d405c1c044006a00e2250314143c0e81101e8205e05141d011004c1d00c50780b0b0302002040d480b81414030000380400703011202c080116442c1c1c52034540041402d181000c0400369800624080410b25a0250805d400000d43c01c040440c2241d600ca841c0e107443d016004002401c50107240801c2d6a2544007180c00030038441590095500c5407c00e4008009a03940d0914015150404441e50401070000d05810851600108002c2c00c1460003082c1c0304074400381c80d0b070000b41010a032080060004407540c0c541400941d0030b000032003130840142801c500e4859000b840382d4403020a442140d8a00d135880303c0000c42514144203450905a014000c00058a00200080c006002c1410701343c1c0020580c1d05804200e090074405c4964900050300294205034050303565001a00d50f481019040580a0108610a880900480a40724450400755403a880e00c0030900084a200394801c203100c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 132532850 1250 132531600 132531613
    0x1608040e010e250c21030203010e011505070b04050106030b090d0f030e0c0d0f060603080d060807050f1c02030106080d031a0a0519030c060c0311070602061801090b1501090602 77
    0x18818500b44502e0600c0460a204c1c501401e24108501002c4040e0000341460500d00140307049550f0650085058aa211414030082e980700c500e64042c000d0301d51000f4011030030800034900030407503814115500074403072400815195105c2c2d0325116a0b02d4280e0f40f1801c2c41c0c2c0500c0059403c0d94003d1130446c50b001d45460100b110300541d4200c2c035a11040b41c0380c03143c003c90105e64900107000054214100c0176070055407d0001565a00c0c0100c0349030702444038003038030340d141c04c0d004203240001152000031900300070301c07003403000604004001c0d44140c8604020341410f00c03112490b0041e1000c4c0901d0000307042c544060007a003c04034101806407000704003918501c00783e8405042c0070341e5650038000705440003514598543e518070105c0401c003080d1600003074203650395408000350065002c81c1c83c020031480780d81c072006213124040442d592a0000d01481016030800b0303001900717444403212503100c003501c050004145c9050644960201403020785803112500c440200100c040e5030080d0810004041601c010103c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 132534100 1250 132532850 132532891
    0x901020114190c020f0102070c061d090f070309020312130b03040c06030902011b121205040506010e090325020f1503010501080406091e060e0102040b030109021608040e010e 76
    0x150708441210014003d03030369490340c0307803403407082248012813541d0784021036603205c4904100c08078041c1413041d4400078075190500c1450035841c8619030300070003000d4a08036054031500510018410700429080405a0b15460400542d4080000003035815285440380ea4525145a00c012504440e40004400b8a810030601001072030030a1810704480851034009002e822782d10040301c40c0e90b9111901d444000031696050107101e42456005900b41e110386607a596a00800c049100341c51040fa030141150300020010004140c541300c04951016040056900d4008520000e48404030041094030b140785c00d021444045007480c1f25104d003024001c89801aa06a0f81d545c250360b85d210500550381004041404101002030340c0e088030803c00c3e40626000000503260703080c2c580f040340d80e91301a2190fa003000c64191030141c040c403c071800e644e1400c0324140b95170b08000e41540a50b1141380120000ea00b86030b001000f040000028101400c00116400d4082d490300b80724841098001c0e042e9080490b80d0915102e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 132535350 1250 132534100 132534121
    0xe030310090b04020f070b090102071a07030518060a0e0705060a030501080c010e0307030f06060302090411041a0d080306060f0c030408070905070f180e01150306090b060702011409060d020901020114 87
    0x32941d0340d0269070207d966a6050417640640a41d400041082c1d4090001c02000d2001c9141c0038031076425507074108010b03501c1c40d0110a15080181306412300341c100c00b02203420184c80c2e03046004201e00200440d072000b907603440850aa40c0c84039681c0c0c8006035441005004100c414030540f48003100900e44003140030600d40010384c480840d4400100b01443d030800301010045190004030007150001c00c007004a03c0c00d030800742100d07255282c0041c8258609052028074605142101e40d4003038010708048050200d40c2d44502081c0d00140003a43d11400034070401984040107001090b5201a600246454618064000d450803840d604119051820441000303001035000700601d000010318a40003400c054210140000b0020315005501804900c02c0003150fa451041c5a440300c4403210741d41004195501c83d03c400407162920641c82d032200b0200032040140d8071034281e43c1000040e00200900c0c00341020006607480c6d22012000c1c80c00394020505010070340c4c0a00c10f420a5040780321080005140400450 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 132536600 1250 132535350 132535357
    0x62a171b0319060911030108061806060f0f191a03040302150703020705062a0343121b090306020a0309060203040f020406080d0503070507060e030310090b04020f 71
    0x112181d982d0101003169100b0b09810403c01070009030303070412901c41e042c0b0035569aa402400380010340d11030000460040d0241445c0f014003500360102509881d02c403841040700780e40c01030a41d03552082c17030508201c000b0740d03030baa151702e000300e0181250b000d095140c45182d032115101e003181003038062000d00c00c100c00310740c003c1102ca00d00c0d03c09251420440c0d80d8414191f009000d44080503160307200b8101000030342c03103160740d0030103e120300c80104c0100b40002100d001075600c0101d413541021031400c4081c0c032203640c1c0440c1e100c5a1006450008902d0529090780390303a0100c03180c5d10440000c4101c2d41440103102a0701c2440500030b0040341d56204080506000752000e0143d100081c403640d0300147c6d88413128072a51042a50503400b44d0150b660b41050f043c01100c0c03150512080c1c1c4075034a81000012400c100094040207050b140e00c40c181950345001080e030760794102110a170b40058403021103200c1e00c00d0510003103102d0405418104189410000b0300000c4559644c8402e000c2c2d80304022844110441c3c0d01a03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 132537850 1250 132536600 132536611
    0x105090d051204021f03140901111c140403030b010f09060c020f040e010c030e0c040203010f03110f0d0602071a09030d0207140703030c030201050601020a080304062a171b03 76
    0x758000c1d9180e500c04074080c58141440a03ca01c0ca150205c2c01c10386600d9007001c12074203209400c40c80c00d80c58041c0f1160032a2441104185a010b0401c80d1154030351140100100390384941500003401e96014011801d680c800316003c40010790744004940740c640e0499001c0080c18414a8849441c82c00d10710007401004010502a00c500000703040e141704e0355240c0d000000b000020000078000122020006400b0b0102c801c0c900c04140180c0c4410541800c183c802e4a040b2554200004404d51843d00d415081e441058289600400c40c0fa00030756240d100c4800310044107104400060361003d4a0801d40c03810341c4040340104140000c0010f10078240000000d581a809000400682d180180e10b01502c5035003c03c09100f51034099441c0000074580c10036201c80901e4020f40090100380e46c2c0f44012a100c6201041c0148a000c00b4800314000c540d482e4003800e80500c0103451030031140d00808416190b0300c80d82010170005402c1d540000c00c0f9480601c900c80d0020000030043c126645581804052804010030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 132539100 1250 132537850 132537877
    0x80d08010b0d18050115050a0e2806090203010311040b040524010e0a060c05060a0b060304060e0309090a0b100c020607020402070c12030c060501080607020d050a090509090c01020105090d05 83
    0x214101c42500c02d1052903e968000000c00444200c100083d488020034410306208901d11400010721166403a08144140c14030354040e0060f02d000c0340b5002e0303120744400c1d0302c0c0740d52680c0d8040464110310520043d40a5806403408414502d003500402c4240c501c80702c10346028604020134044031018119030241341004003c1c5084041140381c0040b41c80808004003140d000c90b005200160480c0c018068064035070180f41910340c80e5131040301540035190400082c1390081c50400005011403640d030f020052942100042c1c80c07038120340b90b00103003d00c00c09440d100d013007640d600109861807416a011007042e408509180d0401e800d030740c0000d80c0c00c0c080c0d0280640550f40000b1604100701d03280705100d014040507000c45205000c181002000d201c00c00d42d040b241c14ac900000412140030008285100d40c950394014202248002412140754000d201c85006000c02e20101003101e94462146600c9501c5000003003540c41c20403c0020309440001c1d01003051a04074032416440f0076030260407100240740d41079 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 132540350 1250 132539100 132539111
    0xf0a0218010813080d02041a0705121b100e0d0905010207090506030c060304050a0521071403040506040803130e100308030907050409030305090607090609141302040e01080d08010b0d 80
    0x30389040d5083d0b901e001c020040c60740041d0b4042903410380d0b4050701c1038441400a241411002c8100b02155116041024196a00900c040c903007410b40f110080000310080044c040070101c3c014041464000c0f02c1c21443c5506865903c0507028050410140321040920320b0b001c6811498080080d4617070381107004441c2e240303845000141d55505c081041c0d6100e0403020f801c0340d58926203400d00f1601c1e0782c02c43e881111030340980392942008100980354a0310100e1064891407030f00ca502e0752900501024402c0c400250b0200b444005511340d10709010380010001c08010710382d508910a507240d600903c94101c06403513038141c0240564604045000340949921009442e40c9841d000c0c00341d80362050580c04940d001d4245031490082550503000103010721899070031200c0540380e00000f81c420010b103006010002d0040318003000841511000c3c5526a03001410400d0181400f2081c541a40e115412607111072901030010400306404100001e0050020318150205504150b00c800031807240c50a0070100c0d48d02d61 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 132541600 1250 132540350 132540361
    0x6060f03020c01060302120601060e0301090210031503061503060509030301080c0d0516300302121b100518012306040f2904050c0a030504080d0c0203030f0a02180108 73
    0x951113000615001000000d07101000c9000580d40c00e02405141d000815001b144200c2c0e00741405800c00e0302ea80100040403c008401f4102d005080c003120102c00c28105010000101c2c809114000d0302254042d480c80038207003142032440070354401814200140e4403c000400a400b00490780185c05c0000711a4141c81c140703142012460319001649002c211120f8000000e00511580d819004c004090300034030418112034200c0030f200311030180c0003501580140c0182c1c1c1c0702c0442e035001071a40150580f4291100c8240050b001e01c2c05003194026144071341e4950611001d828040e0042420681d060003c2c02002d41c0c150140480c40400f00359000f020180c1000300c1c0040c1e503107401003d11000403030002c200b5950940911142001c00c90341090f002a51115911000e0a0034058036214800d1143c50071729110210307100b10020300004205907811001071244409801e018058a0380c0b88100c0e600039626410701601d20010300300f01910761400d8510411621107070b002c10121645400301c0900307011400c0da0341d4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 132542850 1250 132541600 132541603
    0x411060c030301060e010906030c0f05031305060906040b160c1b0504180b091908090105040b1c14010e04060c050c0f060a1d070e0604150602010b120106060f03020c 72
    0x400000d0002400003100101c0d940d6402198440d103054240d80300004196541e505034102d030b0000c42c42070002030841380850f0145001e8070086800140c00c440c4001440010344031141841c0050b6240d240a070844810300003800b111400954002c010000242d121500d00d1002900704580001c0003888003800006c07100440d9141c41f0341c00014071000d0010301c0801c1081d070030402040c0c2124011914540f400e0040380090b14002120503030031121010822800c46c1c9030300c07605003941040554504000c020040401d0500041003c2d2050000c40100e400c51050342140080907510b1034881000c48411400041203c05050f50381c09411580204c0d002a1151000c64100c40f10301ca0301281900303e01c5500103101c03011a001407018442c1d1501f110405c5403d00786442c0f00102030041e03100e5640740d4404542403052040ca800c0342c80d00002c000b0800035a64001e40d104100918081d07100d000541d640e509514110700305071040c0196444280700802030a810040301030301c1c0e0310071f60403000100740c0d0100e0103c000c0e000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 132544100 1250 132542850 132542857
    0x5060f100f091a040603050c150405061e070f0c080706050906090f0409120203040f0e07050403120905040513060b040b01081527090d110c100c0606060e040b01080609041106 76
    0x1d0113401400029101c0c20000d03564100d040f0101e02480002e100e90107488852401c5ea015039400410561078440a200c0c00081c2c0c0d821001310b51140741007000080009215803201a503806e10134000d605a01d4503001000f0300b0221168800c0050000411014915580c5d07503085400050040b100451020070240118004140049000304605145140e00d1000c0e0b130000007074800c0b0f07004c000120f00c1ca15215058140c45201c1551348101250041c4801d00016010059120300110285443c0c104a6070b50b8000500f0b9030f070140d0b4944c03543e401d488614403c3c80b040d40945c0e05042010f40d02400306646100008106020041c40c03840d07450840c820100c090340c0d40450703c41440049540510007065240d1481014070015502604140b0490b40400d4645008007100d0030400707100005407202501040a000c1000448543c4008210004501c8000500981b080308003501f090364a0400503c08c04042c8000ca65051412074184181802040705903030b42d180c4007079401580542d2a902c005c8100c4040b500720700 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 132545350 1250 132544100 132544151
    0x10911220c0201020d0b041104030f21231204080a050f030a0614011e0f11010f05040501050711100902030a0807050a0b060904110d05100905060f100f09 67
    0x1c0c1040e940840456054000e08200340c20318004000d04880e80c02000100c540e07000808104003800d105c1080840d60b2a200403000c94011030000304982d14520840340d204200c01210000708180c88950812402d044040189100c1e00001e40b52a182215443c050002c10041c40202204000140ca00000b4400c20030345001705042c0074070588a09094450348086c01060094001176003c03c4083c036800d600c00d001003403541c003140d590360703140d1220508203d803c1c02011305c28100b401000c1503800c208403000d00c80d0760b0ba14085034000103040d080524085d8252400a00701a0411204032215aa0307000089044000c4090144002608040510100b03003801d0900300045d0890002160413001d204012408109241c8100c000c0741680e5109000c106c0e00c1709080c3e03000350900c080d100c4207115604014500201040c0a5011a01619403050344c00c015214403d40440311a080340c4248440c0640082e841074200703502940080e0010300b0101c3e8030349080424400c20500c00e888400124643d420b40140d80000b2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 132546600 1250 132545350 132545419
    0x7080906160516320c0d02010522050a0b0715020a0215041a010f08101103041211032a0a031413030209010e07080a05070801050d06020d0203090109021002010911 71
    0x1489802800c05007104c3c0301210042d806038048a2500380342c85000ea00708590b05031030700b5080011816030b03035100306890b41500b0300c1c00742c000741c01180b0307a62021094001800d001040030399481c60b0f03150052240320707c609000d0b09140107000701c821643d008100d04191810300306001e101d4ad0b903141011049000242001c6800400340c070004194000e003000f542054400450840f200b80d0552000c00040f1600030000c0302421754103001003400201da5405030201ca80d000d02d1328a010689500c1501e0a50b8000840c81440c3d0344119440411401240046d01140f8901e03405065101c4c00380d14013a000c2045911828019a000079000d91168041010b1001664000c1d2400f40c0c3d070b6854519460f030700c400540c3c6030000f040341980003410340f03c600d0040921440b0f4565404180c1d0740381c41305015050102c2c00003201d0454013402000843c880c20f201071882605240004038003c8054010700c03007502c104017003542c11a4100701c1007101180000390800249802542c8901502c0540081d035100031402403070340da1f441c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 132547850 1250 132546600 132546653
    0x2070305281112160f02030615010f020712110a03080c01020304060f0b0f060927040308060108040506010b070305070609030305100506120f0a09050607080906160516 73
    0x2011400c0e0700240c40444691150304410044001c4550744810b10b180982060104000d05190412445902c20000d84201c1440480d04003c0e1300080c20b0110845200401d21004610001e0560380301c081d0003011607890014280150618849040e040c0d10300501030300c0c03000190304005483c1c070ba504000000b190050340498072003400c0300c40c540c040c3d4005e480543c3c0325810300c0c902ea02c0d2034040e48120180345000a1043c03610303208540c1032201a401100700e1540c0501c8030110f10071401070103101c8860b5000e518804142610b41840d01914000b00608003d040013241c2c4200710000c0c00025200b415100c8803403241d0740b90000313460f04846030302c150342009003800d04040b840000c00d601500b0040c0215000c19000b1031082d210000d225040c014074ad58440c050001e01e02080803002e240350180c1d04078580d100301207515007154541f54508841650600b000881701d0b0100000414140143ea4224521000303101645985180040480c0a48542081e8000c10414030108000c03604d81645060030101c03121440 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 132549100 1250 132547850 132547897
    0x5091509011407050306031e070b0408011e0209031009110a09050f01060e1005161211010506040204060e131d0c03150112080d020702030109060f0b0a050f0402070305 73
    0x2070302e00446009550304402c8041a042d03030141c41a00d20a44000d002482c0d410660008065440008240030030346001d018030220304030310303040e00400143c1407290000c06c2000b500c035903a50010054204081d1098410700910b080f60341c000c079819450400e1002c021400740294101003901d40308502e0103aa00490403400050440304039080318ac802c0603882c80d420490785e6140804d8a40c0c00004a095600c100e8a81c240b41e6000e005001525180d04018041c3d0309141d11603890941c6a05510000c07000b0075941d0302c4280001500340506a80840e0680301541007a280200140c045464003110911509440400814500090b809101c82035a040c00d000e0f261410010403035160400201080d02030300074808050265001c010032241210000b503016000c400890702c0d03820160304510029041e40350208031a60150b5024000c040503e8040d44e80010585007003d089001c443e207400c3c60901401004101300b0041e5204000309030428000d40700542d5803101841c0464907440790f0305803449046048569000c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 132550350 1250 132549100 132549103
    0x309120606080d020604050d051608070303140109090f060f020c060109060f09020c07060807021905030904061409071b0c030b1b030f0105011412070309150902060d05091509 76
    0x30448080d00b00392180414600c0007281c98810480700900741d5840400040c05452080340148607480060800125500c2556503441d500d500252060300000e0726a085600c400c45440030840c014003101a08201000d844e50340c4031160320302c6410261070655100c400019242294040b0786008200e0b40a4070354560310b4200c143c2c0202218050003c0019510740b0119968280c0e108803003004080380c0003441c0d01f03032402c0030450b81c0b0840104214118041c01240b8903a02c01d003d140030951134411400b030754882841c2418081242c42c00d9014001d44500000300590903150760105a0b000b201c1450140340a8450200104c80c0c2008110010117800945030000180b018250342c2d54003072610303206a80c2d50719480c149880c0d0180400c1d14444840d12860b40100100d60040202030f1079a50010005030502c4129584080262000c403282d2000c81d896203241c8042140080454010300c86803001005100c1041e00400c203136002d1350104185040e51a00859560003041080b40d640703d013407820b81e00c00d81c0f400c42c114a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 132551600 1250 132550350 132550361
    0x20304080d0e0414091006090b0d021905100f2309040506190303020a0b100305060c0d0f0c0e0f01030204060905150c03030c120609011203032c070807050f060f0703091206 75
    0x1040311a00d80240802c0b204c4007070003440607900d8020502a1400007607000c00075044d004040303110090043300c0c4002465110840c4060b000002600c0c1d203004520134502c080c140406c04411100302d07000300c580780e200100704030f0161072480400780c40c00609666843c001c42d034404894401c0d510103510410340082050390004021031130341d00c1444d15900316101d9982d44030001c0654000204150022030000740340350700c041d01510b50f0b95850741e004122500c0100340203088544030b100c0200003680140e14800c26080c03541c092403007203a080c6011494145421001001d40c0b6181c091148508a00e0304212034001038441511100c03c00e041c02d03030f0382d40e08140c2d80e008403540c4111600210320111100041407858641e1070035049030300107015607420b0300d01503408070014941c0140031890b00b0314400d64503409840e5248008004032501009182d41403d00d10200d1030131110f0381c82036100e11208c03d030a0f40d843d01c41200303542044515601c1c15403500820300d42942c504000b40c000c80c2e8000180c14440303040c0031994100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 132552850 1250 132551600 132551623
    0xd06050a08250b0406140d050703050103030e0916031104050616020901080624011e0e0a080f0d030c12020a1e030219051e0301120c06020304080d0e041409 68
    0x401c1610b906210640c40c145100d0307051108000c0c8020001540600b801500300100c54880903c3c04030150700613000c507001622840c001a59641c0107204140e001141030021240854503c00303507151011100d041201d10907460001c161300c400b0114624150720013542d024060003000541c40352444080d00b40050000780c000d03446041103e00000306100e0104080c0e00a0403c0401c140f032003400f0780034403600c01013080724403410031a200c0b0101d01804807000b000644054140e46603a02e04060404001a80c001d81c1c20210f01e40d00b1100842e1400c07040012000345c1c030701c9a0305010401518007001500c030481540d003400c0200d400040d90300d01e00369214091000c2c0f6560100c4849030540f104a08404074010524203070244d12200c0010f802842c01040a0580701c21f100d07031030042817411032204001542007a0300c60040751521360003100821009101070307005056544002e40c1030074500760107240d035020b2200781c00041c01074446041e210303915030b600540e1700100300419090306070810214055550410001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 132553956 1106 132552850 132552883
    0x5040306140603060a0b03060114030106030b0f041a060105030f0a020408010903081806040c06080901060e0c1206031914150906010e0108030304020d080d06050a08 72
    0x10041c005000d4011180a4205038007450f16101c0c01821155526040c194084107a450029020341142c0508036541c1080d003140c00824010b2400303800c00781c8400e140340104581000e10021050040340300f680c40c00b05035100c03112488c005050030703107459002410030404100900004440540c000d46918001480c042d41c0d81a22030844466440450210701c0d03500400900e040000141c004019010000d800c82d4941540c0b000c00110b041d0241500380304180000c2080c51000f5482600642003802ca01c0b500750070010305d50703c05600310340c80d46c04a0031005000511141800300e810200644100011005d80c80170780d5440d04200c1c00750b100040326125458201ea1540c1804001c1c90080c010200079002a5052260000c0e5061050b040707003040303500800502c80181c90748601584169041004103803103445014514002e008a640400c1d80810501d2020641d28008900040850340900 = true := by decide +kernel

theorem cover : BRFrame.Cov 132374100 132553956 := by
  have h0 := BRFrame.cov_init 132374100
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132374100 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 132374100 ≤ n) (h2 : n < 132553956) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
