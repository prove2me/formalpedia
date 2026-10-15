-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5158
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:56:28.088315+00:00
-- url     : https://prove2.me/submissions/596a5e90-91e2-4ce1-9e30-36ca653ed0a7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 927517985 ≤ n < 927697841 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 927519235 1250 927517985 927518017
    0x1080c0c15091b0d1209120803090105070306060c030507020d0501060b04150f09120c0b0a11071d0103080f04081e0d0206040804120c080102132402030a14 68
    0x180c0c050420403a01c0540320300344140103140f080382c00404500340b02210f07a10000d0611241c04500d69462094203040c4009405200001800150f08190702d04c0700b5980e603000710b0007582e40c0c0c580704400313900312100205404c3c185440c04006008150380040c001110550600380343c0d60390015800080c08022203c04010525030800d08081460075800313000e0422110340c43c0c0004503401c600c440a03261051002c1d240400640c003800108000802c2c08441190755000d840c4038601c040d1035212176070030395001405410228aa11030417064042c4100601d000512140207840007007080603180354041401803102030480500880c0e03500030200c410003190002d10307001088559401b045030701501548100c07807585825006445c1c0c2003c03180d00108040d4032496010034502d00c2c0c1380c10000701000840c0b20300760542c4d076150400404205001f00748010a80d1581c407080c04e030300140c5002c0f0a11060100c0190f01203c42d50715401007503c16400106031410354900782000c905812101544400500070b00c1c0030540b0b02c2203 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 927520485 1250 927519235 927519253
    0x418020907031d030c0316150f02090a092304080d0e0c10031803120603020d110a0501050a0e06160209040b010305010e0102070c030602180a08060702010b09130201080c0c 75
    0x180640c8860300206000c0c3c0199007a80c0300003a1561280115002404550400c121210342d1401203900071044a202d82070b0902050707984010442110340d010100c5c0d00a03540022207402525012a8680041c0400e610a01840b41e841986d1011910400352540010070940046000c01c5980f106a45004203104010041c800031031129668525a1072169405910714504030340340581700303008040f100712514080240a80301c640e401c940303081314410480a11076651102100598030f141440417580d00031000d2a02c500c00310010072400380160b80c021414003008002008c0c1c4070786c2000800d0500401211415100c56240e0800181ca00325400002c0d40205503504000402c90103000c06810b8134020b400811585c0180000b0500302c0c452880091720380c030a050802c000040240c0c0050900d104d40c429502203000b0b142d40071443c4c51482303400001e00303030308542c0400c42c00550921a03a04505e0007103c0000160521400301416540000d2029041100346000500303110701c07141c00c91b11148081000c86000c81 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 927521735 1250 927520485 927520487
    0xd0215160804051e0d02120723030111190e0a0312050c0c150d0908040906151d06040e090a1e05060105090f07081909120f110c0418020907 61
    0x162240c040d80340704d280e60008803103108131000c0f40601e007840e02030820a0002d1240e0204800455618403403180c038480e508010500c1046000b00c006201c640f8161481c002d4050420542500c09541c01c014031007506001700c05149a00300f0707042590241c903090549940d0000d01c08913407005100d03000541807031006c00416540c1a80900181084445541a950390f900c240042108500d511551002c3c1c0b80340c10302041003013064580c89149590320861615103460750301c2d4a15020b07110301b40c1c0583e034001d81864014080581194101c5000d41d001840c24506600c80000518140114085c81e81980c0c81e500010f95a4102001840360490700684100205019450610190703a940c0c50700329001c0c0078402c000112400d00d4400c0300e014241c0c0c92106101e6541e0f110045a1005c0e005008020584e8070190f8031188500d60f01c03e08070142c2c003510b8010642002e20700042c0800b0310581c0d0490800c00300a0182d1500341004c02d403140c030f10500319030224400c0108010401c41d800c528070080e6018000318144000b40d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 927522985 1250 927521735 927521737
    0xb0a1b0c0b0f041e030b0c09030316030c031101020307080a0f0b180108010e0109051c0c0b04060204031a1b131706040b09162601050a1a0f0d02151608 66
    0x403030000c280301198400043c1e030450000650b2000501e601b00d0706012503600e13030421002d45040140941101d0508403542514110701c0c80700c0b0010343c0807a403460903180038564020f055917110b0741c20400a611358107001000500840d40100f08030041c560301d40d900b0400180c0f40d0840c21103640c006002d000c28820706418246441028410101d0b42e41c03914007500c0c84440c06010b6160215040b80c00b410010750b404105811110303000e14050b0401244e02e01d10300002e01000441402240941c4005803a541076141601c000701c3c0d60420007a403281039130108550b07001454038020703c10b04a86d0701e003902d80150b0030601d0038554a42d00403054959050566001140c40015007500c07070740c0104113500042c0c44e2102016101d4025070020813403084101c1080c0501c0044240386402c1e4400c0340780580143c012a0304850031104281d900b100d2182d111a02400e4040f650142c034070b03101604648901842c0a0030000a45900048000038040c410302c0109020b5441c2100c20b490150302d10304440200744c003040c5000b00301 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 927524235 1250 927522985 927522989
    0x1303051c1a0103060f080a02040234030f0801080a32251d0606070b040f020906010807020a030e0d1e050d05130512010b06180a0b0a1b0c0b0f04 63
    0x249031490000300c0f0148505c400c4103c584a0b0050011a1866020f06c00698030083d0b0580088900c5c0b501c002044803800092001c0d00d000c4200b05104d241249001851101c8000c0060308020000c801031105c04004038219540c070b90b02000d146585c0e940900410100340e00c0014825050403603502030b00f40c60401240a1409002440c112400283c00401082c480307402c901913039401800350f6401100d0900d203c42201d40029006054a0a15001c1c1d40c6950612000701c5e821201c0c10b0410f0007103011820503c1001e5040b11090034640d0461424001c020b40e20006c0e1407000d400c112680310a6041a16010032400d410340e04442c0780030071000a00300c50404241d042101b15020301c1282c0c1029402841a4242c41c03002c01001880e008603483c01c0204800107804046094655580c0c00c13040c0101d03030700c0d44020280240320800004800c0c42c01010000854005d0f40f0845a0341c5080140311041c82e0b20040e00f000c00d480340103040c00310040d1401d100c0b0040150f0781240e1640200001d054104581140140c02 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 927525485 1250 927524235 927524237
    0x60807090f1508090708070510111e0c0409020105031501170c03010e010e27150114030705040203060a090c0507060603082722320702061303051c1a01 66
    0xf03403e80790321580704d541d58200d100d018038a8021040030700403850311107952000c000091515101420400c255282030a400310300044802d20030b010580c0c0b010400303000f03140380c405040b10108001c2050b0340003e411840000c124500c00881d5032000e07e103581c010100e41e1001d05401c101c4c5045842c0615a0407100e61080c002e460000810500001d10441d10003202441003407450821225200840450307504400302c0050f00c081401280f468401c9514200001c1c2c1c004e00414200c200401020b0040c5401c082d041e4000d240918010810420940c441e642c0174030840303000240004074410006002c80e118061510011701d12400c1040010512407160301509111b00071b5200c29140034101d180001c03180700f94000840d048202441c078030809001d904080080b600903a030340800c0100d403050000100e0601e0f071030f840076000018220390b00495aa2010940d00c8084c6000030300031410300b170001c000b06e580c079440e00604005001415106420380700d224445a500030640034010b1a08003201d11056030f40300c2201e68 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 927526735 1250 927525485 927525497
    0x206010f0b040308030403031d0c01142107020a08070804080c220b0307050402070b01030c0b030c031b190e150f0f0708070b0c1210030804060807090f15 67
    0x46045480540808112071285141c58030340340c42d42d0781d03030407164000500035001d05075501e501d10f40c0e1285031011215903402440c042c020030940c0e800007610700310184100145050b420702034481ca40c0001c0c4a4032000007403141c0070140d190f885100403840c3c40000d90b401400f15401007030820400000300058015514214181c030300d00000c240034481c0c40318020350090404099540391010401113503000e8018100c000e015a00400c0d150741c04201681e100324021100501904010010302000e812010040c11a4140703031440c5080c030408030340c00c40c0800740c80d000341c10448442003a0301f1a40d8208940040038200040c1e0203806880001410301c03031003412580e01032461008000f0f51104100112201c180c082d420307550900442e050131102075040303490708407034000e010001070000c6240001020b2080911414407580c0f00d85080400310410300c050601058100c400e0010300000780342d90183d805480303140c03402410075034401a04955540300d650100901d20400c06012900a10140c003c02c0324070942d0300d5030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 927527985 1250 927526735 927526739
    0x3807030c05010b0418020904020d08160b0603010b060a1b021f23033715082803120608010c030b010923011403070207030c09050906180321040201020601 67
    0x440190340140c40005d01e5032440001101c018030340318860a81045c00500002d0a0010b40c0e07444100d141d11511003060310026820345841041030860210f54000c80c00c0d4000d0011401c2d00000c01c0c00c174010f03611000c0900101132401d201103d140d4400c884507a8008080c920003190a441c0d1081e1440b20304c0000c40041c000d20358048448038200343c00800544680305131482c40d03032003200c2011030f40c0064103544100401d803540c88402d15130b040010080d500c211980000c1c5c030740701c400c403111031100f0030b51050003c2d070401c1c0c0078038005102c0e001040311440114840c0e07010503180d07803508440c0c014600e6141c0b01e11307500d800408a0a07038415841b030803149125071010005203a0362001580d407034081c0d11950854401c54042840d010b5900a400c054010060410b4102c1c07180540a00070b80350001c40d0101c0042c2d00c6040c0070420303c050252104014289050100320909219500a131a403c0013080422041a5244020555101001200c00140301003c1c488110104c0302102c40710380d03205880680c010f104507000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 927529235 1250 927527985 927527989
    0x1140a39030507031e15080109050102040819030903030806150705010b030c01051815541905060a170c040b07060507030902090115090806013807030c05010b 69
    0x2030f40c0c103500810394400c0e201c170b200401c5034805000b24400546441e01c00388400985400300b400b514480c00c2c401d40c00035031203c0c2404181031416003482c1c8486940c56940504601107a00600c6440030b44e505440c21041d156102c0c80414926800b07803030b000125460004030784042c44010340c41180c3e5400103c0c150b0f003007200c101c401102e0a014140185808010000c1803624030300e030440c0001d1050712100b040303604110941c1142d03e144040b8601c1c00200c001103080940e0a01450401e44000120211900000c01c0460782c42120301407004040764040c40c200746000004e0311340500c039400200001810796541c0d04846000811241d02d205003420f04100448c0410220500841502c003a02da0b081d62141c1032030b8041e200ca41c00b0f031a000e4007030014540e4850780b032009a11020511806131403c94044880b5000001c2d00902c40402ca07403140ca81908070704010300c04051207400501c501380500d960280c40040743c0c80d034011404408070340b51108200c00208001016040400d80014070301400c000c02031004e041c81 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 927530485 1250 927529235 927529241
    0xc02010b0f0904060f181e03051611190614090906061b10060608061009060c080c030d0e070801090b180a0c08030c0f01140a3903050703 60
    0x1030318591001d80d0620662550034240103141e8840e0043d400810490300d1900e880b401c83ea404280b24400b035000c02c514005200c0800c20310705100c6d400b0030410b0702d0341d6001c4d00d0090083c014144c01c01c0b0714005001d40c10090001c0e11174440e004150080c80588902c42ca8601894410b21038070420001c548110101e010349001c21003a1011000c1c00307020302c41c4694682c8200441e581c00050011000300061b4413040740c80208000e2a1810004100700044083c1008000741400310000d040c1e40c80f403070881d038401007040e9204034000101d03030182c2455018240c15140c04040c900400710020440d21000c45c100400c800190020070045014905440c0c4d800d8540c29514282d0300501c0c0050004005078000c03030307a14035008010783c0e0040509026107080545c6962002c081c00302951100c0d03040e600104003540d07840001d00c0942c01000c4c4d504000c102090248406224403c030092601c2d041d203a481d0041c110102400025480e20420480d0a855842503c032440d044042132241c2400028070b000c00141c1c1342c6000348 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 927531735 1250 927530485 927530501
    0xc120b0102031c02030705041e0501171504050a0f050901090b060a0e011511151f080604060e240106030f0612060902040f020708070213021c050a090c06080a0c0201 72
    0x503c40d0f0103450410702c14907010b5440500700200b000000c0100140ba0b04484500f00d1002ca0411500c058603850080010955a402a071204021107590203001c13200804000c6245110b60a03140411959903128a01c8000c1c00f9071100e68141c1800c1608000c40000b06502403110103106400030115600c589040c031850412074020180c0c0550014018022200d080182d6480e6844034038044c140c0c0041c510070942485101800141001200300501220148044601030661780800b540c02c8102c1ca8207010740c0d5130f41c502410152005a580d141030991040034410f0350a166a068140f0340740040000302c4c4107840409120780000030b441c1006590360040c4a024801c21622596103008514505494450050009050132640f0650b681410302405646001a102d900d01401d05a5114001030040c4400340c0b030300c6008030500b6441000118064442ca41010401e8032074101c0000d511f0340c41140c10710007803d803408040c01c01606a00001490341c2e04c40400392140c102400237222811041c0000d07030980f01d41d2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 927532985 1250 927531735 927531757
    0x3040305120613060b090102010f0c050a0e18040f030e0d0309060513260c0d0b0c16051b031902031218090114090714040b07080d0c120b010203 63
    0x802814030400504111682c00160003003040c2c88912504241d00304071215a440706400d170300f0124560407907680a00c03d000882055100602010950708001442d81c414110940280601c01c10240c0b401d03201c031210800c14400c40001403107541441d0401d020f003d44200c0080740001c00d216444026401c3c403c0b152481107a140d102c40162504200c004d4070160046000c0162900c20344400042e86061031402103007000d910540d0301204407400210600300000c800f02c1c85d0140c01d02c4070500300000e00f2a80c0380ba50111000d0110b81e110444261509002003552001400e54803640d90240c090341034081803048ca1180c22030444403c00c0c0c40b009203e105950000c0081d41c503400290041c0074a40c1d49200030100103045803901c0c003110f00c081002030410b690a80114898100311854860720f410030708a040c0e0800800d041c0301c0c60030018840c40101d00e104900940300002008203c03401000411020342d03030620381c0e070042408480b0351558003e208583c114151a4124142681054994008000c0310822145 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 927534235 1250 927532985 927532987
    0x70b04081b0a03030503070203091801061b0c0b0705071503050601091502070302040c03061e05040e06150f04020c150405010b1e0409020d02030f06040c0b0414040902011b051e010203040305 83
    0xa1504c0941d8142c0004010000350702040000e100c40d640c41c540600b08007807510710000140d50418400801c50b91104641800c166200001880403c0745008200120740b8900704c01c40d40d889d0366103449402d02000d54482ea032a410b01c0d500507040c068158001511a01c401c0c0e9894000c00d554203007118100007095024400b41e04102424400341c202508104040005800c01103080760f0b8075105101071400086c403110343d010301000144054940780c0981075822002c0001032006041c11111071a40080c405803c84c8982c40450540b038951b08d598050f1003490018500b521440c984100710000c030301ca81154211040e51910300840030750301c3d01d141c1e40009654480c104400f05d55208042c000249800d240c1660b004100001c1000140c1c3d04114110f04030b0020805440369041c2403030306a0340200e50f908141c0c080181404140980c2c2c3e20401c8007100a00200d402044150032400140c4559105003400e50540455401c0c82c0288400043c074810310740d0f4004841d40b11449a03201c1c403400c03800203031802000104 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 927535485 1250 927534235 927534239
    0x6120b0a0e04060f020910080103061b090e04150204082d10021803240708011428060917030304020d021009080102120f060a0e18010e070b04081b0a 65
    0x3c865010101c5415000801803402d100100000d003090b401d00c03507110000710084018020004103015504014420010b00515079002503009000760302540580100b480c01e01d000581440b60303403440380f403101c0222007003190f0395502c0d581c04a4980d51401c00d400c00c1b2a40e41d844680d40c00c1102d402c40619000c601010740401401400707410042d520515508501001c100d80c0280780340c0d01030000f02054881009000030502680d11010700c051030052110042c0708500c0010000c003100214044444001201c3c1c91403914000301c6c1c112510b03884000c05110941e86078401050507608814000e0580382c0c415243d44466040f840c0560303507480304482c000d4110380c62215003401810300000c0200426034a00b80303080351946540d070311822a085102d80c0381c0e024000b0310600031220f403818080c83e0018400e40d140740810b0b003420b06243e01c1200c0a040d801070803010350305640902000b9801042c640150405841e0140c0e9500742848a0380c001d0300480d4658011702c3e01d036190075204603005c0300c1300c21800360080c207280f4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 927536735 1250 927535485 927535493
    0x1e06061e050d0b06072111070f17030733060b04060e0a0e07180e0702120d0902190e0c2115130f0f0b011e09050a06120b0a0e04 56
    0x400c00c003c00e50000d0092000c500010f031418910155413490720039500d240880c03450000d11808141c5640c101300e4110140500c80c6920720345482040d10790800d40f8100b0032001d0110b4604e1441a00000f0f0040c11050603201c40c0c02c803011b001202d1344001031a07910038007001c3d4101c94080f103a252080c3eaa2102c410007080154601507140100d4103800200302082d030947c1e6082e010b940d403004480180001c2c07001c1e0080080000c400034800082d145070410310303002d441d200201a55900350003090111256000c16840040e103031603004524419805003101410f2400105400d000f43c0350750196000c40c080b41000142c00301118005c2c1c1d400c00d038a82c10040b0000340403460b200940c0a01415040010680b5000002c540c5c841c8011010004010071000401c030707920392095000c85507082c20805445007015003001e5280c3e4410f0030080d010f0208042500b003000c0280098645410680c8074642008044000051207030f0080119501c01040241c107000e010120001c03c40c00b0401806011500c0350346001190100e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 927537985 1250 927536735 927536741
    0x1060f0510052203060609020319201b010c170106030e010f051e010603060f05041d0f030a020601050603040b04060b1201060f050a09060b0405060c011e06061e050d 72
    0x614909050345016403101d6006400d40981c0003c600c20040e003c1c2c20003c00c5520700c19800103010a01c000c5040d4100817802100d510f15401b02c034000e00ba01e070742100301d0402607030500d044403000e075005090f81d0b10f07a4000b943c90402c1001000d075840d54640f41c98824040d0140e604144c0401c0c0c414101c00c440ea0030404190014082c045089200d99a5640503000c1828144100750040014120b40c007498440c2451418204c2c80580000d070401d402c2c10000c110070200400c900701504e42c1107a010903a140e00c5442070043c13610030040d142e0140f00e060040241000d000c00241000c04031a4291980c1d0303030b25a41400344500c0f0a6070000e240d40280000540440d03c640c4c4401001c0100600010f2240c41d080c621030700b0b6400c1d5401c0340f034010b01030a50805c0b141c9060b8101c4001000070341c0342440400d00e0320707205240d94000c3e44540c42c040c03800015608245d071401c1d03000040c05603500400b03602d03444050524400406844c0100380106106e0113844c094820b50710190b80b000c0c1419501c46242602d003130414006 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 927539235 1250 927537985 927538009
    0x10302010f110f06250f020601141c0308040c0905010305030a051b0d020f072909060714030901080108030c07150905060f31030b06060906030709031401060f05 70
    0x450080021008544406110f841d010350041280500820304500604003443c031152050000e106e10003002240300d540200e00705045410442c40101182189804107848404140d00341c203a01d0b0a8000d424205030300080150b00480c0a1001105030b5500d0b1804076003210703420b00014010f40c0c028461200502d224800a00d06c100364816222941c01200154524188010b590040513030800c09004071100b50400002009040748941e13004c9600c0c1080404190b14030321003c80c200303200f002642d00d0700c640710381046802c6a0b500190120160002721010384c0c4035000301702c2c100d001880c81c000000d0500c0c4000255003e000e400c401800340c1030710786440302006d40c20000d003d000f4444021000120340e03840030060f1411000580c201c0ea40c03880061040541501107042052102d14941c0c54020441c00441d202020b495202d00810700503280d40001509034040c4a011f580d02500000401c124190301030000d030122071242d40000d00585041d88082e099601d14094036481c0c00c0314400401051030406c0038001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 927540485 1250 927539235 927539267
    0x6010f030206032d04030f0201060b160812090109060b0a050609090901060b0a110c120307150612083c0f090d0b040b0f01060f05090102010605092706010302010f 71
    0x88405142d08038691425130088414203040ca03201c1004280340c0c10a0304244007001c984020400f003070602e4201602401f03100b105074502c13030006841c407041110000c03c54441109440c000741c800c4c601040078a007c0c00120004562060a0504450141c10410260800e8400060600b07061645c66010320200800050425036070303640b01c4500040a00540c0010113146101c6ea44c0c2c22203035106064058079050140c07441030b0040130400036503a200c1d440841a5490942e0000c0c1d01200303420303d6440e16015201e660800c07000040c100c1c8a1200300071071880240b1000752030180120b191030a0800c100c1440c030401030607103481085001d00c0101541d031080140701e8558415101030510907414045654002c0c4650704a5602c00c201c03003400144111402900e03404041c03941410743e958100000184070380c1c1d101e81100f091240c00308440c0340d5a8000e401c060080c0601901c5040c1c54600210005003581c40c2d03035054812030324a5034900500c11000304685069a406031a01c03150700820f00d008550103044036681c61 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 927541735 1250 927540485 927540511
    0x309020d060c051b03090d1e05031902163c15090905070f030b010507051c0e01050c030f0318010c0903060b060a0801060e030f030d0c1106010f03020603 67
    0x62418429002c115019648207034032000082000b0902078141414514140e20600101d034803640c6280759059640d901c00046c001a20b02400300e4070001d1100c4d80003c16a000111305512652072000c0703000030001c00c65080761191080844450810b02460040c000d500d41d4200c1111300d000000c0700d60810b103042c6144041f20791078140c1c0021500500a070443d409594024000710285503000d03040b01d000d8a0808010083c44c01c1181020f07000b00c01101e802010305803100740ca0b007000e0303000c0c1060f20b001e9134102c010303901014898036000c209030f6199102d801c04151100c50031141075128105032041c80341036000840c503004039500030f48010307000201444003101e680464000113503c20300490000c5a1075454030441b5500798544403081e290300301d0405016130814060041070360350220321141116880d0a01c050b0340c14007000404e0400d82e409405e004a4440002e41100c1d900c980c0d440440f9901d00d566940d000304015034007198031094203100340440c1298540051016140c42c0c030056411031b044032134030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 927542985 1250 927541735 927541759
    0x60f15030209071b0c050102061b03040b07111b0405100302030a06020d020f0d02030123030606010311090307060e150301061205090307060f1409010e030f0711190602010c020606060a030902 83
    0x2035184c0c0c0400700722103218107441c003080696010010f468101c0340c51500c0404400b00080da03400d40740030042029180031040b0700401c000300d01076150802208600d1098450fa001003500840c1d1520030341d81e0090040d403505c2d0000f03c00d645841d16440a40340d009003e06428a01902c0e01c40c0a504002c6000320385641c00c00c06500c0780001440144406d91a0718405078072989424046040884000c089915400083e610751041c2d87d000b04405a2080d001d0800007000400c259840c000383c0607810902e41c062144510201d0840d400800c2d240c0c80002c21686000044041800001e05000c00e2144c18003180b40351010222801b050341040c3e50042c2c0100440c0d0034200e0540310807040d240e0740e42c400007440c0c0d0b544042c4d0000406924085500000c0000280007680c078451030b442c0e0320711800320355001502d0049010300820260501c00c1d01c940d40b00074281c150041105034803034541011881780001545c81c0c00ea2172802a4008149280b00b40d0300100501d0130000e2242003a070160000d050102d92141c104224 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 927544235 1250 927542985 927543017
    0x14071805041407270621051e010926040e1906090b03010b030d020c06090a0b0406030c020d0201360c080106140114030a1508060a0504060f1503020907 66
    0x81c0d0b500820b420055130f150b82507824126045511041d044800190074039805120350707030144d00d0203d01c03c0305000d0800404151400c0990904070466200c0203d28400c100301e07c003052054200b04000d5002b40a02d084400d2280d0801106128070581c0b40c002081c180400c2001c000c01d0341c00c0a502041d5000050381e9850250402e07411581d050f046240400d96031660420642000d1094011482c8203a00038844064a00c07800b0796103902c400302c4030b44141c1000503220495100d05202d480180840c02100361202e0321440d020b000780ca2009003000c018840c0c82c1015040d82c4c414050040744608104140d4100d030001e0b403071102d42d076030308a6500b00c14040d6440620001400001c40c3d1009090750400043c01d5414100015511501d40e041d2030b0400000d00070040106042e40c044941040242d04002407401d4109031311080c42c0c082e0b9220040303602401c42042929002600b00c10f2113030b8401c5200304050411154880100d48194410080501c500d050920060400f884256000505400c1500d14500c0c0850303 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 927545485 1250 927544235 927544243
    0x90f0302240c07060f0507151a030f030c1501030c121a0405010b0f0604060503010e1015020709060b0f0d0902040f230a060b1c140f04140718050414 65
    0x203480b541a800b000d010800b466101c0040d107207082c0680380071440c21449481341076200c000103468208082e070b183c4a112811103c00c14981d1030302d03000307429211105c203011400742e180d80081c0700103021030041076400c0054a40f83e5109038103032580004c0303443c5010f050005a80d5150004901120540c001e41019080908103d40151182d407050001281020700784040c400c2040514a0540c05403405000c2032211a0300b0105a9041d80d4011211003071030740d1203100036800310300c4544c80303a4510700d04600782ca152a03a001c6004020f030b52140c6400e1040c91b036640200c0b69644a140e01c010304104007030204030410603040d0419041c01d8002080450035070548240308040760501d4041f1011008015001225080c5120351268801070b0b50108000c000e140c40e0740c100c072610440d0b281a01c4443c0040c4510f000c450290301092070341c81c0329840000305150a249032000d9030f0054030255507140f04222400c6010b6000110002920b9184240303003540900250800083c01e0050011503a08000d101103181801d000c00c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 927546735 1250 927545485 927545497
    0x3110301080c030d080c070215040b0f0310080c0d03051e0d09152304030c0813180902130911150a0f0804050a030507060e0f1c090f030224 61
    0x12000c0c00400c0001000c161400c84c042118030306000001080003a0010b000c0c0644e0240341d01607a41d00342d00c00300c0c15122802482603400102c015400415036100c41d51a0101441c8140c200b000700b103036416100c605155440014140140d03001811a01e8000082c4c85030005e01041400c0f0050225081c5c102c2c0040b06040c2c01c0050003003001980c6000220034002410711300a1892441a010443d8520780103011800c2183d1a07522129101e002002c102050b1241c0c841007070554000301415203074890454940c2a0030036920a00d11121054400d80000c012203100d007922040d802400c10100d01c00c1d50a035030b0b01900c1028030580d001e000c150680c410a88450209804900940a9450361105514006001928480944010070031248104070001d90300003035000d1402e8041c209261102594500300c0d02802000030030058a004604118a08110000d4221940c19611030400c000103c20700c0212402d80c214403840c40c0c0c80740c821600700090b082c0313950700d4142441462030500781541101c1080a10713905c0b603 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 927547985 1250 927546735 927546749
    0x30b01031b08070e090907060e01050d050a150b0a0e041107060e0a230c010806121f0516050414040605150d2d0c020f0f06040b01060309020307120303110301 69
    0x800100001c0c0b039402020b410358990116440b445d00e00700752801c01d0f44d40e22a40688018051907035241c4125038011400d030750320040c105005100b02d02d030086e40440071b000d1400c052492018008404126090880c0079518000c003d681c65014104c0140d0421004c1c0c62006440030a0407410003194002c2415801103010441913100204001d010501c1c1c440b501d000705a0a422400c00000d03103e098195001c02c090784001000d00c0c1c040030a0300c82800061107803110500452440c41415021940b010074a1044144000002c000700812b95072008906604881c02482c0780000c0c1c810007050000c00c03032040710988505400380c070000d10141c030f4034040781d81d031650017004032040c1c0300c081145140030281d40596002c1300203001068200c0071074400800007a01801038051406505c44c9051650503100b040761020640030703082196107040741c0c05402616141d05650a13102d100d10b810021034501e0082c0100302c1c40b15070290040c5641d900d444075859001d1215207044080540302c0c840024040101c4016602902007 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 927549235 1250 927547985 927547997
    0x213050408131e0b041a1e0c0618030a091e03080a1e050403150e151e01080c01080106080408041203031a010e062704052d01080d030b01031b 62
    0x1100043e4000c0b11070303550215080050070403092000002d0668650a007550140c001c130348400305010706811040c10300e2220804400e000c0342c140c07030303260b4000b0360700f8050340c40d00400d80824001e85848584030720554412a01251603a601000b201c0d2100c20300145002c03000c3c054505998980e1303940005540020170010024080e41030a4200312a0000124074440403410701c149094034640c0c03591020f01020301801c250b07940d21032000180713030018803800d046224521040324182c0b400c100e4901c840c50001d040f60600110101c00400c80d4030f00001c4c1d989803000140c6035405640e10b000030450300b07000010400c0711450828440040c0b1003074031100d080311403031007a10081b0b00c03003100c0070700603005000e1076043d41d04000d51111032050941380c5600700c480c580500b6030701070700c9151681a0280f814a4007016075412030314000c10001d029020260071207003039924065080c1141104e03a00c3c20300500080c001e0341121f4000442070710225000760b00041c0440d4060502240922051a003481c075480c14804903000300f80 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 927550485 1250 927549235 927549269
    0x260a050105161107060809030c010504061a06090607290103030e01140306150d0e0316020a1a09060901090e071e021204151817060a09021305040813 65
    0x10001030321110b07660501c2d003031001c0000c22450301e64400443c4900d030144541140490317000307401801210b601401e0303800280710311f00301860490001d02002c0d040400d41100848250050302c0c04404507400490014003d500780703512512240071860b50004903102c15184040c802c50303192445442613000314042e881c0e045125080500150401c040c402c0d190002010410800001340d50305003002101c0c03000c0d8a03056031600c0014151200400c1c2c842c11564152201181d81c0c44802c0c0c42d044080c5006200b5901e1200c0f0550b217400c40c0c120a4804200e2841d1643c3c02d20904032542072075000345c02c0c481c0c0b0524080174425915000c0800048041d078070080080d2022500c2d034902e10a040d4400342042042c40180040100545e03000350364011409503e198690089034890810301c1007023050706001d00680803803442561a801800313012104c0d0074100c054054440000c1c032112041c41202ca000e40c010780131100d600d5220700700301d00500009004403100407003440582c450035541091040680840b007000e00c01d0103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 927551735 1250 927550485 927550501
    0x302091e010b0903060703020705152e140a0513050603010f05090d170601090b0c0106051207090b030105010b030408091201290603040206071b120b0718080601260a050105 75
    0x1170f00410300e8050600403c01440042d0300042c1010042e428000301003099210300307200c082d220107040305000c5a403c0000040d0009200ca180100841e20001d00c07907a102201d4400b4400c440e03070140320f120350000120245400e031300e1071038018030b901101c000c0c0001078659906400c070040700c8003541e00b00b1640d4000004408984c3c0c01600d11b9001d01c1f0a00c0343c2600510b44000001c15041c42c40c01220300440c03001c60114a003807025000000039181c02090380720900103a4211655407491481401140b03420101c64801c01d00b01885001c1c10380707140061079031a56076252101d0f902984403070032190f0080581041b900001e2828440e00c0198401d048100019907131740c1c010ba09011030705101d020305c6814200240801039983c042106c5660398050900036030044a40402e418800c40755000200c002072401c030103410807221401380d91080758240c840c420801281c036814614084180144503060f0b1200c1c005100c52544903440f4803420410947d502e000c4102c45444030b060450401049645a4650050101003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 927552985 1250 927551735 927551743
    0x703020603100e060307050f1912080a1706090402011b02090c041806120210020f0312040b01090207020a0303030b030a17040305010b030d08151f1805030f070302091e010b0903 77
    0x4424220014191b40b428200000d003407040740c0310600d200700f00c642c120818190841d50100014941400d95541030284d9003010101d9031300c0015600005280080314000c5a0b80e0f5801c00d501510002c0d0600405541d030741d006452a034980c0000603050000001881e00580d21500c8641c400c417007012400e5240d61034445400200f407203038540d41c03041c2c1d030802c0401d01200c0b01800203100411b40444240c0619451800264149006069641620300001030309440b20303669503171018007547c850005030f401030380d0740d00f00481240034454000354003195000302040403030701c07030740021400010080c1668113440381607881040c448005c082d0322010b000301040800c14030001b882035180d040000d0700076000d40341d90140f00030f200c00b1004000d001c0c000942030a00c0d41d551240d9188121041c1c244211424500003202d014200d91b80b850b040300c4028501290104e114140400c03c0442c0301c00070801040319030304650030030a030380c00c00404000c2101ca14500042d9025000d14a0900034580c001502c1d607a05000c000381810 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 927554235 1250 927552985 927552991
    0x91a01032d0b0613030503070302100c0e0d031806031a0d030903080304081209030d05161d0f030a080705060604060530010509013e07050703020603100e 67
    0x1010080d921400510619015000c404400700006007452520000751003800780d0310180c1d08203803a040e404002c020300013005103c510700035021030b1540c0c0c400344071160aa40e410b403401c8001804e080d40310045030400c2c3d01040c544900c80d041184070040c90401d0822980d0040e444640001d80b144001403481c8103403030380f0341075164040d03402c0f028482041e00c024003403440c02c1c03000030109040000010140701c0201c007170306d030720090400321003400381400c60700c0d25926000784071008071091412022414015420740d80505884440e01c0301000d0b4500141e030101c2c10881110007035000040381100d06c2c01642c040c850000300c14899034106480320b196081882c0390040060039280140e1600409101c01c0c0d4030045d01145c804228000b02450600724050039441c10b800b850040c440398203000904c00200d40640101c8101c91100d1206600e05804a4281480b0480c510001a511180b4803000007140c40190082500300e004804407402c180da41e9000c542150300c2201c0d000c400506003842403018400c20724019030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 927555485 1250 927554235 927554261
    0x20160303110f0309060a05040509010b0c010e07180f0e0a030315140109030b04030210050a050603150606090d1e05150726060a03150501061806020c010e0604091a0103 73
    0x804410032185079580c0c0704040e54184941030211b800020144140308440240001600c616850350303441002001a4000128070b0005500f002210000300c00c00040b920200c51010048585c84000784c940c080041c810458007021450311024000240b107810400c8040c00b5202c1c1e5070001c0e0b40d2401540d9880154900e070020314010ba2000260b4134140c0e40144903200b5640c01116500e502c1d11a450244d140c0000b03400e40300b1b030310390402c030030802c00151342e9120520468054003038491030f00003100c0c10f802001d81201c40c258040c60074810301c0d002c2e0030001c185c0218544140480090408544504446000a030508550950103c54040080542c07061950b4000368642031804546c2d0f46d00328114140c8950901c019000314400001446541e201ca180100840d000300b00460b0030205003c048020780024040c080108030300540005007000454986000c8910aa000d0085010000c0044a08010400115a0001c414880030507440003c1c0304880d8000e05045a84103080c000d003001405450380d94103d05 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 927556735 1250 927555485 927555493
    0x3050f0f0706050d2307021609061809050c061201050a06080c220b0a02010905210a030c0c151d1b090c0f0418050114102016030311 58
    0x10b881d0003a007035460710880e1102c0411204d142502c214410742c80c49031584200400030040c45502c43d004038040c1030104440e00b6000445031111003040582e0b80038400c61005501800f5103412004482d480400720b0f62242d4240c980f03521074a400905c850300603107101280321100c10010006850000304850040c8003501302600540b40c00c20385411a402902c607540c00b0450b015255480390402c15000d40013400320341e080d85031680715180d4024000c142800d400c642920440c4d00e0b0340c1c14001000c0c20240c1144c0c00351803042c03400e08140c2e011000342c415000e08409011102240d100003800303404124a016a516400103a0702241160812402d00001100c010f10303045413142011414410010718511201a103021a9a031200041c01e00148104225130507405004a00400c2d1215042c00e8481c664000c881c0901560340c843c8640d1580e00d881c114215401005e10f0850b010f024090030b4500c5104113810f48007200c618414080604200b40090024822481154103004042d0080c100c008180c202c00010 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 927557985 1250 927556735 927556739
    0xc03060f01171c0528020109050c062d120a0e100b01020d0c0813092a05031302041b0e01020d08040b01030b06150a0503040c143703050f0f07 62
    0x701e1036a40d4000103960411030001105c03120141401d00c03e1961045405802c0801c412100d40203008002600e42203800b802030880384200782c80c14200f0f441c14900362103801d40020070040308008070390888078804403040c002071200004c411212035043c2d1050443c10008902d00400221081c140f105003d906484186068408079450b41d000920552081c2c1c1403c142c9a41b406900305101c480c095030850266000c141080810021910340100c0681c2c1e5007050492180c0e407184452211000224002d070300022000d0000403484a005801c80e94601c0c009071001070184031003402c00b2000c0d0b203204112008503000ca5410056035904106003c141902440d00fa580ca0800c0d07a201c080c05101823002401038010100843d040d40e6802c12103104880c41418069540c410180d00901103401c2164140c660240c03111000600c07444600c0c001f564200014031544c80c0c11900e14030070340d206140010341310722112103280c00640c100308c20040201441c01840100910751405545925003000461260303050b400039402 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 927559235 1250 927557985 927558013
    0x611031306020d091b150521190903080f06010c0807020d030212070b04051c02060f070201110f041a040e0a0f0207120c032304170c03060f0117 63
    0x120340c04003a8400400340c1e0790140c100d041c0000c0c2c440f40300050070808481d00803000d1480e04c9140e8070115854014121030038100a001543e4502a420700410840c0180c4107501415080552440d4408940003007540100c1410300c6140895a40303400c120b01041c11281448011696124000d80c800c00c00d1078007280101c02c5541d40195400350500080c050004030400314101802403120100c2240c03d9051680c507140542010b00c1c0d0088103440c26112030080e98014210440e801040c003401c206290018040d64540d0421100821402031055045540c2c4440c00d01400c004100280728800306114441d4480342440c0c2003070402ca15420284036404401c00042101d00e001d02c840962210410000148604100361200080e01c65450300914507200038900b6981c05400900c031001049c00790791405419032034500041003094015034600001a402d110402204407040110720718008040165060f00c544040400d24102003900c80075201c00d07a050050204036201c01d65040c8107400c000060892481c0000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 927560485 1250 927559235 927559261
    0xc051203160c2d050312250501020307021e010b1c08070204060b190305042001090312050c160b07030e040e0624040509030a0503071209030c061103 65
    0x391038040d0700252020203092241c0408044001c1959076800704840400c40122816030182614500024800c180041010b08000600b464840c401444151500c0d50b500d4503480c4030291441d62150454203007a010001820a001440c01512242c000b000d060701194400d000a000b8050f8404480c1e00d00b0408007c5d60b0f40300e40b507503c0200070940c45140c0d89107031410500060b20a4940280d08903050035400501070341e000c0024007072011002c00325544031b540c01c034049042da6029200074148070714801d4136806400d800d805082400c141410400035469503642c1300130002040d94506001301d0703000300300a6000081403080d0b04049007100e0095103018186586155a4044d45101504000450030307000d0240d2215400922a02035040448a03075140180310224082405540001580c21703000881c000342c1058001d0038060440f01c00618244007114908540f0390700010702d44000c2180702c01980710740110600c10b40c200b05000c0d03540c18103000040e06044d015180542c029442c81082003080281c0203104072 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 927561735 1250 927560485 927560497
    0x2003090c12152203050901120b09151305010f031106040f0b090604030b0406050709050406270219110d0509010c020409050f2b020601030302030a2307030203070c051203 74
    0x46424002c030f403654007580c4404141e400c2c0100444007006059414150010090078010109070b960f5007030880b8400301e46094601080c01503400c5a42d40020800489070324000603070b880405081c1e07020404800c0c5058040d5842070b0b02c6241030032110107040c0140522445402c50141046d94058a0a481c000d00f80302560403030301c035111107180c000c158444140d40e1527080b078004503044034484d040c81c2410b0515600030030b03050301c81c070000c100fa01800044d9070030b00d80a00d0089809403100d051625204940b007008104122070340d03e05581c0d013041100200d034490100358000000c990340d030107210106841c01d14036100e20305509006005080c4260920390b0f900011843e1001d03415030b00814010058038000d40b80001d0320880a2540c042c50070440c8500c01609000d100031400c218019407600c06540060b41c503260207000180060300700704a200c85c6240200c846084905805030001034050000b4081041a0803400045006030000603100e028001c8808804d80034100417104002030091603010150340b4401c80d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 927562985 1250 927561735 927561763
    0x60801181b030206270f0a0e0402180907150c1e0212100b1f0e0105030903040f170c09061c1103061e0109020a0903080d2003090c12 58
    0x8500c001052407816030540116070203082ca940f10310300c6030300302010203031969128800c00f12003000e00384003864021031041c41010050a051012401c24200a26070a40140266040b8803080200122000301881c1c1a104010b1200508400341c1010000324136500c0744644d1404010b50030180380042684c2114240f241704060052040c41419403000c5a42c10625910b12200b50080c040f401c1c0005030103400598541e002140c81c1200c0742d0070102a20120310b071030050813001034180f41021b02070394001c10044d030f00501d004044a003050b584e000c0c0d81c10759891b103400c2048400e40348100c1c103207072040c100008041e81c0c80031240e1400502d440d4010418040f0241c0b204030421a03208075401c11b03c1000204402070f0311014064650342e18084404030700a5400aa5031101000c0709000081c40341454030980d12110a00d5480c0c085140c519100c40d01c89070044482d002c1031a81d500d10b1781990103481e0001c0b24411030801d0200340c40b80f070100c145904000302c48200038012a1a000034440321103001c15913841c1c107502 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 927564235 1250 927562985 927563003
    0xe040503190c0204061e170c040c0909060b0405130e0d050f070203160e0702121e0c0102070c050f061e07030e100504090506010c05030a120f1d0106080118 68
    0x1d1104100d80d403006401d03001e5006494a0301c0440c90000c1100e1002c000d40303015088540d199541d0301d240e41c090246286802441d002107240010616081c1c102e00c0301520249409101241c407010103004507882a0300000c41e0420004040125040c03001841c07200c1502d80301c0c10000b94400c8144142c8600d600c0710410304001c00003d0543c0c000c55840b0681c0c801e940c000c0c04881420f6030300b014109007030007030303001320039024448400040034144001a00c1d0740e01c60909002c10b0516240740244500044c2940e562506942d040c0904802d1580910140084900545030b18418902e4001030152260001d020280150b030100f00e40000380200310304071900b0b61400c0c22070603a252014102154041c11141c06d4a910040702440d124030303d584070001c4c10a82c0d00144041000791a008012342d4010070229000b466070b0020320810886601400700c04a4002aa040100d400c031001644201120342c0d1108a2101400c64064031030b40b60424070500024111a0008101102c400d500480841803400c0d0000c000c040 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 927565485 1250 927564235 927564277
    0xb0d0204050a110c06010503012f0c030415030911010201060510121d0d0809071202130e0f07061707050912031e030604140103081c090507090c08010e040503 69
    0x1030710fa02c0a803002d1001c0341429140c0d004c010945468001c20310030103100f90300300616506040541d50000241c03000220720b030844640380f640e10300c0c1550014002c00340d260205000024101a0251020380812016600010940c1d02c0c2d01e05110031100e05d2071650704680c03404a05205580310844004403600c203a042110051052191a002400d1641400768440e220581640071b03594000030040495000c50702c40e150741c3e0f5a4910699510152817058404080211404d5000750601c000220042c1812400200e160640300580324038000c0311410b030300410381c040c00d8100001341d402030b03c1c00007403041070301920024200340800074424041c0a0344e00f4800c201c81014200c00c10400c00890f8000c0da5590b40790440130100d0601c0030301d1074008490351030085042c0100c40a90446641089050301e502c46401410b08100b100e404015445007881c071055182d40b03804071800700300f080003032100910342444003141c128102440203000e224103901441c0c601c81400c0501001030303008000d942107a103005a010000f09 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 927566735 1250 927565485 927565501
    0x70306212303070b09060c030606090d02031c03061403101d06010f0f141f0212030a05040317100b0a1202070b01050a050d020904020906150a03020406120b0d020405 72
    0x141d40720700554a00200c4503484540380040064190700d80903240364940395450041c62030301c0d060102c9404030070070010000030b030031403411001034424140017170102d2144030f50306d0380403074a00346a660075030411103003000b01100510383c14005e40c4090506e0b407607060502e20100d000300341d40f02d480d81b81019003540c0b82c003400d84402080e4215203c2640c01c06007110740650b543c0c0c9507645240c4681c0038100220951440200f428650b0440740480b01030064030498041c45402141c034021070411240a04500a1000e410024801d0b440a5070085800703010016190a26160113892050440072244186403010108004e5407060b07132910342113400803050540c0d109400141128440c0110f800e07640920310101c0d100081c003418031401c0b0305882c000d940311400175481d1400c00002030301111000b94070841d150000380050529080590300800050154003c00701e60b10007514283d0060304450740001c0d8042420003149509c0800305501010300c178410000b180c1405c000c03030566034000340d0184c011030322500411205 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 927567985 1250 927566735 927566753
    0xf1507110a2907081b12130204061203050c060f041505070909020a030b03151b0c011404030804030e090115030209030c1e1908190302010b0402030a0504030807030621 73
    0x80310703508511400b42d1602d101c001d4485041a01c40003807664140024110220f82c90040744c64002540f10200d038103503070f6101408004e10051004a8006443e0f42d00002c2481400c5c103c000f034684203488050322010000c1480d407a00328024588400b80c0540024080031507544003803013a61820741d0b5000b05660fa0346803030070b07202d40c102c075440b0702006071001840c810301540c9a4840c000d0882c0803410756101503903004100344800801e071011441c08184a0544512400a20040980070b401d4800031600310001050402d404100b20340aa000c81e150100b04001c140c3e00c10600500b801c0115220102c0b07506200303020b59a0b0b418810380b031042c03680c0015006084c0d82c00308144010100010401c40348034541180d590200100100355901a02099605c1c80e852072112204000f5115010024030820901014040c8907202c0c0100c2070341955030f1000c1c010841d03180c3d80001c40c40368040c3d0300c020490f820b082c900100000c07001003110080600d00041400014008403041c2100c01c096254214804040e0600d0014 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 927569235 1250 927567985 927568043
    0x1506240706140106080415050613020c010902030a0305040510140a0e030c0d2001030e0c0411070f0f020906010c0302060105102007050109080f0601060f0e030f1507110a 74
    0x2d001c02250000072004e611000080c450780c880d840400c03c0d020179500c02020340d841550b00581c8000403102244000300306a01514460311450000b082c12003451300400c4c18101403130000d500041d80050180094208502c01d0300080341c651601c09070000003452850150702645034203804105408442408556042003c182119402028054003804a00c1c00600101804d00082ca100c03107440e042c8003a1b5801380c4903044501a210024000f103d401ca010003000384407055004050400500001001c119184c50480701c0a01c26050101907100d0350042100c40200140b40c02d041000c1236465400103540460030070304441d02550f0801480b250b8210030340700d01d10804269440d00d600c4098581003c480051b9040031142e080e21041001ca445100e00d90300d850910940305170799031000c8010046e4a129079101c0c25011843d03c0c2100d12101c0b40300000f810000700c2030316804154001000c0e074007082d01d507080b90340d0488440d04040803203c020b140d145071504104100274213106198405044010011382801071 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 927570485 1250 927569235 927569261
    0x12090918030e0105040b2d0c011d070302010801050d140d1101110304022103040515070b06061317030912010b0f01030b0a03060b150a1e02070612020d0f05091506240706 74
    0x140b50701428450f00c1c000c4c91004060502c010070138ac0c510050400120b95030003a01e0301a510510306d0713800e00c014812501c5080c0b2003185c490424214617140034605009035402c200c0c1a80e1003c842a4003c0c0c40c4c1800e40700c8400c10810014020014400140c4d1040114030391000c03c0303160120800c001c0040e02d41180141c2d80b003190412840790011000d00581c60080070400c0c1308175110b04d9991948028840540140910514518480c100074401903d00c1010400d00c007100e042100d280c1000003021a5091191400c040a142c0d10307002080c440e0324100100c07040c180000c0c80c081080c1032645001405e030403c50b102c0600203076907600c00b4401e0f42e20340010b0195552811507880e6514160842c00421a52070308038191030301e048003030249800c248040b911400302c5110380e075010740c00103c030100f0f800294072518001c1201c5694501500c1c620009008140c4106070000c040c00c03080803d8901c040d401c28004102e5841001914103200107001a2001c408190844d034251755210b00c0503182000c0200b52a1404039 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 927571735 1250 927570485 927570487
    0x1c05010f1503200c01060b0c0a02060309010612060606110a031407050a0c24171b090a090507092408180604050a030311090d12090918030e0105040b2d 66
    0x42503c0705005290b0740580d50300030051159030b01142c7c26113010340c1304144001d40055034031a0151030807030061174120307034903600010740725a8400106042c0d020540b001c440c220380742d01d410061180c10034200c8414112500103081c1c64225554004e1000c02c80e242d001544903800b0901e2020322800300301200b0040c1d4010350010076079031a0500a000020143c0ca5480350581006142e55198410f8080d20034242148036810403a8454800d1924111005c441c2c0941c018402c0c4801c17045641d0301c0800c8401048a164006550b05018070001c220504682095500740303a506a19038031414401d030342850200b05480c000c0d045440d035842c3c14140d2600c038100c0c04198170540d8140014800007062050200d84240c030100201c003c8404000c0c0ca44c040d1782c01d055400058959860007040c02c20110341d9401c91107240c400a40303a1107003480c1c400c50300c01a86040b41c51801c80c8034402019000b10700800c80b00e10900344a414030340340207540509c500c18407003010a461000541e030584004076644020401682e0000303a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 927572985 1250 927571735 927571781
    0x5031806090a02030c0d0f150e0303190b0a03031713020a15091d0708150d0308090c0603041515170303042f0402090310050c1c05010f1503 61
    0xc1e610b1090b044242d20900500c0c01601181c40c040008050865100341c0d506030300300854840294114009140c000314503203804004074501014801140b20300f00754003c403800d40300c50b411424200c03601202e05e41e0007028000030901c0425008440c50f100a400818080050303a14044026408641c1640087d0400c40c2a5008200c2c82007009281e00d080d4150340c0d0700d803206a80c035a8501500d01300c0a2000150f085200040360700e2911030441103034442c15105030341901d100f000d030129550a07100ca03025400034403c0424400082014801c607124104202c409a05500b4186c0b40c200c6c1d0484040040075840b07984625181006642440740b40003040d11481c0b0500b640c0e00c1c4400c41e51a58812602191311070b144903010303598400c0f152004d900a082c203d0703119601200712030600c0300a6000412036603151150f0500030302c1401c01402090b204031400b40e08591a030303001203502d01c050071980c00e0040703009007010018041c001306800c2c1001202d942c00e511803081c0040d45000c1c2d0040c20f0740080000805d100c00d0760 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 927574235 1250 927572985 927573001
    0x80601083003101703040315090309030b01090e0f0a02030309270c0406080a0e0319090503010221101a0906131e05010519031e050420030d0e0105031806 67
    0x2000f04880f0396109828410707408940c0141c40e8415400010190b407684425146408082d84c401940075110342441ca0800e61642ca50750240d2009920040d0210348071110020925814032201c443d040b80d0400a144501003540004d80300c0c040c00340b499003e9041d000c00032007180d0070500e50aa018200525440140c04c020504903840c0e1700c2401042e000c1281d0b08003084070840d03c0d214401d10219224040c600b400841840c641819664000304010010717080408a62940d080c4020300c0b9810680ba4607584d40450390844e6048150014942c450b03102059000b00301ca1643d400b400180351215000b001d6482c1d4890000903054003c510a00240c042e440d08081252807000c03d0300d840a04806401001e10741d9200f004660300e2042c000c807840018405c82e00c0307980c803e010780c1000d0300402581d490380031480003000d104011903800720740a940a4141c04a41011a208500ea0685107202900a000003010400c1c4c0540448842d9902d18108000040021442260003418902d000007040c145e603018188000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 927575485 1250 927574235 927574261
    0x60a091a100c0f08090a05040e011a150304060c030e0a0b070207080f03040509090708030a1215051819060f17070f17010603081c0501080601083003 65
    0x80c058024000c60341eaa0181c507000d0306840105640c0405800c0b903080d11a40d83c019503410562641c2c0e0030030748030300011032260348034000e90300e0b1007091800006450b41c800f090b030394650603144a018015800d410300d030103500744c0000403a5406904440d002c2003a40050750700314010402414100014022290100108010440da9900070015942103d03500341e1515040c1ea110355540301c05614641c0100700c00c10080c1403403a021940a0704040c140c0d840199114040d0b800c6a02076000d010000b0800e00b040c10002c40a0300c2640000d60030244000103490034040800c40c80844070361000340c40c40d8140300290744102c8460140e558405402024020140d550500c942e0b101050f004180d04804400303078449120f9800100f01c41214000509046a51710385007004500e8901c0e156000003a5480b14808804a5007250042003c82c8405440300304545a02400c80222201070704400c5032500b03d10010404041c00207100510512203d18a560416140b200c0c0d104000002140d0102c0c20740200421a0b0415014 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 927576735 1250 927575485 927575531
    0x30818090c09031b010c02010309170703090f080c10050d0b150c0c0616080a02012309011407020c0402090d0204050f070807020123041b031b050301150e060a09 70
    0xe402c84064502e0580c13107192411005111900042c5900801c4000d90321030340080a095009420824440f59030071006212544040700540c0499440c600030000b4621a4091a0040c44110090300e2012554000524840012804401000313000300c0d03c1c1030300c0d01a80c4d1081c04007020040c82c0164285402003010300f250060415680310780526014a0540d0400d0b074200e50072040680402d42207001c069544480903082401c03c03030115075a94400c104407414100001c2132200501868000c0c1d0b00e005407030142582d6a07403003034000442c15081401100c0d40c00042c241905032040301c0141c0c940c00d401c0040f40510103a50806540b1a04040900c410345d101e001c801d034020741701d65860385c415a035060400e90a07a0361a03074591410504415a5540d017082c41c50754640c0240c40780080d030319041d40708082c410811090381c1081d942091602c0c056117011f808442c07650001e0500303a00074006210850007040810405110340344402d0b08500004520740d66070200c01d005440198400c1258400141d038445101c0128 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 927577985 1250 927576735 927576739
    0x50718031412251505010f0e0117060106050a0302120a0c1407110120011a041d1009020a030c030602090906010302160f0c0b07060e0709090309030818090c09 69
    0x142d180e00300c000710490125007498007074110110100a030007030410f40c0c4450003c82515554803040e281d449045180c011580288841007a180105091180c82c990822041e449512441005011075540000c00701c1d1460445200b42003860312000c403910b059000e84074141c107030020b1401fa10b0400c65800002ea20104c113140b50350380d0b07032000041c143e410038009200e500d101403c440180b0351114401e62180b508459007000359480301d180b5240980c445400d50f208158101840000b6895084083c2002e1007107094407a070307800703650411601c0c0c000100d485030f01d1260503004031615070718120159282c00079400000d541c040d082040084d03481c10248003d4000e82c01c128452840c400100e041d80d8441c1c0252421803030b83e8522414151a1691011140d503c8003004880d07440001f04009100d80c60400074000f030b02c0c003501c80410040040440385080920942041d0700725450710090b900401c0d88003080c5001c3d40d600400981da14003844003114801080984040ea0000d03140081000d40703105200a014207000c2 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 927579235 1250 927577985 927577993
    0x20d08060604170304170d0c0813030b0405030c0c09062b171305040519050910020c1f0e0316030905030d03021206100e190302100c030f02030301030302060a0507180314 74
    0xc0080c6e564841c1001e42903500003800d6806600c0c0400c103098001d11104014001d81109035569598525000004903000ea910344c0001c100c1500700c8409001881e00c14100311303070a00040c580000010a840d004100781f0100303590003110130b0030100d90b00c40c00300d000c2c03a00030f03451385030020340c0e8042c040090748005440c2c91241c02c00c80000a4070709250203018015503032204840444510f159515004010060103490107202c0c140c2070f0b00c4030b1012803000b0003801c246100a020043c7c608000070306c946800310710804c645450b040340c1d044400008015104801102031503100c0180c51410100c0760f001203038006070341c14010084240c07103e5030198014130055540da503001c009907640c00b0420400200c406070b40d101040410070b1072043c4c5d2070305285034407c1040072001d820300f00e0b40765004203044d60200310059000c00e40d01300001060540044038001c0700b03651031004526641c11903800a485680103461b852200740c8880206d11401d0142070034200a040300f110103051303d82e0301e080824003021134003d8030b103a03405 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 927580485 1250 927579235 927579269
    0x12090b04111c05030a0c032d110604050d03150806070e010915020a11041104090504020301060828030e2d04060b07020621010320010e01020d08060604170304 69
    0x8000c038902c21a1039040360240d41062500c5100351110110b4040440411103480507070b01c6074129a1030801039410403c50803401c0840480c8000e048401203072000152613228404100002d0030001e900150340704580f0b070205860b500e0052184601807940c0048600d400b41804002100340d22101121000030240c0c2c65007502641c520302081644000b100340c10058000d1440c030004110400280100c40780040c000189070450050a02e44941041c0c1050303040c9a1141e0502017546001d00032030b405424040e0280c40009001c4803081d1354607030242408001111218081c400f41800340581d899035440281c03110465101c181103900950908840140301010210341001c4981402e102c0c10083c7d880750880c444c0b074141c0b00d80030483d06070414100124000d00302891480e000e1000b59034180214400c030070300044010f585000c42e0707540f00c000d010a410045045019580e680c0d001071216804030b00d50034000c20303d84400c000b140482c0300c2d5422100520501d080d919146040001c001c00c100e44586816220801d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 927581735 1250 927580485 927580519
    0x607080304080d0e0a0312110306010225210c060212070312020412050c090108160b0c0c04110a0e010c030504030209060f06030c090a0e0103080f0c010605031009050606180712090b0411 81
    0x8081072b0350060040c1d2100c0c40200c0c20307198841094584080031542c9500d81a91f1f40310009508002201e41c07105c422184910104000c440d103000c80c060401f90000c0e00ca01c03141c140c0801c01501603142c0160401030a001e03944805001a812100540a411000080c554590a04a9444040385007441c05902c2d19800080d40c03004c04103c0140006026442205462406003604d5483c0c12444101c501e034000d6248251555580b80321395002c46440851254031156401d5000c1d129a6140840e90306102e880145000000c0e407040856003501e80c100c2e520942074480030040b8002004070071820781c01c2440042070140513104400517142d1894215400c0701d40e139445240041852a080c8802051720006102d0b501a21340060f0181230342000000001401d1aa6400024075100780c030494000d40c944d4400b41c402c1440710a2003e0f643c04007042d500c060000c03110390388010010000804100401814140b44030311012203800032002140c1019001d051030400d410101001c158010a443c868942070311000995 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 927582985 1250 927581735 927581737
    0x20a090902011701060f031e0c0e0307090e0309010f03150e16024603030614060903070608130b0411090f160e0a1d070e0607080304080d0e0a031211 65
    0x60741d860703036800402e1454001b0903000340100d480000d0800c1001c0380140070b418018410907100030303c9541d60120200001080c503013001c1c5280c0214070310b181800250804c8410010456170098002e1800c20725410818204030001c02d403d45464009072000071000460407450b008142c01604405503044490300008000e9913103010690005100c026050f088149018098030001c40e15900c80c2041c00d09a8000d01216404004002086002c07903600d02003403001500d6841c0514078040140c1d00d0618107190040001d540c2e220710b00c2110200b0072148005a0601c080381507001401e5484241c16126042501e003010b4003c040c4088103000c0c8203c000003400c1d0345c0c0390401c2c8034007440e80109040c000c4184140300705c50410241050741d81280c003014002400d21000c0c0070781800340030b404040c100c10303040148005040c0300280b1032070f5104035403d00030ba00100c0c0400c0c0860750490ba100751525510700000ca00c00014101c0b04907030205500442201005140e000050080c100410250400100303900c2030180281e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 927584235 1250 927582985 927582989
    0x6060207050a0f030f080c071e12030e090c0f0d021e0a052205131a0102030a140d0906060e04150207080d0906270515012d03020a090902011701 63
    0x20582c3c03059002c0002c26981070a10705038501600c40c0600d04120101181e24044403a48500b1122689002190101c030840d000c0e0000f9000c54000341c011000c5507103004205080b1451110712070100724012034503904440e03080b50070240403501050344a9294081c130710025082401c0b00c170314801e42d2042c00d44580283c403003110b43c02d12141e1612400c040660417200c0c4503200c0f000e00508010b1400b03402082e65950001c0302070086940f884049280c21444441403880c503071500425042d9401885008440d540000c08941ea800400300d00b0768403480d00103c441c000e07006120015100c2e600d881b50118010b82006035480c071075805400071b1001c0c00c0395900c012041f80324110020f801c4d1002882592142001070700076546c1e05010382004a0080d50301200ba2007000a02d89000002e02004d60180d410001c2c00d02c4040c26000d0724a041508640c5000202841c070664070080c02148880d41e079a00515121000d02c10001c1d58010b052003aa150702e41c51580020900e0745405d901040240081b101514000303d00700341 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 927585485 1250 927584235 927584249
    0x1c0914011b0f05030d0e100b010219051507081f060c02060703030b130b010f0507021c080d020309030a080a09030905131e0506010e0303030411210d0306060207050a 72
    0x421548810300c101c0022503120100c801510b00e502082c0410010805401804001c010000d03c0c65881101039151065207503c0402c1203080820000d020303a00882c0403002900103030f0020380035071840e24003e07091051a941c03404864000e502480300c22640318014500c24116640d2124800015000900340004030384103020000d01098041401400c0c0b00300034003481c0344281004500d0052407000105003541200c01c8050080d62000076a440b0360b488906902c410206003040b6150000c203070040703940c400104d9002d80e64909061f400c4410040d10390102c50310749040000840d100c1c200340c0700303041e02c0c1d900c05d000d1400017039282d0001c141505098440d283c0850f60681300e90f01130070315290038000c070848011a01084641e6503020f107040e054894002c400700200d41c100001e1545030880001d4400b403000707418a4003c1d03005004001c00945042c110001c4058202c030300d007031122203015001400c00301c0e100c5a42e499000b6103520851a94154011400350b03016502501c00c01612141800060344151107016 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 927586735 1250 927585485 927585497
    0xa050f0622050a242904021c090507031203020a2d11030c070902030405071418040f080c0f0c1f0e031912110a020114030a06081c091401 60
    0x250018442000150502613654400070000301410751002c110303105420f40d4801c503144030f10380107410300d400700d00190b8440e800c80d81181040e0007030f00901d0100c0800041203030466a0780c11540c050060800410000f1984011074844601c0c869174010041d40151220b40c01060889010660041030803105c02e520a00340050040031401c0740e441180c1e038403007164100d106800100400d581c8204144440c00140c60092000360340c0b8105441d04614180d120307800b070070000c40c2007040c0e902c160740c0e00030b51662071244484101000303858508048075540b070074100c001c0c00d81d2400240e494402401059062206c820081030790341c1d02424505100c041c5201d00e02c0c600c486001001c0d0982c11030301071750f603184a000c806011504546041050707501e40c11010401a184041209a05840c1c90760040c083c5000075140b8025004d440110790001e010040140800f914221020001a01e03402c0030384d00503001011401c0403284009a046410416456019114400143c810b88040781810001c0f46100c000c3c907040c0d40f03032 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 927587985 1250 927586735 927586753
    0xb040504081c0908041535220b0604240510050f03040303051f0503030d05071110051e060922051b180609060108090a050f062205 57
    0x1c0c02c0104000000722402641da9880759001c1626100584058410642c0ca40c2e86030780d05610107028404d040c03d07001c020414510201c1000c0000701c1107210320080440e0700e4203d03a201c804140c1e80c18110340b144541a090300060601c148200c4050742030194009860400c044541c0390f024044655074501041c18a01800b14100924101584181e4602c1518600b244c20100503039100e9540740c0c81600c0540000c0e455506006000c42c1c05d51f01808241c0300e0001d03002000d46400c0c0400d03141d0060001e5504215500d0b40001ca0791070080500350490340540090b00e032441d07034403184240100410354000e2001e00c100003150045110304030219029400083ca02d43c04c0395148070040c103100d1007000178074034410000a81c0c000010020030803504036a907001c480300c02d04449942480f0b030b000b03c1d020440502814800c00d1107100d0b19451901900201c0a18051140b42c0d100442d6510f001035450004165110b91081544000350104a040c01403440980005c05650901e03c081400d10000d0340141c0319030031940c4c0c1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 927589235 1250 927587985 927588007
    0x606110c0a17010e120d0606050301060909051009090308100f0b0928030f17191d060c010f14010e071107031202150c040f05010c2604090b04050408 65
    0x9071400d9403105002088614500c40484d050125505c00d554401d000401d080c0b001e1b0300180505006090b0314a045400c540c50840c005010711150711500c18825a0380c4045440c00800202c01d001a01d9840e4060040d08424680189002022200759440500c00c40c400b1481c40c002c1e50300c160440c1e0400001d14200090241001903054290742314540b128942e1884e4014a0003103410701000f507003e54070346000000c2500b41450240041421b96511042c20407400d62050307011014800c8000c02e80c54032005030420000c0454040d00b1500340a0f074801004200301d40c2081c1e05400c0305e80c0040030450240800c040030120901070328030a01034100c1010303400c400903a0140c4541d04c805240c00902d000c85042581e82d031500703040c1ca0440050a00182c01c40b9841040235403086910395044000811348601e0a031401402c04030554290044034104184070f500d020a00140d1925051707139100003410110028500c4003014110f5209120340d008050900c442007071546401c1c07280c2c1c0d200b250003e05091801d403070769003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 927590485 1250 927589235 927589259
    0x501050402030705180310291f0e0307052d06070c0b130b07030503180d0f0e04020d0e0303010314120d050c07060606020102210903070f0510050a0606110c0a 69
    0x85c009826204031954018070b03030314500804c1ca4140c0380041502d128190310300040070340f0108080e00c501902d060800b120903010904800d03000001b4924002c90018900400203081c0034a80d0300183e8810303042ca424145005442e40c0020309006001c240540c10301c1450180003082c094080007810141d0458410002180080011310840c130b048403141c0400d0351526004001c030780140c541600003a03008003c0141000f103130940c215002c1d09640c0100400c1405e0280185059424242101080580c4443c141e064684d0303010344018622105042c00342d03154079113986030b8a0b0400d1009540409404484103004440456407201801420000361300c0c00b0b07850480140038080241105903c00c004000303400c0840e4140c41010302500302c43d400940d0700e06c030300c003104000702144900540c1e000d01e042c41071160518000080b59010383d80725810951144032420200c0c1410342007901115214246420050149115805041580c10b20f843e0a01c028240561a0703941340f114010080e00042c001c83c0900807045500 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 927591735 1250 927590485 927590527
    0x60d2c06010f17031603081024030c020118110f1f140f0c06040b15010c1401060f030309061403091b0a081b0319021008040317010602060a0501050402030705 69
    0x2c40340b81c011500411520241c20348426000540703203c0902000900c8402000b00611951a000c9d40700d10000603240f025044047c1c10f441816550b0b01030850a0303000390031988221182041e40c05032800c007410000c1c110300010304010302c1031800b9003017400b0526180c403031684004601c005400e04c0350b060b940156881200d008542d2035013202880321010942401c001001c00c0706502d00600014102450b190b101050058002c00001c001e1541d61152a64000038880300035170000e803c01030043c00354026138014900c581010002c258800c401000b13064002141200f02d41650b42c030301e1841c20003400e1502e000e020603220030300c0c07a403c5200320112180354403025058807100184622142c1e80c0d203407220380c501b01001054101ca21100030500c1041e20b0b0a010000e82d003412040b802d500e0300e2040c2e0004407070640301c1e51000240088500818189841801d2404119420600790b01080d612042d01964902d011101401c006041500100c1d1a00b014004d4034041d82407a01c550b41040c0c4d40d68150759440b40c1031 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 927592985 1250 927591735 927591779
    0x6030504020d0c060f02060106110d08060a0306020307020f0c040b0f0d03111b041808030106110304080316110f0907050a030b0925030c08040809060d2c06010f 70
    0x406540400b044110f075020000300410f0322458004211041e020b070400605901410501212648180940c9408189291140341503e4400c0103a5940c00024a90300e00541015158a10101c204040b05400050001041039404211561a450030040006840440c6001c5030001215000c0120501b8000710048a07944a4203040c1c9030210340c0902c045c584400c5980c9000d4039002c182400003a42020311458032104145000c2d15135200c4903450710007a61006210f154208007965000354070b5000d0a10984001d0001a011f4995906c0402c203510380740364603501c056a00c01c07020014080c07641741c40c4546480c281e074040c204914903500c000b010348407a00007a0350301c014103807100c1c1e000103259600d800440c821200d05c00d41113031030313074562016038040c805005a900034076240860140515802400d8180d0103503010549542c0d581c094004035055000d1851b030842003034105880552410300c940c0100c9503050315404000c0701480070034112541e851080c03203554500110403204cc8000000841805400440 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 927594235 1250 927592985 927592999
    0xc0c0a0803040f211803080406050f0705100c09090c090b0f0405030609030c150c1c0b040c0c0605090a020603150301060e01080114060111030a030c0e15070606060507030503010603050402 82
    0xf07620f41843c1c10812130841c0d40740041c0c0c2c110f11802e284d00203810702c8282e2101014802210705560ba184003a1281e0301580703040c02400b06403902c5c80c030342801c1100c40752580481620400d503002e046000190202d0210076012a04c0a500429560400e218480682c0318540c0d07642001480d114064020358040a849031402c5401c00010901b03450801100d070140c00c02d40010341d560310366000e041c4c0c149400311002520300b503100414090342d903d0002c1a281881c004400451b0a85400801c400c0246040000380d44c00504245040001917003040300303403000500907803081c481c035655022011744038080c504000354041c20602c0403c07100001c1c04240b000540c0d0103000000c0c0c0689800690f030384013070300364081d010750380d100c0b400c0003d40c103000c000c0560802400e0034040011309480142d1504c0c7d0145400480400d6074462610340001d114601c146501d180180c00004042c1c0a0f05c6101e415074005007058604a0a1040014200b071060342100e820b0760300754ae10b6505503400c12208401a01c00034100342d84c07140f4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 927595485 1250 927594235 927594263
    0x30d270611251509030804120909241e03030e060c120c010e0106050907032c0d021908040315061d07080601020a020120010e030406170c0c0a080304 65
    0x1801000b031402d401e80c24415070340c00018500d03000300c80b41070b85010301e2030090400849000017500700c05190b4200d540f103402c0e101207101210341140e10780d401303600c4092014103041c0c0661890f9095055041004012041428040c1d01ea054092005039143d480321500c0c40c0c045030400c04688141c05110f64244010103076440c0c0304101f080d5510b0050303902140e00341b0030800500c80d8000f020910491900c2d04038003000b031010a10b040300107440518001d14100505407031350b1000007011341102d91241c03903400c4007451030207404200c41c1896070f40f5008508178002d031103503124140d80751046000350b6080365440701c4620701e45411691018008034401d2030100b0300c66110b84002c40c2c0a842142c4480510716841c999410703d00d0610340c02402c002c030240005040d5081002440050307680218100140785461841c4180140684074442c018002d90303400040e1030001040206141740e000340349409071030030401e00402548502110321501e108100002d0034591100c410b0704006844400036643c040d014540c820b160a03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 927596735 1250 927595485 927595507
    0x105072f030c011413080403020f01050706060b03010510090f050d030c17090405010617150f13021b0706020c011b0206120702060a0e1b030f0708030d270611 69
    0x900000c0100c29541d450340381c14104d010100002a90041008024604854180d182c0010500c0399000180c040d070f00a410005844e40202c00f00c80d859603101104100c130319980c0c18041001d80082c05114407854012160200180c80350700c0c4803003a0350450842c0b1000c1362a20342002039640d00c5c46000c9040c4408281c201000c07a90b0440d40c400300e0491007440540d0f41e202101080101d074016000030342401101242514169124680541c0c01200c0d140310186a025490000e140f4400450000d81e00095a006103a6580f0190f00649030074130401e00070500e140d0140110a40722080c5000e2030740103a00005641c0000e41c4690020110781030810703c2040342192075004901e0a502841804c1c800700c11581c103204041d0b42c1001095400810004c080144102c038031041c1e502c3c2e51503400d0340040d03030b19000c030210b00c540d034188203400c01c07400b40b10201c0d6500d43c0d8030103500e500ca4024010185120303281400180400c45102c668400288440503078440e807a856594230001020081c80b08010140140840d1600c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 927597985 1250 927596735 927596737
    0x140309070e100501140307020619180f0605011a0f0a0905060f070201020d02061003170d090c0806100302090f151c1b030b04080d110d1d0105072f03 65
    0x10702c516144070000c18101000509200700040220038003050820800c20881e601040c8503801c4900480300810a03101032040b103002e4621070200c80945441a40000704208103075560302480b03032207103000380401c1e86e80340d10070702c941c2e00c0008202402c0c0b0f80030880307400d000c2031041c018484d060713050425100e210b84403c0458015000301c8a06081004005045400c1d907070100405001800030344024841c9182c0800041500314a612006002d60301c0841e40f000780749100000e0390b2440701c8121003008105510300300072181603814401c1b480b6602580c0040780141d540d01700b1700000d80e5009041c542e01500d40030500f581c018801030030700000002c42c0c010001e0650710304601000901030901d000072004170a01744094080c0442d0111044400c0002c0100002241108040e0340907812104281d00d42c405204d404014109494078261361100005013100f40c0c00127035003c040049103d01c00c8100d001207100048d8200c2d10150f6034600850703030b503031941402400064241445196442e076801d0303015050706040391031 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 927599235 1250 927597985 927597991
    0x3160c0306092906060d020a0c1208180c18150d050708010f1a040c05130803040e0105032a060c0a110f100c060504030e060a09150f140309070e 63
    0x500b00031210314580e481d071003e2a441c88030400d0880d9900500341240014143c1c4100d2800110303076600414a101c02601441401e00b05c1034001030200d400c40840074006050480c01c03502d10502c4030182c3c0b254451442d0014848512600c003900300c5c4c014410140c5103644140c4010540103840c0441540b1100d951644e03407000f00c0180c403c6006003411400c1102e02c60944175408030098085183c001e00c0345c0c01c03003299a2049070320308007a030b4005400f20650000312540e1280c0c208143c1c010100707450004810714004005c2080701d201e500e46950603600c5008140e200d03407400070341c401c1803121294120109800b44403d2000803200601e2107250100c1c1015040c00c21030001c40c16955865400300c1543e03d82030441c21099811030860b42d080042d10007150242042d091440c0143c8190355030800602018060220320300c16610040496460b0012010020110030160107050000b036110068402d4040c011090820010100c0e1180c18686c01c0e8105803090300e400003002400a8800c5c00360000d519200a621680 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 927600485 1250 927599235 927599243
    0x11090a02191706010221030c13061701051e092503230603061503012304110a0f12021908060915100b0c01111903150803160c030609 58
    0x1945440d40e0384100400b040104030a0654001e00c42c0c2d401c011440c125044040300300f050015840b41c80d1115071401074080c0c098030000c0400c203000b02103162070b0400070000840304040f0b0718100a86c0c0f00c8080c07110303008406913441d0b81e882050752801e84a00c0c1c00038486074400c440c004000040c1c1d814151004000840024250110395203854171a40c05204415142d02c98400120280990900c0f101003507584500400c0714a03680d2507140d0b4020260750a40016a25100301c00340c03100c641401c075000c030700c150000740d404441444541c0d07881401800d100060408507801004036140181c94103014414090b0700070012a0f105440d400120803009041c6854405010030100502e040e00d000c000480c90880e464210103000c40483c0100611520b04900c040103844131a04072036100d4111854180c050083c1e5461503030311800101d00c4440110314008a0748c81c070000b5540a20070080070f200c001e02c13105002d00424910b9081045019503401440d488034170903902c680904070903107070b0340e4440008036048a1000c035 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 927601735 1250 927600485 927600497
    0x10f030b0108060408070f1704031a0702060105010e0d080d020f09120a08041520010b1c08030109050606160b0103210206040b090a0c26070311090a0219 67
    0x882400205510309000d0403401009020504240e02c07144503d0240c0d0000805043c0c410101804001c019815200f102c00c01c10b2030683c845c0e03180d2402c1000380c2d01140d40d1821061554000488051000881a04a40041c1c4540c42c1010b240c0044c03004440c2d148400340e078500340411260505265030303c02807a4820420703040640764201c0301d0400050138403500080b62240e1083c880c04011400f481c08860444007070313403042c10182542d04000d4807a4018440d1890041580d00303a421000c540c11340100740c0d000030482e1018070b1007000840a019803002c1c5840a00700722410300c018030800c400c079070045030040700040c0303801c1c244030700340404511b04c00f11400200c403d18002001001048030b80c6609900c50540344050080c02d91044a000b503403903400401c00b50041840402280c455841072010250054104600c844003039100c000d21440820088000005c25544a12000d0b400741c5c085a03c00590b68448292040d48285404020fa840710203011041150780c02c00c0803012401c403c508182d24480991210 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 927602985 1250 927601735 927601739
    0x90c0f040807030210140d0b0103060905040506010608060d05030301090b01050408070b12070305091f0b120c0906091e060604090507180801051b0f0c063c0403030b011106010f 77
    0x8000c9080100b071a8400340816100780348039084845094550b07c054101c000104050610012409082c1e01d81c8603c4032549000301b84000c2c05804501d01d03058503940c2d2180c200c152a020280601940d201c10007801c140c009100520004000f030300658080001450500d0130a5194100c003810210240c0c80002420390024a86000910810015a1108103030500300050700e44586140c0d101e104c031091555010310b802e141ea84281c0038590182d010954080c0c6a00300881d0491a002d595000c1003601034852840040003805520304616030303d00c11a40819112081d00e04501160010070f0f010f854594424420310001c1116003452240b284500700365a01d00503c0002d071460884140000d400280650b4141300c00c01024841c12920341c0202500b10414036503034604260301e2582406585800300c01ca020f507209101c200d8042c0d001103e1b1a888540040d0f025882c146001c0c0e000884c406896020340240c000058042402540001002401810044221008918043e0402d04241c0084072810211141 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 927604235 1250 927602985 927602989
    0x121b0804110618010305100e1602060a180b040c2321030405190503030d0b100c0c05010e040e0601180b0108060901050609180a050403260105090c0f0408070302 70
    0x2a0004640041d00d8a030315000140d4005411004610f1145040c541c841010801c0c1030240e00750307000100890b00d0140885d0801c07001c110849106100d40d0001440390034003080d4004168881e042c2c002c00c0c116481a109100d9669002c0c144500800035550a4008400041c840103610400d0321071500350b8004d1074940d038204080113100624950100032400320b41e10105c40020b4004101d4040c0d580031603c06070110001c0b69003031501b112980200c0e4060002044440c00014190002e5202503421100b007008a15400c0702140e40f0680700b800982960070194042106500403220341c1d1100b24080c0020680c82e80390b040d6146012002e90022844500040d5003443e07010303241c40740da40d0641c1d0034a40140c00c1e060a4000440c40501805000d22460000030f52800c140e40b1201c103a01071000b1511102201d2900703500c07510003090704540913400f00d000301c071042a1401c91010003400d000d07407060308ac41442e4241014084000c000501d000314407c010041c005c007024521000c1e1004144100044c40054210702c1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 927605485 1250 927604235 927604253
    0xa23040e0c0904080309101b032d0504020103020c1902090106021501051005092701090b0d1401021605031c0c02060103031b06060612050601020c10121b0804 69
    0x804404103801004403030020b50758002526400c039412154113610380d1211281c1740d04080c0041001e0640a24000c603800518150350a4040c1c0e00342907440811101400c007080c0c0c401e00350140e01440d040c00c03481c40803190380c056940c071840d0014010300d4014284102d0306141490035880c2d030426003540e08481c1d44003045140c0f583d50f0a014105038400b0306010b0180d2280f21801082c1802590b2088080301266002c40784644251041100d00070079100c0c450307403441c07041c07080400186010701c0720248880000c60081c0300c0340512101542c002d090001203071810b0303c480e00c100c504050900941e54082200b13170205d076000c202440455001d40047c6550704000000c0ca0300b460b404410b000100742c14840000051900030030641e0460b90141444082d241c0143d12050052405010041c02c107468032030041061944007810a1641d5070074402003006460306401a43d50351101c4624030381c0002641b9403043e1142c0704009100a2007003001002c03a07509003c0c3e89943d094041c0d0303120300300080c40541c10402400b4000c2e07 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 927606735 1250 927605485 927605501
    0xc0c07060509061204050a0b04140d0f080c1b0f030a080a0504030207050d0311070b07061d0d031802120c03070f0b0301092a051c11040909020a2304 65
    0x30070181c2c6000d0310000452018000d2601c5021000f1500001805110040c045015200e61118504245140502d440d01ca82e0b11000c0b001c0703117940b140328954a0981c1c05820085220001921820305a540e44050075400c0d41c00324140c012105400700109610348810010079001c1c24101c0051130310761600400050560318024001a1079034203140c24000420b07000b081141c1075074826a401d6150301d1980c00c0c1070307402d50003c600554451080c403000144403c440310161440c284113500a001803030068004054065803030450880385e402c51008010043d020780d006401090a00140c060b0002c540d0700040c44584541d08590069001006030b254149130a01c160b001400100320292004c90421712154081d01050181045065039020301000101e2026152443c2e40c0c00406800d040c0341c40e480c00203055812000110010302800c0031410450300c0c842c05040070f40305411804509003440c04240201800d000700059030801c224190102d441c00c0007146c0c4000007015440003030b0b02c85800030280001c8900f40 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 927607985 1250 927606735 927606737
    0x6050c10091e0215040801140702030a0e09090120070209130c0b0a05090306180d051c09060605130e060c0a020d0f030e0a14100e1005040f06050c0c0706 67
    0x200c0d0288000452101d00c41035078445500e400e030702c1944030748085540c00540c5a207040b51024046000100c0140540282c95007028599101c01a91100e0405aa4a014145070078005c0790010260707411a0500c0c0008560000201e0000325640d69206440100980000801c6521000001e850002c0d4104880707000d4022049640300241c00b8807035110007010081d940900f0141f4a03000481400282c03207081a20071a0900030705554403030801100107429503004c00840c000301d014100780460081d015400340c1d45000c0d04071039001c0341d03800c1708481c14000348081581110034603070f145d02c0132545407250b024aa60b11a0368960010702c062041c02c2d060300c2d00b4002805410b10180c10018141c0150340032890a48100301d904104001070f440c00320603406050310700c100d604a8403505400c0c0d82488909500301500c103210205860000074082c041c082034600440c11001251b001700714031301c3c4681c1c4035072242d6406400303113410000500d42540d544054403016141c04000c0c20000c80d450702c0c0b2038028042c40c0002d00036 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 927609235 1250 927607985 927607991
    0x9070e0105030109230108010504031d010e222d090314090301110c0c01030e0f07230a031208130c15030905030c01090b010b030f010902091906050c10 66
    0x102000901e207110500404003070300d0f143d078618a61411002c0200b9131075040c01d090060f5960310703010194002c000486055002401d5000d2201e05214070106525034658103070b443c044400c4840d018030111880c1503100d11345940350b4040020103231540d40b1811294014080000000840c0386d400d0b80b44000c686015401e20516003108000000c0d0010101c50911411719881d584440380440000d0041102c43c04500d406400026490552103021400090b61042601d0070040d882031603510507968800c040070a0390300d600420041c070940c0e050724450140840404103002820110102154012020f41d008480a00000040d0200c0c0d94000300629888a40c912403100304039410344039042c82201e184074000498542481c01400d4504c40d070042b41d801600a41207903512404002050300800c402ca00944014921400204001c5044000c0324050030003052200556400c00b0455002584201c00107988030141848000b40314410000c818020286ca0721000d072a0101400010300300010700c1c00768045c0e549 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 927610485 1250 927609235 927609257
    0x21204030f26181309081c05060a060819150512030a120b060421020a080f0a03121d010e100207020a1202311d0307020103111303110907 60
    0x102e050283c1e510309003401484100c3c3e05640e00840c142c4880c601400044600b00802c807000e002490000300581c144d03000e20300ca2040d04007046001203410913264190b001000203820480300e441080c106030040d40018650030005000d00c420403ca4140c4408292021000302c020401850890205c010b83c800180141d0700d00034020500500c0c290110b0300600b401592210081805d4841009403005802c0c4460034480200704007403000104410104100d20401d505500803031005c8010450352102042d50004002d19200c0d03075400d40d01903283c0a490034049980d049070215200c0c0240c0c40032441d248042c00003500d46542002582880e110b403d81c1c40540f401000b9100044c0c94240700802120701041000d4906202440069440e4151200b9504001280c13004a9a034116040b41991061081c2508100b042030382c8030281c81c00c900c018022006034006001000255010341c018051070001101043c1c507001c1034a4020f40151402e400c291420040c2841d155454101140740300e40100c4c03d03041200681c9 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 927611735 1250 927610485 927610553
    0xb0a020604031412041713060302031b0a050706050a0207200102010b0f0a0501050c0709020c0d080105030a0201211b030e16050a0611010e1b090703050405190201021204030f 76
    0xc0d030054001051b400520b41211043e0400030291410110003807181c5040c0ba540300c0c1c0c0180603400c142c50b03080441100f50b011131030700341c400c0e012503e0711900b90f15402d00b0318280b0b0300e44000600c401049481080e03000c0200d04001401160001d840c0380300703101c1d0200b000c22000c00081c2156051070402d4080e40021107124a1a6100c40c000d0302126001d203002a59260b502c0c120f5402c19036660b012042c500d001160140e0300544c04603040e9a891182d944243d00c2d03030382e11020540c0d10052080040d001c1809441020a4081d40c081c80790b03204845207a001c20780c000d80d15100c02e0240c80320401c5200182d0b4400407400022000d0007861401c026110054042e42e0820002402652252049e40e0174001da210000c418841c007904080708983c40c550980d82300d40010104468404600c921036485550b044c0000341100c1c1c024490f0f0381c080e940010003403100760150307604140f0812000500b82e040d48900c08030b244e410660381c030060016600c9445524480d2609150400084441402015592284a41000580c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 927612985 1250 927611735 927611767
    0x61e0b09100b0a09120f02011e09030807020f0d21020114060f01020f03030a0213060513060f02160306020405010207050603041101030902010c020301050f010503060a06061e0302040b0a0206040314 86
    0x500c40300b101c02582d440c0c1404059035000ca00d5031011030a03078100001c2005100b45125000c1846000380c03242240c202c0d0045141a001c070280c545c41e40441c207808c400f40041500800680344091000d45181020082900020081412420102c0d68030708125125034484080180200c0d1036111800248100d403080c0e1200f4420120082800e80142c030310643c40f000303d80c400c003e000c20007901201540c0d03580c00c150f40c1a00c0a035214001c80c2342c070100505400206a07100d1000c42d01000c2c2001102031000f030400800729170722266203c0103001c45c4928409007100c1011410400700451003040d006070b41d03615000c00641424116840790b84621002d008200104403421070401d0151701c01d00e0005a010035502c0144e951151080000e50151b290400300220346840ea074a4905940701101202d4213642c0d100e54802c2900c1d5a400740900080c001034400300020b440e9079448000041a003000f504141e1124400700305a00b104100ca001a80800c05000906070829189240340a8040407107240400b51a194040 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 927614235 1250 927612985 927612989
    0xd0903021815060d0b0102011b080406050c190c020411070b01090e120714120a0f1b0602070503070b0703051b0c100501090911040219140403061e0b0910 67
    0x81400c09400540c07400d8550302c200319100c10042040783c50b500d0084580005241c48081c0b9405503190082c401104074210304404180003d9540b1204240e0711070ba5840c01401e000741c0502c001103818421401071940003284840c03600800d03901d129505110703004120544071250195140d4840810911020810b1120458155640c0c8940880c0180701c2e07160180c87c100071440c162500c144045560000c2198030f055034007510118400325a5000e106c40d001b80c042d8800e00d52040c002c0342c00000d030480c07c2ca0094260384020390355a1031a0032030009549802060f07030301940f000c4400b600002954010001e20a20403a00701019140400262502e0301c2100f904140513221610070a201088107012440208416030034403401000900a6580d80e12641d40a8110440221484658a40f0181007801e280c0701303481a03881c0c3d001040b1502101450180e9015010000d10316841c1c0c020000403021804500a4a503562201002000d4420a2950510407071b9060601148250100e04c28000c82c03d00e00016901 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 927615485 1250 927614235 927614269
    0x1e06091721010b0417030f070b010302100906120b120609012f0418090c0f050424061b080a020d090519030206030a180b0609060d05120a030204170706020d090302 71
    0x17030540317403044505e02e0360203404c0c400448144000350030800c210720000ba06040742e20035202c401c003100e01682d00b81d0300d4844900a88000401c050b018045291301d58011060070742010381170b031600c45406101d40d4107200c4125000004d5a440744030303141695104110b1007206070aa07921550f01c03600000441002445548100611451414160200342c02c16074014411203a109410466165881c3d00400c40b0300600c0c425644034911305030503418044100c20344015806482c810078100d1504104054910b80748400003150725400c40000f0b4000155040014071700c00c00306400070940750740082d800030200c20b1560002801000c5181e842d5840700301d50307500c0400f03890f81250a03d07240d90300c10700001c0060280484108540c40e000303400307505200d40180d2450054400303540381c0f01c00f9503c00c8240520302c82c10100c0100103510640140d503040c0c170b082018085003406403401510f015501e00480e18140c1360141da001c0d594000b24010000e0350b404001c4452887c1c4907040901400c1e2440d000511420814880c1031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 927616735 1250 927615485 927615509
    0x40318060203120a02190c150902092a071b15120509031c0905060601031812030207151b02011a010503040213050709211e06091721010b04 61
    0x42c1c40d4002901902c1199882c0701c010415101c1d035010007003c2a103d01415200c0032003488088c6900e401c1800748081c01900174100702e115880c0d04d00e00348a4500000d400a141200d4040d0410300050404c0c01002c010340203900b112101980c89210120070700d102d5000403104150500030b080c0182c0c00111601c10750004520002d46951410403140c154070408501c4410307003c283c08100200c2185a01c0f11a4590059044400d5a5116801902250024900751400e600480300386000070300011140c11692655103409820594a03075902c0c648110110307100b81c002c548805d0203960002c2d0b66185031415600340d1000b41700801894000f0301038101604105410060004006019510745201903144c541009108100301e00d130941d00204043d03c80c2c05620005100801401070341000b29031401003254100c206186070180d441c00383d4501e854404003c440700703500c03641800b0200e0320110503030150981c0c2d4500d00d0344d83c0c2c2d142018048924103540700310020542e6040180105601e0500b0749040c3d4124403819 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 927617985 1250 927616735 927616741
    0xa0507050319090f14100608070302010c080a0905041b080912040909110d1b090608030f0a0e220c02240601051c15050301090b06040f1508010504031806020312 70
    0x381c1d10344541310000750000015480055822400050070451b8a11551081141c251146410743d203400b079030310020b400a00509408004076282c640200300d0600c0d80d080500c00903a0751030114095408540340c0c0281c3c402c03020064001c0c1754000700b04030340c05a1341c0806000d0b503806c42d580d96072490045000305001555070f000c0600800c81c130485120204500145040c0c03d6000c41c0c0307003400e0300d142c0300c20030002d51a421410020ba2100c5c24040c02c0305a400c2c4030040d604082041600100c20b800c40500c10b41000072640c4500190348a0140b05805101d000c0d40e81b07420032000009100a94041c8039500b070865218000e02030480044404040e41c0b22551a18030303116403500c500480d1307036001380c46d00400c0ca840c85034000319044406900554414500741c4040307010942c0c42c0105804c0303074100000500a140d501c800100d040c43c10f0384c407540a404140c0e40000e0120400848402e040301c89030080c584981d543c105002c02d068101d901d10590317040e90510214401c0c20b020b8000e407280540454509080861804 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 927619235 1250 927617985 927617993
    0x3070c030b0703020d021207021c0c030f14130504151a03060d150b180103120e0a09110403022b120c0f1b0e06011d060702090c030a050705031909 64
    0x4441155211702815500c0300e10307a080d02c0b0b00d0144180c0d9104094450443c13091214942c03100c560010702400e890392200070310252019541c0d0300141000100300080c0d4254501410000d4014100703945500080440c281e0410060000300c0d40c9807002c0c9000096212000c10520344400000010300d0807000c1030342e8482d00c4039004a883c1400c0c00c240203110442c52822400c0c02d005a503c00f50844004984501800951102c0416018005c7c007014004015145101031034bd4017542d5061f6140e000031702030121060b42c642442c01240c07000402c4203100b841c006002c205618000c06404100201002400348807541005101000c0414240c0204150403050540301158000c805000445802486601c0c1e079500510307040c045420b40740ca10b034540700b0341030b0300c040b40c4020711880482c4926410303198501c401a10800480e8800d11100c0116403101c410054a0016118400c0060169440c0e90660f6242c0c1000440c00083d18002080f00040010510030808191030900509441c00c04a010015010100b414 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 927620485 1250 927619235 927619237
    0x50112151d030310060f0c1e02120d1d100f05040305030a0e010f0207210f1406010602120708040e0a0207021e0a0f03020d1202030d090302010f050903070c030b070302 73
    0x103040310580414145040060040000d6200e1001d080c1c030864000d44400040d01c0c1b60300503400d071a000450170040708000501001e01c841e0720070100019010070501d6603000440d00062104024070035000820050045608807840c400c13104602424034401c0200c01004c110510104401c0b8020844903e241c040c4460207841110060b60300b000a60f40ea0b070700400c01c041e18105a02c1c1c962800540440c1098001900c0480d401d800c3e10130301d20307519028848040c0202a8040d400c9801d4804006048217100010b0740000c801b8614522300d0301400c1e45615200d17010781000442200c64150902c200040380028800004030380070385911440380c400d42d0300c50800000003809040740094010701d40c00034030989003058154854440c07804551000a0303d8554401800c240168403000350840004c9a01c0c0c0000741c0c2c80130442c110b80c80c03a07104580c00c0181c905580810384040001c20f40141c6d540b00402c2000a0080c02800d90040040c40118275140310303991850014101d034840600990102e03c042004c1c207110b50 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 927621735 1250 927620485 927620501
    0x32a08030c07230a0b09060c030d051e010e010605071502030f1902041a031807060f030f110a0f0905040c0503011d061516020603090d080a05011215 65
    0x1100d4844a41c0c040450341c0710143e000c2c880440e012002d1607a240c681c0f0941d965020704020306048001403919114810a8109a400b664031800a002ca2414504204090074800c0f0300c420022404d818202e0507081d203450f499080360304014500005110072010003411504441c000e240159481c03502d4100720781d644840f681c1c1410403d00010038022090000c004107800b841070320b00380c907400c28680007403001244114425404182d0980c52a01c0802c06c0c503e001e564410f40b40e407817500c0d1407200854402c4c1071003540c2d04040c0104a6150b0840d0b8020751500c030350a0110180a403c11040206030784850b40d5002c0c142d4107004100360078044a140500c110001002484068400c0c0b240f007400620141544d0424002d146200c0e06528401c550343c00580080350083e03001a0015015888a01107030712264406411560720300940440c440058817080020340c0300b0484007000e040c9039881000001e29405024020141c8641840014071808119426501d01715034001071160031088814030b80000b41000e4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 927622985 1250 927621735 927621749
    0x604290301141221030406140f0708060604030c03080904090818032103011e050d0305030f10060e220603060e0d030204180e030c101d07032a 62
    0x8800024849101c080902c0303075800480384591078140b02e540d030a80d902c4603a03410610203400140d000307554040f80002181c100d4014000466040c8159494114004042c0d45a1600e400c040b020840059402492240c01400c1101c01c5450145181c558000f0f603241d50001400400000400c1011903456620002031190701282240c0c540b40141c240d03c1800d074a000881c1d029019139008044a0700c0c900c040d65000e0031071312011506590074800305405400c9015604844040b0b03004000c611b40d40c5910a130030100b482030382c1d43c40c6d0f40d04d00801403485110000d821850020f00c3c040d81884950b412079101d00800d071065480ca10940f20034000b0030708a203074176000b81c0c01d46481e00101200f4480260402d00310a0201c0084404c6070524003821400c91180707210f15800381072840340b8400304140c0358000144000c140700442c0c2c1400e96511903103050080d8245c0282419030394201607800d04204941c504c05081009010b8220941707940c540341ca44000c9054480c0c800e040741506030041d40c07141c13140304002d000070b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 927624235 1250 927622985 927622987
    0xb03160614130b130b07210c020a080d1407121b050102030906070e0306070c030e030a0212070f0b1e07020406080d0c0c05030304061202160503072004090f0b0604020d0f090b07080402060429 83
    0x601c80d140e5403200ccc143e007008070016808404004910a00e42704440f0407030751158040040e020302c1e05084465100089c0221410039002c007460000c2042400078601a0b40784101401d498100f52030b018121013290740301c05010f60007510800c0340c0241c21126401c880d5805040200b211304c0c64070002405e01d054032000a51240490240d110182000100c4209680c410740d81400f5150f15404840e22900442203030102d84a060803400040304176100c05010b078540b0151001c20b42c40c1d110807009040c88000055240050041c5070b94106200803441d20b50000e10059010b1031406081c40744c02488441c1e418040c0a02580000380b0080c01402e8003041d08a990300b240503a600c0310780750700e4030320b100031016440f40141c0f202040c62a591441c007481800242648240b20040701e520644e00c0c120031410060801742e20a07802e011080320740360680214007040012020004044140d4601201d002c04c02419100801081c1ca0800005072590300454041c3d0f60800c100c800b02c0c061002142d09101c1303c03100301408a00c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 927625485 1250 927624235 927624239
    0x601051e03040b0a050907120501060b0408010e0d0315060318050d051201060206130b0a0e1e07080102040b030f0c0c1b03010b03160614130b130b07210c020a 69
    0x18400d014501840c4110000c50039034903030742d0100040d11004d0f690b40c50242c11486040041c103000030044885e42e48180004a0368a036181e40c03200e10303070300254032402141e510f0f041c11590501c420300c00c50064049c142001c21010a42c3d80d004c24105900c0e00403030040c11340d21a64060030710811520300080c00c2d07110040f50030b25140003000600b42d401c5030704101c0380c90004100202c0c0050000c20b400d403245403420b040d800f0f24030b0551544003000c0d401400d40881595201001102c2034010310200c0b01d40010034440c500c042c16034024003480c00610b0342c8891086d034414081440f1000c4104120380d0420798582e585165925402603071070749841b800c40590064481c01100601c03205050100c010340c524220002c0049806080506840b907801a0311111030b044042000c1c8002d501400d110468854640f400c2800c3c803411031900751034100300e034120082d19000070400c0e1001202580084c00504010f0010714200313240c03035482c036414087e01c0e181c58040c40581d0320303042034042c4078101c41111960009c8c0b54140c12a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 927626735 1250 927625485 927625537
    0x3020301050403050909010b1c090311010504081306050405030727020d0f06050d0209060645060403030c120e130914030a051b03120c0a0801060c0506070305060105 72
    0x2500915505001b150240000544c0c2240e490030f59600f0008905140c084c80c040c07260140040405502c200d007888041c0d84604504442445541e210f00d00c55110b04c1d90f50001c10f2000c0d4651121940503c00f0030030200b2046c001c5e43c070042001d008448030503050f100e503550340703410804405860904141505101245210031182039070425030380380019200400c01c4640320001e001520010100180d0010070b4880424924280701c002441c42030101e07996441402e080c2c598a50100a9000c2d15004410403045170f070b645400d140888454001084802c14039140c034580d005012242c4446010b40070655000a0401990250541c00c0c4102c0000302450500491480a400200711842e400d540403c40090b030a1800a0f002044490940b61a1145814024580b041c8101c01d00308001c499140c1c00b003408201000e45a40003550701482c0c83d211140e8844203881c10007456a5016031250301040450b00103100800d41c003003000364200742036190204540d5682e00050790240324407c0082c03809641010030f03071180 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 927627985 1250 927626735 927626737
    0x5121303031503031d03100207110906090403090b0d110f0d050a0b0607020405061c2006070b0106030509120c0109061d07060c1109070c1101181404060302030105040305 74
    0x418826102085030050850b51041c0300141c501000b80811550000c14000c424044c500901d4410020210382d070911800c0710f2031051780c0000c10200c42640901002400c2c0e403801d4921940d00a800307541b01e00191400741c5008002c0c15142c410901c200c40d000800460040321038210608d40c81100d480f05035141c0c9505010010380d403104040740019850000802c1c40740c2064043d20701044801000e590a11041c5c0c4c080200809001d40200e40c04150b10b0004100742201941404005003c0d007100700030031440c542c1131614800300c54412803080108020100c00200541925815601c00c1d1400048942d04d214005203815104013400080ca0300c00706144002e03103015004265468400c500500040e0448540c03001000311102884a942e00b0208c01800704500c19078910448138002d01d818400c990300c0e0008200f03031090590704034001400c045054400c1c0001644404001a000c0c079000748401c03056825441e02e206280114484280c1e145030f100b40c1541d50350444400740d0f40081c02001281402e19014200d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 927629235 1250 927627985 927628021
    0x405010f03030315080717030d0c05070210030605010c030302030a0b09013503091c140d110d023d05160f05040b030a09120201051807081c0512 63
    0x60704200c0c81e4401103840c1004d040c1181c5038070b0300600da03441c280224805a0014503d440c44944800d202c3c0041254280c001d00302602c00c10384401d0759071840340c01400990340700031000200341424080d04201c2640e02c010b82d880429011301d00161203489a40a00001c1c00c14010415400b9082c40000304915981d01203020102800044010852060000c247d080f0785148050141c903400501c100281d0782005c0c6001545002825580b01314000141d6407071401401c4203459803002e903c00300301200059000240082e000c4600c400074101170284c3c9200a640c0e1000c44100c94002c0240c042d0241c4400da094031400700300d0b4a00040004010120707002400800b0101d82c50319100000a80b0042041c0c040c6030495041d4038130350380d4186800e0401d00001c01a904c06002203090a40d0394501001192080d103034201c1c2080c4580c008289400c00031802e00210750805001d40f04c5411150081107603000004410840c22400c80c9811451181c81c40b0070350302c5026890b10b1074150400c1d2800c10200c00007413441100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 927630485 1250 927629235 927629237
    0xf05030711090610090302101e03020d14011206090c080102070f1a010f0b28020c04050a021602010e1519120203100b2a1513050307020118050405010f0303 68
    0x140303a54864040195140c640c0e1301050206409103800c0c40581800c0d4500003811805007841d00320039688400036007010800480d843e0000342d000c0f0307201804a219014aa50800c1c2003d01650554105040c42103600703035001c0c0c000d0102d6501c403140380800803880100002020b40c50001c5440d40c090b81050000c407080071208a460030f154183d9011b10342200d140c0e141c180c0d61540041c2a6050609540207a15407104d40340300218489a8240c01c0983c45100c403084c02c0e121603601074201c4410030345c184410b81e07001501d0360b0306041c014440700803403c20340a0044540741d0240703404203a01c00d484020a6042050900007082860300040d0b81c039103240f800c10501d0030b084541d9034080c803a07802c801e100000c900003520441e00b1808144010001c2d00c0c0031501030030300c10031031481001a02980400c20101c8400010840420b60400034038200040041904280c1c03005100300d00c0d079554202c0b55101900c0c1d1280da60003e05000410383d914100900c5d10340d40d407000c2c09028004110035615480044c6580200b403004030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 927631735 1250 927630485 927630499
    0x2220b07020411070b0c0a02070f0f031a0114010f0306051f120209010c022701080d27090c0507060f0902120f0601060e0d080d020a02070509090a0f0f05030711 70
    0x102c3c400030a8022205445d800c41c003d0708442d21410441da03010362005284404500c115a40802c0c50410034038000010b141050589c86494038624208107091041d0050040072042c0c01c00400c0428040700700c41e030342100240307498548948092400d40040140384c00c840d401c201c03000e0241c1d41c141c4003410340e031045d5042d41e1600c3c80040004030a00080c0d00c0380901d4640044c01d410301d550014203005551200c0da00a1404d401c42c039003076103010381201c00026440780619901252148100e01d400480e0003448004240203640c205a50004000710440240b20340f036441aa0f8001d1524062300c00c000742c0e501640e110340b040c4030314900c0ca83c0c0500580310103a000d911030a80c1c440c0364405000c00248414003843d56038041c0600d0ba29002c0b066482d5115404c3c070a401402084600c000201c45200a114000f9034000068890220703010003032500f00a17030001409a9180350504c0341c00400010180d500b180e002014002c40602407800038400c040c001030040c082c0c8000700300304042151040003407007800d4082d9005 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 927632985 1250 927631735 927631751
    0x7032301150201240e0c04030602130e01060c2a0b0a0f09060c0203150601030e253003020c0d060b1e060405090a090c0806091b01050d02220b070204 65
    0x10b00003c0070130b1403025000d0700200d04224a14410750206c6e404100d1018250170242e99840740d83c02d83c1d00103801d81e06401f080349010300c100c2d00700100041c050145841c080a100c0d0041c2c3da460140c58031900c4207401e20004514110340c40003400c000801070079a140d1141d8403246503942c0035081001007056000429203031f140214030107200b030120040c40c54004005009842904100f8030b560f0f000500028100754403402468012441009680c44802d0f4401c0da4641d81648401002c20810031138022060280411512080d1b074010716403010b407110000d915042c01d0601500e416840c00b0100300c8079a070062030321406a014040b0075400305568100507110039201c40f0b5a02e00615500320201c2407168400001c2c4014000703030a103060101e40c02020802d000079480d8441d201c0c00e0f860302c41a84150456030180c010041500410312282c99110b05401c118960707074600344006001800383c40c110b00d03034140d0f01007186243d01051007440741e21002c00c071650315071250b100c01c8400c009610030b05c8240e00850808140b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 927634235 1250 927632985 927633011
    0x6161407080d11031309020a030902190314060601230408150a050a09080f071e061b0c1a06061309050901060e060a0b0310030c180c03090b07032301150201 68
    0x11a401c8045c001118414507040062640c025044040c1b140c003015660700354900162a040b00107581c1c0c5e2050100401c0d500c0c07451800d030240c00851803145c005600701109008403640c100020708415030600c48401e00005030003104803a540540e510072641c61060254490645000048040c02050400005d0085540b076081100507212043e80051825004000d181800d61484015120b0300344075414440d420701500c8030584c0c07040e88854040c1d03031090f5200781c000904090305801c0c41003004513042000c20401c0503291002d01590086004062103483c0b800600e040e90b54400300e0f003103c8050803c0c10419611354903100d0003400701315007030780c01e0750718094003c41e91042030940c1c1449400002c0c00310b40304909201c035055540d04090254940f2200046010002601e0b60700c2040c083c1c841c6119001040b941c00d00410252040c3c6030b851401c0c1450015200041440341200a512403140d09020403038dc08806002c0560703103244004482c642d080c0340c002160503010302012095003501c540c0240090901044 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 927635485 1250 927634235 927634237
    0x31109191a102d030b120d0f08220f02101d060403051b010e0a0306050403030b060408031b0c101101060e07021e0709020304030503180c06161407080d1103 68
    0x180c0c80c071280000c140c0c03400c044a00300e01541e1030043d1441c0106203200b148012071001240c8007207a8450307400c2660401030099000000c1d05600c41070b07180141c214203016480304011803a0064965648024807800c00900051402c0081c44039070181c0301e01c40004595a00429680095203d0f0b001c0145803c1c400130640b610b00d0685d01601c0c2c111000d051402101c0c10700300d4030032441d54520381c103001001848400640e1452140c030000d50051030040307168a0940f40007812a60021044c600c6414184018080314070000191415040c50001d081c0007120140750711031800039054080c80e40081c1d2099105121035002e21b010501e900c4100007840660303140d202008182104695902c016844042c103c1daa88130000d45109841102405844006458a4110059074012101030b004200004240a070b03e074884a00c08100410070030103824040983c50000d4218070803251200e60705441c1074060300034401007007102140400c1200456100568884000fa2100b20020509000c140c98055a080341c6c10080 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 927636735 1250 927635485 927635507
    0x60f02070b0f092806030b21070e1015030f091707021e030606060f0c1b2e0e030c0a0618060e010503040201050c100c180609031109191a10 61
    0x381050458070b0410004074010400382c1c84240c0d001007144500003451104409048d04903e2400c0076000040c244408010500009040240c1101801d04108042a0031f01011030700c00b0383c0352401091500403000c024020b000c20308405452254209541c41d080d90003400103105482c401d4842240000410110381e1400200582003a00f607004080018014a84040100304140d06c2e50718250602e07464030b010341d2802604100b1044032540e44c90301c024051402004000d9120b2000c004600b0703200c06004004c00800403c560101400610314a03013015940c10f0000155008001d0300030100e40d60b45100040c00b8113500d00301c1c80340e0003040c0321f80454180d10a051441c880281a1105499030b26140c0c01140d05501243c10103101e4011000002e0701540f150003440148021030356080383c3c880c8943c000c1080d071000f5901110074400300303a00400c0003c00306100125402c3c4210b42803092550f520040070f4400740130b180c8640e101803030b02c8141c1e01e00404100c002c00301c030344c0700380c425521502c3c1e138240c1071f13416a8030781d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 927637985 1250 927636735 927636799
    0x9020a0303050306130204292b021b0618030a02030a0e041b08180102040602120703020106050d06060806060f09061003150e0906100609060f02070b0f09 67
    0x414400e10110380110000d607041940504076208044400e502c80040360001d40004101860b030740e05030741069462034444500d0070800200285083c260054402c1414111005030030008094892081c030241d0681c15103076030f2b100c4080e000c251012842001920303904c0454540d28002d5041c0442d988620000003920100c00c030f2900214600068000c05440c00140c2e41061580240c0720400c0e20744000744549084400c1109807600005410008501301040c40031b0048501641e10600c01001502d038005800411403031201c42d41d540d91415410124090017290308a203802446520030101003208680c445411908201c040c0c1d0b019072200400c01031894200e040d0264031144d41c0000c01c0305072500344048519070b0518240004c94144c0d140d80c2124002d032550007260105107031020020620424010a580a01402c02e1441094104a805803812440e401a02c0c1000385441c8000c01140c000c2180e18040e10043e549030b61112050740c0c11554a900181a15021394003020b00c0700c2070b590420162809400b00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 927639235 1250 927637985 927637999
    0xc1e040c3c2a020a1d040303050c091513031a07170c03010b030a06050306090f0c0d0f030f09330906080a020d06050402131a0306100f0e031005070905040902 69
    0x907940d00b0140c40e00204001e99000581c9403002a0901082e100c140c0805d0401d40900c0040c580307800c01904542c0000c107102d080400c208120400c0350b5416607a070101403001d070b1159031290030001d080803400300c103074000420b890490300124020b030100aa01500c1090555152000c404600356110704007035003a102100040c40038401070060440003805194007000311507000503201d0703851001a141c02c3c1c0c00e071124030454001490745050558280241d007032600084c1e65140103800c0a54030381003102c000030000f804102012414900316485514054028000703a05603020f014034490b00081005024440600c000d082420303101c0d0100d0117481c407441140d442d0b48903401c1075903d00802e0f070040d501c0300390510041076039244040b4160f510340c40540440340600844001003400d044d101c82c0502c0c2c01440242606106200300455a84c0c1c0890010203400309103009043c08104042c00c1d01d18407003070b007880b940c140074200c1d0300f484c1c40c0c1190b40050712071800f030360300c22000c6030b6607100b40002c545122002a41000c2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 927640485 1250 927639235 927639287
    0x30309140111162a0501090504020f0904090c2301030e0c03121e0d060e061c0602090d0803040506070e1002250308030c0306030c1e040c3c 61
    0x1256408114414056405145051141001d54813003500c0c00c1100041440f45030024003455900000720400360405440851030450701c41c640d80319a003e51440248143d440d0200f02c800c00c0440003038040103110031161000c0118112a4035403e521508501600007490440312802c4c41e4000280061082d5001d4007400160888400c070309019030007007006243c05540c80b0461901007031031100400c10100102c3e80060000e05210070f170400044080e128030300c150001031340014020060741100c0c0c400daa120310011390303071009070000c04c12590003040050621f0300e0202c10803051001c04a5120310400166841c1d607031344180c1c0010880c5007180c4032801001640002340f1000f58080106261714004c800000070b0159a40c0c0ea82d07111500d92003210203c0b02044040280b0115080402c0041042c82040307612440e118800c9441240d142035850406200da81c6034201e028002d4010101c003981e0b40004074060081e01c2e160200b0700c0002c0e510041540803180c02003083c482091191800701441c0c02d5103602480c00078 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 927641735 1250 927640485 927640507
    0x1224040308130821180a0c0b090f1e010306060809120c010e07081005091506130b090c0a080112020d080307030f0903030b030c090405070b16050307030309140111 71
    0x1c0780b1504031010301e070410440c20500075400d404202074184448800451a01c0e81c0350426a59145900c0d4415a001c80040c50018024012441c00d85a60348030054441400c600080c90255499104d40d402c034402e41c0c115640740c80d414402500c83c15003a00c0c1031201c2e95440d5012500080200e90700c0c0c60a03081000050031030f0900000605950703056000104080b140c40b034490313041c03148540c404141396003d403a9107000c0f600d090240a5000c01040d0203080340c8814402c400d120007a0040150f0704c12086015030010b40381081d07000400100c2c1c00303441743c8202d147c0010500b04561000b2900c0300450070500000a1075401d240303030032905a6001d007041010302c0300c1c4c0c5d03600d51268001500800038981c84100580d18505203100d0710f202c4034000d54010886030181000d00d4100600300c0e038805c0c0200d0301c0790100000f24800046000c112200440050355400b69140c102c50b010350584030040c41404000307500d43c1403543c96001038001c9030260106d400d2240c2c080c15654221641020010703ca00c0007400065030320 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 927642985 1250 927641735 927641761
    0xa14090d03020f040302090c0a0909140c090d050d031a040e030d0926070c061805060a14071101030b100c030c080408150a0501050609090103060b06091224040308 71
    0x90441c180044c00c054690740042c080c2e5504650380b00a018010401e00310041c2d020200c00010700c00200f003000604442d40c4101c4084000403c510f207100000a02d1a915031512898800110742050075100d51803048440107000d03290751181000c0c1e000100b030a003d2945002d1083c003c00e081c0e008011407038420400c03140c5c009048104001c0d203260003c50b2a00e00340424100105e0030581020020b203554601a2800c828000d1303036600a41b00300300c544403081c0ea2180072159020140c1e0700480304d0310740f10301034540100c68106103c2c1e040712040102003174005c1081740c035031f4400c0027600e4243c0f41849007400c43c2043c40701c8060541081d00000300c210b103010001c00e01641e42c55101c00d0248040600e06610760404c1450310ba601a07480100384541020400000070700d110701c9015007400c40c2d21710301d000e2a4400103014048103000c0500f0703003030707462040e01c080707641302c90468250013406840c1c420350f004440841501c5018041d403c41500c1d08000c000c0803850000c08150f48155896100c01e07580d511040c8240400d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 927644235 1250 927642985 927642997
    0x3150503060f1e0406022709241c050f060c120403090e15030c090c0a08100909050a060f06050618030a1b060e100504051e090a02030a14090d0302 64
    0x7442d0f05600700000c81e10000051403056004083c0969500721400d2058044403862102c6002d00110340d80350440c50362101181030300711500019070044010503000504480c07800303080032076108090303a00c40c21040ca0b035951000140b0303000c0c2e03080e611019103101c0c0301da480e07a07804c69007582110405c0240d81040824a040d0740d4120f8024601207807101e44070460140084015101c4009070000d074241c1b03107013500d02084015070f854005d540700c0e141d07424518041c14060041e035519109000b184000117000c0e9000c0f01480008111000c400d01c10a40107061007a214102c2c0202070310814209805030f6201001030084c1c208a52000d0003a42c0341c8012404a4404031000300f103010780c1801252001d10100c2d49100603c40d1408681407030310340c518507055020b051460406d80305809186010f0050f2001504a02910103d40e01980d000041e0403031040411001014070940320b500054060601c2a88417071640079600c101403410701040340441e1450252001981101c43c0303401a4084076410b49580d20a80203852 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 927645485 1250 927644235 927644251
    0x5010b03013e0f0715050109020c100c120e0145120e010c06050c1c110a0e01180e160513030222050c0c1612122604020103150503060f 59
    0x3055490305c00c0c405e42558402c0c0d200404031600812080d440b12414000c24980c5000310500b04181044001d006d07214410348a550561b490b03603031110305c8006000390094080d0300035003c00445091400103000d050070104c140940601960800091601c210000081c2e07503494000c5a00c03101c2c040c04510846202d0903c0b89102d0400900c001c1c0500015024060b0134000c00409481c0ea4039048100c210000141c0b401994280407810030400707210b11410001101c0d1140305502c0c03e262034802100041c0c41c00c1403003c9101598001c060790000b040c46404402c4c500486070b810300030b00402c09204045490b40500310000340e116a101000704014a03060070222030074095044406584030511000008035071040740d05428004000032030407911030b024014917410000c0300303403c2014039040c000301003001054210018041082d80403004c2c00349009a4040c04604002040e040035511229011896208103440072404030b0701700f0003044803070456000c0c1d03001601d1010f002842144c0e43c0b0030b1030403062140601480 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 927646735 1250 927645485 927645503
    0x18060210021806270607020d0210030e030c0601060f050307210b060705011b11120304030507060203040303230118022a030a080603010501140d05010b03013e0f07 71
    0x10342aa1180d40c060100d00e1003a83c0d04c90183d044524242c0c203036001500e0329902c101d20400041005944006100f5030f01c1c1d4055610f403298401c0114250014201c0752000e000504c00030680e61408440003030401c0c16035596544140f00401020015106c03800140c900e1004280981e8a6114810319005601100d00708154007103550084100132506980c00100c085e0390594543c032028032456001943c0b141c01c3c46262404104000310941c4d03c940300d030402c12003103416080010128007414481d1054442064001a08544da41068600074000304407102c3c2000c40cbc0c0201940700708a00300c90b5042a41242e8403846040c648041e42d0b40d40c0d90080d4440e015550b20b851091400c041403050300100400d001d1046001155915600c01024041c107500925591080e81130100611004d0082880d41000060503100c50340c0305840b51800d180036150343c5403802e80661802c41070881c4d50450807090b6100902e80903040b03a80c02103245080722180d10400c504801001e0420500c803000c1c0f4020024907400340034071580 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 927647985 1250 927646735 927646777
    0x2062205031f020901230d0b0f031c050d051305061b16051c02070e0907030f0206030c0c010905010519020309060c0c030d020a02031b030a09050405341806021002 71
    0x89a00d00004003254806e01c00003160042c400040c9101d80c0d8400b4604036415120040010000b980c0c6022800d03a00c0f15000782d1100460489009200b52050035002410902c0306d40391154070414124000b000c252098802d0b0404582c440340080c3e4510300d07510b050101c07a40381031a0311409054074560100c0481e000e1146101c100c0c4400040c0308071302c0c0090859805456024076244803420700f9500900b000b1784907000350070100001009548018281581500d07419183d90351065080c1043c01001800304440d400d05c1040420081c040d40001c0c0300e44045d20460010360105041481203000c201e800513056880440802c12040d64074014100b8a21a102244d03d0402254110801d85e00302d120300e035015920200f0602d100c0c0c8005020f03002c401c001d1400031810300c2000000100248400e108007070040d0b40d42c001040c0d0030f2002c0070f0100500c1c14010706800c04002c0d441d00d1000003032945e00102d0000380c14a40b451641e0180358117030030112010b0b035000301423001038456408002d40c003030f8042142002c0c05180c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 927649235 1250 927647985 927648017
    0x60d02030a050a02090601090e070e0f040c0f020d0c150e0118060e0d0c150906021e180306060901061b350f041206020702062205031f020901 62
    0x11009442c030400290510425610610094000c058441d505010080c102400009603032009107500c002589400000700c112440498503200e04040c0580e00300c4d06104655480d039411420103c000d0441e03608440152600204c226041c5980200c01030100c01d4040c41032100c0d0003150000354142000c3c00000030480c82506c0480010f4400c1034040780e40644441040b011204c06004091000ca4541404140c0d0314143c2e40c2c09205001c030220704030006590341c50020030300010303505035203041c03103525102161080c803c195000300ba00800450f401140040c0106078640c00e01090440c0920000380000300c55901f440c0050b10081004030004401e501c03c1d08014022945410003080c0300c18004079044401c80603003211440140308000c42d6129005c0810540001b0704910040341c040f11440b0b842400408000d00e0040040d108031240a94041d90205801d86503558021610811107000500c48030721581e60411305d078440c041a40c21580003c0340503880b5034817801580040514200502d4060180d00030380d40 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 927650485 1250 927649235 927649243
    0x6031009050703150b0105030123100302121312081e01030c05030f01090302190c08011b02100501060c080904020c0706050c07080a05030a0c1a011401030c08060f0603060d0203 77
    0xc0070389655210060800c1800800f0501c490012000c0d00e06005954401001070b065110610843c0c0c141601d09402c2580710a030305014110450000b400c03480e051074402d000502039000094404040030303500d408a00001161241407840f1588607004850b500e40e046000d8890070780c000d040c03c13040c0e0004601c103030040c406a68440d019601c0703020005000e600b807800780340c604403072002c130302031140e140c044101c011a400003075109a00c03001d041825080341ca54600406c0040280e07201860715820305610001841d800007900c006002180d00300e03001100310507240001e43e0000c0c07259401161220520502241c482d030014003c1b00e03005840580303044030182d103044c079001e020b901c00e400007000400c6d0a011440244002c1005000701d2008114a80e540e40f6371607101d02c9032034030304001d003d240c400c61000c00161520320720114103801d11050656075100b41c02030340c040b0b003401c031140002c2c03130480c440501c07501682140b03001e13090141c219900d45401c2014004c1580c40039248581c0006444185001694200 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 927651735 1250 927650485 927650501
    0x1b03100902070602072a052103031014031c03020a0e1305060108090c2b0c060503100e070507020f010509040c090305010b01030501081f0914030a080a0221060310 71
    0x10f1001a035648103801c0900039078085000154140340c07a407a103a8801403005190000391407003150a03491243d181403006448804901981700700b404080100301507051141030b004120392500d00b04501c0e0368211402c058464882145224040040b001c1d41c0c10300038800e601401c0312600f5400c028500c0c2030007400081c95102420b0030680610746510822109591240e41e0582040100c0f000340500c1076150300295440c216180c0c8008a000050301d211102400ca120049030250009001000140c80306001805544211691070021444010000f016082407480030310860155880a0074414540d003040b001d240130700c0c0414104030f4107001580407a503540c415a1644580c980380c0781d0100c0d01d0345c60001e00f510b405952a0341490f02d07041c0100310b190408208810301c0900c4541b60300801446001100c003c151814000d42842e034002031102540000000801202c0c840341c495448030f5460184000903841080100c0d40f01070f946031410749412410854041d007180c401010f54120500103640201160041 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 927652985 1250 927651735 927651743
    0xa0804111806120c0d0201050f120c1213020a03020f1302031602070503150f0405010e0d030c0e0306010302030309060d110a17010e311505010504141b0310090207 71
    0x200c4140245440c2450007981c2445088004d13150302c40f4880000346880324110b43c0030381401000240c1858000852003260a1034951500140403800c1151224104c1e40043d40747c040303a0f4000c078021821175845072802c515042e5006013422500750459003030200118807901c0091300050700004803001c1c0e03210f40c00903521480c0345041d608808003c400000786460361503840701c0c0c0650098046610100580d08000d0f5101511691090b90394446240c41c40c0140351407004100c590044101000e6882c0d17154001090489480d540c0c041d15203a03000030075480312400c0c4402036141d40104181e41203030401a01502410a00d81c40025034040c8100d00104141d1040056a000030001c690350100a0000100c5901410b5101486016483c011800214803c100302c4450404c854840258035074008560310b5070b542c19401905005a1001c0a00c020081c1c8420300820b48030b0b82c1820b103191041e4058949007071254900b000403c110720076120401686034005049031401e07800d40c04012413a8452800240354003446 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 927654235 1250 927652985 927653029
    0xa05060637081603020705070504151206021317070312020c0d0c030203120307020a110406180617010b0f100905030a080c07170a150b04060806091e030a080411 70
    0xc444054554001100343d12801d040c814040c845c00f003400060f072003060301c1b8161400110100c0304007804a0030500c0354032210340c0550803454101000322a8020340441a0064148104c85454884200082c06a2a590307140c0d0f521200003040440e08403802e01411a41a0050703d0b007680844000c15800a0f400c40c003a1030145024030b0810450a0404c4a80c60076024011000e0960405050081d25a401004094800400d5500e800d0283c1e80320752105006111100d100340c1c03240d080c00d034030001500341031040b02824203000c81044c06010040c090303d2443c0700700910300301d82c1c1c42d045000c22040d1401542030000b08141c1c44008221a03c0404c0844070617801071038002e0320760340c65880440c5400c80e5034114174540501103c640310382001c0080d100c1e440725840344410500c4c4100c6a542e070000c0c8151603289510500f000c81c0007800220115145016090f20010350760b40300c24880d040c03021050f001d4403e08090707000300b140154180c89180b505030803602c2000075040203111000000d1802600b541540c0c40486 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 927655485 1250 927654235 927654241
    0xc151e06050f060a14090402040e01090902040f1503030c0516170f150105060a120203100501020c030106052812030509040c0c0c090b060c0d0c0b0a0506063708 70
    0x34010740035500b101d204551043c58808110030090441100c0d22200004020100d900703580c2ea5110b4041e60041d1017480030301702c900d41c0e45a41d0b2002070705001030168040ea2a24521a40c1c080c2c441c060120300c0030340d81400d0352a81e807542d03504541400d800701c01911580200103d005180312444914802401c1c0080e00140d0624041d40301400c0603044120001140c0c00001100901181000d6480c11180c0880c0ca0507260005100184d03604030043c003140c2c1a8610000070442c420085500001c1641c00aa080f1040400202d00b07141c204c2d0341c02d000e00c41c1c0c02035541500c0000001000a11101407400031420350a4680e150140c1052084040044000c5007011424a040b41420311840061002d10f1418940fd0329013a21900c80d8010540031714080385c0e48580d1840303025240c0c0301c110303404815a1700132500c944c00d6500c0c0042110b40c0c041800c581601c0c001010500010040c000d080c081d101c01407046260455201641076800425407240f0610304e20081c40404c4004000c2c400b90384200c50b521405450300d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 927656735 1250 927655485 927655489
    0x405030306120705030c0d0f0c030804080f030f09040905030c2d03031b180306010b030406050c04080304091a1e0406061106060d020613091410060c151e0605 69
    0x310300c2c25031000d19034003409081145603030014004000503c141c5400080e03102a040150814003030b402d0207418519420800020489807100800443c0c3e42e05041d15003d071030355500c0b02e89038030030b544605828510900070350341e0074070301a48a0100b40c0c0c400c07011a80b80c070700c0b10340110381040347c03116010044a1080d9030402454000032442c440e1180520302841c41c51a244a01058099550175061180d05022070300c10000541000c404280c1400102206d40d0303981d580b070030092940d0003110110fa400e0b0510022402c2120400241c400381e40c0700d00051801d0070309007254007000341014902c0c43e4001d90045440003084c1c07540c4440362001001d0300810070b00e98000380240004d45070700d0b03032001c0d00b0401c004141031104040490301a4100304111143c2c59420090300008580d0701900076070740001a1400700c002903e11141e4010a42d50407018011501943c2d1400522100d203007500c6983c011078120310f0300304001080e0310554410704038080c400040481d4030740c01380707a49158003100c1d00b030702d041c5d40702c0050241e8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 927657985 1250 927656735 927656749
    0x5150a0b01050301050306072a0506220b0a110f0703030b010f02120403021c170408010c0905130b120313051e220f090f1e030e1012050405030306 64
    0x440000c2c284245154984004681c3da00c0b0014198000c002c010007034100c5101001d00b035190603212200704012040d805090550702d81c0b00a4032640c81c0e050109440b184108080356081d80e83c650414401c681960350809410082c00c089103000c03050000800420f0320f0104a0000303003c500b40255000220840c0f404005400201d900388440195031040000c8220100280100c800380c030b50644420180c2004107a042c0c403c00e02c0c0b0040103010100c00c4500e10034040c0c450024104840204d00244001e4070003050035110543da038060240c0203c92807003046091071192708108024400900003035600d01c06100a00c0c195000040710780015054018104900c2c5000c040c2c0e010224562a0107040c0c82000400140100c0180b803c80b0650307602c0070104032001205640040d0815080b1203003031140440a00c4c01d000b903283c03128002c03200a0390702c5028000d03951550080301e0590b5850785980c00c0400b841c10402821408101700d600c01c100f520f1503880c10710407684c00750750b014a00c41c100541d03d904104040040d9 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 927659235 1250 927657985 927658001
    0x9050a03110a0c06111608060109150503190c0617060d050a1b1701060f050d030210020313380c070c03050c03011b1202090a0504020a21090b010e09070305150a 70
    0x217030006d601800e118241001ca0b0003811107415500c001944545d00781040781d14805544655454004c24500202544040c840c0001070b6108416076408243c8468094030120680800c844019684800159080c100744110103040740c0240c2c100c50006819680320714151200909140c14542055002c00070321850a0720310760480300d444020b02485d402c0061041029155104480c840d004d2407052805143c000d200fa0001001e01c4801959a0300d40100f4901c0c0c14001c04800325100e64201094484480410400a18403580000200f0458441d424840c06a200c0984480c10602c010080354000030440041302004500c1900500010f0a41800b050b00311005801200f0a0415140c90005040c1e4806c440d19003555414500584501c400004901c10041070b0308840d800ca80b00080039418140c00000b60b00342c0710040d00b82046e0b0004e00402c6201600ca1808009200700b00040040c0900c54042200316807000c840021501c8a950380c0d116203140c0311029101e68a0384074003034140a40b0310024028110 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 927660485 1250 927659235 927659263
    0x1302040614030a0f081902070501090603020a1704050c1806040b010203040b0d0c090b0c060f07091203050d020706050f041406010b0301050d060e0f03040905010909050a03110a0c0611 80
    0x8019154440820b0300e4003c11030004140b0715885402c1c60030482c240c42a101c030721051040300c01146800c0701c0c0107580d402c03407030168a01155910000003001c034031034003c80700c40c03461079540c3d200c900a8040e482c00107810040d00443d214041d824170781c4d45580340c18501c40074411100325071202c00c0c01c0a80a00045a00c031010b5141150010403044c0100d0001c801140c0b00300e4481c907400a00030800720300403a070324075503500490380e880b0000500c00d22512000424030f0264007800340c5000c00c0c1d101c0c210203a64015141c0304243c0b0185051801101007401500a042c0710303085c40c13001601d0030308503a03589030803604201c3d03902e103903152280d0a10041c85100664000c0389410341005150550410301100001d0005104043c440c24902ca915801c000da55007008041041040031200e080d00b060341025129001070044000c000c2c680800040d528215000300006130340c20501411211090f610111b611052400881005200f440d103980e00050710301c04218004c00140c1d880c28188035499541a04080c2c05191a00c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 927661735 1250 927660485 927660509
    0x60e0106051605070e0a0504050d0c030906180302060c16060201230601020a1a0610020a380a0f0b0607170a18080607110607080c1605030313020406 65
    0x30081503040301c02c4410302c2002a901d80000302003860700929102d451380280000101000622541c80030980240340918400ca0903220300d055042c90403224030707030a5580500040d00f9000e0801c2030b58010010642000082c00e4a22000c9813a0703008224181c0c040103101c0403c0d1300909580c1c01ea1402180032401401c81c5200074071081046000c7c15180000c449110403008030340401042c22a8000c101e29440680c0c01561620100082c0c900d141040c03004440f1107000385070400e11020300d40d1010400c146181d51056001c0030b03019500340020040900031000c0414212802080c81c2c085001c030058510a94241001080503400800c1e40d0040e200e00050880c01a407080c0460303400183c0d01c3c440d15950002d92900d40d9141c007401001210007100701141c520020b240c40c1000314402e0404140544100c40f02e40768409800d40c11007440ba59003000302c8100700000c946a02140c055400e000003008000d00446d6001c1160006071900e50950b4800d49900c542d2a101c251a5030441c101405580e004008081d040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 927662985 1250 927661735 927661739
    0x403021c02010e06090f0c0a030b010b180d0303150503030c031207020705120c0301060b1617130e01210812040201020111040b130f06090303050903010e1e010f02090607030e030f030f0706060e01 85
    0x204800d0103000d011049133010030f007584020b417031001030b0314400380c000c0c00d17160960110b00340500140300c0c0d000700c161082070601c070105940c2000403c54500001c514019483c0c0069400b442c1c0803d84081e212208501441c54000780300d681d64200202c0001e0310502822010083c00300b014211000c43d407000c0b101000500840c040d200280360b07501c00c170580046481c25450000804001d01d489a810b130043c0800b481840803c0c0d010b107042c4c1490595084840404440000f41c01c0034900120420b0020803804040200304aa070240e003002c10341040c03041c0000701c6d6042d00742c104240f4940054111110136200440c40c1c5825003400a5454010711a03128a161100d00b0120300800045940c0409024400001030009039601c00358070004480540905079540d8001d6501d000042415204418a1960074120004581c10240c4222910321000a02040ca010000d95040e28101403041401750301d400b81410300b0001d6a400c0c001000ca5420442d00c0c650341c1d0321a49061011034405420165182a80c0c3c001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 927664235 1250 927662985 927662993
    0x4050f01180f0b09012624070c170d0e0a050a170403020402030a0f0f09260403140604050d110c010c080c0601140a0803090a06050f04031a0708060103050403021c02010e06090f0c0a03 80
    0x11f452802c0030011224105aa00c43e0020b944600c8150310003040b02d51140b80400c10490b03620302900d147d019026050100301701500038181d1301c130070725003001d40181c0000f42c00400088040c061000c0d544843d01e00e032801c00b83c0d2900050203c4c0c1044841070096078486803c2100c2509038460108200f4418a04100421003130311045110b01010311079540380c0960501e01442500701000782c800440d80b204000c00c00c05010386040c1d840303610550b011110340c422400c5044145001e4038000345003a20b00f80080c80000751440044401441000050380c1208003007203003240300c20701406a00c0c06032030b0740b140030100f00c2c2c1c02d0000c0c00907511083d88190403a81080c8038101780341c1e4400100c0c00407038005181c52601c5090517000c006c0184030b2648010213414031800e120a00e9010003115920450f099180d140031527460f107005506652084600900503003000705141c1c112024001c44420031076540c80005090001c441106290540a64184101e54031020484580721000c01161044240a681d09403441c0e2561391 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 927665485 1250 927664235 927664273
    0x1209050a020906310b0a03060c0f11030904090f051005010e07021216081c050601030623090919050303090f0d050403060b0301092004050f01180f0b090126 68
    0x29044e00d900c00601420f809400d1a410207007416500030f00160140303070790307250840041684210340d40203d11100a0307525064000e6030300c8829180c0200107103107810740d820100002800d008030101c0714948040c0d5a000454010400e1040e2041c1056000174070b941442a1103400300b400829050840d445041d642c2986103d0b402660030340c01c0301d00d05144045003a443c00411a0003000c80f07010300b040001003400121802074004030300640f020b0324104040c2d604c4001d10f0350030f80c0c2040c1e40500406030b06c7c1c1c0c500e002070420100c400d034404280419503412680012007908400d0703041400f6181940003200384001c1d44d80502001d100c1142503401008200101203000d0028000e501c0b020788080e40d40c04a003030a94a0a41040035656800640b0040c0c620052001491203080482841c0c021380c580800128a8140452070605840240941002c0510b40b07c4009010344052944500e0700ca0311060311200301d40303d071142280030701036080340202ca014510000c100c13031406200c0441195480b803506404400d21003d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 927666735 1250 927665485 927665539
    0x1101021f1a03030c0c0108040c0812030a051e010e19021b0f0613170c1005182808071a0402090f01120308090c0901080d0e0d0c0909031209050a020906 66
    0x20a0402d0b0547d12424012040c11f070580c0300404a0007051000003000f81002f005621603502900d08000c192a84202442c01c0c140088445c2b030001e8081c1d0040c40030b4441903040030303070111468820280d60b51101ca600400e0360082d0f0f0001d0701d4083c01c18100c034280d04043c0400000d902e00e24004241c0ea2078030b003c4c4064800070b1440c0241ca076100c01550082c0262180b800c55600d004038104036920414182281c100401c4116064050003c440b02001c145080124a00c02095040c01d51a403000c2e10144205400726604203080b0b0304603e04010b101300017205c40c00c041c0400384140840207507a2030700740103101d04c4690041c4070841400f2698018800c0044041200851f241c043c80d016045a94803c01d292800f861005034950140c00b0360000107030a2400600c91403011020b60320100c882e444c0c80280100028144001090410240d0051142c08000c6d071011a072507000349460000c1031442120b5070202e801d0b41c0f07010b80385034000788240029800c0180d84540c10440550720740c0d072144c002c080c1125510400d0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 927667985 1250 927666735 927666737
    0x801091a0d060b011e02070e0a09110108072a020103140403020a0f06090212060402131a13060b1804050f0c03060d11060d060e060a03020604031101021f1a03030c0c01 73
    0xd01c600c010a82d1141721040309029000c0f083d070400d4a15044065a03d942a100e02c9012070480b000203194154640100d07090175521045404105501c00015071f200070000f0021020000400c03202081d80111102a695001100f0300b004000001313400014159040c000e002c0942c41003620a10001039400102004030f2508000d4400e41809180341c808040d0a082001a43c000302009058034903c030b0100381c0d00d0080d03200700d8201c0030080245d10170368107460071012202400350840000c2900e074203001403403d00241000000240903a210028a0740d2600142a072400300d140c07040103010b0a041c10b125068018441010118062410055881d0940300050515000d0b5090a0f011b208022100b460680303078aa0007031125440328620000302000f044688101350703a8442807004552035042803042001a240c0150415103480d0844d21081241c6075a0740089045210304032a00803012034070141e001800800903004038150382d0b040c0c0c1c21310546401c0000e46110790403c1100c20150ba80020b86d011441030b003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 927669235 1250 927667985 927667991
    0xd2a0813061809200c0d03050a20090301020d1d10020f071407032f04060506090904150207140606040c120e030706090c0512060103050d030f020c07060801091a0d06 72
    0x20044c88400c55a0340b0800102021011a100040300c0c0041024034581417141c2e82001181da448072900c054400e0201c00562100d42e40b28450704200c4c400005043c0300c034014002510386502c0d89050000c4960320f2910a84c1690a40b04081c3e81000a200e1105404400401982013152000c92111240320318500100a2503143d002003500c0d98050105000a680080724054009200038214031600d0210a100c1040c03102498941d4149c130706485150305541001c0e10841c1041603400030f0140c002809442511012403039000f0780c240d0b400c01d000070007815210f02c2c450640c01c0e4030801d4070383c07601201429032071186090100800c81940d004800320152410008045a20494580f15a00354480c1800c040d1015007803101041c1844680c4c51810101c0354255200340b4180c2c0403000c481e0f1641407c0c00014081c0d013025200124040c8030360415015540321040040c60462241019441c03d902a0712000114590340c004220700081c03886030032100600141c0400d01c1034003000008122401c5100c00800340d0713507 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 927670485 1250 927669235 927669251
    0x115081017011d1014130f02010207080d050a031a0f2b0f0c17032709070c170c0709020a090e0a020c010b040c020d2a0813061809 57
    0x3d4102009001c41d002e00e4030300001c5030300e0380207484441400c4a0000316041551403201e04141c1005148103074601881d41d408084250754003460030310080b034241d0440c85140300102d2245e00500ca43c0c5480041d44c3c55070380d5105c02999001d001d0b16800704011030f0203200440700c41101d8031502280385000104850158200741008000341e8a030035600b26031442280410100d038100b0101c0c02d190101c8900404c0c61080041c1d41e09050b041d0400d410005c504142c000b44040039004011101c8182d1981107810160292410b10740031421f4070030f00729500c800140e11b008840c0107000c008034003c0001040780c1021442c01840d11a0b0558582a61050b24105a8000750a2908502c0b6492003005050301126210507810300e0031064000c6d402244440f03195528001e4131076000e2505102c3c03100c12036180d80241c2103074001400251014407080401a0841003580400b80c01d0516000900700319502c82c4003881c2c0c83e0480d1b41400c03200381c1300d590080b20034000721985648140c00d551030380c28229044510701240d441 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 927671735 1250 927670485 927670529
    0xf030809030f13091b23040302090f0604060f1512060b03012c01060e0d030e03030a03020a020c150316020a0f080403050c041a040b0d0506040b01150810 67
    0x12045145219032540d001c502c8820f0300106880f00c0f011500041c5044c031841020344240b0100100300c2408a0105081c004803050414132010b001080d00090012282055980e030007145903400c0440b40768001c50f08100410000d45014410500641962084442c1d103604200b0f150081c0c1c2000c8001d80f0901c000e070382c407980340c06609802150241c4030524043d40c0700d507942c1c0703e801c88046043d110305c0c0c4a009081c0a08080d4410f400703005040310b685644410603040500d0a111414000c1d02c0c0079010041120402d03000c58030104001c20f610092640c00603514500c00780000d05003107540015610440d51504400340341600c0070103403600304180003c0d041c82d421900303500381d1a00c5821580103040343c0c6125510070600c51118050004c413405441a0307040c1c0110001080700315204c40a407103801c005c055804012506042e4440c6035980c0000e001c0b50391008007512180d00d03000d42144c0403200c03046103000501c014140440806450b080d5801c0078415030078510105140c0701c045029082007510303c201003803215 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 927672985 1250 927671735 927671737
    0x211d010e01050d0b030708060f0c0a09051003020d05040c1703030402090a02130312020714010305090a1106070204050c0301170f150c1917061503060f04090c0605250f03080903 77
    0x601d000307040381e54845d910320f981238031900701b00c9500c01d01c42d051100080148080300c045642d0413000340e881102d1542400200448000021018010542c0c203105000c3c160009104907030055000e2200d10600500d00720140354080d00030381e6441742a07081401031200603290420b400741c00101000d130158a80c94203426102202c100d941c030103001d104210710385542d2076402103400b00541d41e0f4503544d41801c2c40c00000540581d013044c3c511500c16813100500c030011400841801d1110000104841c2c9884030075000242690416a51481200360000041041704000e0300c2c030800b8400000042e0900007410100d0b181c84d56040c90b207003050581018000303014004030108440e030201c524840c103801e103114003c0c020700c0e1034a55000364040c251840c0c041041c900d860458034150b4481e42d52402d180d56034510034410f1160b011001c03c0d0704180c90312000000a001900c00601400042d03071803580380d415280c802c1c4120070461881c5000b444c107462001c1d0100c0c4c00d0070743d400079190f05420401c600da22808010761031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 927674235 1250 927672985 927673001
    0x21806030118081c0606020a020d05030d11121012120c080706050a05010e0903071401020d020a02030d05061804030503060d0b1f08010e030a0807030207211d010e01050d 74
    0x4001d8078402490304022103000a8030b101504c20203a844600d0b4040c0404d801c1340d0040c01840b0159000012000c018901000c2c00c03804c0c00d10550036281007041d20303c0c03c0f100781c0b03e0441480305c81810200314801482d40e0001d070b40703510042c0484442e1169251140416011036450005060300110494080b40b4a01640b054012590f2188440f641c580607801c04034000c01c02034880042035814040001403800e4144001070003051070101862070000190381c0e02c5800322188108961a5400b0b011198010b80f8030710181281151079000b45507034400903c00502100c1d002071060713120303d8001c44c0d8445041141c8060591250745070410b1556900c510001808d2180e03400002080a00c004042191a00e031f00500c59140201d164440700782680c5454130306007a10808420303444690700501c5400903551003210185e4000f25a0b080041c80c21015403034091002d245052009110041a180900355070380c40b415803041030303480d040c1d02da12010721900002d0491812403401410000e000c01c00050fa02429841102 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 927675485 1250 927674235 927674261
    0x81902071a01180b15090a150206010812030c090906030307020d0804060207060203030c030411120607050a090518040b060a1706090d08011409070c0b0f090106080102070218060301 79
    0x250481a5200a15040700d0900407807100c3c00700140b01c07540103c52030142e2241d41d040200007400d00c05560300c1c240c0040c0c0291001540c010340e0a04001178140e5104048800c868184e03011f13044940c101282c55281141455441d61040c1c410020000810b407620183c41648200b220080070070740325400000c1c41e5024252011f9400001140101c04103d51b0134018821a50680c00345c8640594031242681c41e80002c0310784030308040d0104005400503103800c849001100008089910040015112a2404a08450b040041000011606e0700303da080f1285034020071084603103454880c1011580740840e200508020310340142c81001c030302da03980c811050034040c1c001c01016070342aa48802c1c3d11540c41d5001d64804985d03010307400420907450310490069040c0c1e01c8908070301404001c40d1061214a460052003002041000e0f1248000244e29410490046410107286c0c495070400e50072075400c4070129441400300f60b00c10408800161680b07106c4245500180d14140f0042d6101004240902107115200c0703 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 927676735 1250 927675485 927675503
    0x6042d1505041d0d0201021806030408040e07020a02012a03030e03090d061a0603130f060b10020606030606060c0c040207020a0905130b06150d090c090c09030203060a0c08190207 78
    0x200922003d021025507542c9200701c6283c03020f400c1c800c1e801c0b4444d000d2115603e80030401c0c00840342c1410001507410620601c5990318055a8151100d6501000d940940050708242285015981c2c014080410b580d4016000c060940000c00e5640070840c910348010180b503100d54544c00361100a00c169038200e2000340068050b03488034038100008010005c401d08401141c52035810303943c28900c080d248a00d19071045441c000c0c3e040e4442e03420328940c41303030126401502c40702280780c983ca425485ca600b8141d160000c12483c109182010704200c0d00808081c0a068140040f0040020010704281d10301c0c0261070040e510051400829a141d8070340d0000703170105040106204c24018450080c000140c01036107683c50f141c48120030006001c030b07549030980e0f504a0600960400c15165072110302114450600506190f541c4d0303c21400b680d5000c0540e20200e28400300c2002941402c0c40620f5005000314003c0150b44002c0c2e802510590011340b004148a08c05500c070484d030907007035044844a640142d808 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 927677985 1250 927676735 927676751
    0xe0f060d05012a140c030a1d0616020405160e040b0315250e0108010311040b0904060203010918021c08070803130c050f0a1e0f090506042d150504 64
    0x2060f008200024150005403c41d0102c01c150b1941d142134520141c1c007000518036040c3c40106c2100c030f000c01569409a00c42ea0030f00e52a10a5032a00d00400c4503440840e444460004140100700450708018550481e11103489604072030580d2180b66021400011940010382017180c1010902e0302c00c5c1d024031150700420190510098050407035840d61205900c917840d007100d403040427040f2000d01da9841c1080c00f20b02100018000078078000d80c03148a0500281c0005810844400041d404600998043c0d848590000050000e9031884c0190502801040a00c94440c81c46601141e220115281d010b024840002c40e107200b0080b0302d0048804c025040b803035280c1c0301d040900c0740404503144400300302d800310f40380d02c000509418248030640c40820000d121511061a141001d480d102526480f55500c61a0344004550030741c50300d0fa00c5002d01410383c030020355840e08000740012038010040007501d4607501d0b00900c1c0d00c1c900f40b001b4400c030701180a03c01b0418401d0801044414051600550f600c0b604084003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 927679235 1250 927677985 927678041
    0x13080d09020907050c0706050a0c230d0c020a0b03070302070b07210606080a0903020708011104050405010b090a1202030a0b04080703030c080c0702041d0d12060e0f060d0501 76
    0x50040c060003295001850b49888101390390900c58840040d005411500040150a0240001d4200500b20b41031803510141c03644d40b4580350903c04011880408143d000c1000c3c1100200138540c4004a241000ca104a440307400007020f030703051807040048000000000030091032003501901c04450f0302c424240c42c01c1c1064000582031100d800d8150348904101a00d160010056000d10000c88010340c40b412407030b44445002b1001760905480070b50945c4103103074000030819824800da141d8114240382c007546a60502042105861069200614880702400301c04070030b41da0b1560035012a00c03000301710701c00c0c007001c0e201080c1494221040500107130340d4441040103014502c401088114840d81e400c021415500c20b00ba1a43c40c1e0a0307a8150303d02c90300303211600060402da0300c884240d9110421400541d80074200c2c43c1e1501d00c6000c82d420002e9400790703406102c0049409090058011403400e4010307032400c18180d10300c503003000380700c01d100c2c3d0412040401800030a5200b00d100b1000a44070b40340d2001c0c41c00c4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 927680485 1250 927679235 927679241
    0x180c03050a0b070302120a1a0907050d05090f07122105030610081b091906030c110d0806060313060603030e030f070305120a1808010f0f0c140313080d 66
    0x11040d0b81d03000c2c045001504203031080c8202d504028424002404035100c1038040401481160750f1641103002c904e000c1c0c0c1d0300340e0326500501e00c10010b070758030310383d48080b909200d4003541c201400f4518154041d00010701040c0000c100681524103020314200b00408a051042c40e1840381c507220030a90540401d1b5080c51a48032006511424040d1224281101e02c50021501802c04956080034403501c8031903000c0c205115001042e050034000e02d51452810055008004613220398000800b181c2c0c1c90096040e42070708101c40314082c6072031a001c1e120a214542c0d020f1720480004141c3e502c24000040002d6010011000601c01d950300505c08001c0f4986924010f840704801d0a40c0038032a20884002441000d8001401d4040c3d81d0300c14054211190f840e016000c40d0b401c28041c0f0fa00b0701c0426600d140c403404c80c0858400003030442000100f0100240c4284170101c8581116002507181400743d03488503e0380040346d14000803209050103a40e5a00d081e4100f01d174003011034004002c00e000241c009861040c5030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 927681735 1250 927680485 927680503
    0xf0607082808040c1409070f03110309150c0c1506041d060103060f020915090a030b090a1709060a0c02060d1a040c0801261c02031209061009180c0305 66
    0x2d401d081c55180c0f85e100c00c051001d003600310f46034400302e16000107403041e02c91140100c9540355070038007088070580d0800c0000d02d5001240e080c130305580301c0044004d09641c0b080c02103130044000c081503403070148800c2c03550f5218501501c0301c41c140344680c1c2c04160341d038880e0707071003111031014041d8035466001c5a0010941c4a65081c402920000d04080074034003207c7c120300c200c03030241c20010003040e200503050002e04040c6e040840d81c641d02c07d014150010100c0c0f08010098802c0f110f039005444e184405250008031080c0580480000c4030062000c02e08580f071300c40c1114124141c0b8244207018090510010701948502c01228100600304640c500603550003100790307403511208840600071003041001c120765022091040102070143e41d100e5070800200c0056402406000301e094541540c0740805411502c401188030740010303400001c100312540030451140c1e41020050010701210304240150240c038211074081c03040401d950b480000f20b111707030b42507500c0d60583c0d01c0ba0000c8046503890500a440d0a116 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 927682985 1250 927681735 927681743
    0x1806090320060a0e191e06020705031b011811040608160321140f040806150405060103140105041d0f03190507031409030c030105041506050f060708280804 68
    0x700312215441000455070a4403110030307096200f40170142d138940200f0852101da007074015107402420b1401007001800200040da0154004554034a4689010324880c482010340700c045034908421441100002c01854076510f800001c00c04154601e400020020031850303002605a12a8110032034030300d030110344042c08607402146d0b042458032003000f003009900d0100700b21000003035019010303420300e071040005400d0090400c000642010f840e01d455601d080c00503034030401c15000380200300d645032400c3d02031250720074000c0c601404001d6000d499030030401818090144555262110000014611003031400c180c848441210071000d12040600d4499000a00d03140c142c50b1540390001083d40200110303816030b5410780e00c0054000c4003c62752841c41d0040f11005a15009100e43d2031504c0d6070901805000320f00401c02203070740b40001001c0000b145d8881e80458028001621480d9290b941c280546109a4000c10600d95506074a40000e80103007128110043e045505203416820070350112410307110f2032003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 927684235 1250 927682985 927682991
    0x60f0201022713021213030224010513090210050c010e1c08160f030b0f1e03010b030d0804080c0109020603100906050402040308180105160f151806090320060a 70
    0x240d03003007804d07480798048841c0035458002c0031500302906610390321b48450191054804010b144054a203d000d82c40d111002c0000c5004010b0000f0b14103246041c1d40b001c41040e04004c600b207182c1c0401d080183c2c1010282c140031000ca001c015a50087d007008040880700816601800700d03c4030718240300311041c40c101e40000c1d49200001c4038a004000c41c3e075904406034441c1c0402c10841807046014001d8801800d8219a6611200d0595120380030702046c03401c4500b4015076990318081c02c0c5400c4400305c0d40e88910039448601c0080400380c10940c000e07046038001c26481c2d6a40c0545901c1809404003c034001d4001c0c00000800c82c201700d1138013003242130b500d807903c05102c0181c0d25401c0009034005c90201920002c0100103602182200f95020f070b1140a040c100035041c81136540e0204010004d505003038980c1c468907c1d84c4d10800480b406440d60005071b01030308200152880d0001d410012030004010040c5660b564040e0500d030007000d401007007550b0700300b800405600c10300c40c045e121841030702c4031114582 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 927685485 1250 927684235 927684259
    0x50a0c03050603063601090201030f0b06160c03020306091506030a110405310b010503011512140d031a0a0e431413060f02010227 57
    0x4424081d103401a500180181002e86504006250a00403000c1000d100608030291039862203620703103c1410040e0440c00042da0b408075000241c01e03201003880c04800703940b401101090703554500094884445ca8200c0d030140d072038060f1034031a807480d900d41c201951500ca00020016080000516091000ea10154404040e1644800e045d6102600d000c0280417400030070a0b013086040683c080c641c003031600c004106607402100802c02e002104100380313270201300d0019003000912074803000f064010076007580204840368a85d40030345002c10050007820524000b051498080c060901200c250b0400440c0031340b88401d16580f0007400030002001000150100a0141c02c45840e0684aa004907085629a01415500d012400c44607011011062500d181e6946c0104402580c401920594400403e4030743d01104101c170780502026880d13940a5086002000b4000c0e179804070380d410f42c08a650a00b052111022403040a034068004c030349040e4442244500d502000c2c00140da100d42c0452019290420440 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 927686735 1250 927685485 927685487
    0x6120601090b0f09091915060f0801050904030c02032e0501060e030a0b090708030c0601080f060412030c0c0f0b060907110a17040b04030501060812070f03230c01050a0c 74
    0x70149424040c034200007805007054030b08081c410241c1c40740d40ca440c40f40705a0304100ba100107c40b110045403101449076503080c130000b500300034031415050550400001a40c90036001074207015004000404200314110b4620454900704082518460445080f442030001c4101c0301310011a121034a07402903040600010302c180c01603400010f420006000b074405503480e51246610050090451107040c03090b4040024013040500c003802c0301802003c080c1515500d0031010518005d45d480140d40755410034070a000c0050f054620f407601c490550705000c80e64070650242030300c100041c801c000d8907540724181010101b00d98403502900c24002141c1412081e00c03855401c4134564030000701c0303c3c07440e40400120f2021480a55900c800094003114880c601a00c4450f510700b180c125a1041715160344800c418415080c0500009404c540000c02d59130800d6030945509480000c8601c005e02885071140000441d254a5011101e51000000030950748010304010103009000441c0c003820079a1420100c000c0076 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 927687985 1250 927686735 927686737
    0x4060501030e060406110d1112091504030c03031401060e03152e1e0306050105311104080f15280209030109290720010b06120601090b 59
    0x2c1c820740d40c000c0c81c0b581e40b942e0301e800052481c010380041a890034010703c50064034a018034010202410f84164440800d9a10882880c00192404070581c022a010312081c0c01c0700c107281c591090f09450074408105d0b01d8102600140915868400440014800490942d4100d92202c00c030f0301c0c0540885031211814182c011400034142c804c05d000c10030f020680c0c0c2c200000100650740031742c000d41409018a946081c01d039030361800d068001c03001d0b0f0b01c584400c1051241510451f801070400755904c2001844580c07180803403a210342801d5180448881300500b14081981c094544800d000c0c2020342c0d9035480c0c00d22203549110003610360f001c44c4910b0314072261802031200c18a00441c0807003464101d800c0c1c03048a800141110104072281d0701e6003030001610542d400d015900e0854081c00d03814680320440c1c04000c0048480d0100c2c145c40b01c21a80c18013240c0c41d404004c0b0b0b0050b03007004611413202d054581d031140c0900707110001030364821004981d001c3c074044600b074681e010b0602622400c042564a080c00921 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 927689235 1250 927687985 927688001
    0x303080118060602062a030a15171009140d050d0e070513091703040b07080a05040510230c0d06170303010311061209010c031a091303020114070507020406050103 71
    0x5170410001300303042000002000007000c038800e141021050010382c1060080d081211504002911118240c001c115000c4000380509924511161011510b074100359460002010708070300e90384c0d030301c0030700040c4041d802c0d003090807403d00d0045c1d61042050f000020015006043c501140c00e180c65141e940c816000921310f402c035000034020003c0c081010141b2070041052050560391030f13000f81039821802529100440c841c51144041403031a007000301000701203820041080c0329040c070780810b00c0045000000ca42e0710036140c442000c21941d08000d00e50010810500f1500681c6040c88144141c60051001502261040000401c42a80d6907400f001c0c62410211036070344950000c200500c08107030f441c0c03034028144401801c43c9180c940a60b140c3c41c0044011a01c01c000d40c0d43d160040300d5055414083c1000049440082095940d54000003601c1000c01130066144003004510702004c040c000c1d000b003034010328559520080c9190080006e01998025081203101d207182c00800b1449600038401c0b040c0d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 927690485 1250 927689235 927689237
    0x10f1815020a02120a090f051804140712030215090604020904080f2107180b1b0f060915060427020f0a0b0418020306101b0c03030801180606 62
    0x100d00d040050814025446050108218040e480c412034040ea0f4110040c40e80c800541d0700c0800280c50040d400000c00c0c8141c0095118034281c104c1d9040e00c0c03101c50409a0000d800008200b4565442c422441ca0300001d913000c000c12010001d000c00515030049030749142040e4075180d0507055a150003007203844100842d4000c1d403248041e000300d004581000d0190840b80d81c41c042c000c0c40c0c4000540a040200540c0d007008500ca0211810844030f140d00c072209243c40316582615a1030b15060490004582c000e20307031030400800441d61303060100311040000c959613407400010303650035042000c54641c450308d41c105042605c2e4800d10200b403445c201031144100c1d4038400c0070480c11051071410520700001340400240d03403140382070003411103070390b2910700d5880141601c0f2240c513992450120301c00b00640200603c03c180c50f10600801460703031902d02140303510265074a44640e46080385166002414003000d0054540c19900a0120406420174005170507114401743e0500100011b200174801d807815401110 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 927691735 1250 927690485 927690503
    0x30b04061a071b0608130620071401051b0a0e19030b0c03100e0c0c07090b010f051c110d0501030308271f060e0c0306010f022a0f030f010f18 62
    0x40610103031b00000f103070703461103541d0200e034040d4040e50f04580d103001650110300b071000c001203001c10401e140902508500c0810000e10541c07511100c000128600390f0b0080c4814100029114001441000c281740131000c000d00c224440c242c034940703854401d582030008031203e00540303000c00da0f07050041080d24419035150424a54241c180304440c43c810344003030602d02500006000c1140d4031030080c050303031000d003104000010b24640560001041c1002507203041f070511108204180b4119003140355912841c10f8108041148032840407001881c0c03041c00001112249000c001204146c1d0081c5060300078201c1c0740100814200d5885400d2180c01c0c0811001101d03401540c20140c400e214001c007910040c04074900061742503840009124844045514404041000003080080e40e007016602414600510013841240008400340301400176103a0709400c4e00385003034681c4829981e41001d403440100b001d01034588000020214601038081d0341c4a4050f2182450403055080c3c910080c1c00000e1a0006800 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 927692985 1250 927691735 927691741
    0xc05040b0117090c1014070813081203040b0c03061c0618061d03030705160609060204030f020109140d0326010e070f02060f040201030b04061a071b0608 67
    0x12008000c0040900e050203400007110301c1154000e0851807250010b00d0280c00505121001c1041c1400800c40c0481404100c5400d9100242e100003551586980010344654550b03001c40029103c0c001c03075200c0d030036900c144454114480c0e584030155006612034a0b1800301c5468540c0031402c0e41c0811034849410580603843c103002045040480c82d0814024180000c510a90442c00341130808820300960b0300d035031650104881d041da0200d00d04294030050001d1820f40c00c01140c004d00a00c85c10582ca1203055881000704248081503000801080d8042400c541e2035a89140820b0011000c038801d07804580c00100000354050166588054020300034441310808000e540d055800d64540400e41020019905403002c000c2c40c8542198080d01d9078007002a80b40c0b0704140c00608449108000004541003a018800d1650500704419085942401c0100740c05010b500481c1c001c2132503501128000054000348400b03800c101005041160041542c03440c1c0d01e4000e00c0c03407404845240725000000d5086400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 927694235 1250 927692985 927692989
    0x30105011706010c06020c010e1b0913171b060603070e070c030e0a06080f15010e12010212010f060e0117011e0b030109051006020c0918010b0402160606060c0c05 71
    0x181e15400041418142c0012810391030320000c0380c0002c1e0684c220350307646258034544504200f1240e40b02c0c199000251202c0020080450400c03540030b403034041100300c031900145c00c00800b0001103200d10b000e80c61903602c0d8501e45109040d250440d140740350250250342d0108a11f41008101c03001602e1104c40741c074500d0380307811000705d8024005910030303000c0098140e101440c964400500100400340d03961024810b003040702c0318040c40070001d4040180c001444020031816604061186d02080e022104a03100301415440f80d4060301c1400069054a405a4001718102c100e10810100381c03a126a0703103c202017415030040d0380c01160515031811000c803a0004010070b03104403446950380144900c11f80102a034070003c030400341d082a00941c401d9911076041011545203680004000e00c018801001d10300f4000c1d0102b4003290014115500c0060107040c0301860b52025040310610060240c8111f40ea030000740c5007803140340c5181c01d04681c001e041c1b20000880c42e1080c024003001582258800d1780c000e10b003c003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 927695485 1250 927694235 927694277
    0x8120106050703022a041d0606061612050d0e0d110708060c0c01060e04030207030b0c0a0512070207081603021201110406050703090315091a130b04020414010303020d020c0603010501 80
    0x180c8500130000400400e1006d4035640100e2000090703040740e00516030700c4181e040c0c0c00d056000309218000c1c40140103020417011104122215640c200341c072400c1e00d2541c42c0b411034861187d1014040c030703641000121107903c0310001d1080d40120310b991b5102640c07a4513250030f030f40350001d40c4101134565100d0f00100702e40c0301c0280000c113030721043c000001843c0c607500c4410000c0c1440c225000e0300560004d2001700144a82c20400d91390090384603011754546640014040d00902900d171108000084000c0080c4900b0b0003046440003401e0000c00322850040750480d01c00d442881800201d01909845c54848103101050050f002645140031a0a003000c0c14101d044655030410070054040090280000010452050262038070028170b10001c2030ba50301354205541d40c00c8a0070b101e10701400c0c00c0b00820110440b441044500c1640c02400c81c003a607142c0740001005043d00c020700c500d070303803076410000010142c000a0300c1d0f0788000c403a000e5800c0b6200c41c5041180e1070209124007808a1904450b5400d0404840 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 927696735 1250 927695485 927695533
    0xc051b0f070608061315031704080c010306030c090203060a03150f0f0203071b033c0206060f060f0c1009140f0d032a05090f2202071502070812010605070302 69
    0x18181c0c0003290383c4c9850303040c1d00758620110a0000d0b0f00004003440944ac09100703a940780502800c0c140215851a81c88039032a102e80c3c441c40300b040ea804404070b0340b607a40341e0810000658000341c2c0b880c1800071940c0c26000500000b29801601d41c900100d8000d204814000c0d68032079401c60f1103042c5141c0942c504081004070520040702001148690b8071408042c841c426441080c80c0c0070240c08840ea040c04150640740702003070440540d44820200180d41d51414024403000c602618030035290024911840e615020303000d1040081d000d021072000118000b0790260007883d02410005040091032000344e91583d071440c04202294012025035990780d40243c02030788040c6100c10014540c030008190240a2803138070700c0380600143d40003032081c04038604400c04c5080325004407050403c0141030603500c00054841c440e0300c002550041518014004000032120010344003010a541c0d4030040e2900c24101d508c0502d0301c0800c13544c2000049001c0d440345080d42c2c1c9081d4141c00404007007024600d00b44d82c043c644 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 927697841 1106 927696735 927696761
    0x5150c100513230616050c06010b130b0f0d0b060c0d0c050709151202010509090a0b03010c030c0c0327170601080f030a030c051b0f0706080613 63
    0x2c1046034100c41d01d244201a0780d0b581c07000c290f4041c0181f40c200300c800d01a1900005001014100410b04142c50040480d2010b4031021030391043d0207002c480d02070f11902030100c100107071400c0e8041040000000e000310b00340441c1c003034000d02c0c09101d02c820303000003900e1800c4901040070070400742021740141801880307100000480d451140900c1e10407003155a02250000b01964003540460b070a044003d880c60449140527984480942200b0007010300a610f04031500e08040d01c203104000c0c0240c801d0f9100c00080c00c3c162012215501109080c0002c00d030f41d60080f20602c0005000c00300145201c50600d440310f0070864445003040016406184160000c003004c41c4c5500703001c03040340d4590b019406c00003240005480110303468098186412918844000103861121001a0307034240e008440c2c0072a00d40b191150011245031400b42c505940058000c1018130482c280d0742c100300d44002c44 = true := by decide +kernel

theorem cover : BRFrame.Cov 927517985 927697841 := by
  have h0 := BRFrame.cov_init 927517985
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927517985 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 927517985 ≤ n) (h2 : n < 927697841) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
