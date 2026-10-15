-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5021
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:29:11.16268+00:00
-- url     : https://prove2.me/submissions/40f1b113-6a42-467e-8081-726b5131f168

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 902877697 ≤ n < 903057553 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 902878947 1250 902877697 902877727
    0xc0a150e030a0c0336030b0c040e060f030a0b100305011d0c310b040507020115152309030f0705030c0906120102032401031a0105071a1005040e0102040308 68
    0xc101d020170002c00d020f41102400c90001040000c803a01c50310704100090081280e5124420b5004140c22203650034a4a8102da241340704c40c1c080c250300c0c0244443c000101c52510248041650705802240310030041c284401c0441d020384941c8400d81d000d5182c048000c104014180141c611085a0001008444603038000c010000440a007540354600b0301d103204100200c00440f140101c0d1403d903800080c108107400c10300c0180c1c1d400610410859252000010b10f4005118000042e280b01c540071620040d08084c0035200f014090342d041411b07503e250182d0004815120041c90b08850542c00d890340d40c1c081d42c03174a60f81c0b2421406002d034990000e9240f41800d080c0302528a600190042990082e1404529080d003260310940d610f0010344c2c0c90100007009d410381080100f00c640400e10342000040c6081c6c424220095141903002d041110020f200010301c10140c4544c070f0800c1d0048110a083e0031314003100c0d540301015114107801903042410303061900d141031094504481e00175001c54501402c1c180402d403 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 902880197 1250 902878947 902878967
    0x90f031211100c090503100b06161a15011707050d020a031d070303020613110f010c0c060e01020f06090309060714030304080304020406080c0a06050f0c0a150e030a0c03 74
    0x701c0c82820086500d5041e24050a0f01034511604e895454a040074241810714038120b0351844020704180011110340c0b0b4180071500c079a02c03060904840b98003d840d00000c50b11842303000c284100350b00c20a1042010511410602540090301c5e00951240c0540c030842c1c43c0001101c9100206100384010b202800d61a00100318204180c82c0004035074000010006107046441103e803001d90211100f401003540400a05402940f2038200074401d070341583c0ca0b1002e010300d54024034000c20000f405118240d0107011006191a4498401e401c5951151002132034200900c0100303005104541c2404420074002ca00c0c980103d110308007841c0740103400000c0c007010303901034801200c0302c800d5000c80c2c00d034040003030000c1c5014074400d148a039641e040c98010070060300d0704d0f034101002e680c004000e0b400341c0703a40780c1c040c80341111001d05065844110b03c203412103840c056025141541d01608045100304101d81c15a40000400424204103c02c0d40303a11181e640d0190800e56008104031000c044017213401074a801c4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 902881447 1250 902880197 902880227
    0x71e050a0903051f0518031603090b030405011b0f02100b0111070609090f020a050328020f0d0c03050f0705030603160e04260405041e0219090f0312 65
    0x11000d507896441c249400d080303111511002e265003080600b4202c85001741074010030030b003c0d0041d00201385405d10307445e4420b15104d80003814a1107042c000f098007a00041000700581d885141e01c80c81d09051050191020018074400c034103004d0501c0440780d01072a00807081c52503603402448541200000c2200a013071200703011341400748090300038103454020810500a828903540d42c40d003681c60302c000c0e142a01c80354896114074900500c001200710390302c0b00a0f01d030700401120001c031301004240700861f400c05041300c44440c0a400000c9500705941000c0c02850507800d4110108449103101004600b01c58061302c08181812402c008908402d200301301558101c04000d06a0742800c10010480b1619840d0340d04c400ba5280354242080144511080c0595090842a00e100c60911126069161030720440c0102c2d4499640d40503040440480001c1303042440c52907410855440d4a01c050300d841d6240380e40744d460000303213502d000411307a400f0108682d000ca0340e00025005121500394070030b0325090312001c101 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 902882697 1250 902881447 902881457
    0x20706180329040c06082d06040b0613061214010e070e0307060903020f040926040b13030b091506121009031110110301060507020111030f090405071e050a 68
    0x9050b90002c031640c1d00842c030401c40c060060385000b0340506201802040015030801010515020040ea41c050030303020860002c00d540c2541d078400000e0010084414103603040030300850040b509e045050032440546d80701c0c4c0c84881d00a070800c2c1940c820755103407131007000110400100401c114a40c0c0d04400350480c102e801e02d0042c0c4851000400d1801002c5da02c410f000a042503401c006500f4907084c07070400741c0c0c015a803c0c088801d039a22200e490354004101e04202c507000502c6804201c06000503035000c1c0a9150545980d51141d003215504040345000076243c51840740d02080031007000040405010f220680c903c902d980d561001c02c200c0e81982c203e41c807128001c00410040c00b406900c1a81500d03413003030300c40d02c24020010341d0b15440c101810002803011841c1020192085903d0401d490440714285041c0d0f50b100514401281c864583c080b0b03032510352001240c0480301c080304402600c1c0314a01568101305a030340d50f103812213445090858880c0d0001c84004114070062251008045c094203900300 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 902883947 1250 902882697 902882753
    0x1230a0611031c14091c0e031e0105060405090f0c040207030507080c071715150102122706071505090106230301050a05010302060a03020d15060f0207061803 69
    0x100700001c01806007804500c1d999182e4202680c1c1207134480b941101c41c0000502d0040c48201000d6241e0084201c15000d2101c208810030466800b04421071807000a01e018451000c20081c48501801040c2c5009100b41d04102c0003607880d58001407500759a501c04802441800c1d0a075007448000c0d4030040b025800c00804205041c003040c16000288003c098900080003803a1610400e4855502c0c181030b54075403a04462005080c05003489059500720f29240442c107200c80c1007500507032604515100326802c9080108240310300e210a01a12423060900300f071440607840d07001040140c0351080a80051080c2c41c000000703084025590300a0354002c042d00000515035481d080450280e98030908a20400304046103482840d04003801041d8114100040030702c040e504550016501c1d014403001c40301010f44c00328034459082e01d540c002c82d0361180c01c044001200340d103603903000700b62422504094025105a981c0000c102c1d20031040c162650340b00113010f503003090465a1315000c00800e100516030416071121 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 902885197 1250 902883947 902883967
    0x3040b060105040308071505071e050c0307060606230f03010b090102210a090e06010804020d080d0501141908030d0f060914090f010203010311040903020f060406020301230a061103 79
    0x50011501840804a041001131580000d0312001000385040100345200f100307021a006d03042500c0ad4149007400c43d20b0342c4e04141120700c4d600a028000c0c01603422700c80001100c0d5004443e4018188841c0902c210703400021008401c01d100c1ca05800a45010400c0100501c003004005020381c400705205070346070f030081c0f11141c0e20780c800300d41d480c000c002900003102480d0940115440004006400c14409589046e400103010144000c2020b40101202c80d058010003d40c60704a58072051f01100c01c005558480c1d00014241c2e0200d0109400354141e80f01105034100071201c44800c0700d0328480118030300715201c1c00c9000504104010b0f0b03003030140c5800001c66180f620b8042c00511810f4511808018030300070300c0491811a5098408903184d04c10001400820000e0f80506502d440c00d40e40882c0c08032581c5001c17458000f8084041043e401880c0503c402c12140d03800131412a0310941c40040ca071300c1603000751000310300c4565a1961202103010200a000d0040710b02a1090ba00c0304282e0382000e007054 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 902886447 1250 902885197 902885213
    0xf03040603230406051012050d0311360306060d031107170c0102010b090118091a07030c02060a0c08010e0c0f0307030905100204030f0204150801020a1106070f020303040b0601050403 80
    0x280d000ca84d000c0d100c10401c008100082000303001060110a00e01c0b100806031616070321918082c410304209600e0305140000080c944e000c58210100045500009840c011003001ca01140d004072040c0002e01641c18844a04e8002001e0303014082c010129515070b07a41d80c0e03040c3c82d0500e00c100c4c440030501410400243c500c08a403115050784490501420252210300002401c503101001c11500c81d281100040c404d540001403088001f400000700010718248604101e070300044981410742000c08100d0801039081d5042d04440c2000318142c00301d91007600c801c014001510b502c0444070300014100d0b0010880107103030622044d00001581c55030361234180300358911861580203c8940d004662124104010000708001c107010065103000214245070959a42041e01d004140b40a03210380d071552880081e054884031828000c002c8400210b585405000e03000d4014100d200244038136004010018695900580d9034010500741a80514915540d940c1e500c950840c01030310041c1044420301010000403012 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 902887697 1250 902886447 902886451
    0x5210c120604020901080303070801090c0c1e0b0c0405030a0b0c040512070f290703110d0c0507052403040609020a0303031d120a030b0f0415080607020f0304060323 72
    0x12201070250340c542801880b0400310180d01550140c1e00402c200841d09621401ca5815280ea0341000310b0b11260001d0101c0703515051500144c0265428004070015200c01c4130030503c080d01c106203202c540d0795000c01890403406148035103901131b04180a4080042c40c803124103680001152080740c205500e440201c3e482503061069401c0e645d006000611010102500e40c2e002403205d28084181c095a41c10b030b00884c2c0c0d1171441d0603042c0160200e42c0504041c09031050201c10460036084400343c0c9010381c40101070305145841522603010f10381c0c01269034200305000d11801c140d4001e5640140c400100740d6200c6920040c07050f117560f40d0301d800305d0005940c1c03d0179100045000780d4000c1a64208000110322485034181c41c0300c80c640c462550809171300c4c5004151407804c2c4490070300040c1005007001207510018540300541e8800d240c40840c12034042c00d0140c1100b07036074442c4101c4440396143c0030107030382c2c40c0f00e10b095107026548240b00402c0901c3c4a50040800109c454000118a0402100b9542140c0301 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 902888947 1250 902887697 902887729
    0x61c050a0501061e08070e070c060e030d060b0705030f1303060e030a110a03212c070b0412020616081306020d0221030c0903120c100605210c 62
    0x180e19040040d00482e01003054a4250304455004e014500200503644081d01d10517103901130700d2540081c80c07250140c0070100c03115800800a200442410301c0d050340f05d03440341400f440101d28000340820707524840340c01e80780d189902500a52034a0007030400c20f2400d410451860803691030301e400c0400010702074010070a280d2030920065403140009a0041d00b040140d10343e624a66200089110201c1d60110707c04041e19841c1d1050200c0d03115620207280038020405015507155811a001c0b0403540c50840e000303086265a07c141c640e15901c0f100c80000600c240e1003614269907103500b0403005031906034002d110040c5989500d0278410323400c0d5900c40e20fa4222a5400300703800100803041050740e40501030b807807621040e031014050406924034002004207d02d11085000d00e808000104c8003403000d001c1710800c810050842c2c100d840001500b5a1650007a21081154002c503481c509404079240280700585500a2160003020074000f0340110f06002c0c500750300160702c2003101042203503c40e0502d21a1000d8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 902890197 1250 902888947 902888951
    0xf0f09060409090308180c2e050301230904202206080304062106120f11060a090902180915152113170307030b0109030308061c050a0501 60
    0x1120f0070054400c040c000c2404d541a204d0400c95815000040303008601c41c7c00c215080c0410b08035600c203046003c0038030b41742c00350030007214145280c03000d8120000d54102c641c110b03c0c021000000151910a5001116203143c00c21a030751701181c0000c80e034a28041200443c858244e00141c0040c001511000d0b0071101c0210303044101685016100c0d1600646024204205c021031903e4981800200a030480561141404081000e804840080d46c0c01000c0200101030031001076001030300700341e040d500a80404a88403040410441e403170f820160180c403542455611008001442c004e402000f035400305641c54201c1d5123421143c940350380d0b0110703242c4c010002000e600b071030745130b114040c04280318481030202203000c0c0520406019011407a8000304940139685440410b40326000805e420342c0c0203030001080c0030030381d860140522103401e002e58403e003160b6409018509103000155860501c82c0405000076004100042032420021100080f0206500501c45410150346890b4101604008122680d035 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 902891447 1250 902890197 902890211
    0x11060c0405120c0618120a06140a090b010504020706140117010e0604021c0816110f0603102603040902040501020d050f07111c0b060907050a050f0f09060409 69
    0x1c14a101c484034200d00b28402442c103407104400141d868050400c00303460308007610001e61101c0c1c464040070380140340f01804944800070316203862006405c030b102c0e10080320404000081e104519030701a808140360048032002040e42031809210181d804000c003a10700f1030b210402e0060706400340c080b5034004c0c1142c00c0c0d8284050101c0007041d080d55088440302034141c2c0300318144005685d13140d032050000c1404071502910310403070b460002074501411940100700c03042c40500fa41480440c40d81030800d10760440780001c0c4652541c0c01c0009078002070b2101c070180e00b44150180103004509140c0c0c0903030024007110140c1070111114140c61907220342c02581c0f8103500441d040180b96010040d805003061903007171050905002c20b400c1002c9000b08a405448181c00b451044016102c085042074030064030401400a1401da06003041c03e140103990a0340110600e50000c1c036913a1041040d5803200e44243e0341c00c3c0c0703450084000007103180c020249204800104024003c61aa103440c01800240780e040c02c081404 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 902892697 1250 902891447 902891449
    0x412020d05092b05031803060a0903021c02070b0a03021909030218060609040f05091005130b190501030b09010501090c0912031e05070203190c06050a11060c0405 71
    0x10801600140481401140b400ea940d8081440682e40d640b0900080020010001d850048090301d010f00781340400104021448003180c2c120103200019400c40301c3e65214401031401310b070110700024006030000c04040d110410254030621100c14644121030405031250b50002c0c040d4822407032440466400038805055a401801c2030425904c0c50400d244600d145030040f816080516201001040c1001c000515139039883c400e942003a030b000303401040720030b001c1443e02e001048280c420208920490b11210346103000b40c001c26225038003002d20717001680103950f5140815140600141e461104030803d4000c001c003644607041c0218000c5030b414056090508450b400c480041e000062498101170028214503044401001102d048107041c04090760103060072121040c440300290a203200366104445c8807a801800307851964001ca081e51400981180e0120344100020303802480501d50807010486140100090080007080c1d0508107500620412140e043c240d0032603008841640100d401c1c405 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 902893947 1250 902892697 902892703
    0x5030715090509060303070f1502070614060a0f051e030a0305030105180403090e0a150303030e010b04060e04020409170c060f090d020606220e0304030314131806030209041202 77
    0x40100343c1e0640d400d41130001c00300e5224070604002070085980521341710300300032004000d04400c0520750302c11501e0359003078600713a80a001002203100616842d0008035030301c0d1030115140022952b5004003501078901d8902480f41040c801101441e08031380c60800414191418400c8641c402e200750b550036a00c0d810202000520204503807a04483c00030a806c000000c0d4102d000e8400b038800c6580718442543c0c903c100743c0054100c560b50b0703e00c4514103050000816800da00100c031401c0b0303504001d014542c8540d00340000c1321050700c034941c1d20240030301c0030401500305070348885002c50090710355170b41c56149044030381c01c5584007101c043d61030b6210a0130071003106842c444042c1c100200c40c0203030600c4002101c00a65401c0c0c042c3c0201d200d8665500c0d0f5162504c0103400782c82107001d2030710302070100300b0641c0c40550b143c0c0c0052000340c1c00b05403000c0210544201850455252041081c80f60780064241144540d401c03440103a000d00265940b40b010000d030742e4080c0c07441e106a00c103009c043d0340b02411201c0281 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 902895197 1250 902893947 902893949
    0x1d04180807232505100c140a200301020f0f03190203040206030a1a0a091b1b030c0602160b06101b0b1b03090f33100503071509 56
    0x414070340210b0202e00d0519000c500e001641d90030103100c003298030100d105089000900d81c0b046030320407a10362540106581008914880d280103d007214a402d41d80d170061601c400001d5001001451b110301084130444048500d10b9005401400044c10284031034585041640100c2d0014001c80000c002c011950766070640ba0b00e0920210316042d4158201540840c0b5680030240448a01d10745401ca45103004070b135034101c030404020041181c40340950301c2c01000300500000c82241c15191a004400c0c1c0c1141c0203043c22400074440031a5802e019149841c1168261440802240c03001d408121560410b04804c3c00305c20158050038019800f030411004002003420340b03400c0c540503c4581c4d6000601c1e02801d850f00e4048640114020041c2c0d40c401414202d0750340d4440712464902400710034862070003070000307140501134110070440f142c84443c243c91852541c40740c2c0c9025052190b002d2062601c070500356946400c05a040c103400149500e41002a041102c0c54100701241e95880342824403169100b08194 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 902896447 1250 902895197 902895233
    0xc0105041a070207030305070b06040f150608130c1701061814060406030206040b09030a08040608062701090905010f0e01020d060b03060312090a2c010603020a1d04180807 75
    0x800045e1441e940585140a246409040200c1312000591a0b846540204001040e0300320b04000100d114641c40c40381807442d000d80000512170b200041c82c28101072103800ca0300f58000c040d00c03103107500e8100892000d0040900c4613805540726080003610030440d1428211954030303401d021a8a941200344201d15600043c0228440c50401c80c04101503210a002c450649440400065452404c0000f180c039041902900a09101000500050040c1e0041c540e50044c0d0702100e5039401d0030000301450b81e0b0400c024454458500c60a0300400a443c1694840c0501512541c008118000c20000000480d4061030160b06940d4000030b056900314100e100b510040c01a10841718210709000c00866a9480050702c80801c81c05c0024202900b682c5404260004003882110702d81c030407213a8040040041c01e960321094856407601c001058041c06402500c883d240580d6410402d8480240195400030545039166042035540d80072035049121509445015130044101e10350300d064500e400100c815405441c4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 902897697 1250 902896447 902896453
    0xf06150d1704030b0c191b0f14070e1e060d0204091101080703022b06050904050106090b060307020d0e060c15040c090612060e1911041407020a0b04080c0105041a0702 73
    0x4121b0213031211000c04190340c2140303088407800001301c04001c10402440030142c204d644540c180c000b00314400f0001650243e1f104207642c1c04950b80c8400c801000d41c11307130380742c2c2c60105a03004840c440b10034030385810f6201c07400402c4840e01c030100303402080c1183c030030300003d440014084d2510a042e58201e1219a003204c814030701180b8001510520261084c000c10b64035403054803816100e02800c0c1c06070407080140100070b00c02082d80c1007501e8102e009024910a2060081c01d0901c80c040078500780c81038a200d4107064014142c201034508045074000c802d15078175a4000401d1054039030460702003040f0218a0007018242480341820b041c107001c0a0740e1503110144550a000c01840502d81051500341a103070b20030740205401c0c419484041c28141c040505004800d031002000b010700155501c0805107203000c0d00c041201903002e00d0907000c081001ca492a0160380080c118000040c074954540354050b0003009601e0400030801c20303c03401c0d207501f80c9040e6103100d019482200400812000543c100d6507034001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 902898947 1250 902897697 902897707
    0x60f09011205151e0a031b0305010e0d02160302100507140d0c0c0e09031204050a060906141305120d1d0a031409100c02041424030f06150d1704030b0c 66
    0x400d1a649400007d00380020741180c1d1100c00c5540c5042c1e0301450f8024020300c108841e2944039030b600c64004604800500c103012046510500110558094940183c00300c1c0504001100545855202d2101120181d50303200500395402418440100b680c145a540d08c21450094242001c803000542c006040aa44030006e10050726000012641c2170b120691600c0c4595840e802c10740e02b024110726003e0201801c20450748100321941e481981c0461410201da450740d02d803202c2c011512800c1070300050040d0300c0003409000303c40707a40703010701400080b00c8030201d5462001140301806403901c0300d52554035844482060105a0407011340030010b62500c0409003821040c00000300d00403046051001402501c01000c3c0c00c1d91281d400c140810401c9004540d080d0601c1404070101a2041c0d03a00d1100c10500302d00022507190116244401c4903c00c00140403c1c0c48151402c0310019507003036110740c8410501f0b070050000d00d601d528000c0c030207080007455484624604180c4d920083c01402c10b5803031002044 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 902900197 1250 902898947 902898949
    0x3062101062c040209070513030b0a05070c0b071b0609080a20060c0d06080d08070207050102160e0c090913060f06030305071b0513020423060f09011205151e 69
    0x10790b2692103501100d940003152601001501c1c288500c115040c85802c500380003001307000d021040c0d03a000303441da0701c01000a41e40f1840101d491003050135004056201039408250b046101ea264484904074400240c04100d46550f5504100c803001c003070484001002241c0307680c041d6081008030030030b480c4400d154104104220200b0391030300c1000300b030101440004141c60484900d04d504c501e0280c0050000c0b070b00050400070014000340e9003114090014441c01502050a501c0801c08094481d5011420b018040c102100303911540c0c4010400b01c00306406001034005569050003240c01503490300c6841d107080845040031003d560000d450f69400c01d007020b00400000750711000b100c005a03001401104000c088202d007140035111a03001c40e47c4445400442c040400840d4018011241c0b510b0410902d000da102860500c641120074043e40400188001c00104400074028901444140340c4000c1d81482901d00700c08072a800c0e40d914110300340030446944241400e03070000703880f0900580c00040b58030101c4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 902901447 1250 902900197 902900279
    0x8070f150302030910051311040e030a141210030c0e0408070206030901060503060c0d1a150c07080105040803061008190b0d23150112080306210106 65
    0x103189102010380c00400900c000106005a1042e000d00c0c0c2c105202c00c3c100460b1340715801220110580f01812a658003604914043c400d061031031031904003544c209849a00240c40080150340809400d50081040c3d0b0100d0412011092007070364a00700c1c0181d6203085081070007000580760800c880c000300b09418800894010015102c4031581204d56a41d00d50b511b40c0c1480c00b40203d07920054151080406014401c0d0362035028100b501030180c0100114080f1a0301038502c10070044559401240014860100b403d0060003080070040190443e07130250b540c0c0e840c150031a41e0450b07081e100d008001c001e2120514200000e41411102440d1488160515140c0c06803481c003407600081a0540d90390000056440e4071411345062500900180020014600c0480b05456410402a41802615190007000441000003416626110a141101091a511100c050b8005450b20340d1111a1400c40005520b83ca00c684000300820400492024074040400289001044d0508008030b00710703092145400c032030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 902902697 1250 902901447 902901479
    0x1f0611070b070609020a06020f0f0a2001170c0d0b030607080a150b0c03030f0f0f04150212150109051806040207061d01061a0703020604030e040e030a0201050108070f 73
    0x11140725619842c900d045001020798001c020341190300158006607064011401810465080c410b848075421315003449600c07054030301c000501ca0024000d00e0084030704001ca603420501018100755200300b5003103c00c1c074103200d03040310b0b1000310403130014080b1040c0300c0d02d00954014000650042200d07084c01080074042400003420103001d180c1e65501ca481d440c269608001c001d03c20902c400d5038400c3d1030503440380c0b254412500390800d0341007000820410082084094803c1e074020f00c02d540291207a40d1240e00d0000c17266072107100c1a809100c201161000c41035003a0150843c2c540303605c1540780703080003d4400c01080d13000d5441070324612029030361f60450f2003409501c10380c202d40040e51031f0103a2038907000034529010303826160342c004207091040e03903015030042c030030340c0c2c0c030801e106c1141c03445d5404032100da04c00c0010084c0180c0200300442c1c0028000c0e42003800400d0020408113141186084061031508010403c10061b03448a00410001501f13009000107460202504482241814903408251440c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 902903947 1250 902902697 902902709
    0x1507060504151b2d050d050f04050304060f0e0a0e06120303070f03021c020a080a060b090d0303230c04031b2108040906030803040614060a140102030f031f061107 71
    0x40a6007543d421606071a0300700e40381001003031029400344d0310000404075044820041481481c10780400c0010704411680c0b41f0441e885402907203807508114040b51201c0007a031500c414001a80308414890b60399103485005844114402001460b10404218003400b00c03130002d1249810401c2840546035019440b01007544e00d03401e02580da20041003c10031400310094a048405101080440459a0050780503020700b100d440280300709a00c9050fa10514401d84503401d50140b02e0780401d13800240240c110650840000420944403122005404a05842162002004c0e03500140c00d10822040b095000d14400da007000c042150340c18103410948010000142c0c910329941100c05408001d0b141c000c42c0c0c0a4070a80d001400040daa078945685603802c260340855440b814900416940710000072510300c2404020f0080c44c4071840e00214502c40034070100e00c141140000c102184404c42c044000794040c84040b824100100c2c140c80b42c0b00380e030034207940040e0100f003a03106415404200002d074060a0343d80d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 902905197 1250 902903947 902903957
    0x5010206070e150a0201150e01080c01030e010b031b01020d11030304081e0a020109020f06030402090f0c04030503070809030c10141b1b03250909021507060504151b 72
    0x40c2d09000606030594840f250312100c0000540310340c59035040d08001aa1001e441c0030581c1103171185140450050240103807012540031380b40c0c980d92580f1170380002034a200d1070400041e0b00611080481d0900c0c0340f4414400466441f045000001e5a04100e280d00400c01454040f44040200c0405a00d9100141c00130301020700210751145030211080742c8200404083d00515910304818401a028222190742a4496000766801c40c0345401c1a204691003294000d00c1031055a0312040c0002000502411382d000c0802c042c000803000420800081a0041c050f12010b038a4510030020589852081700340240a021021594010720b60030a0825a00c8030050040303d80b10543c501c5881003044003588940c0b002e00c19501c1540702c00306011240042e8a40580a840000b1140d20b504503094030390140701d4014035034080c410403920885900c41103100384018880c004920300002c01603625004400305541140d5907009010401a410407040c0c55081010410f011400942000c000b00c94202d90604040c00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 902906447 1250 902905197 902905217
    0x7180c05040e0915010806011a0a0e0d1704090b0a060201022701140d09140d050906030a0f0608032805070308040507090f14011a0f1c0c0f020c0a0501020607 69
    0x510900600381314821603d070f0a006503030758030307103607961070f1428807800c00c035a540303640c8101380b40901c00c0840d24110741a032600380682e031084060103e4000158401d0b20828501106052200c030140020001003a074501c001c00e80751403c0c8100111150658458815a8410080984951310951507a1ba09020700e101101c00000d1030380068036002400d03680071034403260000e85138038080c03642e42c04000c00d00d0080c904040029101e00090707a5440c601030f59030002c510280507441c060702e4418019030740f1086d00100403449800841014054070800e4100e002990004544c4802407101c0950f080d11084042c0c0d00c40c048001c103004040d04034407500402030204101800050180072040001d24002d0842100811480390300c49103140007020b414482c0504465203400010740c81d100c694071140d5103a12081c1c410700d0880801c01042a0340e1002c0700f818011020718807115a526500d1141d0300386401c8035201e00c07600d84019800203040203a8010b40b6440750b84640418480d60340c0c0025072a034000d4180c05c100c0041 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 902907697 1250 902906447 902906461
    0x303110114010308031e0f1f1725210326070e0f03030a08091f0510050117180111070507030201080112030813020a120507180c05040e 59
    0x5030501e00310782154a10180d00000820144400842c81281c82d0040c1e0603a000b0281080801c180040e031303100210360030100118101c4010410300741d081c0001601139011070f650380c6240d0109003d04658030b0615070000c074103506000c040c100c000c030781d003090000f401d60300c16003402803062070190000c10303220800340781e12545001c050155a8182c071035807040c1122415154469030b01e5550300002c85005001414232040c185250600b506c00b1506614010042c1d0f0506000b000112038601000b8010380700c511800310ba5107a0140c01082d0700e440c0001402010405140200750500c007218190700141c10082d004c1031550003503a041510640210307078002c0c0c80b00b2604000d107415024007000c48144c4080240040c08000300600000c5100c1281e00c00e0300d8100c0140e03030b038405501060301d20392006000300d00342d503001031410484541242c0e03640c0e200814194000751120130740c40d50100462011a0305034010350b001d000c1d440d045000c84c03107005200c0c20188100d9040c92401021409144245041002420081005 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 902908947 1250 902907697 902907701
    0x2a070308070804091d010f0204050d021c020d0602070b0601082205070f0f0905060102060906130201020a080d0b0901051912020d0807031d0f0a140a090203100f05030c0a03031101 78
    0x90618090a101c01c03000040170401524a41103940f40c15843c00d001440905068001d0f581103d40080c940954002d4540038031100d0100c0c820171080300c43c2c00c5001c803401607442c10102c0342814041c1200681301c209524141d00300d00e8000c3d16031814400003c5c1005891082c1c000342d44100320190304002c0c1040d4061420601e40031440e00400300c1a03c2405001c00c200103a04844001c032005003005101c962035900040e030701c600f0162403c01103900007a0004081164821144a0041c07041c4125240711900d512004e086801407803210701e21688501103503210346000111356000d2f180c1101e80743c03003c1d94100c2c0c0548140405110b65180250107030540c105550702c0d410030b00441c0e900306803400d0340c5103114900180750150900ea811003000b10a4114000ca0a0162070340726003500241101c00b025042c9209010800d091030a40396210000380e1001c134500b9250300156009458819020404a0801e00c5048001c105500114000e900002c40b4204c96034500006030100e07030301070a240c24280303100400180 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 902910197 1250 902908947 902908949
    0x8041814011211190b0a02212205060a0f0915030e0601170c0d11030a0b1b070c0510050d02030709030303051806040b0601020c152a070308070804 64
    0x6000264800010000d014114007842d0360300c5408160b814030840400c0001109950b070440c03000b0906800b0920011011100802c40074a2600465201d13807075440c210311b240010b41d00c281105000106540440315136101d100c4031100e0740c0e07a105e032544604140214a907405003448103010040c41d4540284990301408440340030303103154981007418100c060341c0a805883c0f00c88950b089482404c00002d50f043c810303400101074103131140c05840101c4400c8104410840b041901b910070f10202d000740121590204207142881d88542c001401601c0c00841d15610701c01c42c032540c440c0c409401c100000020f1034243c00310059070403c44034010003c0030100d040318540101c503113032400ca07840081070011254201c0082d001b103030302c02c0d40d052085030740c1c11000e98201101c090030110347e80d10410120300000c03040c1c840268844018812a10b95441e0750b80003400b0f00c02c50f0303207850300e50003800035112840816445e0801c501c442d038011f88111508000000e03541e207006070b04c0060048000414244100900300b01120 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 902911447 1250 902910197 902910221
    0xc0f0e0a05120a0c29070303181202061b0417070510050c010f0c1205040305160f1104020406201e1b010e0f270705030412030603080418 60
    0xb1840604100600340d8400c2c041c0d60503100e40042c4400028000b0034000c0f003c4407a051982d5801034450001d856440580210340c04030140364440309200c10b9050f1003002c28a0090251160038460180e40b6000380c200030001d4210130480c0002c1c54400310160048080384c2c100e941e22403040040311360002c0070034144600c5800c07203a8011400c840f003202d690f6000014000b04101c000003004025824585502210f00c08004200420040c10402d45400c1096120a071f000d40a0304002d1b1414003042941e601d014030716401200c54882c400300c0141889545080021124410740b0218a050704001c0c0180c00d80c00e8010400c0031451402100c80e00f021410b0040d5800140184210880480740d018901d444bc0341028103007014010a010b5503072158418024103501c0403000d4071010300041c040090240c1d00108840005d00d0842008540072069603032000244142a107a480a80300d00342803900c0120840c2032200c41c42010704020341171001c58504001c6a00b25100e0300000b1f0302d000500c0c003e41015206c5100c0328 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 902912697 1250 902911447 902911459
    0x5090f1c05070608010b09010903060209040609020c28020303030610030b0607061d061915050604140909060705040b070f02091005041d030a180909080d0f0c0f0e0a05 73
    0x89001c200340040d11070140d80840d114812140c0e00c031580d003020f50040345540c03400696603040c03c0021409030b43c01807500900103040070032840d454103c11400c0c0c1e4007018500c44141e0011070540129050720020300c0303082000c40c808c1500042c090b00060ba803400301030141440b500e082207071792440d140a80d04c69074078282d01820184d115100d50600c10010402d01d060b0400d0321221071a20003600201141c103c1c8500302180d502c16202c40000780e0395008004218840502c46009907011030b9540c2d0702009400100400002d03001e42210303010910900d00c4000e824041c3e02d07440740c401c1c041c23210380120640d020742d030b040e040043c0c80f040541480f000d12000003c5c0607402c8019401840601e0110170aa0400e0354410f50f424407005940d14040d104c44010b02e04801c84039001840705d00d0b925845150000d10a2207000f2200307841300d44801f584000c4944828048401c04000140066019020b02a0340c5001c4204c00042003242072181014101900140103079003002541c924900c0742c2c0c3c3e280080500038200c06408 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 902913947 1250 902912697 902912749
    0x120c0a0b011d0105040903020d030b1314090d090e040803040303020d0203090606030d0c0f0b06040e0f0a0519021e120f01090606080d3c0c0303060e0705090f 69
    0x880042c1950315804152480784000114542c00e190040d600d030540d0690080240c2c1c961401d0460041000640d081d9002052030b0704e140041c001d038054030180c00409c003407405860429030010340c0b80070303860030304202840000b07001040820710072031180c1d03480303904040074a90f03d60301c42c0380450091041e40c0064038910b20100500ca05202c000445510605064085a00445030401c046d510f1200d0120002d0600c10064244000281c0b00d10b0301c030750450805807001c240f0204508180342865200e603501225644050b18010030b0001c20072040301d800c009007141880700c0995801049003510188580c13000205409092621901c46030080204031050701c00381c1d18802c1000d042d8a020740519802038810a0030403901043c100c0b804241b411504250791129000700303000c9800307500e10f50382103207880a1118844482044409114200c0c1c450317421203036540c419031141c41c6400707811228107410045207000800c04014415800408840700504212809040072440c14001200012120b807001c00d50181030342 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 902915197 1250 902913947 902913959
    0x12100608090a12050d060b0a0e0604140d082802060c030f01092003010801020a0e04020f040608190c0f0f03061415071a0123030c04270308150111120c0a0b01 69
    0x7400c01e0346016510101601c10003010044940a038cc060880c0d50345010b001c0c0041407400250404105100307082c1a0b00308039110300021141c2c0003000440403440d2440151800451b81031013919485421100b0f412300310305200c0e08a80c00c4240c140034400c0d41c1070380e41601c05855000304032001000444803000680c2ca40c0c486104d0750103034100c0e04940740401c04281d80b080d0780b0701d80b80c020b0382d0740c0780246c1e2003080c00c003458003404031003521010308032040f1000560010f2643c41e00302d0084003e4141c09451340d6428038500d52008014606168101082601d00b240c18800114a01c02da2124280c1c126007083e90101e0180d1b001141c2c1c441e1050041078107070340310401101118041c00090494403100b04031503201061850552101000b240c5865241c1c1002c007074042103107072613481860120750600307001c06003402150090882c1d1403d04002d5020891480c208140074000e82090244204c080c41d00c0c8c1e40150545480c00e0f9904200103003a01014800b180c81d078840c15041104503101500004140c000d940c0d921 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 902916447 1250 902915197 902915219
    0xa1b150513170d0605030f03030c090d05070f0e070809060105220f05041205030f041709030d0206060a17030403080d1806020a02061e0406050408040b12100608090a12050d06 76
    0x3e40d40c51030a05003d40003940340340200d400c0080341c0131310303002e50300e03564503a110980385a01860400f07600900760142c03003021644c00c100c904041c0400320a2340d01c0c1c007402d10b40d83c0c400c3c40c240100700204000c0101c04100030310070080b4170b0318110368040d200d444d040040243d8030341110120740d0b107000d255890105900744910094112900807800380140c60440c9103600d1080b10b10340b0040b6000305c4500c14081c00306001070704842d0303259540d800540000307090110000019081c00c3c0b44000d024010f07406281400a1031500d00c8500b0b00601e0b0002c241c07800d51845a0200d07442e80940e1101401c190800300d8884140e0b581c40d0803103c3e00302030410543c5078252841c80e244000b0740040e90b104006100e424002250745a2401e10340540300f02850710345425543c0ea540d4003000d440001c2084505030720500c00040c42100040180102801e03040c1d1100701d41c544841d1644000e56250b010408100424003440703086580440c1100c20203401807a454070040f56130344140e03450b100300c5441500303151805a0000702c00c4512 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 902917697 1250 902916447 902916457
    0x807170f0c2104031205031003060e0c0901140d02060d091e050d050301050f06070303090c090623010c02130902060304031d0f031915050c0a1b15051317 67
    0x54810b12040c400072650300c400c90300032404010207400d800a905e9040b01d028402441e4410034a81603210b2540d00c1c4c0d903074001991204d02251b0f1255000e42907869003480c00d4010f07103016000d41070110072210f1286001911206030500040d008560003d030212801251ba0484034a142d0010913100315201c00c4480408074090034082640c0318001e00b108a00c00501c56422a030490388014140d00c050b0010800300005588403003c1141403640d25018040040d00054840c4000d0078507980000383e503840d041c400c0540030b0441281504000103042a1aa580c0c2c0020064603210b4041d107103100540741100074000103080380500031354031420101c104010180e0000480d2541c11240400805045010f002d2000d10300c16180c030303503500d50850910410406005590704250b40d0054006885c44800f0038686004c030381003039584814858001480b0030206421908109002126451181301c0310195107901d000c00000ba0b802840f80c640b61000700307941c152080c01440440341c100c02e0b41d00e8080446070049000d40c1c84 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 902918947 1250 902917697 902917723
    0xc050a111305060d120c06060e07140418020702030f01050c190e0a180f020d0207031b030903081b0321010501090b0d051017010b040510030807170f0c 66
    0x28051540072201168011140201c3c8082c2207808200700c0d50b038444184c040e0041d2008100914100e0a00120b902d50281400929842c810841c0d141000a8010480c200400c00c1d0b0301820410403007080355044c480075145a03084845801a268581440081c0c00e06940305030350b444560030501400144005d01d001008629078014402140c0c0602120940d03120214121459101c80521002c00560142410310040060030311000076144003a1a0900c08a0f000524070742503450b40400d0b420201600070500f41d604481c450b1040c034150071135541c0184403424601000b42481e202040000244942407030350342120180d041900c1d203500641500007121281148010a002400400015154025040344055401c4030702c00781c1c13030b000200c12108040d0a0192961003143c1c192440003542510010381085504000300012402c1c5103128104400d0750405004070303010303503280e000800004100e40704541c491988400f0003011005400d0800c0031a00603045184215140000c00131100c0300081804a2400f00c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 902920197 1250 902918947 902918959
    0x60219081315031407020607030c03150b0d0e01140406150506030c091509011b0512040806010f050108060604152a051002070203030304031b06021801020d210c0c050a11 74
    0x2803408210f1303071502c02550f080015801210100302d1861103900b02c182e041010b403d01049542404001745c180300600d50014a80c101c0110f02e205150070a406055242201c140c020701005094507030811140001400081501c1d598111076003e0041045640008280003001541c0783e10744400000030550146a040344942c030b0696021a12400701c0e016681813841c1a900c030306501420032201d10750109240000e480301d20501c1c60803c240c1144a000304040d12100f400390045500d0144030030503224a03034000a05101c1004100b05464940500f514100c0d2400ba00c110b85440b05403c09131801840c481c03806021140f404c1c03000007000048003d489860b03100700200da0303104080341c468070300324041d1000080d0316410800200340428440d64411415251171802040c2446141d03a400d0105da0002100b42c1060130460b82441044da01485100990300ea6405c00c2603101303084210001d900340d03040c10118005036881e500220120310400890000b15848400c540520313085051423a40c1c011105041403180e0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 902921447 1250 902920197 902920211
    0x510090f12140a030e01050f07120c020907020a020312030a1b110f0c130902150d061d06310f06080d090b0a0807170f0708060a06021908131503 63
    0x40800100b03d840150540e8a800220003420b00441d2241e01c00e4580c801c0c050300078424030001c41d800c0700380740e403d46465440f408020741062040c401510b500070040303400e6412595041c8056140419400c4604a04081141c0d23039a90316440c3c9801070451401e10b081c007241c000c3c01c0c07007400c5030030003110250300347e50404590007051001c039081c1e039820b0741d01006600083d812100c015402d503140c21406060f4801000746404403800714000150360085c59005c1012030301c0d100200304504480b0342d0041181c44030b2102501500d00f00d00412980c40000a0b0f401001e01d04140035080000d00080c034101244105206010780c0408001a1010b40f82c0c0703004103440703401081d4610400c40d00a0083c0c40899040305122410300e0f90181041c1c800d010020a110f0034003c4280c5021402c80e409150148a4940c000c20100e141c141038400078001c220041030700340a10b80301c09003485803580025400c0c000d0900180080003d00030761410360098084d1450749660758186a80c081600700c203010007a07100d8031265074104604 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 902922697 1250 902921447 902921483
    0x1e0f11010c02030417070816051305070503040209040203010b031005150102030304020a030311010213030f112b050f01051024050702040203070c0818090a0c090510090f12 75
    0x321801d80111000d40d104210402001c24024044400c00300303640241c8440603500d1002c0d6050400040c05844005500350301402540341000c1d180b1403101040008114610b070410001d01749100140c07010340315501c110005011503609400680e48844083d09407481c002c090b084840c0038042c1552100c1d008041107038000304d95480001a41c1c4203540040c41e40b492580b5685003a00c0302410311101d842c2c0365400704400a050122484001c000310300c02c0c001d2110540280c1030007000d0040e03000c00d240c400c00f080b01c0400c0c40034002e82d0303034105204408610075070b40c08031360301d4403034030309607018800c14819400e080401034202c80d801c1c4113004440901c488002049400a09000c40401c11417200f408680280301403805410113038090b6502c24268141481c4401007070b01d030b43d0041d41003100d00500951110000340b80a00300503d0180c7c201c48400070501500d03080c808068047c4050f401014080c044020414120030321408110b0003d1011000c041e419a484250091a0780041c103000d44401600719000006 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 902923947 1250 902922697 902922701
    0x1a01090f02130605090a0b0a1716141b0601060e0418030917010e190b070c05030f0a030b040e0705100c02030a060b0612100e011502150c0706050c1b190803071e0f1101 73
    0x1002607a81c1d13820300400b90401c0074081a4102c4cc000c10311624402555403a0340318100701c800e010308400c0d250f01228544d03403001c0000303861100121035208142c5206203400a80c08c200c2000964400c2c1803d60b03a40f400d460401170050608050862281c4a440d01281000c40c20711f400c020160b0290f818800b0f19a204101626a82c1c2000070003803483c0c1c01000b80c911211160400b07042220304c90703d808101107207090f0004043c4c82c031000584649402006041006107810350702e807520003007941041d5009400940000303894030401c038406080703d0740714000d82100d0350300e0034225a2a14061445007115051010403a0036514a078054156480c140c2000800c10070b18100c880e40c5010417590040c01c08035280110741500c0c210103031010b614405c2c18042c280010780a80140ca2040743e400a2013034513410026240c400b000c1942000a495820200c41488011180504411480e030407181c0c203503607500c0d00303030048440c00701d200b0005601048108041410b15030003e01e00c0d440c140150380e1190103101107104030382 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 902925197 1250 902923947 902923981
    0x90605090607110a03050304020d020907020f0c101d060405090a02030907240e0a08010f140112051002070812071e09050a0311040204031a01090f02130605090a0b0a17 73
    0x45a88074501307010000c1c0c854402158024406000400c42d0340c0983d020030503000040c0c45000c013682040c1440d828060301041104143d00045a40b807000321000320300944110401101003500c250346584d0025641c036442d080f100101000350420b5418580a60340400035001503a01c80c00901640200050340001d82030045a01c1009241c040d1003400e01d88000d861504008003c00d070800c4044500050b42da80070f2180340350f6914000c0000c280740b5100d4559083c0d00c2016004400b02901e5010300d0004110009071103d20440b0701400181d58a0413418040c2d242d00491014000a10118003080f44043d840201000001012038082c6101e6000e4241070755014114012950410030512041011522684041d041300c00c0141005140a889440d091070000c00b69240304006440e0400400c5451490311610a00c82824242103090103100c00c0d140c0100d10726845408200301c40440d20942a175603030380b032020040c00030180f015951052064040d0000c0110204404428501400a4a86840307208005 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 902926447 1250 902925197 902925227
    0x60e0a03150e0c0303030c09010905030607230c1609141603091403040609031505070e01080726061503130308220305040306060b16110102010906090605090607 70
    0x508034801c00c0040802011030014000007441540289802610144000c50203100e1300b04000e5540d0740080700141121000d54000c038040e0340200304101c00640d00c1081001d0a802d0320100703003040c0c0b05005030924035008090f28207101e03010700400e0240c14ae480150755012280344480500c194448c5404c9150341c00011a602c50303601c040c82c680c14030002e109a206500c43c3d889509022111031103407840a01d150410f0304018049400c1602c20b0040c41410046040750402c150307801d024910700071a00810b5044503494260501c284080840c10460013400d2603240700707440e20380c8100b07248402070010500010580e08a4043c1d100090740d54450954201141e100d0948043c104090003010798046918210007081700d41901104107520900900c0c180201c0c8d481d501076665191100d040d0b0410700c04440d1903901c07121543d2800c01040f100203603000c58034407071603401c441a034044c4246080180d0140c02c900100500d058906031100b010060160300c40da010f6003042c01101c0c01a82e03814010388401d550740b4010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 902927697 1250 902926447 902926463
    0x12090203070312021002030a0b0a0b030903040909020d0b0415240e0705040f03080c01050c040509070c080409060b1804051b0d0b04110307081f030b0c1b07060e0a03 72
    0xb4000300c1d0aa500c488a10f404904c12280390380f29081101040744c000380c1d0002d1000d0b440c7c0d80501454508464060040c100320104245075080201415599204078805c01404c0f0362205012030a5540e0b4411145086400501d5011145004c1c5050318100d408080c115010625010091030417403410b05285251845603040303007400341d0509420329200c45008100c074003006000c00020495000c00c0040400661103180c4c1513465045945405003926030040c00d01d0b0a5a074280000c0000c0d66444000e0f68004407142888480d4404508181c5040e101c5c0f40c101d0300c0100d040000000e0305050f2200203000b5500c620016010340304041c0100426100240ea501e602c1106120440200358156001003c0c0c6072400f8000050f100e00282c0490107031100310b5014400f181c004001c10a100342c2080344941d0060038074900154500300d01158806820160101400d6003455070002040d4840502c11500150400300c0c410f80000b050b02111a43c4200901072b4a000880648841d0040c1c03c0280701c10040d40d41c001c81d1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 902928947 1250 902927697 902927699
    0x3050d150b040e06060d020a0f1202190305060f1c0203190503031b190e09150619050d141e090d03230106030b0f060301080a140a0c0905071209020307 66
    0x18010844400780095074001c5040040d001b0769907241c4001c003864a19030b21103280603040d0440c040c044040c1011000702a50042010306500401d440350492120014280011103844141c04a81c1000481c00501c1d04002d40c0f920501101c4c071442041c5498500c00c030308485048601013440e485003140c80c68010720560050007c5000c1403803640d00114403003512101c0e10700740001c081480f507a44010646071401b1840400310303081d00342401c410b0960710900c1524525a105002d4003c40e145115040b030300f004203118801c1c2401c1e01d80c0700310f0484501c1c142c03d00041c403013a500e006003100050750075a05091007205981c40203501b0318441e0402803086d140580504000c83d1084015000f0b02101070340c4500780500405000d0308250600c400c01c0c0a04495900041c600788a074083c000204046280284036071018001006401c0d80011180b84041e40640c1d031144040b05086000d10b80001580010320030303820703150049000742c1603610a0b441070005558070441c01600f103000ac003c655501380d0180d0907400280b8 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 902930197 1250 902928947 902928959
    0x1005010c050c0409140d0512011d160c02062817040f06060e0a050603010c0c0c170c270f0402010c120509030d0e0306070203040e0f04020409060903050d150b04 70
    0x400400040e0003020b242c005820b030f04c10170030305004000c03003c0c401241000c5528800c0740400300310b01340940b150003a1040602e1140400d42c05001001305007482c0c08040c00d1085540030b1103081c0c1c0001e403a80c050242c54031444c21010b0007001c3c004800241d0504501a240c45424a12480c41e0300304d4640c0c3c0da401c012007503c541d01c0e407007010032500e181654140d0700d4000004450081c00c00051254940c0c03400001c2d0790419500309400e40b40c21802c0d074000c020040c0e80341d10101d840700c40000b0840c0e2110100c4001160b055802904016080000c03e52002004840c0341003a40d46501c424001e814402d0003014941da01890001502419140a4009415084031000181c030ba171a444c0c0780a515424042c3c241004200082e180891010441001600c903082c261014101041415000b660300d0011f9400c1ca03003422544584114001c02c0301c0c84054094000c18255121a80301c041c441c2d80210090044100904000c0c0440c3d00c50000000c0d01c034900031084207240341007408581500e00f00700b802407410b4a4030b1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 902931447 1250 902930197 902930201
    0x60d030e040b0904060b15032413051303030605042714060c0702130240030c0e0f041709041104090c08070c0203100c030917031005010c050c04 63
    0x1064a40069540c1c084100903501c00c03003c1403041d4030484c00171603070003015000d00c00c8540300c50441000f00380c0d0a0003404800c00f4000d11600c501c05481207071201701d003881c4001070b1604114500d0f03120801c0c40c19080c030088143c400000c05400d8000e0301c1c1032100b01e568a061001300d0b500d00d4813007494440c6002c04440342c01180f80031001c0c068002d9a00c0e08a041020400321b04181d4195401d5901c5030f0005032030401c60070004003610315030401d0f810450800c03040d407940102021100d405803603412120b0b140c44955512000400320000020107003140b02c0d41e2a864425031444841c01420501d03104140082c0c5410b0341c00e040700e44100e6211400b1904074560380340903c0356801412445034055114a0843c500c000103d01500060962070000301d511594200d005d031171400081c0680c4100900c080c6400f015842c0050441040480002e0004500f4240d20085004009001c1e00402c036850000c40c0800c2050510007641c0108804040740000694070300040d91080310100005002c1d07000801060b442c0d203416 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 902932697 1250 902931447 902931467
    0x225030204090f20010314101205030c070e1008061b090a0503010f1b17060d1515210b04060c020307170c0c101e030e030c06040501050f060d03 63
    0x688200c091500055854001103420a020850034010301c44d5500303002c1d0380c10b00a0101c101100070320002141054040008000024011100b861541c0b2001a08003c070400c111a01048032000f61030f60b41d0340f10740001c50303202c1c3c0c03c1d0303170701c0c5c401c0003291501040c02d4201061036400b6032051020380c46140c0010603e00119045481100d030300c00c0c003d080000f5161028015041403030001030000030030707006040e882a00e0310700da061036004000a107524404400d09a0103115007145c801c0340c030580e041e0000c1c41d0405585031241d03500c05d0241d061010343d400000401c800307101501c0e01800109000312245208000009241c0c0d0080c101da070244000c100810500d40c86024180d03c1841130300d18001880d142d51091220100d200c0440c0f502c0040d103040c19900511100140c0c44e011200301e0700f080c0f517109000b440c6500e051002001ea001c00c0941500c42c80c041d50003003200f0014030003944e45841c080c40d419038480100b21019076440d42058001104043d940c0d10a03071045e0740041042d01c8020030b80e00c00302c0d900c41c10 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 902933947 1250 902932697 902932703
    0x11060316030b040e012309010605061206030c18060102060916060e0604080d1d01020105010b0f1b0709200a02070b0c0709020f07050f120d0908040905041101022503020409 75
    0x3858091310700c03070030082c003a203074030100100c8011190003c1c0304203041804e10018240307400d5900d0301c9403c1c4081d645207030860711410308002c092002901c400000030300b0214824401ca038045d00c0c0038044400d5040040040e4400d0100b602503a0650741d8001c034091700c3d644130b40c2502d2911690080c060141c00c0c02480c0301c00e05010b000c0c04450420ba11007516a252104c1d901e800c2000c03901d404003080c5040421404003010706d40030310003032000d54074041d19100b65010b502c41200709000c02040400d9080c1100f03e031101c0b02c0a00300c044075507403a903c22204000705030060164603460220300c03209900000140450f903400e0f100342d00400081c0d05d40070216001c0e1304140084440b40c003030803000080c0c15030103001501d1000105002c417a41d030782a031714009103031001c00b59040b00c903908064400004a01c4c06001d6444009203444d02280080181c500001070b0311581c0c0041c0407503440c181c01c0c04284400304030207055807442a000c45071880110341141c450541500c11070070b08000340e072200344014101038100e51003140c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 902935197 1250 902933947 902933951
    0x13060207170c1c02030a08060d050a080c0d1407020d05070803180109090b1806040209130b010e030303010305071a0708071b050a08060406020c0f0601090911060316030b04 75
    0x4166910040d81600007071200c04031900100d0300c00c449142c10300c1003500680c41c0c26a501510403040d5400b035201d000d210701075020300a02c00009000c03501c640e20724801480d442000d86c0c045070300078030f0001820b41203080444498400e608212944500528500b1a9100720003511800c00c0101d40c05c115a600c070100084a01f030113044400034440c4001c1001c0c042d1500c04010f08540900101d00040030f03008540e028204443c200419802c01c0d4071610030350040c05040d10540c505a507951000300d800fa11070075000a4100c045101c82c410782840d25804907803d81002d0717999074100707045801010750b240004ccc007024009403c142810014800705e46030600f0840f200c042d001d8144400c6882c1c4030a141c100d040305864148615a0f0307552151109040708028010807550106681d08121542e569500010401040d0130307800512013249a0741040218001103038681250083d40e1513808000142c05404030464072101c8000c9081458900b0100f1f503031145034821b441e01400307410407000b00c1c017a08485c030605030060307 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 902936447 1250 902935197 902935207
    0x2010302160803060306070806010c0609062405090114010f03092916020319050309070512031b0105040206032d0703022701171008010f0b120114130602 67
    0x21541c014000010350160002c0e9407a440c10001303040c2040b200600d5402000144030400c001aa08103c41107040d54000d40700040c00381d1a803034210014246c07881a140e00020b0f8000011801303072111601026180e090b590021281d03603400742d904445941d00c5480c1e000c40c02d01d0544240c424400d5202c51509805040c201750401c800710070801c46103c2c00600d13043e08030340b150200100b18000328041c1005072030300d1000f146020325903103907450314100b01d41054003008400008528280f030304021902c05024010000c000074201158082d507a0351091041d01c104000c490302c2c4101c40038040c460680b0964000c1c00d8185196136451601c0c01c4003442c0d811341541e0040e00100c41445a51a940880c4680001c2c1ca0060b130f202c2c2100752440d01c90f0ba840801c000f824140b11814801070741d0181c03c5100042a98a5000b010344030b14000c081081825000082250b281c034a14404031803064202880400d07007520091290b0ba1141007007402c0e6004280700402c40690b01000c40c001c01000030306024001c1c05044014140 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 902937697 1250 902936447 902936467
    0xa02010329011809050406020a1e050307140f0c0312010e01061d030a051b030f0a0c091812020a0c0e06210a0b0103122010151d0406150305030906030402010302 70
    0x517002a0760607a0b0b01d0342d0103d0340c40c1d4075541107840741c1006416a001a468401102002042803000902410402c03d0f03c1080080c0140398200351100d62101c000d0030307500c2e081c0103910290307030390007084900b40e640f198940009000c0449007500360603902c00b9600c01e8a00b4100200c3d040a10020305280f80c0c1620803480c1c0d10011400a100b0310500081141c08013012100f114101480c0c41e5069504c00e1154210321a4840040c400c0001c4508580000e840450020403d081725401d03101411400303080860181211008a5130100314500001d1041070000b03001900e40700009070131101100e0481c0c00100c400c0381d80c5240384010404c94803800010080b122401c5280c0d42d620600d280aa10484541500c00c508005c0250410b42c0041500344464084007061000400259035010000306201400d940c0d41070001d0121410030030700054900d0b880d91b14140058900d005040310700855060340d40c540341051850340341ca04a08170b20100d0340c1107001182061003d10030850b8607407002d0003c07030501d50b007008a8050 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 902938947 1250 902937697 902937701
    0x60e011209030c050d020c09150301060b030c030f0a0501080316060b0a030c0504060e07020607110c0d110108010501050a02030409180c0b04090f05040c060c0f060203090a02010329011809 82
    0x39040c0b20341d581500721030480c81d040d460300392150f50450075508180c1c1500c0b200c0e00c8101d83c1561000c440713140443e0005850380405d00401013a0090b551020000003042003004d0014000d6010342664985619a035690700703400c40440e0401c2c000c83c03000d600b0821600b005128180b001d0080e0500680001a8038030606001134000007442c1d104550150071003404005924051050f84001d009550140ca070034500302100a441d680000c0448050040c14a910709a581341000b81206024002d803c413601003410303040c40d480310803001142c0d5001903030318400400d1552155041c4c8800396980c0d0019402c1c00d080000c064094404811200402c4031601d8a80d0b01103551243d034070f0010320205036445d551f40d00b400451003c0c0d501d0b0310650710071a4145414800040c01d503d0301c008c00c0b141d1030f1170800913010807481d04a8074800c1d41540038080030b0000c41400710603000883c0005d00f0f20f1003601c0810030211462011112604501010b02d4002820521074403254045c2c8001e40100c044000204805070f11010407c2c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 902940197 1250 902938947 902938961
    0x11010c030c030e0a21021c03240f090b0f04020a2304030c05040c050c010c0305060102070909051c05041535061c020405040506042604060e0112 63
    0x4000307611034910054864140c480c801d5a400780501030040300c00f20b91142183d040c10f0380410302d0700b04249130600f06400c1c801d0240c003441102c1590301900074500c56100038042c188810f1901c1060101c800756081403146007c100c0103d6003106d103069483c51034148460014000181c1031034014444050007542a0f9541c8000c3c254590781340c55580c0c50400840c1d580d198001500064054400100024404205010141c00803078804560210f490100d0100842d040e008116000480d5070800003c00c1c0c40642540041348543c1c0203a0840d115a0b0b0b03201e02c90800c1e10651000034140e504a54566441100441d41202c1c00c0085411b0041c0b41a50f81e25240c124400c08050b00000500401d1948422131843c48250305c0300e01d29924111300c540003420b005410000041d0400c1d124030100c000e041030300480200d9080002c0d40040c0704020358a06401c1858607140b0440e8101c5144103507000c0c1604c440e030209200700c12103850b810a241004e00300541030700c483c09009102414002234450004018859005440c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 902941447 1250 902940197 902940221
    0x309120234050a031a06240d02040e090d1103090a14010915230a02061504110d0506040b0402130b090301062412050c0a052101230906090a09031101 65
    0xb00100720100d00038254414003402c1184200300d01d00c0130540303c0c0310343c86d145401600c3d85c0587c3e40d074586a1008100080c4501e80c06104145040381c104251181c0200d030076540031009480341c0340e680780c0c5040115220b1003201343d41d50340145100d2042c171800c03003054400e544040043c18108030f01900c5040e00c040c0303801075554040002e01000d903600303c20441000c08640718820500c840e070812100c2c160107511214000c0c0224100c20203100f80d9107041d915508191001816411290344d034070410055080a40380417600340e0701640c1803142090300f9040c288200d42c0c18440c2e0203544550142800805101030388041c0c0100e034550340310300c0c0210b190004040205141c6d00721040d80444620501009020340d07030109441c0161910b880c0810040b0480c901c101c46403100c0e40e04c0d02c40e50b5241c0c0022040116540c1410090340144050004110049030b00107100b030009034802c0d401c4880560300100a0105402c5411070707084814580810300c0c240040e0030603804a44070342404e5042d0a6001c0b500d070f00f1201054405 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 902942697 1250 902941447 902941463
    0x3040c0303110d0c0b0910060b0c0c0f0a0510030f1503021018050d03170405060609010b13061b05011b0908060603030316140a0309120234050a03 64
    0x20000c15400442c0b004452100302e01604945042c0030014140000840c0040c10750090940001d003015001d06c16020190f1100c003080007d0350311034481e0881600190b603407083c14850440b011a440c81c10150185086d4070041c078401c0002c1c1803000703001000b4404050f130001d044d12001c030030f500401a80120400d10300640d401400d420303d9401044000e404003080c41d01880480b2000b03050240080d0b882405480c3c055800c1406104185070854030024a801510030420803001444100040411424040c032000c40740603a0903602d800c0c0005903486003000d80300a901c07401800b008030300d0080c00c10203071140030385460441c10744064980b1404d456002c0543e02c40c0450b15081798218a800078901d002524140700188002d1034103001082e540d2002420b1143d07142c0078488103a00e99803148410801919070101840d44030310110700041c029002d422411690070180c14407081c0e440340b00041810301d01302200b407948036120703410b00c00300303040085e41d07401d402c2c0441613034004100c5485403a03000c00194491505 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 902943947 1250 902942697 902942699
    0x182102040615020715170408040801050105031c030c0e060a23070302281410110909270106140a1a0307050f040e0c120f010501050711031203040c 64
    0x40004581d40d9410000000e656000055a40c950026610003500c40d01c845070541c0302049402a11050040c001d0500c040c0117140c104000c000820000c1c10483e94400d001744000d0342c0b50303003c2503100c410701b01c002420b00050b00c0206d40c0700ca1080d04100f020201c1c2e030030703c0a040c036502c1001c100e01741d00c202d408a0216602d1408903036040600c1c040c1c81101b07909000b8850a0070404d550003134444096449549c1100411701d11203010b4103210018012580d8881c00401c1061503103101c154a811540140c003c5142c508222080803044031070440d0204a0300074080c0000365144040040000440c03103090620040001d00c0b0420131030700344a02e0010304101c244070708485802100304152031885800c5a100c480080c0b854a1800f5810b60a482e0829a24140b190705e030b40e4840d0711418140119445080551101010b00c070164400c90003c02c0758004118080406994454160060300c1c800c4c45094001402084a440070400035003040711005001010394410b000100d2a030800c940003918107031b441450b0108 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 902945197 1250 902943947 902943949
    0x117100b16170c0709050a0e06010e181507051602121b120a0201050c1c2106080c0d02010507120e09011a07022e050a020c01090f06182102 61
    0x10501020a400c21a520b41625426219200c040c24420307111040e031111b000c03a020f014141c01c8800b0751194041141d0304d940c0d59891555002105685030902e410a103851101c8010700460700442d0394400c0c1040307a10b580c850f6541117400d03031b21200d030305a002040c5000741401030307990040c0704100c90001c0000b0440c6a80c10162010100303510003840e0310903100b403002c0c4100d0403004210b1031507450f02424100c0d21184000403081c109142020000d018006d581000c07654036030090120f0700712400301041c0c546c502c0502d03200e20084801b0740c000c01856034040d400b01c3d0b44916004d0441c0c003080788180350507800d1540071364440120f81610111a00444c19070280b446c44da0810800c000c0c01840a0304041d1140107101e110200c0d1441402e80290140c60300e15200403c0040180c4203115880001d04a00d500d184056002442c0f500003080c094010700500c41448181c1d84940c038000c05940c1005800307810079180ca41c0c00e507056076824014450040903000c00160002403503045003c8840c085100354402010381c8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 902946447 1250 902945197 902945213
    0xd050d0e0301021c1e111b0c0901031b08030d092604090504060207081809061806061315090f12081911030f0c0d0504050117100b16 58
    0x88040c80c080d0380b0602c10032002d1801c0f50b001400c101c940b850000b520000a04696007070110304089440300c42d0070541e010640b8042a0024410400380030321a036000200010b0a54881c02c1080d80280c1c8541c03900c0052000c940d041c0c1200303c0101031006c21a03001a0349071101303801c5800010b6074515030f035550a540b50902c4035440c080308039001c0349240103170942800010f015103070246020340b040c290313500e0340060104446035040b600480c0d000040c00c2c0d107030801c0b140c80380e4101e484403441d1070264072828003044007824844481041a5241085c040c0c1c0d5a49110038401550000220031420503104140001c3c0c1010500a000d207440507555010308081c10202e02da0411b41c81740d031100f50169807120680f40070440c0b003001d03212528909180020300000264044501c81400c0343c2d914858000000c65500e0140c107080200712006c3c440702511b000c54580c4000341c400340250311902c0e0200c0c0321800a03030140c40310b110b262030744815036004512543c1d8442d940f40b100d941040c051a401078040318242c0c0c050007050 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 902947697 1250 902946447 902946467
    0x4080a0819092a0f060c0c120f03110c0d0807060b041401030b15130f1e140c040509060d060e0a060f1406060f0c1f090b1e010311030a020d050d 63
    0x10030f03071081c2e06141c0306004580390200d1080d001003200c0e07007041c0317400c000400748010002c2440e80c0096805141d076081054181ea10303250200d002ca02c202c3c00c2c659944c880030a01c0040039400074035440711000a92100c00266101610480e1402d948085440141e540d921401e610fa45804802c0381481d810342ca49036144841c09000000f1855840380000c9081c1c0d20075801c0e206483d0000380c0440c1c0700c1c00c3c805869025040c4204eaa00e8860322071074a0702d01048a41c0c0c003203031040e445003480d822a51104079000030359220700e0040603001340055000a0035420b04490211240d07225410006005a0751034103281400c926040132074140d80c44100150851040d405446550303864102c9403039460810b80e0010741540f00b000c5403005402408250210388030828040b48045051411010141e401c01002640081c4110b80c42216540382950200d1340c03043c03058440c07000300151072808910903400c41c0c59020f40030844841c815494441c442c20b00006032208903111401074800c10090011020100001d0107078a80 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 902948947 1250 902947697 902947763
    0x27110307080604140a0b150111010c052101051c0f1202060f01090c020628180606060804080403020d020a0521280b101d060907030504080a081909 64
    0x4465106004030703440306e443c02e4200c002d58990900840103c001600c24420007140c104465181180108000d82c00c40014074150410b00c00211421800300300702c00202c0c40a0240703c0e0031240c40111003007041c0e01c640d08898403602030003810178810004c0e601c44904074650260300d001038120505010704100e1092441d805080d504c031080c0035030869110025138034100204108548204540c051a50881014002c0807280016500744061080120940340d03140410030f045070014a804000145c00744203210740740c0150342c41601a03103028036540810010b8042a01c040e80c0c841c600250006107a510070240d0038035003005c02e0304500f951030481565401c209078801c00c000302192945190903210311294410582a80c88a4040c1085d11401003104e0302ea9803580001102c0382584050449a400c1951202c4c45450100e9440740e203a5100c100480a40e0030580e401410404280001103074036000d4007460b80d00504007004220802c800c0c4007030606595002209540200301c500b118004282480c071f41c42e02880c6 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 902950197 1250 902948947 902948953
    0x8121003030f032c03090907031509020c0c090109050f2a030901110328180f110a171005060307030201140405090720012711030708060414 61
    0xca1910090840102d01d5900e070b041503a00c805090004180c1c034440c0c0c0d000312005103000c05141c0030a1400d43c0e070741c0c044100d2620550f00000012461482402100a014007500703041402514004032200a50400d06400116009220f15154a6150404010700801e070b84040842e907800d2410a000d2109406401c500000c62000301c4100f4162040c0304014441c2c0603c406070f59a50380da02c09460041009040c401e40d0410000140030107588a2124003400c01a6800544007031006104248122036003800000c0107070fa40c110f80319010902002c0010300c51f90207004500000d50a90000a00d004100c0c0c1010308a01d8031200c2000c0b0000b42080314219404803c4000c019605000300013a1742c41e00d00b84002070401c2503480c600101c9103220800c0d10020724001d800e81100b41800d1401412280c0900d1400480111b10403091161040500590680f00081000500c2808040f02049101da01507802500c2510820312090341580b002c114440c0205400300151405040600c0e01501c18102c541808010354 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 902951447 1250 902950197 902950199
    0x160f06060e073216020d08070305071b060c1202010b030f0d030b0d0b0c09030f1002030a0c0f210213030b060a0e1006120b030f070f05191a090a03081210 67
    0x1011440c01c44131200a00c12600d90000e41c0e6100003403c600211000403c08031010500e0030806412902800381244920000a03071a0f8809416a501d0026442044001040c0e400c010000c2290f840080c503012406100104080400d100444e140c02c00000c17401e040c13584200701128203640c1c140700310308810b0821900c898a1200e0b42d10313480903410f0041c28401c540d10000404002550b001c2041c6101e1952a500780c4200d0380511600340d000350005c54118503414100710860601c14422440081c0c40e010f2034560718140942e124101d0010424074481d0312055508028650b901283d105116005601c6007011910510f031020a00550302e040b80e00500011140c1e2090013146420650744c981641c96500e805c00840c0200c10010000d02039844100e5014098601c084e080104042070090a44801c040c076a04260365a2042c400c650100540c40c1840301a0b2140c240107064001000043e128480c3c948182800c400800280c00050b00e640304950b01c00001450880e40c02c4200c220640c4090304001080c031103 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 902952697 1250 902951447 902951537
    0x10c0221090f100e0f010302040e040b100b16110a03031202033301030501140d0314040806280204061e09030c091a030102160f06060e07 60
    0x40d2150301031203425410003140003081030702c0b2911090380c480c070b000304220b590494041015005010418440c0e0090400341403580055000b402100d007103501c942041841a40c039900c074003c1610000d8415050212090300000b510618500a0040c0b69031290381e4040c05a5189000d151429a01c01340c0781c082e030282001040425003101240440c40d81c04180960baaa9030b1400180f4038100644500b00034201d03812000e2405030b11a542e070701c003910f000c4e03d040101c0e90300c408012808040e0b00c900750382c0c000d08861880d00000c0c851007800303000180c0ca409550416803101202401c0c140304840e0208500c40324000c01d445030a20081d2040002000750046103002d0500c90018820801c4052071a00c0d000b443c0b060103605031040e00c0384001540c108450808103a00c0b6103242001d4062900006546400a002c040d02460180f00b00c0f41c41c6884c0071240b2989914642d641c0000e49030f00042652507a60f510400544085106915441400d4946e10440ea203c2d0311020304503c4424415416111038058505240c4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 902953947 1250 902952697 902952733
    0x180506041a0108040303020f041716140409020604031a1b0703020601211703090714100f051315200607200f070f050904080f1605011409010c02 63
    0x1da65020300e4240c040d0781e16824150f0180c443c115401041100005000440000c82c3d2080b8900201020030754460740000b4200c6801421940101d811109050b40c9002591510354883c03a000b0380301031300c6103042c26920f1f268843c2c1f0030508204070214020310700402040346400071b007410550b00d291040c1400c0c007034140c400070b42e10380c0b050088040503160a0640b82072407103040d40054641e9071202c01225040090f0b0a11001508141c51041c011704c50b0344030104800c910049552440240070f0114552034880c50001c03100d5034050001300702405000c0200c102800070101820b80609440d428910800b01c1f0700d04020025448524016280c40800e00300239041034000c150f50742c1242c2d25240c51140342c500e0030700c800042100ca00c800c0b405845042c403060b4504401250503400c590840d141003810543e0b0700e043c021659822a4001c22400d01002540b803107100c1080980540400c1c034142d141e10780020303070f550781c2100d0301c407007014080319655410464503101c02d000d50b558115091000d40f441084c2d03080c0d01c031a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 902955197 1250 902953947 902953991
    0x40b07060902040603050307050d03051024031e0902010e04020906120903090307090506030d18060309060b0603040317090304050a050d05010221011505160605041b18050604 76
    0x4010340c0c0398072280080d540e0742c0c0c00080c003a58020f803e0384d81c0ea02d981c1c50801d60307540f07036001148040b07400d1400082c0052a844036120403074100c0003500c0209000d032104030100340c0101608a0606940e425101c80c429030042d13210301c245200e4039001a030999035000162a008004145e0b603c50b500400031500e0584a17442940e601c0c0c1d880c2032000c0881d8a90b40f60071401d6004100700590144201304001030502841d07000341e40204400c1d0240e41c561808004201c1c1c2c03c5400c440d10086001408030200242803080d80840045801a80700103110701c10600011790580c002e0700c0a5000406100100c2d40c029003e8019981250302c00e00114034191820002c1216816944292481000510076242c14801b00390112159024404440c8850f404050644c41007101c081c050716002c100b03521684540710307000d9000c0350f00b08441e40d02c0c42c0d98000c045a4400e4003030703c0014001ca4500010034400500031643d030681a02800300d0884a60a032480725a28000302e4800804051080d030506040d12203240c00020304c0a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 902956447 1250 902955197 902955203
    0xb030408040b0901170705120c040602071503090f080c01050f04050601090b010c060606090602070b03040b0f150a060905011704110d14070b0706140906071b0b0c03090f03040b07 78
    0x140c03280f842c0c400603514070412000075062800030301c00700400c0c164130000034a03240c00c5070018003415031149030304004a801079000304400740c0d10a007020f2000140485d40c00d46002e2543c030b40414200c6040e9a10120f07404289021a6030190100350007000450a00503558405014040012a80350a403105582c80030103104d40c80d00a03984000071b590f01d0f40301c2c42c034030f00070385800200a029455607071000801088640c49418014020101c0204030f804104c400ca81c082c0350442e01c00c20301c50300c0303101000c403625801038030056200b800080360081070b454400e03102000309410740707900904618080014109044640752140b01050310000c0000064080403d82d1420000740d46421100070f0501c0c01103040c40c06440c8825641c412100c00041c400401c400900307100c2d218620034000745085240816800300141c4000c0d403241c008200081e41984101c4072541898281e90b0065100801c42d00d4581c0103850541c1c0321640c003203000040040c08442000b030740041150352001140380c00d00c1d043c0044042d0240c0c203401 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 902957697 1250 902956447 902956469
    0x1050d051b010c0c0b041a0f0301060e1c05060f06010c0302030d0b060c0708011a010f1d04060f1211011b0b13200a0602010e120c011b11070b03040804 66
    0x70300c016034415000320040036132000501e06140c3d2510b51070b828030b0f00a03100e2800341b21500c3c894070402c030480382e05540540e0740081e42c003030440e400c010094035190b4071100d2143d0001601002449684c4c0344144844282d0b0103103000c4c4c401ca0404111880000d440186864140043c004060380001e500200b2258108098080001c00b04000c000164461151484100452086c400b003c11803100c10340c41411551101e01900d2032101d404001034a40b18060040c00001c10014080c54a8800302400312500d114001400020b106407941c42c464084180358118010f800c150100080400421408a40c0c0c05002401d011040b04204128268440c0c40040010315042c200b8020a40c5000506000320800b5032104959111040e00c07031424203420313040500584200060100044c110b801882105001143c0d100509141091164400115800340d0300390000d546d80c410400c40c1da0640c0c003032140244030560340c0302501c614000c04001d180407426048092008410010701c00018020b80440d42200d60f28509 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 902958947 1250 902957697 902957743
    0xe012705030106080d090f0b19020a06050a0b0a080601030506060d05010e0604121d010518120601121205090105070609030c0506040602090406080a080706050603120a090e01050d05 79
    0x10000000800d6200c280c00d582064008201e1070360101e800798041d56903035513041510307030303511071034280240c01348110010755008102c600408104140403814001150040341c110600781d94410040f00c0048413041800ea68a0440b0310403440c0107002c100003021400c00a07d482c0d41540c55498407803a000e421248284a81d8030080e04021007904058022140081628100d00d45410425114041005d840000601d040da0104241c00c07541c0c41d5248000d0180d4819003818800300c03030700c0d40c0c1d40300d030941c199401154403000700740ca1041005807031b020b401d1314609a405001d892a10300c44d9001c1501e015000d000080c0088461668042e06507520980c210300d010500c00440d040640301c240940c440500540501d00421041c0420394005189260b0190b07810803010348e8032020652100d04c00750005210040c00c00001011801c140c1007541c000c04000c0603256541030140340c04120758031166020010400e451350800c07941944540c9980109015140700941c00c03010741c2d44c2519214121034240028400c03138a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 902960197 1250 902958947 902959007
    0x23011503361202031c0c080106030203070507050a080a14030108060f040f060f1a030304050622080601172b03050403030b040606020f060106020705011205040f06050f10060e01 77
    0x3003424916030007041481c0c0c0700340b401c08001d480b039014480c224010004100403c00d0803c061288560200e81551006c1c8a0390800c48110040d600c0036042e942001410702c2540080740341400085803891040e100140c1c0c0d0340034008050b03e0902825010031080c00e042c40104010640440c08036440b000c1d40c406240390740c0d5585084280c40c800442e002e40494a0811120f40c00b00f203c0c0d010081000740458002075500c0b40c0d0041503a070384100c0c000c2540290090280340c0b5040181c0030400142c40c030003500a184541c965604d6071a105007680121502c2c85500011807095806210001d02100080084081100141c2024850315215842d0b0000c2590f81c60008052510982c01000d680100500500035180c1d1594000c0d9030340a40b01c1000d0700b501501000141c03450001666804a42c41a110b080007142c000d990b100040c04020425500384444022200c00203e80f0310406101d01881c01e43c040e50b9003020380f402b40c02000c49402000074801c240c01030580580e040003250320f03400c3c814025620f140340541 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 902961447 1250 902960197 902960291
    0x170f160e0414040302010e06060907170603190c061b0f0210111f05160c0f0312140114090603031606140403020f16050f0603060423011503 61
    0x1041451009100c02c007400105541900807003140b04564003143c64584401041040301d000548144003c41c0b08002c2c034202d01d003035451425900c0b010050035140c4d012400802d03000381000d103032412a259202c2d00d1040c441290020507000140d41c0c40c8225503410102940d40302c2811100341d101904c90045001e269110a01c0380c2c5007680003d89178026103030806000c0101c4807801c1d164000104940b41071034002029901c5480800b24101c0c5d499803003034901c10858640b140c0e40c1110300c0b002d90402060344001d0279491054002c82144010002ea0300e585585003000a5100750190103034244514111800d000c1700341d90000907a12101e070380c44180b240c030040c289041c00040142600c0040e11400310320401c41890f8002c1043d4200c0074200003990590000081029810a2140505540810711002e00c001504041c000381d54001e8016000050727075092010b0919042006000d21001441c0100c011320142032024050309138011a4241408904c2c40703401c00c1c1501a03c8d1410a0312070714124174030950844560 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 902962697 1250 902961447 902961461
    0x40b0a0302070813030503031608100311130e070f09050601020717030d140a0c1803030804081b0f07061407260a020a02180402030a1101020c04020a170f160e04 70
    0x401d031880001c0717649117006900e0f900221180b11802c28031070714401013140103158942c03185910340c9070004180d0640d92918201c2d9602803209400444503034840180c01c10510900c40350380d800800501d0102c1c544030002c00000c601d9040341c91814205400d00049980018070042a0b51328000c0602915200d0701c13045140d80682c0002c079802505002c85589035054581c195406600845030900406200300d05c152180c0008440d00304210106800410103e445001016002031041c400d4606c2c0c1a11000130110030342d86009001095049030342c80000021040140d03c00074802c50411113600000700000f00001e00940c2d501910040100170000607280315024044949030741d1a500603260204108002d6907200310010481c060f07281048400d400d003c0312201d00b480303150b00078001d1015416940d560890034500d041c04505600c20034800c40c141d95143d00203000660025030321846150101d01c0014000c01c2c01904d40342004100384240001004000b00c1840c1c881081d080c007040030039046000c03c1c0200f40b0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 902963947 1250 902962697 902962717
    0x51b0c0c040c27052103040306091505090c0307210f0c050a034e0314161d0d08070809150d0b10050301171006080c01080705040b0a03020708 62
    0x240003ca40141040d1840101919401d599044075604c103e6407042190802c1405407246520902042000440d039401c0484002d00c0b0b0070483c00c40b0381410504105039075040c0c802c0c007030680200803a85210b0408102050003040004280c03501c00014100152000c01003040c0903011840f501c0c1004244180b0000d2040140009800710403210b699090420702c10001c007146107110002c0c1c44011284142c0c144c0c0102c00c03103216076100c01c000510204000380c8084170084904c1171545030b0240c041d00098028090340711342e40c1b40500c10262009460024019484020700c0410b04401200c8006580c613403001c86942a035100004540d508001e003481d050a0160401695020881d502c020621440000150200141c0102d0900c4407602450030080c00c105180300e9040052001e1004220804c003a5281c0032081d800c06c4282c440d0142d40c00e68850669840b0f1300038503055800342c0701c0f48006592054503140c4c0170407a85005d83c241070038203181c0782151003102c01c071900b090b0b0049100014003200301d040b1130721012 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 902965197 1250 902963947 902963987
    0x905180a2a0e101e0f090902040b0306090105100501170601080405030f04060e01030b03010506181b071a1b0307030c09230312040302031f1e051b0c0c040c 68
    0x5003850024240d60140d01551151340c1e040201c03420080d007050180700554125500d00c0000c14244090b030001450302010a0740e0180c1c0314071454140c1d880621a060140d0f40d04400441c0d40d00d888940c130840c81e403e95106a0401c40c15a5154550170a4085000e4014409103070900703d0361600c5c01e2040c03660041c8020000700c220005000140c150f0840344c14109203600fa20240080707211641090301320382049407543d401600c00850030590500d0a41002da2001e020080d0481a20024404564039004404204e4800b0303e2144008039a4a40070341c41c076400000501070039420a945240241640070181404042c142c49201c04080d05018034001c001400305000403410b80340c2c62001d2011212801440913000780a020f24102d94050750004030340540e500500142034990701c0b8141810b040c809007030007040380e03a543c1c0203201c04860309001d41604500b000c90041010300303101c14a89007010950001d10011201003015003880d00c8003040811a001c0f04070340010f0710200c011010740b04400807080b0301c22120 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 902966447 1250 902965197 902965201
    0x10b161e0b070519200106090501090b0d0f03030f0b1203071103010b030c0f0324041202011b0e0f0901060207081002040b160c0e010905180a2a0e 64
    0x80124400694440e000381c250a80da629964026100343c89100d02e50644030090450484800c0d01070111a08409140b041da8003c0c0706800303e0707190031a0084d802604105031200010000b00c0c0303075402110f03004101150542c0b9040500c0d84d80c40e07004204035200406054580d00c8101d07282d01183d0102908010140503280c0111420800f0340c4c0b41c0e030041404980a0320090001000350605120b0452440b1019009003424a040400c01ca4002c17030369841345a0500c07070185407900741c42901341000300e107003008410649642000d10300b490903181100042411685883c00042011090000b090070307914080c2002c041380c45600f00400c580720044850650400d608100008410790700003111800c0b00e41e20780c1a92503a86d00f1444400503481240301d103040c00c001c02c1c402086400c6007800340b00005403151800402042d80d558482c00c4440382640b0244449544008001410031721201001001540e0406004161400c1c1d880401e40c040d0100240e0300103091001d90005004540b0044001d07107100e02c0102418 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 902967697 1250 902966447 902966483
    0x10b18090a17032a0301090e0f01020f04151d102601050307140a0314071d060120060f0612010603121404030809040203041e060c0905030d08010b16 65
    0x30764070540304160711444c074210403c0c2e07045000c0e289048601c01d1140ca14956482c20010b24050701c034541d241c05060007460004021081e0900c01170400700590549192207d192680c44003071300e44481004410b01c401851243c000702d1004142c0f190000b81215011001c0602a40854000084441e810313803800b04003c11403080b603900fa0380c09049503412000c0b0f840c01c90f242c0300c00c10711400c0d00d642d944e41c22451001080c0005010054260361001020080b640b00c04c0d95000641c1c42443e821441c0b40c0025412024481c0c9941d12806682d002c1c003222a90640d07404603101e03a0b130ba50f9240200300e46a003000710400300d03515a80300e100749064040310314020702401d6268184a00f01000e00780702c4101260f00c9260203041410000e0075217045903085600c00b801c00340b8903403d000c060740c001081150245400b16107070001c690b000030410784603400781c3c4000618a905c0440646810b03565000503110b54096101e082e01c0310340c4a10507a042d80d11060006843e1501a002310b0f4a000d2110303001006028040d901e1048 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 902968947 1250 902967697 902967743
    0x120403060906022a010e0c010503130218040b0403140325030f1d010b01180e190207030203030709140609060711030102040608070e0103090c03020105030618180f010b18090a 76
    0x32003201c400802585d280c101b485a0f1700d140807542e0501041c010300006e441c19008001e1303032003064000392584041c24a850204030310000c00300d400715100410082800305050384442040e001000c020041c9246040071848820080100c01d84040419105621040454441d030008441140100000e10599030081200d000320f202c41c1001001941c6800d150703a001d50b2040301d84a00c0035403110720300355541e410700e843c4140c6410024100e10451800c1a04001c5490342031006082d0303507000342e0103961a4100804000e00b0707811194000c400581c1c041d80018001e6450310100c48912000f103e4090351507030549410b6040101d4458060707855440400c002031003541140300e07684101026a11540d800c84060010741c03c0318255a40503208400d44c820034401940280011038201e41c00409044004908100c1c0d100e8003071048441c60710f4040d0008a00075044030400a0486681481000380300102c030f0301e00843e410710004088070818280070b601080254009002e10621700e81c00070042a40242c00c105040c0c0c03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 902970197 1250 902968947 902969017
    0x6180e0a200d2915070f0c08061302090c090411040906030b070305091002090f10031a01030e0c0f1c0803180a050a06020c01020423040e12040306090602 67
    0x40c06401d02d20310142400f01280407a074000e075101c09040081c1e00d14024070140751000c0c0324141501c01c0402c6802e020a0300340c070b199503400784156001e00c002c9003880804e80c10081c020b014032402514000b140d03070050b581c500d8144c3d402884200d00584a0f801040040c003d40711207414a00002e90001e0041501c85058000400345d0380220503291841e12007a01c12000c451040345c4425668200c16984240030900d86c00415104d00002c00c1c0134a086031010004026400f07111b05c20b408a90345060b015902403e04140902c410001d090422011400c6441107031035a600002162154401c90510340311a03441c0c002043c10b074086221452816002031030303c174223141c0c416110701d09400d4070214041285440001c041d1425580f01e006800b0044150352000069041501941c002d55000d00c0046100c0390810000260303002c2a41c2c1110028002d10103000481d8510f105805098001b40d00c2d40d8180c080a004a90441e03a001c41d0000b680442c6d818220020302034164203c10a03008816200a20f034005a8504 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 902971447 1250 902970197 902970217
    0x11031f0e0c030307081e1c0e100209030304031704080307110f04062103050d0c0c1a010f060c031202030c090316061409030a050a0f0b0106180e0a20 65
    0x80ca401e0035020030940c0e40d004614000f00031602c10054000036184e81144101012003102c0c01c40d0134021000c400c80080304004245d8008195510696109108200600c803903a5550310000c51812040c01c0c0402c0d264880e5000141c004803042124a518840c20f90446000304860019640c403520a80380664003098282600c6100d0245150921280d240910990303048407a2510441e1010101090442c01e4403200107080c0c040c450b00344601248005079000e0101d01e02d001e6551948070800c00c0c0b60281c0000074520122040380441c3d0300501500303901d4004c0d9400d8074428137200c980c1c0115460226171840c0c5407054001098004828021101c0c41e405c007400c107100d000c905440035074000102007929540a44a0b00740018085030503d81c82d2846000244203881019041c2d559140042d12500c4c80d0948982c000c8076100e40d81e204403418801044141405420035213001c00031400d00381c514060030300103400364504034151038000c90b11044096010200740007014061601d42074010000000c141c01401d03c0e0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 902972697 1250 902971447 902971453
    0x2610020f1305090106080f06010306031209050307090504124b0309171803071d0c070b310c090608060c0a0c1e20030607080411031f0e 59
    0x8286468200f1840d4183c9000342d56801c06680e54281e0000581001307006107051690b038000120104070700b400b031000e176444142c40c0c1d220b409284c602807501d48059544400d191503d0302042c00009a41040003900740221440c0c501d50b618400da9070300c5520410850001420742c80d5041042841e1000000803a201450340314600c1007207071032030081d001d0b603140031002001380d560102488401d4000d00b01905907000310007a45611181081c0110f0701c1e006098000050b43d403041140540504c0c14034808503404200c0b80100b44c200001561400004000a4000c0e00c3e0380400d041003c2010f100385950f0840b903062442c800004500070b0400340c010301e038540540d02602d030410002081f07081c80000d48501402c1e90002c5035251841d00541102d4000c03aa010841d507182c0070140110448803068480480307640648da8554016520802e02c041003c02203c0c02070098019800b085038440d00094282d0317105030400e9601e07003418000e0300041c0c144a100050004607210902c0301c070a0740700c07440d0303c00c4000c64800011 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 902973947 1250 902972697 902972699
    0x31b1207032304021014130503010c02120d05041e03080103110301091703090a1704090c030c021e0106080f0f0c090105090a0c0519180501092610020f13 67
    0x207070070001426018202c0104182d00041001070401d030941140101181c0303064450f5040f0200b86800b03e5000208904405004407020f005a16081c4181144000c090009188490310f1303401c1210f8a002d04424181015030303032000181448808407003940d000c1c3c0399425505e50014035140103800360b4030030702040d1503244580c030810055040520507a06425008a400440c0009080e44c0c500300c0d5200412444007801044030400008852240034031074142d0002981e074440e030421144008842c100d0240504040c201030320001c0080d00803513115484020038400c0c8480c1c1402200950142509611510b8544200070022500031400304a0b01200400c1400344c0d12509814010452280c80038014507901041240218845082ca0f0344040401031107400d19600b0b095103040c60711400d00c1c2c100c1600300400d0310b40d04c0031076000b81c0030052040540b009080980a0031b00708400c94001e1820001d0404400203140d00c481c101e01070801c801040024144001e55a9041484000b8000d40101442c1e04840d00d10441c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 902975197 1250 902973947 902973971
    0x18020607051f0519020715050103050706110d0f050306030a0b130c092a270e07021507200d0c05100506010e0f190b1c05090a0305031b120703 62
    0x74030b405101184070034951364044558440003540100011a000078050034403070420b40c050b0040c640258010b1002c2c01c892490228094030030300450580404c01d40021008802ca81d400907254446132070146000340e16580c507140031919203128088082e020302c03900d108000a943c1c58011552400d40304000840c88180c5d500c405100352640d0500300540c515507100e00ea030100c0250b0048804806a501e03185c14140429046a042035450082c1e40c040d41810103018440d2814884880750801c0103440200b0700c191244a00308090680606030908015030301c000b610001c0301e894030700100e5908a4007070765081e40b0070b1400544041b0340001c00700c4050207207444144038500c041c0b288900c18074068582a03011500901001f003000c2092903030302c0e4410228418000031112424110700035102c108409541c80050b508452008105504980c030181c0c2061300300714581c900802c600d00000e5150610b5500d9441e00e02000c520350314600d02c3d8443c402004152034000a89405445005114645007001200340b014 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 902976447 1250 902975197 902975201
    0x50f0c042304020919060f0603110a09150c0c09060918030e0f1c1b1710050405190309050f0f010e0f04020c0a140c030a0201080a18020607051f 63
    0x852001004094500003009804c00c2c3c05032541c402043d0503c1500d442d8408018412902240c000706159081c108061003007981600c1080128590352401c0c60070484104802400e81e8078a0242203080c40a403024112624060800c40030b45944c400724043d079440c0c030742400b103008148a215513016070381440d0001c1080403000111f1018650181c4d1071881e007c1c040014001600100e8840b140c10010704140d0f1034010b042c2c050b140c00c40034170801003544401046250a018010b060b00480d84005d044030700082442c4001500a40182071244042580d50319414441c4c18400f402c4840d11180310100c2c415800c06601c25144400d0b144111070f18520780355504103004400388080b0040f40482ca0801c0406514a40310200c2c00d08084001e10141c40c00c0c100d0480b45003040550b00003110100b000c501c40c0d80a1140a01020403403440580c0140b004040e2a00020300180300a44403602550361000c1d000004506100781c9000160007800c501d5076003403145030180e81c0f0b0840d003a0f00b010403403508070b135803040c00f82d18 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 902977697 1250 902976447 902976491
    0x4020708090d03030b030727060e130f0b09060a060503031305090604060915030507080304050a4113090506160c0813031a0105030d0f1205090607110d050a110a050f0c04 74
    0x9030510aca2590700d99590050007c1c2000c801c1d0303007000748e1000f5007001030b85a50049109040060250507141480c2c42000256034494002600c01c1e00103100c1603042c0281010040e046031412903a044454807440045001803d0036000303050b01d1410100106c1400050303548810407a40b084007200e6201ea81d0f0100c0b95107031700542c052158840c40b0180c041141881482001c0121031345000c1d040300103000c00c034001f421000f81024104000b0a40c04140742c8900e03003000101c2c841d808006040c0032105540c4d44039525480c0c01001c480d100f01019030f070206114450030005030216404194150398000010b100100c031a8188000c495002992400807444101d0507101412075402400915403800200e070305481e00700202000d00b00300410502c405100d0450741c02071a019511800203004c003820210303402000c5500d0008906200d50000c010141415401000ca807040d25503840c0c031104400030f18400908000d5240c001500ea48602c01c24800320704ea01160503d62998211006c0041e0b245050001c01a0303400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 902978947 1250 902977697 902977709
    0x904090f140102182e020d0905060414010804150c213804110406030e0d0806040b061b1501050307060519030612031d04020708090d03030b03072706 65
    0x203071500b0525a01784403d4102505c400c0e180c0b41d503550300020b80300116402e14001d500c0010382c42801305012603a0000380c00300c080d00065682c2840c144c100300c41949890000450b19042080c840002028400043c1600783d201c0034110040c0b110180c06900106204043e801000e8403075101814403240740c0152141c1c030403e000e400c0c10419000300950a00c0b661214a04003c040070b41d1215040d2040d40d601c6c031607460f41c96001030044c0d4445090560040849410120078481d40d8007002400c0c40454001d400154400c4c002c87d004500405882c000c641b25014a05940d00c441d003270034054010320b42010407580304614025503214a141c2c1e0740c90030160f44030a5482440003040c010003402d03812403102e400c0ca4403200035030b0501066855980c948000b02c0c00881d01c00b035000400c101d401840741c1c4100e00003201e45250481e410350410110352641b04080c81a00b1541e4841d40003004800300b054000e42059811800040c207880825a82d51580d00c03d0026000070744188140030020f03550700318180d01c03034002a81c1d0303 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 902980197 1250 902978947 902978977
    0x5010905040302101a030f030c0601090605031207030207030804120b0702030405010c0605090a141b040b01050d0902190b0a02250608042f040c1d0d06020904090f140102 74
    0xd0314001c3d240104510494600c0d0380174580700c800c1041c2c5040082e021412a803500461799600c0d0030141600380041a0001c00e04039007450410403051b60005401e07070b1210184010240d80e100503141c2680b07046410b500c010045100454005800c800902000e1440c50040d00440c850b9522000100d0702c900c031f0380c050a400314200200c3c0c8030101d0b005070f012070f5205420500315514042203440b682030045403106260a543c1c02214038202d08417207421498000d0074103403000d000542503403001030094050103281031603999680ea042c1c0255514800f60800e11100c09201e185e00c261140b0181065510410f0307800003522400c50712600b1722080c81501203020314652103e214032424031a0460301d0410140c01601c00c418105080540388040d01c8400401109503c1980c8a400c2050240001e66203901004414081c0219030710303804010100c40b1556240c030407105080d89051500c0c6c400c000380a0080c040342c02500e8110b2007020800c00c030301303611112030091420469062901a0542c240d22a00740048a001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 902981447 1250 902980197 902980213
    0x10305040507061d06072a051503091c02210708040e04020d050f0105100509060109062001090b0a1104180b0d05030c1507050c060105060a0201111204030305010905040302 75
    0x600c2100a10a2550200f0f03078130480e48041c0c0c00280d00d60700a00400d6868240d05003611300e00d015900300700c40350001d40119491507503213030400240040300620b01000444000100240041005010b0841403014180b0f21601100f2018002542d80c0b030400c1d2138500210006201c7e80b42e00001e042500e1400f94083c1d00c06142c241000070107001d41e280900300f240c0205641d074501000074070500c02140c00100101c0009500d16008452105101d07003070384824000d0f90300c0014007020303980c0206254180c800500b800524800c18203554018000d1000c6030040a520705940c000030044c00d81d40c01030207800c5001c0240303e00980004c400d60148140d01c100c0307609420188440082903119042080200d07001012070f90102c070191200c2e81950311840c1041e45076003045064003e00140300c02c00720341100c1c0c1482c24030f04140d21044d002d596100180125441403001089907011240700750030000e200b103205500c040d10307850445600d052540c002d80d81240400d05000020a094640d48601807017280c060b40100284 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 902982697 1250 902981447 902981459
    0x13020a060e090a090f02030703030309021509090a0e07050a0609090b0616030c0206120a0506040c020c0a091808040612062106150b0a02070303021504030f080910140411010305040507 80
    0x101107507030080705d844000c40c04a402691702440302d94000c5000303480100309000f40c1e1041151040b0000810f40c00c2800c1409542c61503119481400c0e403080c214640000e401c0e49178440a4500b030080da2146501601c600320201d52643c0c4042508101c541c106002e04c0030203100390820100d4003949840c0103176609040a4400030a01c69420301100c0c074000340255141081c1800ea800e5519000c4800e001c41c0340c8c1345d10500c0042c2c01e0502c18a030940c0c42c80e1001d400c81364038250000c0d070500300c540700b0b801050b501ca88800c1c00103140700d502184c449510003101c644d102c0c0d5842d03020341000350726013152000c0340c6410310000740d034003d00311755090700c1220201580744101e01d6134038440140350746100524156051000800c0c000110001000c0e5503240c0e4006040e031501d186030080c81d0055031207552124640b803209000c0006e8100444a2910549040c000410342e60b01c0b03521440c04148034048030b002801e0405041e010010281c0d4503008500496070452071041d2500158142e83c4196030052480c6c0c4004010000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 902983947 1250 902982697 902982701
    0x10302030c13060513020406081b180f04050405010c08010b0304080f0a02010b0d0507080c0f03030409020901050f070c0501140703231c020904060f081515040513020a060e090a 77
    0x86046610400543c541c1c4038000301d000c11007290104509980d00003400d10000d40c2100031640e00c582040c03c2614000300b411001042c0713000751190517a045154040072805650391040d041d4001e107003e00708220034641428080e0207400c14581043c00311741c4100001c00c5280101044074440d0350800d644c00c0c40c20703c3c10000004154004540c000031550784080790140c0c0d0340c07442380c5070350341a0041d00200307061800c260004e8100443c41208502c20f0b0040448016503480100c1900c045400403c00142c4440850300141c0d044d00c1343c0003041400c2800066074408000d2144c070744030152802030384c450b185041007030004116489800d0010300494400b02c103100081c2c81d0b09410f07034030394103043e41824240301c454540148000214035240c03070525004a024890750616118000050424504100f0708901e041c0304161100b03441d810303441c52448400700117032550802d000030110b2050007520402161803c00948405c105100c541213100d212809400160b4900c0381c0380d001201f9200520b0858030b5103c0003c4180 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 902985197 1250 902983947 902983969
    0x10e071a04181521150b0315011505040503150a06050909030408070e2509051806031011030f04061b020604120905030c120f030c0a0606080d140c070f080c04060e010302030c 76
    0x1003210784441b1500880d45040c0300c00710030113200d0040b13148154100142c042c26403000c03c1e11501005000d000800607a80c0005000340483c0050082d18416161b921101000c1c00e00d507003010790006010b105205107601d0010080081300d62020035200c8040d2504c001d407888080640d4481c4409121620002034074100c02d108881038011800c14580003030b03a4002140d41c803071203200c2d440c054029110800901d805d05010680300c40c060f00404103c1d0f000c204820b0748560102802100c1990188000a010000c03a40c0c41003581702142c11869003490156440250764010841301220005046110b04a140c0c1c0600c242d170301500c074010b0141208120030414014901c1002200c82003d201303881c6008451003090008000d039440100c007038905002c00b42400707403d43d80c05900c50101e641c0010300303c40c005503202d0000c050344d0a6903008160703240108480d292400b10310f40c0040000c0e1000043c001094800001c00030380300d0405803400c3c41016505c07140444c041c4001d20020b074145d0000710300c0007003e113040030940c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 902986447 1250 902985197 902985233
    0x1a060307051003090303060f081c021002040b04180b13020f0f0a0809061008060115020f06240a05090a0e0a060501080607030e010e071a04181521 64
    0x400d0141e84000140821241c0b0003154042959060800f081c16410b010761000340c81d0394040d560246142c01e40e25581c50364841103404410032802003403400d480c400d004d00c0c00184042c034401c1d900da40e207842c1c80b41040d900904c076030b00d203140120040626081290083d00240c0d1801401c20403400c0350942040c000c3e40c065241c09003118000c002100d246403480000d89480803c2e40e8800c02c503849c2c09406149000e1000e050003c108151942c00c000360200001c0050540d035161000e0a000e064140050745002c070909000c00306400b40104000f403200b0086420200b41880e03400380c902503a0901c1c10b12914411a02440c1c1d0002c00ca1b0780085e406c0007081e02b010840b284c0c078008580021a0702c3c0c40e0310341201c00130313008002c1d20380045007448a0b035645402003100300c4400000800811002643d40391f626450380c4241c0540700010f10755150102c03600011364000b040c14040f1218a802502c1596008180f01424000744580480300400c0340034034070b901d03ea0381103821000181d0110003511400d800d0b41c4100f8040c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 902987697 1250 902986447 902986453
    0x162304030f1104050f10031b1d07030c050a0c0f020a05030a0b24090f06030106090204091506050c120c0c1c0203060105040507090302040f0e1c020c09041a0603 70
    0x1001901484107610348a015031011071a8600c8881040140d0314082e211908000c0154140701440012a00d5202180d501506002c02d406a0107800500c060543e8809074004450341005009818000039052050b0040c1c0e4081090015884003599940164070014000842c1240a2000034104102d0402c0c5e00e03000070039070780500d6540da00003450b0420500c0100c80480859041c08001c411034801c641c406071201c0500d011664119010800030030008100c1c0c2c000080340c0703000c299161020b41c800000740c100c924096507116180c45c03411000e800a030704140c422094004000824504c00e0050721450800040034000c031841c800001142ca0b0003c0203046e1030350046002c440aa6030364501241e00d2994106541c2d0811480e42c0109424624160301803030003242001c04000c00340da4865101404c1d030382e040702c00083c900c1c4481100070080141c81540101440340148002289403241c82c030038401042a4211540e00110500340800c41206807402400352000c10b12400300c445601000c0c951041c03002d011 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 902988947 1250 902987697 902987699
    0xf01050702160e1915060905011407020d06110a0c1b0e0c180303070308011805010e070c0f17090a0603060605190c0515060301060512060a150317030f162304 69
    0x280701218280d4170f0619080f80210740800c60b03103800c030b903210b0010324013424010f001b04c10054241c7c030f403481103100082c07003101c06050740c0c0308118850744966030b045109814617456040c00030000e0050101074005803502c402c951000344000c0b4024601c2c0c825500b00074401130b141d0f2a041c41c690120f4010302d482e41100c10f8000781c0040c030b0b80c608101400d56a802960355007069450311009100780082403414001c401e06100c0140030001c2d030510300c603400070818940850b40c0f1f0390038204801490303618100100703c002d01d0546219a042d01101130001c0c1507088862624180d500c0380241d0132503d0030710070f50010550901c200401880ca141030038800c4134181c10035000400300c1da9a903d007401e0390300203146008110a4280440d50a0920849010b481d09039484403044c1e80c2050070741d5441100030011b00320951031301e001a010301c040c189402d00442c1e01c206040040d106140c00307400f507504100c440c003500c5849500080c2020149035001e0206031559103a0140703030300d0310766005070600d028400c02204071642040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 902990197 1250 902988947 902988991
    0xc031509250e010b09030a02300d03150f03080d0e030d1d15040807020f10020a06470a0611010b060301060504140a1203020f01050702160e 61
    0x407000303000030701c9520441c51030421200c1c049008068206810340c1c0c0042c0211606034800240030052550102c030019004e405d020031121040182180340e10f2441e141e2940a90400b8001440d11700c003400503103061006006011300d82000c008184115500900c0c0c2d13031010070126610310010141c1d00d0070440041903251040d4003032440c40c0d01ca5102c80754001c0e80e070400385c050015098181e40008140102504c010002501c50403060719000e08060130a40001600e40704541d1000248540c0580182c0f019504141c0c4c0d040107912103001d1141920114140751742125402c10001c060001e00d0078690a41000038100d2809458043e000c0c0c540c14201e6880c060050340c070f90766031240d2800601d034642e2084689046162540e094440031308055000d50002e0006004854000b03007a01e055900d22000900e68244110000f4a0b00c12942d03c06502e00900000030406e16901144020318110310718001d0029460b42d02040781e41c0c0715103130324074040c3c1180058140116505e00340480e4010760009401c440d0f18080c40 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 902991447 1250 902990197 902990233
    0x15021203070c170a0f0e0f1c061803050d0b010306030204110406031d03031605040e182a0d02030c0603090a0510020a0c060e19050705030c030c031509 66
    0x5200c50300800c001803480001c0103401c003d0b003080c10301e403811450300b095500c01000d8106501c4103404000e100c0c99100c1c43d1400d480d00d00ca40d40c10600300030f10800c100c1e200980700040700c2d440c1400a645803410102a204a4800240c0e0801d409030f155903010315158441c4041801085510800380c101619135600002580e03c0780552002e800902c82902c0c1d0b00d03071600c1400740c00c403003640d203100021087c0c80c01000c038a40300110969501504890745681c0c5199480c0d01100c451007140c04c160700041da800280980c001e500b6000c0211004041c0440310100308103044081c2c40d1b1100d00d000007201d881e400310708040d030030300c003901c40401440541241d40c192010310016507103810880340c4c1c03803e59002c1d814210500030304202c3d452131240002802c5140041c03841c4002c00f00c00010201500464031380d05076610b1243e0401c041a407000041035001d1000400345000b40c0c4920351441031510a226a56442034180303004102c40c540008024020150481c41150307945c540c28000b44202040e006030701d4103000c102040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 902992697 1250 902991447 902991451
    0x804060b15032403062a030901020415030515040f020421051c050f07080903010e07080610061e030b060f0909011406030411120106090b03120306060415021203 70
    0xc502070a4503440e000b0b580c000880011411440701e42d25541d4100040c1d00c010402c150020075000c440c0c000041c0d00071208010340c10b041c0b0380001070200001046411a010f50280058440d80000a4209250100300f1019986c082e180c1c09000c00d440900a036480c034260380320700184030000c1d03005818560765000482442c51800d001c010105444400581041002d001c02c061100b0141e014400c80400501c0081c4240130711403d140c0071540c00210207085c0b108581c04e640d03084000500a1007114861a00c16071141c40f103204d1404240706240c00300d001188940c03401010b441165840c800303520007141b03008915014404c1d010342403540e62040b07004261100e400818918282812070313a034a1200340288110a80d05030310006000185440d00401661104100c0e074010340c01c025210140e1500384002042030400601034034079903280060002d085a0140c2221022a0382242034602c0d190f05100a960b4034801242c006038403c0d01080148810142e20100880260305c034411103001c5004807007880501d9101b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 902993947 1250 902992697 902992729
    0xa080708072c0f04021309090203100c050903010e0c330a05031e040f031d03030301080f010e031806030907050a0e0a050a09030206070f050d050a0608060709150804060b 74
    0x18078074000c20b040c240b241c0203030343e0400141c608601d000e44070203840c01185014082c000800c1e4807520410300b59601000310210031003407598108000c0c884860007600e0303a0300c0004c60600030350a024545040100210701c1403d0310300040c001b1281e000115445600203d1840d69002e1444031450010031800d04140c040d102c48050b0303843c0c450380e034140f401001700c4200407881c0941000003071008100000380e06d100603920b1294582803c0010101501d08c54807141c8000c00b034a6018440030000060100c0006200340c441c0d081403000300035201b80d140141d5180c0c843c075612020ac0703040b404154951170501100441d40600352030291214075031038900060140a10390320001c00720400c5002d00046d01c510340304030754000301c3c2c0c400c0401501003e682c0207912a41e00821040610600d054000443ca0148086401c0c3c0d001b40c9900300020710300b2113021f1000300800c0c0944010381c428000082c0b08140904043c4059800313940c0072821080e13231301008480c000740042c0111843c64840401d08a1512404d80040c00049 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 902995197 1250 902993947 902994017
    0x80601081f090501090b0a08030705070515090909030d060f0b160302031c021206010c020109051212120412021203042d03030b011805210a0b04061506050a08070807 72
    0x250101000103047c0a5000404244c0080111000180002442204480f0180c0d000d010762a10502c4038a1b00780210b40c7e8580e00502a4410845a448d000c03000b090301e44c01d40e010070405551168400c01ca101c1c000c1c050b2410340c0c2d4041021010019440403910b00700741c82441202d150004004904140348016000c280c05290041504209070448450349540310100386007104003c0703a2600001e0411000d0b2141900070022541036100400c0180804880c00c0c6511391900c1c2d0b0f962000150800d0f4500c100d409844102030f40d46070150b424800300f1942c0b0340016944040b8210746490311400a0b5140514401c90006071240d0071a10402c0c1c85890703801003a01984002503405a4403001520700d0501c510180c3c95840345000c00c1c0541c1d41d550554036041041012140341d118081504e26190014a1101030024000c01003048108070040c2c014418260407814000405079441109444501905000d1408540b004000425841c07044002c3c0703031310005502d4480303034000362100c417419500420310310340b01081 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 902996447 1250 902995197 902995211
    0x609030a0f1103010c081314010213030309140114030a0f060f0806150a23030c06040e090c0d03120c0c3216050d140102030f1501080601081f09050109 66
    0x1182c00c5c8942081007405003081c903907524141c100300d02c0141e80d41c40700604d20301031246a00c403c210254192003200d102622440d0080d0b80707038100034003071001e58450500809848070030340d13146522030264885a00d10007803419040d40c0300c400d40704002d00524515045001d9440c000045e10546044d400d80041c4a100d026204a00b05070200b0381e5a0f281720340e0101d0203500000c10420803110b800f807080c1101c1e088522041d000c1041540007a00780252080c000b94449030101300403851151454809015a03680012141039041d518140280d00d9010140a00400d5401410340722110b4260889250141a0311b020b2004480c0780e0344050800040f4100f018a6401c20050044071403030500c600844103a20030000d000028042d55941008002402094010458140c901c1c08000000c41c0c010000005213000707640300d103070211580291140488605100c0c514140d00919070394045e44d07030a401000f040c0d482d5032966880081101207107500c09542c04190f0b4080100007421403031482402d02901030314402103403003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 902997697 1250 902996447 902996449
    0x30a020702030f06070203030a0207050715020f070e04170c0a1b0801060f1503020a02070902071a130b0f090c0607061406090708150d080a080604060b16020609030a0f11 74
    0x1081403c8400500d83c01101409109a000010f403640a1405d010140e514501460b149003880c016070301003c04441d514194500c0b041d0049100c008070103030032048a81c41c603541c101ca0350100000b69001341c24140d8900b5007010700c034007c80080c400c0307040c50001c8500416460740e035460350821106024240003600700003402214400c1c05018001c107040c2c2000140541407420b01001c85900102881c1410360028015510754000e2211600a01303000d0800c40d12000c3c035090051424131407c0c0d182e03000c0d8020b500020b0791107400c03070b401c925041c0e040b841c849500d03039450b003030b411580300081d107a00b680d48030f6200d4140c10340d070b0f41100500d041d82c4030f11008a0040070741c901211103a0030142a8030321828120080094803503004480705c0d404690780700491300400700704003c201d18141071240a0b09a0a0010700780580681040d80300b4005d18060710204011580ca0901d03003036600456440600030390b10b5070014805868a04c0150440307100003000e94040b40041c3e40c0e01a448411320000321800da00100409010b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 902998947 1250 902997697 902997703
    0x30f1a060612150d050a080307090e010617192a0203030601021b0d0206041401090605090d020d15020a0c120306030b1611030f071401020702060304200303030a02070203 74
    0x114400359035441c1000042c120000740140010601e030540004a00380c0c0700c050340c4841080341300d55048402d41b8145203c0307007011003080e030048900202007803050342e00099030310300c0c024840d0403103503503a407400a44c40f2018010301e0b164802401c007002114400c8520035a140461140c44e008003580c088000c2d031032442039084d040d0201c07056a02d10564106004000c445c0e40c011992000c4020483c4500c9018080e550003e24403500d0b0080107500054080381c08905980f0036500d2211009090700e51242e5a42d42d890126020721500c0078480d0050f59404a510050915881109200b8421000484030400940340541240c02114110700010740d002003040c24082081d103840d140001614080c808282140c690000d5500003915030200c0755852141d20508034480c11110840d0000001030325500c3c0d660391109049500b00c00c0c010749807900203035010200c3da5414800c881c245503018045500b107a03079503112084480301e06005003003500c5003001c0101c01c5075000d1004510070281c0c140c006844003407500525103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 903000197 1250 902998947 902998951
    0x2d011a07231005091501052b0602040905090c24070f0b0103021c0c0e070219290907050103021e07060614060a2102070b010b09031c081f030f1a 63
    0x12160400201c0f4150700001107031450647e14140c03125551811508422040060195104c00c140322400c04040d0030030286800030030890303940d4441400309071203c10364140c403012501d090300c0d0311080002c25401d0411807214a0482900d030401b0550804510b5125912000c100c00780445004400381c0c010b00842c5008080e034540a00042e5042896100b1030396205901c0786280110036180c0038a0b8005106280308000004642da907441801c10015594a0041da103842207820100010000300143d0340e03403041451205100700300c803d0007041240d251100540c029484540e1103d02040c01400c06499002218010501c040c82040c0004076603262021140a401506240f18440d017000c004c101c401d103600c0ba02101c41c061802c0b4440c05140c1101070410b00034410f0342d1000b405a50901e000084400c6510080e00c280c0c00160709560040d4040f00550740e5052007050880e004c1081407000c214009410030011402190801500303110580b01e440d0600b20307403040042150400d00d0a0351588052424840f066 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 903001447 1250 903000197 903000211
    0x90a030906110309010c0c09020c07030224120c0705070e06040513050a11060d060902220602461208060a09050415052d011a07231005 59
    0x62102c1c000c0b000107900c0303124280c011810030100d0b160220030b2202c203620700f900400c0f0400f011943c60008119035911508244803e078460342c0550351032004034184c0d80c00c4240803000f0040784c1d07241800c1a41c039140b403d034010700500c000441c24000d01000490801040c2d0103001e650205444518140040205590004088049a1305051641c10019400080d5000e12590055842e070358080701c040424414000c24070400001d1381020300000c1d00e103c0d160b004042410004010f48603a80032607508620303555041c4580d07030060303004414480c0601100d2406411041c516481e44001d03254007036250b20350403a079003c1c2203010000b0400003c00c00c0710030a2551441e040c5030500c1d448030300d846000a0040010352194608083c2c44c0c8000030f0400c1103030301012a8030000020300300400e050541c6038083c00640150f4a0401000540c020100e164500c40d1080c100c91100726038a181e88017450600202c0d8101080845204020b00c141000c0c00307142ca55809903100000c0020540c00807007184d948240c550180c141 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 903002697 1250 903001447 903001457
    0x50c011104030b28060b0909101202060d02090d031e02011b0f120c0207031403030405031c02070b010824010f0306020a090b13090e0c0907030c090e090a030906 70
    0x1040040e0b0380c050116440904d101d003203501c04041d6024101a0391001101d002802c1c60b201c00814010110b001419201505442c140a10f0b034889020401e0b400d414082e0011420b1004020720040c0750900007031089003200030025040c00090030204410501c002401c4010410501a0580140c4407040c92010750803248000c1c09101c0203040c01000c141480b145180c108580403251342c407400e00980c5481d40210b43c10104000d440c4003244000e456071101c0c002250ba960160b00707e81104c00c400000c0c0c034003d60f00480a075140c4003109215904920b640040b0f640410f03000d20039000403d0500400d1802040e440b40034103464400084103145110340c14000d440580c40040050182c0000c10810109695000c000142ea4050040040e1020a1168005402c4890019044000303a1242c82640f00b01c80201000740881000c404c080f0703891740c4645007101c0c2c000044000250165100e500a84e020304001e04000d400e40351104031508003a83c04462060b0030f54031801d010810954465144002003d8510300 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 903003947 1250 903002697 903002699
    0x601020a0f0c060e040b0f0f031609020a110d0516150e060603060901021806090406230a051c1b0801020f030402100906050a12020d1a040501052407050319050c011104 73
    0x2001f0700340d000e404c0d038001c102c03061010300180c4042103070071556503104289a0610381d81d51342081c060340c070100a80e000a01c003504210210300303000440e503001d43d8281ccc50741820407032003002d00c440d14031015030240c034503076003081208203001900d124084081842401405040c5018800e0500d0a10060451402c50303104211240d804495406079101501c03080303035495070f1922001c000070b010703200e42c1e0080890b90304170040d4800c1d135004600300c144c0086015901603003030955483c00c205092056864002c40c0140c00d24804001820041c580d0040c1c820011642d130b0b40380c0c1c86075905400c80e008904070004540c0000300348019413401020710f0003542000d140081620b8109440140980940c1e862401801160300096600c10700c0d80c0c040d50a480c91045c0c080201386e060b0810b03024031010950342d00d401940740c1400820941021a64076405207542c4468000003141102d56032400e038440ca02c251881d000c18040c400d0b1550008800304410b80496a41c580c45918444000d42103c8014407803021160301080 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 903005197 1250 903003947 903003949
    0x60b0c0d0e0a0614070b070c0b0708010e010504020904110c030a09050a120305300106030e0c01140d0f021201030c060302090f061b07030308012d030b0601020a0f0c060e040b 76
    0x240183e400518100c50b4000031000c1c501120302a881c80280159040d504102c000350b840181000e4050140071205616110001c0640f04034500707005d1898402d0500d001403100e401c0c1074004100300391015000150300d500c10914cd10a90300b00c080c4403c02508001844450142d0004a05000c0d0000721409500d091900802c1100d4001c48500202070020109441000c80600c810040182142c44014101c80d2000034007580510024013410011a2500940c07880319040040e0404502c03006840d40002c01500134441d003855000701180303c0b071040d180d114442001c041d40c006880e034034510480e1120319504519102046140940018080510505c46c0881950321000c0c0002d0800081c0c403181e0b0f9035102c02c0000543c41c5404400c0c20b125118100c1e0010400d584030035414101c4c0c40040703c189004c8041c0e4407170041e0400c007915401d4034000c150300c240081031404e002950085014012201c50106a955240c82485000015264031150349010041c0ca504a84c600d1040002106c040241c260700304 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 903006447 1250 903005197 903005209
    0xe2103030a1d0a061d010b0d02211b010e030f0a061503020619020f0123070e100512010614120606160b0114010527010201060504060b0c0d0e 62
    0x6141c1421507840d80324200280382807444500410089070241c0e90342c0401030400e00060318102c5500340c020942c52000020600040c882e440508100810000e502c0c4200d0f000c00c045100c071001c3c14180c480100314030b040d00c218200044074030301640c003207101815442000090240c0031020080b174040c2e00960040c5400580c0070503030501e0281c0c0803400003290309440d103041c5840c00b6170b508000d410070800a40d80c0c05000d00100c02908241d255400c80d40710406081d101d42c00d81e4001080136494142207180845a802d1480116501507240d240007601c8250007070001b8100440c405000c1e020130302c001105218200103201d55800b501d800d040c05600d0b111511200328562141d481081c025184003808100c15030345400071182034101c120184d40340c40c1da0506060607002428807a0840c03242d09954000d1081d4060001e80c3c240052100352000d8649414801c3d5021a004030301c6503045550301c0ca000301c4c0654451281c00c002d041d6040e806629420002c00c403901c0c02003040b45900c00d02070203101c0403075140ea0300 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 903007697 1250 903006447 903006451
    0xd1508061b160f06150503070506040611100c05070501050903030c03012102090c04051c030f0c0501060e0a050403081f06050c01060906030f0308130308040b180a030e210303 76
    0x496545a40d0380368002c010780148038407031001070003d1030b2645210244001500003002a0f000b100440740180d6031001050742d202124404d594000c1342c03e000401009002e100d00302c28540c248025500402d100b525440119081900d104021820104090041c0482440340e20740c4102d25038001d52542c1820400c4030f502e400148038400f105400782d000001030869240d04244055409041002c4609281d2400310886c3c025004040c0909424581c2c030807802a00c0642c5811503405031150720030240440380c2103075000404030054620313640740c0314000f410b030342000702d541c0c480c40074850002201e0a1074900205100e0018108d0708044100c071070911642c5d000890300030225810b81c1005c581e43c1c003414443c03c1c00b41140f6804080300528040c000400d001594901d00485440380e6202101507a079841c02e200d85100e0306801500256001c400507001621200100350080000c0b42a610342e60401c04c030540c81d058000008a001400110400300d0f107081c03258002840024501000101c1c0a8003092240c0d68000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 903008947 1250 903007697 903007741
    0xe0f0703052401120f0c1b02060d0b150304150c08091e0106180e0601050108010e011203050408031305040501050607030c20100f09050105070f030f0509060d150806 72
    0x7001001c0c202e9038050516580ca080070300d1814800c10b242d9018960051016103054000304401c0c43c00104442c610300d070500c803e00d60081c12a818007446400d003500078401624003581040305043d4083c8400e108002846c80340380724481c11903001c0d2400e01200192a01c541c060700600c00e03801d050100808020800503101c0b10088811003410058110703c40c00742c0082e50062001c80290510304070b5100083e00140700700c0f41a0804c540e2140d98982c01118408001d11600c4480c0f0084001440b480302d141c000c07442024001d00c0c00b80d04003070304c8110340c60466000d85900124502003500421941c1081c0c0561401080101c410070b003450407a0302d010702040240c19000300010403000301041c01240c0511220620030010740a008560300c201d90240188d10b0741544400403034058400014258443c004407003016500c810000139145442d0f0341603414484c0c0001031024080b041c426500d4a89911700030b8510032290a502144608807070418400b4800c0c07070b400903085500100100140600d0388420140d203401 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 903010197 1250 903008947 903009001
    0xc1e0d0e120d0e031603030806310c030209060d0e070905010506090d0c0b03130309080604031409010c150c0e03010225030e06070c090e0708120d09020603010e0f070305 74
    0x3e04080024140540094101c624006005020040c198818407039882441e040d122907803013031601d000c12050b0020507810041103441485a0400c00c040c5500100402103240c18050300708000140022000e400021105000075510030180700509010085e040042032141c404100c07550502c2d011a14501c1950807160044404c400d008041002a0402000400e00b8a88054413420202c1884012009a6009030001005c0407004501c0c0701010846a020316415101c4201001d100461802c1d160800c9a8060510000c1e2131050042684012050001100b070040011291000d800c045e0919034815006030007a881401b11303104603241d0003002c103c034400342c5100c105201840e01d401c0701c241d4412010b264210030041098020458100302c10000d4401a810900c006540400e1190795a6818800c3e071001e41e01c096a03900d080c120b880300230009604402c40100d0854410303004541541d02c00c0c1d10043c662144141004199000d0202e0190445003038a8103000c0c0d4103040507580a07600010f002c101c6d0000b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 903011447 1250 903010197 903010217
    0xe010507110409080909010e1911090a08010e0f0106050d11031e03030a050106051207030203060105040f0b030f0f010e010501030f1e06050a1d0c0c1e0d0e120d 70
    0x804441c0340364a200308020024000e00e0624580440b00ea001184c076907005000510000c070315400040c84e41482007400740c0c0010000b01411b07610202070a1480c005142180e02003080d10480e480d0544414041c081e01000400c50320001d055240c5000c0c4c0201d00803150342d2400409010640da00d9664800705a00080d480103810700300c200083c2020041a0051114815404140c010880210285201d01d2030385400f00000d80c2d80b8402941e05100300c05100b14808074503070004042c94026805941c0060046c58a603081c00d489660103404041c0c1900000c4100001204110307080c10f0f411200d5a03c01010001c1c900d055141105010342c2c0302d01130003181c1c103040d1910300405402c02182d1100c1000d0340f00b10050030f41c004081505400420f0f07036004d158000d19001c40c0120f0082d000070302401d82c159000003034035000d66804c000c03d02542c118000e296514003039149079520300080100c030702d9600583d000140c0301643c540381029194121000d29180900708401d20888009800b20b10a07180084a043c801191 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 903012697 1250 903011447 903011453
    0x1b0304110a050d0b0420011b03260901060b040b040623030c03040320070504150302100908010606091d04020a0f090b01110a0b1b04080d0305060f09070e010507 70
    0x1104950b0409500541041268014804642440b6002e5401780e0000d00e0182024800d04204c88100c21310039000c00c01768203624140140c10705a40c09118003e16007544000b01721034a081c1003a60a15001c25a03aa03500c091042032502846004c00400203416100d01d42498407040d240e10b4011172080d1414030543d96115007000c8510710708104e000d0104004540d40c0c0c94603952a0703c55810594064001403030710a10b14100042040181d15241010001080308500d80307010800036002451040d044842d544500000580b04c604064802030b1564440b1541d0600b0410301d41c1c00c5800c154080401c02002c1101040207400424402408081505c030340ca0141d07496001040c001440c9920010313a8180c0c9542c00501c0706826403002c841e69800b607980601c0203849110550b904d03840c450000d4490800c0c00c0109a416180595403442c0b0300707074900d0a904040d41c880c00981090034020044010a40320030802540d46810381d10701d409102c0440b403c02043c04d140e1002001114940720f500d0503c00300140e00824 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 903013947 1250 903012697 903012709
    0x1020606210d0c140c09060607060f0e061e010302011418100201064419030c020f0d1a06040e01020418110406080a02030c0706090b0f1b030411 63
    0x4403151480031100c0c1504110b10041809492200c00e0710301d43e0380d54202d848500030200304c140038820001c002e01500d40722034080003015802101c007195401c0d80c40ca81000c008059000741002c000b0001c015000d51703c1c1803111144a40c9816152108802209005000507038005d820401190114a4010307110401c20007800340140b6860489640b14280c400d600c008982c0c15002a000d5401d40001c000080f0030030100b94150140002d124528240231407684100000b280341002c4483c0e1200084804e550b0880111003110b00d18440154001032020340b0010550601c1c800094800405550312005401c0544810300800c003603604400c000710038400414003d83c0c643e00442c25101010303008564880e5201d0380000300e001d031100019841c60030150040c9400e02d15000390f038111038094440010740d80e40c02d02c00390000d40c80141641e152000c140302041c0807603100e200342080b1611503c5407420b207080c031400c48000200c0007401941c18080d0120003125000e034500503280c119030301548014074180d0030800281c13 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 903015197 1250 903013947 903013999
    0xf03050403090302090a09060c1103070204052e050108060105090102150c1902010b13200703050d18031403010602150c1905182709120408010c080a0b01020606 70
    0x540452620240011b0702c003941d0181b050903114103010480c407900300c00180c5035030120803182c098a410601c101710150400382c100d561700201802030900030030000f40c08030754030003514460407030200003d490508c0303a941c014080075006070003424014280f1310380c840000d54464100120b107480c00c41140200c0d80c1d00c1c0304c0030240e8214440345883d850b0604170407031001b4000c1000072216440b4910300704010164004030701c141b02d01100c140310b44802e4900705034086d940030b920496080381004810094200e00701d41a04c01c00c44458030082804a00701501d040003461420121490020541c081004000280d00040d8440070892a881d200417981c2d44c221a044190141d0142d0044030240a510350918903400001031014201807100001c000700c4030b0081c001e9003041c1d82511082a940ca006e03030b03100c40d200b50b11642e5001c2000c1046858104911100300180d400c5035001c603031030741e4460014090301500502034a9010810b11800c104a03110000000d40e2103a004e8600ca024008802c40321011070986e80c5228 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 903016447 1250 903015197 903015199
    0x30a03060801112502092a070302030a0809070902070b040209060f131d0f1e0105160e031f0b0f03010207050604030513081207150203091b030f0a0f060506030d0f03050403090302 78
    0x9a0985007c008180030900000040e203101c0c072002c8495009042098203685901d901a8011400e01d02c80300300541e29214007414402952181d80000180d4080c82c0c0002d10f0a203200f80501051802d140c07044c44808000680054420304011041c3c104a031980c1e0a0003101c004030040101d07140b140c8481010102d01042160070070741c010008007500c0700701d000407406080a0300c2c0501001c0e0081c440e414508841050310201c0050b2421203011080911941488101c01d1004040c1c50041002d03400408100302d8242400341165241c201802d410301c5c04800c24410640181c00943c5004000e64583d600c88100400003003c0c414041003d800c15820b140d5030300c0191584104070362400442148103002a04a880200c0e20003d0400e0038400d40b4510b4026a0700440c0e00c04024404111307140c0d6030200504001511580520910104100d070b03007010402941c145000751003082000400c3d0803c0001d4802c000e20150081d4412107164512560104400c00d81c4505031400140b43d489600d02201c2000484d800a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 903017697 1250 903016447 903016459
    0x60501080309031e1b011b0309080f0a11060a090e04243e120105130203090a0f0f020a030b0a151404050a06080f030a03060801112502 59
    0x106500800100400501c0310850451310314492403070102c1c600300b0400984000039049108028020280401c0341070410750141820b00c048042100390880400c013000e4183c0018980b1001003000900078058502910307491000380100014a803200078082d5020140d40380541c02c0001d200c62094443c3e0800f030040c248150a28820707007410704003c0d07840d0410743d0244406500c5141100c881c100715200710799280c1070142e070b100740810a2504492140c005c03a00800940450b042c1341210740380d68130f030007003450502508000b030710340d41800e0500480184245003072050501c1042407114880c0c0c001146500550b114104c17400d01c4030180341034180c182c140803009400902440002c8104504003942c00d00c9064031000400c2000942c0000980024a034810a402d1702904851490617007841c0d04400d038844a400c80c0030850680e42c0200358a4548203e1181006800102d403052806074540105d000820100d002404152040441708605102d02d405d001084080d12040c07034040a103a40303030048216001440 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 903018947 1250 903017697 903017699
    0x207122a030b071b110d050a02101709012309030408010c03020307110601140d0503070209042f011d030c04090308060a120b0f10080a03030207060c1b020105090409060501 75
    0x18440a01081d6840c1d404200c1a40c9141c3c3ca00344608480c4d80099040941c401e41d03000b40c2400d1080000188034260303010f0040d818403c01584540e2900d01800c0e00d87d543e0120307900302421007814104006030024040e42d0503c0100789a0380c249000340301e480150301d000d00c21251a09990140b85103d1680b1840b640d5007085039601000742c1543c0030b94880e00c0c8946462501c1d0b41c03200042511020240601110320898440c0c511940c01c0940300c101d0032600c11b0f42201e14000c0940c000030800c8c03a049801310f800714424045a041140c112208103103c3c0b0102c1c80b0011a5205500082d001402001e011003400c6500c482c02c500ca640e080141c0104e801003d001000101964240100050380c00c440d6103010301f41c00c030070002b209651b41c80034001c0941c112405014548402086c02c00301c0b54054000c80201c40590390114140b0418092602c1d00f40c402c2d240182d0303410051521000382d841140c078503420311402242c000088059007504542403542460070b10358030500040054010401000b01412051500c00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 903020197 1250 903018947 903018953
    0x5040c1a04080a111c0201081b0f070b010519140d290a0c0c02011d06040b030903030f3103030609020f09090606031009020f07020915010f0207122a03 66
    0x7141d0a13a60b20569500d5545c04070114440100c4803618030090003d0039660000700104008402141c02ea60015505071502000307601c0081c2d150880481540c1803411031004110510b82030610030b03441901c84121043d010710f442d02e0034142e403d600030010b00030450315440400300700340703004005c0e002c608218211400903403003417400700c841c40125000e6061510b451070301401240a034030100d44d0994142d540c950240305c002104000444c042c420290007286c18040403403e0700089010314070034038107900115180e28180f00302c0014000040d1000d006c6609074541c0001030b00b139006604100350064020002108041c2c0390490041200d039019900c1117202049200c444801d00c3c0003483c040700c00b117402801946032700d010046203210036248103100b403005400820646070b45070090b044002421400906100ca00d4001c81d075002800c40742c0411091090065036010740c2c0105085501131440d200405840381400460b5800701c986090142101902c00d030704c5160303c404070f0500c82c1254103031070300f244e0032aa4a203 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 903021447 1250 903020197 903020213
    0x150a080a020f0603102702120a15241206060f020f0606011b03020307020301020318010513080904090204090f141c051222080904060905040c1a04080a 66
    0x403031140c42840041a09454202c060f80e0017182c00540500d401032412010181c2c15024000020b140300f224003d45081c50007610142c140880080120b4901e0324100003220101d801019400c0f4000c0c510103801c0c89440c0c181c021b0b507404600c014071070790003a40c80d03242c003500c034130f170064010341c1174a42050070114050f54484911034486141e6000c554410110307140c86c0c1d0700c8101c212480da002403020401c80240f0300b8001c1942c244240203006a0b031501400fa000300c0d081e80e10442d001c07800009030f40d0100444500074829164094a8100180700040d002e43d41c00758188150740c441441285c64110b01d03030940d5070b01d80c13105101992161145800c04810300d41003054003002c0100c0c0b1024011040e07003890502502801c021150740300ea540070305d0090252440044000060524514004100c002c6070f00e203030b4110b2050b0394441c01072480c41e40310030105081100b5681c40f0307000004a103040405100004000310001c000703a90100b44800c0080d01844902038450040d50b00c0900c85114001140d01401004 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 903022697 1250 903021447 903021463
    0x905010e010c031104121b0e0f1008060906011e05041b080601091401120e010e0c09010f05180a0b1801030c0e0408031504061e05030606090c03040b150a08 68
    0x10380f03092060350b40c00c60b10400306020307612a840f040c181806403100014031083d600d444e85c2c000c0d40c0f0564441e9485004001442c5812659070510303000c49400c0c85800d01c2441901002040c400004040618100f1348140d103685041c45000540d01000c810700b10b1181528462202810019204200c1d4005408441e2200b162072403140c404075907801c0208100c0e5110345240c0055404d60707540d82c0d2031134280c03000445a0044121070391700d080d5554501860009028015104004126130003041141c1590007007004001d03040e4080403c0000c400010481070f2204a00c0c4080746990501c2e0f54496a40e412294002c0d01022030302a6200500703500b0a40e480c0050003006061741d0086048a410700c1d114400140605010386002c2c3c0350480510000b250a12140c0345040420400341011079560307500c000f42c8000706c071040715281762541490300500450900304070199000301c0440702014581051000d1220070300c4058800780424040000240400075050825490f50300c0c007074084004282c0e50300d040c80e221590 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 903023947 1250 903022697 903022721
    0x30f030a020c1302040f140604120f030f0206160c050a08070f06060806070e040b040b060f040303081f030210091a030a0f0507020d0f21021902030705070b0a030905010e01 75
    0x1000c0fa441c54618100d200741c0341a00d43c030070603200300c140c10b1a100d9181810b4203004a079001408100100b40880504442030046100744004025082c0516010300300721136480c0360504550003803040000700107040109070084020380c10108500100350032f01c0d50410150a00181c20308000064403070411500300d811441542c0074080800840b0340341c1c0704050301d400c410723520000054620140041c0501e420350156480c1c08009000242d540081c1012641540190004506100e00402c0410a260b0403c2400c1c0d4000081100d1740e40b00d0302e403c2011000c1506030301010307000300300311282d01414a000b01d09601c05088500e00713444104403203481d007130121340c000c0741c4200c1404d05020340002802018041c0c940100d00980141454084c1d504040380c00d4503044001000300304001048000445020317040004c200390005004d6a00d0205001c208140b400580c0c4e03850866104020070400305101049a00030354684004c019600c48404008a01030404040081d241c0d510b080700612405805502040c2c101d41 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 903025197 1250 903023947 903023959
    0x1002031e190f0906050c03160b0702010e0f0d0305040c090906020703030c300204090e03040f17030304030e04060305031b0607030204120209040609050d212306030f030a020c 76
    0x214030002190810080700c0b01d1404200403400500c5600d0142024210032411710341241d04240c9040010b00c110030a64200340c0c1e150031060144a030302982805803106103400d04004080d940565441a507944a481084504159503203000c1010840c074540d0700401040082c03000d211700310f1f130b50401c0720003980280320440c0480c1c50650703444c0c140c3d0b002d400760000d2880130120f00c038110114000f5060414280c55010030b8030759800c00002c64065024403460702c0201d00303140155115410504054101d0300c2d540c001c880800c0416500402c0d000340001103c1c0d002d0362510b00304207082d400c0c0b0007240c0984469000101365000204247c0803001815040003220042101102d4440e103400805800300c5c4a50700401140312010082c80e030242c10045949038026204120008100c21035441c0c1074101114407000360001000550382c181e0050056208041c403e10880041142c03041c5003a0707010003800e40d8019030f56001c0301c202c000392066405000c000180038043c0280c030741d111200d040094889811000c5280714030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 903026447 1250 903025197 903025237
    0x309150905090f09030a031508030409020909060105030c07030f020c121c03151a0f130611060c040302090601210f1a2b0204060f090b041a1002031e 65
    0xf01a40d911405404604040c501d440c1c019076044003c0d0004107903103030000c580414000385640302000280014140868010303120b40500c01001500200682054100704041c4280503c00000404a8940e40d515003170a902c4913600050a90620000c5032100c0e601001d085031040308820042a150039070b96203004c0010210340015000d80450320401015251020902ca080c854804a02c812840d00041c1d003200038200482a04800480d5001200316000300f80d60110402855802c030050a8510212002070f01441c40d0404040d0302c0c902070703880003910a00b082e4000c9841d60b40148800204035103030700c4010b01c031043c0c026101e1010300006003548908038509883c80700700c1e2090300c5c031510318010020461400c20740c1c8008612481c45042034080d07203940302d01034001d006a50358410702e001400400e030094042407074282c0850440303c0ca01030b518000ca003007448060603403001c03102020105e0740032669174000704d003138210032440c50240b500e4ad031501d0040c1c960403015860f5900003402107402c070b04100020700 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 903027697 1250 903026447 903026461
    0xb0f090703050304060c0c1505070b1b0319020c0604051b011e140d0c0903060c030902030d0f050c030310031e03020705060702040b03100507090f030201090e04030915090509 76
    0x340c56544006040d5030400e10040c0f103481d10408004810500501480500c0c907142c00840104286540000780429000a519401c210403041c0c0c0940c0880305503103500108400070740316605c910004101c5c0100d80300e130441008620f1499410b942d030018400d012207000b803510b0301c1d105592f1000c220181840c840c0c908000c0e807656115403d40e81e04100c0103094607100f910001400c2d00d029400701c0841c01540c00502403883d2007001840342e81c1c1011f0740f507602e81c2d503601d286040407000c0390401040d000c10103043c0706030440940ca00051301b0540d00e10314030b001c401c0303407a21400803a602d0140c8442100b00b03010000601040e01d008030b480000362401007403c0d80c185007090181620f08205100010003507042a03004210601d002c5000d0040c8030b002400202d24201000e0000c1e041200080c00c41c501c01d0340d5602800310f81684580707032501404c0e00d508074a0341c245c11030700040c1c5480c2952040b0301c2c6000b0050001010588169004c4004080e0503414010400000b0000f41050080d40a01c3d801131a442000401c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 903028947 1250 903027697 903027703
    0x30f0c08030a1d0307031e0e03191a0108031602130e0106031518030e0a030602031f1401120510081e060702061506072310060e0f070516050a0b0f09 65
    0x1d113a5144d1118840a50b10340052142044071f00603800902210380440300c2e00c1c0d2030502c1070141800d00803c001d0780c40045841c243c500d45440d004050b01c204204401441040c00010440c1c407002c018075241d203842151440001c90304030300740c15200c010134102140c0c100e1403074054011505481c800d00c00403a000300040c0c42801250f0104032202c9042803052000e5003c280500c002c950f6400e000780c46c10440580321b442c0c1c0b209036402503d0741011b0049502280741070740d01007041342e4083c14491100c46d404961000000f814070802104155105940da00450000c645142010000305400e4090b240c0510003030081c03114103c81e00000b00100d000302000a01e48500c0801d070240308180000020030750101240902950381c0040104072040c1070b0b9440352444040e4080c200500c0c090300103004144000f40305118906075580c550001d000364110100f07010342c1900d25080c0d25030009292411070344031010740e50400780315050500c0c00707812800b074100c040c014458501903942c41008280712101c0c164503000400c940d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 903030197 1250 903028947 903028957
    0x60c0b010e0609041509080313140705131a1302040503100e0d0807050705061005131a150712030605091f061d1206040203011104060c030f0c08030a1d03 67
    0x192110030f5030001400100006000100400003590006038502980e840103107503401942d1481d1f1035007210307401d02c0070041c040ca0094201c0604c90090800d040c80c0c840854000c0c0e002d4848205c0076501c3e01d1100101821040e500b02d0024001000d03d070000c001e590a0b00300a511034050355009015098146040c031560b0300503191684800710040c00c2c0401c018104a03010b41c000b4181c0010414100104004031b0420400580101c0d01c4c4c00c14200d100745048200944c404c40d000c406280309040444d141c805920400395031b15030f80c50a6400c1852180c0d640c10925440c8200000200001200c40c0c0a0140651607440708058034402e80325031109440340d2251201c10a2200d4480c031021074103100a00c00544600b92490201d2602081c088217440d200780040c0400344851100c0a050340600200300a5140074080c80e034284a414072000c2c9001e0402500918083c102d80c030203418041220740c4050f00b50700c2a411800701a421030080e0303803242001070404000d03154252000a00c141e48800008900d003010003161 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 903031447 1250 903030197 903030199
    0xc0237121a100504020f04051f02240133020609010501092a09050301020d1a01090602190c0e130201030b150a08041a011d070801060c02210304060c0b010e06 69
    0x602ca01d420308000195010351000e184009051000080c0c640356496a0b406520b5080d10b105081d20000b0300003403600c0400a03413554030030b2031400032003894084c0c1000e45054800e007030358000d120085078900941d01484400c03040240d441841d01c1d02c2107680d01050150040c1c01010007442180d030f0f82d403a0142507402e1910903080ad110098118458411415500b4102540703030700307140c00c51036581e0000a0880c0c103d415103201c8a901d58010900000408814881030102401c1071451203080c03000003075880c40c450380c00e07011822800c4078240502032115000402042d199103861024035001d04030030480c0d0680c0000724040ba0801c0030b000b030185005186058001c4420942c0b03424a40c0e05001100d4103000500240c07500c000001c00c131500c100b010a03085020b80312000c4143c4000d150b92460f020ba00744010200c2c0b041280385001840040c2e446021034400b250101e640321890144003115030140301c1d28044101542c480040c0010740300703412500d42070007280506030b461401d0380d0f1040c00410381b21003200d1302 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 903032697 1250 903031447 903031471
    0x703021605010f030c03150f180203280e030729070509040902121203061906080a0209030c1f031116080c03040909210c0237121a 57
    0x10001c40d40300c1d17484400b0040c1545004941c0984902041c0c0c0d0001180d042001d1400c5104407d2100e81c2c4110b4508100c00345a80c011480d603d0440d580d080c142b41c00c070403c6951078845000100c00150f40d03030094506114a5002d0f260303101c0d2540707007030340070030452003c3d58400c2107110301084030042d50411814400c09071911030a10340001d0700108001000118812640302c845c0484141d81d0002c20421a00c80d40c18a000b410750b80d04001c810400044203003580c1007200002000140038041d400008590448003a0707801588620300200083d0600c0e00c1e0040c503035005079000003851155000c045060b03002c0c410545042040180741a0b20103501e00c1480030311040101444103000009015000410415a840c0181c9043c151910320480540f621200180c0c1d011812001c05482d1081c00c1d00030708022091410070403100d000c2c0b540403401c80e991900c0d104800c3c5514100d42100c81c0300d00e01d00200381040d101410781c42e840c0c841950310f41850350080d054a5a60000120190000c050308034103024459549031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 903033947 1250 903032697 903032717
    0x114030105070e01180314010e19080d09020f060d0903030b011b15151701060b03071706120321090109020607200405010306090b090706090306020304020420070302160501 75
    0x107507070045c071100c00104151440900040400c1421a294502101c1d43d0008107500c0e0501b11481c1c5805004080100032204448010300090200703c100d90a440e0441b002041d14181c50000030404240703a11040c0c2c000d400014907540898050340b001d40c24511a071410030225019038011030b059031040c10203140e940141170b82034001c1410100701c03188400c50080e0215100880c090071a0300703080e01d680300d0100412243d0310107256801c01c1c000c000207088151040c0d4114a00140000c152020b00004030389500c001034041401038940c040c0c440307280e6411604a0341d44039140c0210106610b500300d1600b462010307101c0271468030340040c003400d0b607903075001007070541059016125414035415034102040282c01c002106480c60710b8900400b4001c41c02050b001a00711918144007603440d00c000d04c03200c169040040d0900c2000d801001e00b8064075002400182c0300d980d1840424020401054410080e00bd42c000fa000c20100301401000d2441c400e509541c203c058800000c07400300014020b030342c007185c1749000c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 903035197 1250 903033947 903033949
    0x4173f0406110d21240324141501120e07050108130201200a0605070e091501120b061201090b1504030213050901090b0414070f0803120415060e0114030105070e 70
    0x19901c0085265440d50150120500c007460700c100ca07600807100010940d18070070401010940300d04201b00100010701c480c0a030f100c030714910480010141072241003001400c7c842c0b8bd20400708995280d0b441c280401c4201666083c455540c10b191040328005924000000c0120b886880320401aa81c1a1201000c212801200d5003a091090b0219400b034828a800300380880c00a020315406642c035a1540301c4844080c9041c401a801e0042106886025261408445d80d03401140e94010080d908400121210b000f400a007543c401c001400c108440c10038004101e01c8242e074000030180e40102d85034010000d80c0045c2d03080728040e510011758070002c11804108170362000e40020354015112000014410003c2d540c40c2e0711800c081e00d06a0f420030886502c2900910300b082120003901307428070340c0725042d4900454a5500c2c400c1c196903900c007c00040114040096a10204105030811041070205644407185122400ea0910a01c079506040422a24907420107105031402a07800c0c0c1c1c0c07a0386045400314 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 903036447 1250 903035197 903035201
    0x30e0d021f1e050a020a27060e0402130e1008160b0315040f1512110409110d12020d2109050c0d0804173f0406110d21 52
    0xc54221101200140c000744420070b104461080e504ca020050711011081c00c010144012200a16850f00200d88031820700464241644202c0c0c0c1d03180341460a4009540218000c1d0244000d503d000d042c00000c0807440403228111a442860170116190005548010070356550864560510707040c0071a100a002c0e94002e50700071a40000300f0000d696034901d012000c07400b00c410259040c4101d0381d50b07454054902c0502c2c0700c2000100a607c03c1401818181d48070010039070020074070a4032582d613686603041009a02c100f024000c1c2c20050058010628600303100d00c40780c05507a030300c50060080d222000d00383e502a41d00b480f15150194150b11b01e09050401031002008489400d6800d132141c14210401d42d91400140508148240c0500f030304c5500c0c090700800b020b00c00c0c88110820360401946181a40c2c5801c200c2916000041001c210038100c00f20034900a40d000c41100d50b0403500003801189035604441c8011100310541d003260556548410216048840b621101010010601403060b001c0741ea6 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 903037697 1250 903036447 903036461
    0x70507080a03150314060415050c09040905010902180901060f0f12030e03060703060306110316081302031903020f0d050417031b0a0c210b07050d050106030e0d021f 72
    0xf140848800503143e80ba045203025484081d000f49500610070401000708006241d40d01008201c01400035041803c0c00a010380204c00100b4000c540da8041001030141c250846601d01c0e8024000303c01d544034126507200440d0003101c405005609110002407000c8011440e88212141118104030060034261045820841000c080d400c2000521031510250780510005004c2d081c140c03030000e20031740f46140034416149441c1309282580e90a0040045a04074041c0d510301254003032a00c5221541d84926146402e15401d03806501840b820201e0002005c4402c1e0344a610f034041c2d0221540041a03036810355131151b41501107800940e040c0000c204041301310701040701c0c0c51804000d481c00c4c402e1003140d04405604080c5443c5c1c0b01d9205012080074481c6002c0031700d010f01150b100c10701d10080c1c1038107086110490707184000d0101d5071a400241c01035104509851200702043c0040c0129692840010083d00034125101060b000d04aa038030941c40c000103e40514108800c0300c21030206003940960020624 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 903038947 1250 903037697 903037721
    0x9190f0612020c0609010506011b200a08100519090c0b0a0201060b0f31030b0a0902040e0d09050303040f0e150a0e01031a0114100e1c0209070507080a03 67
    0x92140d43c100b2601406403500c92410800002a6850018001032109100500c00c425041c42c8500c1c81c80030810b1004980d1840749414900046991140c000c917841c400c255200384080c0c0640c820306410b2a20641203180164150103000c1c180c110725030354503000c84a05031001082d003005c00004200e840c1c80080600790600c0c8034000010055170300c42000c051356102d00700007488000005030b02500c07144142c0000010700200800008507035032080b01031110410a01008e012000110000b54032502c81c0c0e0001c1a9042c0d014006000141c5808081696100350320350703580200305103220100300340c180082510122421000d42040c0c01e407515071070744000c01c1e01400b0046035450b05d0340c11408684446007420002e0441480c000002d40c51800d00b00c040155080c000b12800100308010800107400c41c0c810383e80c032001280e100e182c100b10183c081d2046111411010f8002c229440c2c1451600c6484e07a4201984d4001d0304c01041594480400f160f1a1152003c010301081d010300c86003852920940c030480e03803906 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 903040197 1250 903038947 903038951
    0x6050c2503120908040f1703180402040b0706020306090c0c191b060804060b0a03030f050a020c12010b0405090d021e16091b11030301061409090702010209190f0612 72
    0x1204550510a64180f54025540e1036400141001542d003503030305400042c81c58009103010074001012203034032489032281031010f0342c21f80031180900d50365544c111001800c0b4035981c0d0f03a581c3c45d14a0700d100a500300b110018480e020b4a03000401c00d054000449112a415201520584600400c0321000840c542004d660200e9110a0302801c403400c00c02c050094607550b1200342c01031a1910303007002589c0923603041600801420004000181d04000c5200c4941c861342000c1c1d880702c0005404915000b4210542c50340010f00c05c0c2040c000c0340043d44106c1c0c104505032802d10096944241840e512035040709001d0040e0300c0f0113a110492981103a1400c0c0d000382c1d040558440c04483c104030400c160b000d40201034842d9070703075004038a083c0800354040005007003420014000301100c0c51590300c9000501c50b007418000006960000301008030304030791035030b600285150014200014024000d4101c0b0701e41500034141c0340064065100400340e61400c031095060200002402d2000486440c6904002d103100c1903 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 903041447 1250 903040197 903040217
    0x41413080d1a041b080606070503070209090a02031911010503071b24050c09060c031c1b0e09070e061b0304140a0b04050f010c05061f0f060813021804060906050c2503 73
    0x10b55165454ee028205003001418282c807140109810f040301303900e00008241d0309000140c00a4550166413640c10000d003011616a41d49900c152003200c002079500042030094100c0d14100b11900540c18030a81c0030020b0820452810503844080b503d069901d07030b64150003400940f500e440c100340146070300309150342038a08001d51f0702a420101d1202d910180c12043d1a0300381c04040d200021008441ca405500e05000e171080c04401003103503120081c001034100240740500e4005a2035080481d41d100420182101500c01e4058000f03880b900103000d20715800045001c103d031180703001240142500c180c2ca0100b4601440c01007006041d094425045050160b03901015002c07440030301199114917113042404078400c1c030000252407000e440b03030811240003540c0e0030103021150344824555445642c0c0c00341c035014449180005103c0c0404002e481035942101c034100b00070000140c002c820018441c180502150300d4140d20951580206040120008000380c080300c00300000030102c0120600030f00784100b1403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 903042697 1250 903041447 903041449
    0x2003070b190f02070305120901150602030c07080601080714040b060319050601030c050d330f080102090f0105030403140f0a020c041413080d1a041b0806060705030702 73
    0x8814112842501c0034450080c440710704866000e041c1201180c250214a40b00c0903a402824034021500c1024400300400009910385209621a45d408400500540381456440d40000e64030341c010701009071240220300000271081780006000303042c0c2d00e502014010f02c0c3c0c1002c10310040744c0b007004403031507120341c0301d0002c1e02881d1a20380085000741d11208092150a1001034500286c40001d080300c0d04052409006a134600c0c0e0081c00d640e05508200d10104074004090021b0580b6410a0844481c2800e000c130007540242c85c520403042101c2c01a1143c00340030ba0b855002d80d0807800f401c6080d5030018223a0305410794641c45400119401032213400c10303d8000c5002c1140c2c1384550806005a00788117000540b003107000d9010001d40400403c225014058000950304207080d648c809002030200c40540c0501408101d04001910051060208108507125108041914440d02c4804c1e0707501482c80d1902c00c1d004860780012860500700941c503403107882c1c1c0f59a814401240d10006040d40e850000740040c0c001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 903043947 1250 903042697 903042713
    0x102040b04030629090109020c070e0a0501060f050304021324090b041127031903020a0b091606050912070b040303090806043810090f0606200307 64
    0x140d40503c6000078802c0340d140d01d41041c40490381e410000e031034804064132480d503601815a4107490f101200940c4031074504100502d0f0484a82101c181c584540d0304202c40c000150380018100d079001d80c2c9117407000d4020002541d07944400d03034001c0d401841155504603800e0301500720164010000c4400d000191a40001008040300d68001c10342c031540310380d440d441c3c1303142501620116041201009203401c0c0550015035040740f10303282c42c01d03100440c40c80b100225501440301d4040038400400c0340045034914680252165220181100c401880d40040360205074001000d10030401e0010b07002d030f034582c00c104068a041d00200c2d551307640480d211007062102401804448002c140707445003d0380315810f5103000347c01c560180e00003040d80d03440201004041000c42ea0900d81c0c242c80d100c099001d00c4072642039582c82d0ba0007103c105400c01d0803078003030044138260840d401013215100841040201141414541613481e140b14400004a4039030104032000d0303c1d40500540f40300c1503400c9034a041d0480ea14025 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 903045197 1250 903043947 903043949
    0x17070903060b0303040f0e0907031b05040507050c060a0902190801050a0605240706060518150f030a0b3403060608010f0e0415180203150c070b04050102040b04 70
    0x86420104004014803801601a03205086010b14246030621024200703004d054030404000c2e22011000c00d40400d8240a10006141c018402c40900381314001007403001c14907440354900031440c000014020f94410f00541d103412070024040d2013151541c450b44006400c0400041e071f0b0203021600713a150110040c840a80040204500120702850304280e040111585580811b01404c581c07001000c000a16840c031521400d81e0880e440c0d00d400c40341c28a10000c009a401035074010002c40b4100e00703820703034141c00750344a19007402d040c100c421100c1d02030004040e42078100d181c15031701100c844000218030705c09059108051405032016004880d00b15110b2400e02010948554080a500301200c0c8d414040d001c00340c0518203101520b94900740b40a64000b49520415860400c01ca020a081100c12120114001d0038582c081c480450983c030060050116640101d00c41d105049101d1031011188842c0c91003070b281c80c40010708022140c1c41da8000b04000902c201c0c1e40755420000070658140100140c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 903046447 1250 903045197 903045211
    0x109090e0a0b0f060604171c0c0209060a0302060a030b030f010c0305010501110f030409181401020442021e1e0f0a0210090b0409050906061507080a17 66
    0x3074649180c148001c1c04207019100700f010380c4021040000d0358480200311421076000526190400d10790100950400c5560214022041076668182d03404507440a1482d80c01130089840c81d80c076171110810016510303010300c802504401c0030320640c481c0d00d00a52061001600c050140d03020001030400701821640f20100d82c1c0d0100741d40380014441035034010390001500210a009107009140c1b07000b0300c0e659002b80e20a1511250300c0301c00c2000e12031100780040700751a50203142c40364200325000c001c5e07020303410a005022000712140000c200f9640d104100c600c1ca118400031001d2001e01a07202d41d22000341070840f032001d41c800c1c0240d2180101c6d20035500d8692010300c401a001181c0c008407c041e008042c40500191544644010720b000030001c503a40d03030950750403034208034240c805090507288219a60701101504030086030004207180c40380c0100d88515000c2c81039503815a14102000543e40c04510b003000ea50a0610080c40040c4c0b10100a0086440906040240c1e007600c11003d50800d504480300703 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 903047697 1250 903046447 903046453
    0x60b3f01030c0936140f060f0a020f0d020901050f0d050a050c07030e011206081603140d02060a0b060f07110108060f0f22181401060303090308090109090e 68
    0x1001844158800c0900c254840c501e0740d000f4859645201c1d4180029001c0c640b0113000c0348614804201034020304002940950b0291840b44c843c40d42d806850b46c004880194003525842e000800002461003260f0740c1c004089a03286c100009062020001e4001411440c103001c010017240f00c0a000035000740110241401c800700341860500e0000c025a0800b0b0105c451445003400114000380d000b01e0902d03028402860005894550311040c58060700042c1e02200c0c90303028103120208144400384a640c01d690080034000101d0400c030f5130441c0e5600740c10744150300507000700010039521449a088000740c0341c1c00801841c00c0c91800120580c540d072240600312101030300c010980d450313940c200c858250301850031110900e0340324480c004566041c21114015105000140511243e00a119280700c880345810b802002112122162079803041420f00b001c0e1b0b01100b81c1807941084100501548040c1c03a45035651200803071035035079407035016000815000e0600c200d0318000b1811400385d20407054030088240003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 903048947 1250 903047697 903047699
    0xd060b040e040302101505090712051305151b13091506030b0f010219031b05151f0512102f03040816050f10020a03060b3f01030c 57
    0x64a8a04c031890418817460030800004090440851150708880003075030350041a40d21000c04486040041460000d06890a010700413480003010611800d10b12070801c50b0b1210304031403455044060304644029010320022250041c040904028001c091a09820b1026040d1030b07804043c1502e00a8402a1621a100c10104070580d418040d1000100c000e440c1c0c203901420200000351690b049031a01070b941140d16440c2000c15201e040740c0600c50122460300100c0b0003152034025120038260410a146080990100300d080038400001c406d103d03c412941c407070701441d21050090b035480701c0000d1b11990103880803ca03605403150007410345103440800307010f1054036082401c10b1b0070000d0360442c0704041014410000011480411682000410040c0900d81065454070500e88104e02d4800e500500030342400a468a001d900078016008541c0c4041c01100c2c2c40b06861580c6000d14042285c841c009102040b8440540800d07025108070b46189a0390396204482940f5180038083e070007164a480d440034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 903050197 1250 903048947 903048953
    0x6020a1206050103090507031e0b04050105040215031501080c190917070f1a0f04090903020c010309020f120715050904060f0b04030830060915010507080d060b040e04 73
    0x200d40710140409007403c00c46101c030303602d5140d51804140001051491510f040c1c2448004070100307240ca0300c0e40709960440c036103000d24103580079110648040340119000c3c040606014058019a0300c2a10807a220707c0a424040d40112081030010342182c240403410055010102c01c1e125580c00202e0b1a52a200011841e04d140c400e284800c0d401c11420a404c60001031002e07803a00200c01d421200550984c40c802c00c5282d5a070300440c0700300d61909031a8207001070005008401504403141d0f690098003a02c000c41e4010300103500359031418100a60005003809030105629007111410b070589644000c6a00d125198081c44040007010a00310001c01c03800318111102e4030f0701c0d00a4002511921854111592814400c100540568000286002004a12207001040407034400c039940c0c0c08000e03062600c8030f0f24000a404c04506842c698040c088403c00500b9042d255040c504120006a407054941b24036520b8500064000c501c41d10780150302c42e0800200e20000c0703000f4001411851030034040c5400d0503d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 903051447 1250 903050197 903050201
    0x50d261e0903040b160816030c030905040c05040608041b06020f0f1902131103010e01081c022a0a08010219020a030e0d03120f0227060703140706020a12 67
    0x3420300107194010042401144955000c0e10301c48045202e240e030f405e00451070001c034280150b883c00c0c03081e12600310511003403580c0605012121070080c0c40d803101d07032502c0b10f05001c00e540c0500c0180300450000c0000b0020584200600c1d030b800f03401900116004c002a40300d0998010726076205a0041e404400042440300c0c05001c9800107280030401450030842c201d4a5460200309400d0207131043c00003030500303101c820b0702d038000344100c0603040d010755aa5030311503200110703400080c001c10040b445600b4128404010340000301c0c0100319913400030110281811402280302c03141c4009002c250074001140d12040d05c1d00c003c0c200c05000403400250721025a001c00d10f0900100d00c0d5800110361028030705030042a00158212603000080e00d807426441c070281010381da10711244c1040010280350204181c00410964040c20f40030400302c44162494000c010a001d1110f0b0103030480b0b9000c007041142c00d002034014071002c411a5458003007581021503070303100d810890f0009108500820300e41010b440c5255014 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 903052697 1250 903051447 903051451
    0x15040209120601060f0801050f0d03110f011d01050603060a0f0b0301090b07030b010804080307050d0e030705070810062103030b03120d0507081611030c0717010605040504050d261e 79
    0xe4a446d100d950b00d01800120401c00c2d03001040d020709003904040007414441c609003810414020220307800d441c00002c84500a0030024403140c9900802c4444e082c40320010300680b40a11002402005a071725803071030342d0004258000000c0c00c520b42d030b5210914551404e00032403014034003400d86003800f450084030240070788032848901d904000c1c4244c104030025545806903500002c0c545030171621501c55a14640003003030103c0c54129544400303d04002084800145a01640d100c1c00585c0d03101c007100d11007041a20668000c1e44140c48400c01103d00a04001e031004201c54041c0c6004600b2000d040e01003401c0c0091004250828480003551070140d41c03c1d4081c05030803405900c1c00311010319001d20402c56040b0015205d8040014981100403591010002d540d43c0c9281c0f8030503114546e0f50742e100a0b81004e401401d0455030b50030040005801c1c50644a5270303100341c0d00300014052100001c00101e505292410b0804074621211001e9503003003100c1c15000e0700c110000381c008000e036000301d40569541000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 903053947 1250 903052697 903052727
    0xc2f12010203100909031e020a17031008061b0f1917100302010804030c0c051005180301020a050406080a02070f0f020913121412040c05150705061504020912060106 72
    0x522080c0c00019a00a05486610480c14000707c0d01340c1810b4800c80c00c1c032000b203c0c041c060684011a150441003500008d60007886155024100c15554094150302c850b0102e034201c1c10700300d013200504594900540207116101e0b0074107003030303151140c002c001c0010011101990070008034002d041c0841c40c080b0320031140c1c00100c540000c4021903c0d66000800c010001030004003044028003a010411545014900280c4002804442d01603644c0c000100303950002065030300e40c1c0e10300c0400b03e03250381018801c6582c1c0300344e00d0766001e15190821600740d5074108044c00c2c045407580d0821425000c908042042140c25100f600300f0350250420303004101404001905400700b080328420998006242103403465134810043c100114454003601c0c482a00b40203106441420b0700b0050100010030019040820507644c00b1102030100200d100072501d018000c0a030300801c181d00140c0411020101b071607030081680e2004001510b8810082c000c40c0c00e80018001100c2180c0c080307001800400d4000c030360051340f401c0c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 903055197 1250 903053947 903053951
    0xa080405070801050906270a050d1205060d02040c0504080f0706080a230c0405031c02010c0c03050304111f1d010302090a050f2b02100c2f120102031009 67
    0x5c0c90703005140c4502d4090810340446a4400d440e0441210048030f078054885e07c203090307070070a04941c00c2840d2108043c00301000000c140d03000610030700c007036071103100d008074400b800200c40000142c1c28440184002c15103102481014040055240810010511046940300242030350b04d18008010b4826003015001c41656400d00034201511090001040d64600d00714071801c281d40c848140c000854031441c3c2249406006004803007881e00d40d141101c0500c41038a6001b040061250242156000102c4c4401000500708101003004980308182683c044074004220445100b00e100d00d1043c140300b40e0a0b85404a070107040552240f8552001c241148902802c05510707000c1d00000259040342c65005441c8540b14400c1e1181b02d64032214001c8500c0c19001200480544400140030070f4034100140817480f0758031006113071030034510540500cac01c042d610515100e40c1e41c445103030039803025102520901005a0300d00111016035140c0f0006640c114520000682d2030030900c0d0342c03200070754060f0803c2104034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 903056447 1250 903055197 903055201
    0x3201507170f07121b0c0f060e060a180e040b070909021c0908090a0b0301090b03010209101d031b0102010f0903140319090602090909010903090521030a08040507080105 74
    0x249000c210742c1095440b0044060280d507000081d40c4040c1d841e101084418402c2c0544406c0009403a40c85098981401849624039540d00702120805040103119401120500401e01c030700c0c0c0961900301850070b11044050700c064684100c42c0411004860581e0114204001d10000c503400414400180c070540e0b03029840d1494024442455100780040c400550350307903070210790600c180b1000361110440c1c000c2000c6500c968407a044035440e002030146070603541c50501031082a24051003118007502c1d01400300f01844008103030542d00a4500407401c65080012041d034101c3d69010310801c0740c80d4010560764446246180002803c5030007004a4038541031414080703501094001c450324001d81212030071190350340da61850755907880190398074a0b44007038180000c040400840341c0141000e080140c803800030aa41304400c0f02e00f6a580040013501080200710103001d5820001005100030b080c01c0d070320410917424400700900d9a4070910203000028100e00502040100521000d00141480c000900040c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 903057553 1106 903056447 903056467
    0xb12120c010e10141513090503162102070f21050a03020c0411070f06050a0b0904051509150a0c031407170105100206010320150717 58
    0x2513010600080d42d81c4801c03410400000100a01303c0350138035201d00350300f00140700b06a02a0f9150100b04511040c0980e09504001181d03c9091048401c2115400c61604008a10301150854100440802529103554403071000c0e00d920102055001030303502c4041e0700c40b120602c00200700b8081c221500b01810380208172080b80381802d580c207001003942d0b807000703107520721504100600c03007400c62048802089580d4050f0742d10010158001680600c00c000007140c10740f046404031840d07886025845104200552039541241c41c0310000c2032403489251610b00003140042c00030320f09550b165980001e0720320940206a64600130104106141040c3e03a0041040300e01e0b0ba040b01c0c0b0615210000542c90410b001000d150040590103000725900716a90541500d9002d0416044000c81c03000c5800d5658800c400d03580301e6000700401075514450b61401a0005800c0d403442d00c40641c00703001010b80 = true := by decide +kernel

theorem cover : BRFrame.Cov 902877697 903057553 := by
  have h0 := BRFrame.cov_init 902877697
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 902877697 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 902877697 ≤ n) (h2 : n < 903057553) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
