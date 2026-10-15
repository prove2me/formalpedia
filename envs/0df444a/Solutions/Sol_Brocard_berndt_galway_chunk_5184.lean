-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5184
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:01:27.989761+00:00
-- url     : https://prove2.me/submissions/b9883c28-5be7-418d-b5b3-9588ec2321f1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 932194244 ≤ n < 932374100 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 932195494 1250 932194244 932194247
    0x22101120210050a0207062f0307050c0d08030402040b061204111e0d0f080c1b041401050f0f030f16050907021c0e0f040608102924030106 61
    0x8038020000c0c0d0140729408941c484551282040f103030f285000750024521103181c02c00480b08100b5092030a80c1035121403880034222800360082203070264151000716141c0200e070034642d040c0f1520001341e41c0b14583c1d02c660a03000406040030b82e0781c01601102c0004400d134002011441f03a100d00046404032201070002c000804c5426203404801d00020355406c01400d03000c20750048a0130700b03442c25992200e00600440d0024040301949128544101c49030760900300380541052900309584e1203445415050720400c81141018416044107a48040424110b9450a004600d454440d0304640307000e51074106060341c241d103080140005040810b4101d42140d4001ca050b200b4401190141600c200700e1000840e41c40c41c400101406802081c2e601c882c0817a4034032038141c40d80700d1700880140c1c0058028280000b10b684900c5003034000c0001c40003030801c5040b180e450208071078404034440d0035944441002c6d070440d080690440c500d18400d0b1170908c03000e10240314190031a0750070a0081126000000046540c5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 932196744 1250 932195494 932195519
    0x627120f0203070b01031a06060c0a1b05030d020a060e010c05030604022d1c200309010e06040b0411010903120e06130f060215190b120f0f0d140409022101 68
    0xa40c44400c009807c1d490784010010588a002810402c582c4a840c021001c198420303004010190303600344c40e6545da581c0c0c5000c6030420104070158005038001001070014082d0324000c0503400c00c0404020003c088080401510794000070300603a02556000c1480001500307000090a0359011800c13403060b85155180e0340742010f034850000f4090701c440351100240c14001d1405a281c0c12131000750040744030400351942d480300d50802001c0707010541d219a040401c0b09410701105000300d014000342070007031070141054460b500059003110b0400101c202c040002c9400d0340d5550f0581e18a600d0a01d0184170304900044140c0903000380070030101c10f13401d8001401001103001c80e00301e8019409903400401041080d0400e402c08403038100903040541100846060700e980300254541e0b0007004400c9140381858002d01e46902c04003e400d0541c4031400402d441d40d01000a640d1901d40340c5000162410007041daa801d5000354850701d8603694011454030300040c00581c040f0714480035420481c0003507a40742961101d0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 932197994 1250 932196744 932196773
    0x4240e010b1201020903030405040b2b030915120c0302040504060b070b0903031308031003050102071b0b0a050409020c03070203120a090e0903070b0705090d0627120f0203070b0103 79
    0x2d082601c0480c18858418002e039061107a0007005541000d140800340b201074040481065880404c0c0d2034500c413a0141d01410070305801c5220030740b4010002da03141c0a004141560008034954000c003c070b40e45000d40c80007101f130f962a00444040345200c1007050542c040c2c01182c04c1241e1250500d01d01194141d00100648080c0d40602c001034282d031580349020352648800d03186c00c50040d07800c01c062800b08040c2c400654000501da00c0ba07d010035507a450703171800ca070010340302203030f2981d1119540b100d0803c0c04a1000c0140903145141e615000303440c80c1c050070307600c130b9407141080107900810200c0c0c2d011414016070f100c40390003405840e00da103d1010000e0880e40440201404502000008140100f801050501c81e1280c43c000318074220050311805411130000304048200b1504110000b0300343c0b541d02d01d5400807886190f0105160189242d815401c0004400c0c0003440c0c43c0890b010408100301a41040211a90341000d0b140d034218104124114800c070b082c00f82c00b000200000108004401d40c24401 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 932199244 1250 932197994 932197999
    0x120306040501060302040b070305210c0909070527041b02030c0d030603020a030b09010603320c010c1e05010606051c060b19120c02060f07020307050604240e010b 71
    0x8583e02c84030706804a00035409112010a4188446400030740200c000b0810250400344030344259864100803082010119040210350078003241551903800d0540b02da580025441c02c10b1402c000099010740400c2000710340444200c43b13130500a0300a45c41b16800300c501911703211030035500319215541c040d40c1c83d80700c00d10402051090002400e580c0d840780c411082500e6008180c20100d9103151540e83d50000701070300720a8a5503881e00e0000024000008054003038580708540d00d149442c00304038030f001c0c0b0000d4840212036040001401d80e10b07030b40004540b1072564091400010441140c00d0242d01d580400001002c540ca0b1000201e0310903007041c05444804034002c40340920005905526041d6a5284500aa0843d007402951600c40001e209610f4003041031030f10200c2a0003400035035060710104448040981c12840a0018140580c40c405a01212500085281070513a03914155613080003440903001c085a100205c81d0007200d03064009801c00c071898188050004094068000c00390400075a1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 932200494 1250 932199244 932199251
    0x60a031517030702190e0703020d021207020715080112081b0a0312111608030a0902181b04120803180102070501050906181e03090604151d1309110312030604 69
    0x6940c1d8001d4070500f000e1b5140001d0300b612540710360000342d020790817140715111410740a02c401108a409010740500c0b0b0451540100003491a180072180341c0300d0800191010042c029006000c84195800c8030321080345d1003c002540c8845480c46010b05c080c45449200c20307401503120080c14141d1200360368540d084d20440800820076100302681041c802c00411854042000c0039220120301c40c0800303580d011410700404142d0b1052a40080e004049110162008110b40c10030f02c0310117043c14000b01604995100c00c5880d10b810400b0251820303035620802041c0a40000004820084161650100c030480d01c0c002d54031102285481c90107043c044848500300d216400000d00002500f10a810751444500f01804070080c030082c1d240d4440c00300103801c0056100c00c00802e02c2940356813005000030314001d03801800d1400d6558000f80030b1420b00c00c0c0c8140200c00711061302100d6507408600c5a8002454a0018101e0064909010b2080c22006078950601500040b2401d8061410085104501c1182d080 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 932201744 1250 932200494 932200519
    0x30201020f040b191d1009050a0e09010e01060308041505090d050c1201110901030e0f0703050d030606030204060f21060b0d0f0203071b080f0a03060311040902060a031517030702 78
    0x407140101e001040000c603a008484800580c10f1600804030404072511f05100c9494076003010992540007030b8041c9103c10b030200d080128200003031040d0340720100c087d0000d000740341c070359161034840d4050b03800788640c003000c40341801d0122401101114154003000d4201860381c40d40d410007503141d142d00c1207030b01d002d418078074552075000c941032240d580aa01e02c440214103004e2030100440007050b60314004c000d144651201102c0380201045164015486030009010743d40a941d0000c0c1502c4495200300d0905006100a0101c1508850804c400340e01c113140c40c01c280460700d0b140100c152070b0704d00751010031454024085403e002110052034a01100c0c0c1c02402030b07030014422081207110440385000020071200010341c101d002240e40e103500758001c1102a08010303d202e0403030120703808004000e02080e40d505040040180071541403000c45021281040001500d1300030825a100b801341300c6040560762000c0d46150503c407110540a042c4840703628090750900c261542c3d580c0e000341000c0c0c0c420520704041c0b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 932202994 1250 932201744 932201747
    0x80403080c13032405040b16030603020607081e0c07090c0c0c090f14010e0a0e2404170a091e0806040b0f0603190b060627130b0102060112030201020f040b19 69
    0x303403401168801550301c29035589400800c000708c0020135600070151607074000030140e034981c4007900980c1d00030024140d070b4084441c1a051880503aa101c40f0041e207080c0954803e081010031082c046948100021a0320000580b08480c0c2c0c0e00b1500c001441c035100b664000c10142100d503c0805582d00c0220100310092241c40d1203084003001344a074819905036030000070080003c0c6e801140640841c04210303110382c00310159528404810140d103011040519003044184001c06880403003143c105000585040c84007200100f80641502446030324810702e44025110742000042070005100060944101e402c05140060500704160b030110624003211010500500d0041020b4008501103c0702c10004403075235555001c0030300b00522a0b580100c0a1242514540d10107400c8101407030820600d1000300c200038104208200750390500040507150640c0a065039800203030060641c1e60010302e5020070382c2c1c10b140c120301910604101c82c0e000c200200b400030b10440b03024091712090b00c07290801c040b82c4040d07000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 932204244 1250 932202994 932203001
    0x206120415090c120302120d0905010b04051611070f06020f0c010f05040e1314010f0e16030f02040e250e060f0d02030705030111250201080403080c130324 68
    0x2c042c20405042504010b00c0303048a0340c008010703201740181c8066140c00480005180c2021515129060f00c3e000d0340380402000f0720a0440400341201c0070400d038204460207681110410381c06c03400748241c540f84e034041da5004104400c0148403610348100c4007a15030340000d48408200390700e0000e6100f0041400e450798010215000c130b0060f59500e050600e440c00d0080c0c54840d50161000c661010040074000c003250b900501c0c43c030140b2000b8004144c245049400e0b2089803541c021001c9207400407000850540c0159184c4000c40e0340002071003103003221a0000034000c00551440368014400c0c60440160702d40d4240c111218482d1300800000d02d030b66100c1301d40100301005c0301d0301e544c08089100080744500e01190f592104500203421181c1854844000c00c2c00c442e020914043d07031080100e1240c3c1c0300d50000004115211030010301a100c8030055001074028940030b4002414044500002200c101501084c0d58041e1912010030700b4060741c07810944009103210301c045d40101560071849000e10b12500 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 932205494 1250 932204244 932204261
    0x306010e04030f120603020d08030f071e1116060201150e0108070e0a020c121c060b0406050309160e060a081f0b0d050105011409061f0c030c0206120415 67
    0x1200c401c0124040d5034219006090040c40700d130000e42d220404030150b00d421401d007007094401c140ca0340c0d8a0411307001103480d02c800105940200700d5102c885c40c0c2a00700c200100522090756040004c5011a8140c0d11810201d049800e02120001c208001800c103905400c51641c0c180342001080c002600c070814100603d03000d006104c50741d40140020048802d00c100c1450740300c030701d0300c00042c200f4102070681410005006681c00f5814004a47d40c01ca12081d070080c401d40c122814010001107160400104040c001d07485083d080c00741c04000201e0340c590510803c00152007a009110400d40c98040c4c0b250000c1c0c1c1650302c80c1c00f03041400f0010035401c000241c1d0405034a16140c0c000300000c0002c0d8000301a10384045255005950701c0d40c9a0002082405440e01030040b0865100c41903001800b80440204001c001500c11880045040011803111219580505070303458903901c500d110f406c003a600c802018400a400240c00103c100d441e0410045003030180c0e10892520b104034295940407400d896048 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 932206744 1250 932205494 932205497
    0xe01150807230703090501020c03151f05060403030801090f0c081522021b0d0f0315050607050a050607030b1809011401170d03060609090902040905010c030b0306010e0403 75
    0x21001c1020a0b000301e080703541d0344195444035101c0001841948446400442046011030b0703c2a074280001c0d030701400400d0b1221010f0b13008121036000020080540d0a0291001044110b443e81604001c0106070000020b000090304031a51990780b0716004020390024491482f06170b00e4008a56074109981c0122250b8510540e00c0c25240d0b112152404200420750718520f41c00781810110850368680c2c07000c10010f018501c1ea00503265140300d07602d12445400410140841d4005801d4107542a401c180c200c01110740310701c0d00092940103400c0c42e8035503001c4d41d041154011f001040d0032040100c0043e010742694810f07016506582c441c0766044e01500c4440d910203600040c100c804ae00d5009101d1700450b8441100c3e4004140d8003246c1000050102081e08042041c82100e40104080882000700c032051190519041000e0341c54010000d01140190040c0f022054541800710155615900114034a5400000070005145440350280c02061040800c0e0f00a0291a00015840110180261046070503 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 932207994 1250 932206744 932206757
    0x320040510030602090103140108010903020c0604081c0c051006091505031207051005040f20030d0c03020a3c08030718080d0c170307020c0f010e0d05070e0115 70
    0xe43d99048003a400500c807041c1095500d0852185640711901410300815504000040362541070030001e0419580d24100d90150b04104420040b201c00003512740c1003035000d5034001105c0110302504640700145810080d0440c802c0910480e0070b030703510b40d208904031891200308106248405400b0f40c90003180e84540c1e0782c160001881e40404044800050411610580c186d42140c589060036500b29001540c00baa01e100005c0c40140402507440c2e6910021101146100103c0d10f4010019a90300100190342040110048120781094000c110032856190300450008092411070100300d403c403400c1e101c110040000021154811040c00201c00358160402c18840c0f450350b83c0502510100054000703410210100440007a00031024080f2801d103c8a030b81e1036407604100c83c03c001e41841b860128401d645c001c10018030075200d400149a0382c0c2c2460954841e00b05061a000603158441c10f8642c0581111055555008200000c1004001e69100b000d0010326a41c903005100d20341c050269103280420758 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 932209244 1250 932207994 932207999
    0xa0201030209040b04020d1a010801030c120f12030c1d0d08030405120406021f050f13060227041808160507120302060a050106080c0a050903030d02040320040510 71
    0x100350020b0403030a001800104241403481e01003401c076800214110a241e503184024031804043c10b0258510100910b02440254150f850784030840f14a88130745801c108200e014002002031000c03100c070180d600968080c000c0f4041d80009006020785515450000700450221401400c0c100059081034030b0241c0303448420221035403110782a600c00b60064649105488160101070039220040c00030f40f5044d4041e011241e00d495a02c41c18010b0881d442c1096820003040000c404400c2c0000c1c3d81c08071950700c0c80000c800c1c050604100910030414030009405a0242d403104500d01c4121103580b070b260a0b90100311021440c0786d9991412035007070004101100412620280c0440b80c100421400c0c0a2001e0310701c00c40d03031503002244401c03d00e0400c90161300644200009030201e841214014142410407540a10340149030454501c5600c914030140310002c41c541e00b5644041041d1401c68546800c215a6161a81042d02070402d100a60b202c5400e00f81d054003203541802e0007464091000e20041181660 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 932210494 1250 932209244 932209247
    0x1e050322080d02031f05061602212d010203070c0f060204080d3f18230609010c050f03040f0f061b1d0909070816140d050a0201 56
    0x36001002510600c0d0107200016140020b4801140640301c00603c140c20101d11482d50090403900b940810701c22002031065020700610001d50f124140d40c11196034515820300c0710301e00d41712001101c1d04683c0b0305c1402c504882458100544d540d002c3c92103403d00c1080603900d00f140c0d080c4d11003125980001040d20107543c0002e00c80c01000c01c078251051a001d0b0416031600c902c1880c1410b0090f000000440c6a5142c000036040700c0b440010500c0c1804500c070300079541e40610501001e12500c0075402c02c0e07594004c014003240a00105490070790080d00a140d8004007402d591826201d0395600c04c45000c0c4001043c19020140f003502614421a15618200001c040c1007820729000140305582d0180c042e514200040c0c0e0740040c1d0080e540c4180b40004890241e1b541c11743ca034089c440040c0c0b0502c405110740310a1507030500c03210014024111071506403130b52040714440c1802001d43c03103c26184141c2401c7c80080c442c00d000b81007524503100780c0d600e0348441d840c10080c05003041c0c903000d802c6410402d036840255 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 932211744 1250 932210494 932210551
    0x605040b1803032202030f06091b09270f0303011214150610030e01050702100609060f03060f090f0c030b0f010b0304110f181506070203100c020a080a1e0503 69
    0x11700081c01e8404c5140c050707051505040c0d08440703030340041d080300205c1400704070500000f10b001481030306e030300f021458010347d05043c09540349403803523502d404900b03040390b1464100a00c01c440080841540e44a5960310044910711340d102904455460116180300d000050000d40d19110715500004440c854884000b804100c22900460368105911800441c0c010303502402018060b8546038002d1801103c8040510101c640a07000740c4482800e21100304a0506903640101c103803a046038000804900100b0680000d1540f00030090503011040c2d420f01c00d101d08003d031402100d00603c0c580c1219070300c1c1450281c0018090203107508bc40002d01c0401c0c041852000b844a000c0340203403041003010340c11f4000400552007100102405110042004102a04010304004001068031114140300750765001a4641c920200315079440e9079600724100b807251081100c00940f54120314820340d00c2d000d03504010103503041044200800b180c0110040843c074803804c12240300b0640320308041c58040c841250414130 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 932212994 1250 932211744 932211811
    0x90302150604090b070f1d0622030f0c08060109020301032103150b0a090905070f0525210804030806270f1801020f0f03130605040b180303 61
    0x40d94490729000051420a4011701889903500d03554413120340d1101c02000306640c07440b0201000380144d4021215100e05042d00c4402c5c03a07004403003d03842603507140d49400091a60002d0148a13100c0c4d8074100380040c0031103c8068038881c20507107031580c1c5ca40d00c8603010303840203101c020480381c1061410101580e06101c180d683c01c04920b00815100c1c444e041c04500300d209a0000c54044c1c00c00204168190303040440c01000b400304001c10300083c5810f95010745501e040403100b006001c0002584c0c00c070880c0d07a0200180b0400390b0b10001d10304401c2e50070701d0584044203c080c440c02206c4514081032960040d01c181c0e110703a40c160b03264002c641c0c5220038400d002c0c414007450300c80c2201003900b41401d4501c050106201d11a80301c04101240b90a4024428840300c0e149107280c1ba900c104207440d0020b180c0001c94013003a099882c1c541e529240c00e9101f10000c038030b060700540380301c1c40c0800344002c02c00d030092143e001e202c031010000f001004003203659480744400d841004200ac00410703590800406410711004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 932214244 1250 932212994 932212999
    0xf0a020f1e04110354120904111315050d050414060c0f0a1808010c0309050607090b0301141c0f031206060503060d020a050604180509010903021506 65
    0x181c0d4048100440c058a500c4460b10709058400700c1004240c0c20303a2038100340c0c0c60782110342c90301608450011200380321801d1860032802104805250031101e03411000e800301d00c030b840701c102c03500310759481c20810842d000a20302d00d00c20350406c201e82030811240001d95a020148400e035040051030004200000a084081b5109110050110386074003052480740c5803040c1e00039002480d02c420792006a80c02c1c240d00a00500c200c02080c030a0040c070344615016950b052456041010040c002c03281c003260744050a900c0141b032582412003045071107516801055125105034102c59042c0c4038103000f92002d0070b090044044e0240103100400000f01c14503800c0d05442406030104400085000307061001d064000c1d4190f540b055415607160805620242d01000c82035044c404020603800c0001c01445403101920561041100c105504155a1105903000c001d01008140554032a034031500005a640120085074030186407070005402558103004404482d40c0c0f55020300300102d00081c90404407400908101d8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 932215494 1250 932214244 932214289
    0x70504240522150801080d08070210020315120d031109010c17040e09030304030906021212040311010e0c09131e141209090601090515091206180f0a020f 67
    0x84052032040b0408080c1d6051340c4801144d070600030072030320300300c1034902010400a01c1070401c81c07080d5011035000006003501c600540d80c0d032540d4080740c1030b18200b40c4041d86d100800b280940000c02d0009029005000c0702d0710240032540340309941c64624042c13840041e0205442c1b00c120800900d81c16010360450074000080b40c1020b84405a015020348121521640d031f520010078801416040000e210081445200500f54000f02c5030504015000744004002100d05010100d010507000b520317150b2514807990000c020b080e043c109220b696440c0200114001e030000ca000c6000c1c0382000405e03114481e04a541111660203110b600d4181042141e01a1104610014503500d18901071100c00c8090110b640140e40300c54180d020000281c102620440c1801034081040045860340d90444828044901003140c5400140012a455005500405401d40120020402c07074a20074100002241d04500c1101e11461007841055038030301034050069482003d59160605030b24004140881c1041c0c2c02c122039 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 932216744 1250 932215494 932215499
    0x901050d05150c04030212030f180402070b070201231e0c0d020c01090b0105120c090a0902040e160e0709140a080102030405100510030c09020a05040806070504240522 73
    0x414035a030300b90f07404446a800014100198508950b080c441c9254400196240104440c01c1c42150f1141003101c10349036204100803682680c40d541034844503500041d03658214607020500a0003410f40700a502d50440e228108048102040c4422510038207495100c00c001d9410800394244000e40140000c80030301040009083c2d03034015002078004c0942150000c40c0c426014902030902c110140c011a00441900031034844140340007070504004903090702d40f140d6588504500d10007801840b04003941040c1040c08800c06030600094001200c440d99000f0303608152507010008003030109440140002d600038105004d107062052078100e200700010592022942d4404941d800c0e6001200d0a55003900510150544c280280c000d080c0c4c48513440000005030b078250356540c1009030740c6018004220782e020507400c400070b004008490260a10200b2514a860103000051a40e4028014248441100c0d080421410000c403d41c041d00720040d21814100075241c00200c8012601d2600c0c44904c0d400c00400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 932217994 1250 932216744 932216773
    0x90d0507030c03120509010c03030b031018120e0604230d0b06010306140114071704170f0105010e04080706060b0c070602011b051204140d030218030a020901050d05 72
    0x30040d841442c0c152001c40c07850500074110302c510000b10041c04001c009115580ea80500c24a60b0307194103043c00103d015904010a00d02075142034558107003890141c450070300c0c0301d00c96140f140f1144606d21004407034241040c01c4501c0c02d250810341d90800c0091100707000d08505c8900805004403040000043c52032020005640c00203148001e5a4140c05002807141550703140c001d00740982220001810080f400000003449094400d913074200303d00c0082015410000340425910304842051286a203494079a20084444600c4050300040c620400465025010040c019181220303088106002503079204d4940200c07950140c00211142c41d500e000c042032803260903014043c51010b14009180e01ca05005001e42112142c1c4180d503002e1041482e071311449584481152030611f5090b0701c0108540f0340e854641c0881c094080207a000340192042044410b07415409007802807420380f01c2d00e1071030000e8001d02d41c41d2000320341d020350401010001400305003005000950f4a40c890422902c0c200c0c2d0103102c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 932219244 1250 932217994 932218003
    0x60b0726030708160801050109090e070305030a020d08071715010302090d0507180203100909020114030118061d04030e060c01050c040816080c130f020a030605120102091302090d05 79
    0x9542c0c0200b0051410b2010400f400c460b6002d4003c031030700740000154104400130f40300c19160b02c2007a0140c1c0d2034100c01d00a1030380c1401f041c40256407200c2240e485070300001c406900c5038590407580e00064943c500290b0b03002d00c5080280441c0d9004503100c0f0581e100c0d4481e21b001801700e544800e052680801411600f0b4a4094002c10740c10300403001742c0611030074800389116521f81150080c1200380148244000743c03108108000840da42d0090010b95000c40c0d00c0161a0f1107588030207045440c2c4040000910b110200b04100005505c2607010401984c4405915500c120b1b03070549007000c60765030000580020300801d103e40220030000c040b2400e14550050003400c3d12000c540b2070402c02404030301004105c40c00c100c00c14400d452440b4034200c00c1d0506018554442411410303902c5005444032410050000d580880048510420b0540d503910f4469406801b506591007541d00401c070554200c2c0b1450010301c01d48a03844001000c040c0c110a20003042d10282d0000800d0503401640c808041000980800 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 932220494 1250 932219244 932219251
    0x40302090a1e0903080a090c1505030106020c0a0b032e0801021206010219081606020307031b030605010e0d0503090303070524010f05060c160b130504060b072603 71
    0x80388074061401000e240b40c04820b04030981c103007420007800000707402249081d4007194024001070081d11506111440c5403607623110032400e01061116402d0581d00c4402141039034440d80880f07030051394440a01c5112a00b604c94902014420710100e00101181111440b05101ca01d4008141ca28981c4220315600103d0380401d80b581e600290800002c52a64802c60f400354090015103035600106410621441040c3c400030000400020400ca9210a099421032502e4109a00715180d141085e406002407148644c00c141c20303540d41c403c084042d80709001d88070558206070756488000350b0410900064040940e0b085405000522200d5001c1e1002c001410065000b6001048481c102c000c0112054007240c494400030026103005110310b000d5000703050200c4400350340a40c0d480610210480c00c001a40d01a10030110500100003440700f8554050701030f0807120843c0d19082a5180704010482d0131900c00c550811005002c0034001c81c044e03054004140c44000214201035103030510380c0c1010750044 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 932221744 1250 932220494 932220511
    0x709050a0902090102060606041a030c0c100e0c030d1e11011a0a0e071407020627040c08060f01030e0a0c030303061a091336171303021504030209 64
    0x300d00d0298940e8100b10540c0c000300c080c1d0b146449d060400b1145054884c040d40b0002c10780e0400404505040d59a00890f2003886802043d141c0d04903612511002a0200412a81541c410320b20110218038010030006030640041d2503200d461503450034001c90540d00c145110041c44100c031500e030040b860030301a100f003009050380c0d080341c41c0098030304001c8807000a401c0103a0b001c0d41c1104115032160000781403074a200c20b50503c81d80b10411440014258410745c1d1030b0f085014181c03460008204845590350004040484090200444628044400340c0307080301e066a002402d680300c0001d03540241e1044148010ac0d409a079560f40042e1100200c498266004900095a5050401c40c1321034864403130300e1000405400c0303032a115400c4001000642c7c040024072486544401512845090501303007a0110704000d15010b500e42e044a40e0072140507411010740c3c0009c090044003101e45080c50485010000741c08040301003d05680034440850010924140403501c204404000f5030b03520418144a401c00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 932222994 1250 932221744 932221747
    0x1e03030714070c030206072a05040e01090525081b010e0411030a0b0f040f020d0b0d05060403110309041107051507120b0a0302040903020304082506080709050a0902 72
    0x814801007030034514044049468405001400001d40c10036010700803a901220f56645400c071504161200b0354050440d40715100d9032960403c40a01d00102c14021100e08840070400a04041c03c0c0500740c0c0c030100002070031038201c246600000f50b44000040c0c0c1100201c042c0c034081540781e40748145082d0100b0745000b1611981d1030740411541c2c0c0304001e03075146041030340c06101d4204c000120014a0201500a0003001d44480039404d15407100071030030000c264010000d204040c4a820100000d501c07051b0084a1103041520180c09803d241420450341588039000300349507601c5031001c49400c28500302c5058070b40800c00c08502c60396100c0c010159800038241e6029a0780d10180b4085240044440500a0030312042c0200142541c20a6030400c4400316502d0200350916280c3c000341c4950041d030002507016140403c4001410341c0000038000792407400040320307141100040c2c09003032120f0b4400039031a81d0350003003c24000c1511548249800200c10304141a4240c4c4940010b0842c40d0340360840c4100650 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 932224244 1250 932222994 932223001
    0x9090c2c090a082d040308091e040f0b040f0b01020d082508390a091d041a15011119060509100203090c0405091e01050106080f0702060f091e0303 64
    0x1031030b80100b983c0e800720159680c603051447d03503184108c7c0220540c0a200d8110b0990080d00705182000041d800200140700708a080c610041440003000b03140a0980070f140b91400400d00e00e6050320481c0e0284005130003c008e610401750b42260344503001013003641c00c0325500755807400131840c01c4200c0e642102c003911034800c1d0f840c152800d40d01008184800c003002c5aa1094141e050b030003044409192070110001555481c0060002a6031004040e4003681034440264645d2080e8541d01c11b5150080744a191180244140300c45112086c1200392418541c2a444460b4070385198060700c49d03803444400c0c3e0420f4a070301420040b02603025040d0400252000358036072007000a08035080c040c10500c200000011411810200c034032951b03132000e109404d8001c175613450101d8103400b401c01640311005814041c00c2c002074003505101d80602800c4c400c25011079554000308030900a0a1112413103030354558000d2002d0354032401072041c50417001e40603076442d00542a41c0e604100800342500d0b80740c00c00c1d070b0040d40d6906 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 932225494 1250 932224244 932224297
    0x504032114130b06131103100311030d02120313140c03010b030a0c15031419053403060503030c0309030d05070c0b09040f020409090c2c090a08 63
    0x3940109800d02c8002120b4602c0005603500840701d811440640388888492808034000c8000c140c2c18400fa200d2901c08420029040a44480c003010f6900c00c110b44c0702c2042400050541d5a0107240300c0c0e01c0541c0008003a1407013941841c2c0695800714188010003210703070403a15140c400f42041400c9008070f4005585a5071141024018040791910540081c090b840854980703100075903190160725000820000c0614600d07120b50003c2030f4113080d48510400a042180d801917440301c000040600b000e05210010b400540041940384e94282c5904030000412102080e50702d4001d0350210f68410305a5400001c2000c1d03c0410242200b490400001c5070b0710880c8404151501c000900070400b0030804101c2040010784180d042411103220107000d507107411813400010041d008181210805034404607000646501c9500560740d014010480c0c40703952a22000c1c0800300c219020b083c3d454003001558002c4a00d41a011110390010000c1c05a880d50302c03556031201c80540c456140b00c240424900c01c55150300 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 932226744 1250 932225494 932225531
    0x80a02010b0a080d1709010b03071e0617040f022b02031902010e2403040b0a0e0f03160f0605040609031202090a031101020c04060e070e0f031005040321 67
    0x200003e0300200680ba041550007041c0c0061480d41e084c03502080b402181c1c440e4001d421410116400900343e84559031284414028119180400026100728a4000884900038000b07101010b60b10800030459613035a40340c00d800c600d42000c08a80040c0d007482c007410f00d02c100b1001c0c04094440f1450300210601d2074010503140c145100f0500c0307211490903814500503070f0410407400d4483c00a8400140c1c840320404034852581082c4415480900c000041100b00030768003441511840204d4010001102110040c5940d1f859074060800d4680c420004120301c0c2035501d10720b454051003034182070410062070351408142c1d20152000c582d2551211010380406810400040e40141c0b00c2000310709040c0d00d100001d580c403a00c3d100140120b000300c0e070042c001c1d0b4400e001884500c10090402d2000742c0c0c0c0e41c0c1210000c0042102d00f07200080c0e1391140040039240000030000014002001085403044502055000304070242c000c90034403004660f04403089078504079041041442080000d03045a01c0844d14104 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 932227994 1250 932226744 932226749
    0xc1208180105060d1b08030711010314070f030e0705030f010903020114100302151b0c0103060807050d110d2018063f0a05070b040305060f060d080a02010b0a 69
    0x20782d062038100300700c2e500c0d04590034003419000b5003c0d0a4a00d810b144011105100e500000e500d4000005d0200a21030ba03500c040c0c000e0802030385d0030010646450900016280c0903201900003401c6a122188180e100f6040a210099000251020107589000180c5000340350303006014281d45411a1030149a0288513042805010b21851308007880c0410700020704550a000091081d60450020006008800706840702c4580501c503043e0b890015141281d82c2d042c007008000c0c0003900300000404e0800c00403485008440000d80440c081107520384e10150025051615035400c816254000d101081000307410003070400c41d4041241001101100f84030203064008404501c0041c94000c2c0f00311341c4c41c0e01804050f1082c0c4401440203000d5202c808a0142e446040e20403252002414000c07915000403880c0c0507014407840807110340f1595010943e440380994403016060703070086000518445540981c0c0380c5d20500051080d030151071240d40c2c0314001e8000840440060390f485070f40c0351040c100200000d01 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 932229244 1250 932227994 932228041
    0x21c02010204050a030f150903030f050105060f0904050402040b06040b07060b06160f03020a02060409153f0c091e0603021309020103060e070203070203120412030c030c1208 76
    0xb5160628011420000c12031100503c0c0200c41c0407103105214545401c2041402c0e00c410900210240d0305000f400b0f09407901104203007030301d0a000043c55191203070846860300c0d40c3c0e0780300d5414032442804100c002c010081003680c0050700d0b0700015115544203002000540a441615502d40f912070034440b040f034403c080c6050042c10208016440620544414441c0759401034104d2407100c15890100d0030440d180a00035044900801d000c5000c0d4010b4010203000f040031003079420050f5031500d403501450000903404800c410008003008110b1400c003103040100000a00b901c411800550311803422002c50b907c00340e005584e940640003514040100482c016284038802c0c0050341c11070700050504850420f005a0641d5151045011a4040d4100100408a0005c106543d1a0800c0701a45913407245108074440d000b280005014090400103030b0b400d507040900c006c001c0348030540c1c00340c035180d440f07180a60a00541364503110000300e8a21000b4482003e0390381c0c4080034201743d001a000044403d0f4090b9 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 932230494 1250 932229244 932229247
    0xf070305011d0705090406030c050310290114070803070807020303280b0d0506161701060f03270201080a06061202030606042c0c040e0a0f1b021c020102 67
    0x44030b00d40c07105280320b40b8020400d05001a071030380602940c9510800d0511604941042c0c000000c0c4024504000d080700d9080d0151040a401004154100c4048483c0c802a0000c19210030610020341d084407401c42c01c041c180154600401032100900d50807600341124410740001c01c02c4441903010400e030b03401c2042e5000071411400d0007000c2502c81c066244070146805481d2240c0c00e035122558024203001740c03001e82000c01a00c0e140c00c100b03403614412120300c2c0304c00c043c00c01c030244503601c2400302111010418140405590030600220744011070b0521f01410161584100801d00420300d580060f007001e481d800e0001609a880050700c40700e0b000f01103941c0649000410440e140e00030786c3e4080c52a0a5003001030740d0341d4644000400d41e005580042c0c3c80c500d041840660300403001507402e90742c1105010b01c415195103074640b11126100e40c2c06442d00e5100102c011507512100c58200c108562504400440c050305100009004d4040100c04000140c0c4240059115842c94002d50798041110b48000e5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 932231744 1250 932230494 932230499
    0x90b0318160305102004060801090e03031303180302040204080d0e03030a1704230601060210020f180414070906120911091801020a080702100501030b180a0512030f07030501 76
    0x264981801421a0207a1611707104034041c100c1c0625514000e0003040041c542d00c8541f00d14009007445400d0003200c8002c0d28000c02c4110117100003056074850741091207601881c0c0740075681211304400d0003483d00740407145042c0110059840e070000c0d001400e081c070000d00600d0181c25000789002505402240203810070000e500480c0c1d44240f04d0014000300140b9604961181c1ca031111a405001d00000760618481c0c8110302a80300100e01b02e4100c642641c00c55503142c1011034220103c1c4241a00d20520f170904020800c8013242d0f50091140ca002e004000254910403200480e81c2c01400707d45900010301412001d0203815040903008945a803c0078080164641a0391013220403110105075034840d10480000620b024503400d150310100c403d41c4000d544800c081c1c03d01030602d4030103580d0880540100e64040d0041001c1d4842c180c1200d41003040740c429a101c40c150b250480d44c44071400625409441c038a0b01c04150200036009403540040101c40e560719040c0b508500c00704020300010205414103004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 932232994 1250 932231744 932231753
    0x1008040305190e03120a1d0603010905280608010606080f040b090f010606031a040e061518010f050411031005100306030b040c05150a0c1101090b03181603 68
    0x2078500007070540382d40911440003004195800c0411a241c0b95161041c054110340302c4804001920303400e070b01e41c0c071032520b00e400c04803050141812101c01c098101d00c0a00041003142c042d42c020a4100c01c0c0000c2030040c1941c5060120140e00c0100c2809140c10b803182010800e07110244510402050360341707081ea00d075003451400d030030201002a0002e054401810040743c03405005002d03000c90100040c0c005c100c6140d8804015001d001104541c40c0e8900184001c1050350800340035540320390303042e0f201400c0c0c503039281603022240d0140c00d5003d40e005204000003500c101282e01070503003c2d201080381565203a00d01400c02090f50f48000343e203042d0900a1045c00384800010780d50750b05496040752610b14105d4900302c00c42c002c0c00160300c0a003007501c2440070b01003482210002e020644909a03144002070001c08651065445075411080014640609482c04100c0c1e003111803400001c145000841f2a40d184c2407010150410740c0c0400381801c103010240c07281101044002132050151518400c22440d40d01c4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 932234244 1250 932232994 932232997
    0x117090a050c100c0204021e041707120203060a0c050d0906061a070807111311030403020c04061d0408120916090c0807050d09060c02151003080319061a091008040305 73
    0x1c028046d5801140381c00341882107a40c070401251145410315101da540e14001c0821400c0d80c00013590500410380045541e030f140c103500c4080a07070080c1c02800c1540343c008244000745000d0284004006080c0000300c0300c1c503018001c00d020325007d03040201d58a07003854012000da9140c10788070180a1001c1080e04005150401900c0b90260000135407001c40206c0d60200e0400507140c40f54007181890a80c0a80c020b44145016500490180e03080f074104007194410b02c0300700c4445000b0f41e9446030f03404030b4500341215000400f035030003031107080d085040521180c0c0841d061001510b181a00c3e42200d10081c060074002135851000304003502042c0b08641c003208000e01503141c00b0b0481c0e002c220300010019010036194105040031580301030108030a86044070029250700c03036070459100040088011600b4501714402141c20343c3d030860b441c1869525003240502e20022140a0090a5070700c032400000e05e4050014007540242500003400d6451703008100700201c0464009440081c400d80300180008640d0040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 932235494 1250 932234244 932234267
    0x6040303091a0405031204081b0a0b070f0b0a27030e010509010507051b0414010b030c160c1412061611010213091a0a0608150117090a050c10 62
    0x902c200c0e680840307000c020b80c6200701d81101d505446070210190804503000000e004655202d419188103480c40800d412035001e2904c00c80742c0c0302103182024040e02c09200300824581d842002107103407402032580d030340c140c80c2d10031101d0024103551900c0640300d080082107201c0c3d0311640b81401c0401d072540382c0c1e405800c560100c103400d410400d01184182c201d9020f501110501900901215503220011020101e80326043e0702180c00740b424002403a2680c0e240300d80700350580c1c440070850743c1580d940c280403031034507084a001040e800410390071100c040384c80440c0803400b07070a4480e4109403216038502031145460000e0820b01c0f01d40e01c02800c00103000302146540c1c2030990149084134400860104aa0280c05600e20f1640c210b40704001c001005c0c0c00d1540701c50300c807075880d04140080000f00010003050740705610590300441c0c440000640903600038101c0490060301410140780807071070601032060282084486944540c0701070480c100f8460700b0020390b1801941254642580080300900500808141707 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 932236744 1250 932235494 932235509
    0xd140309030327150a0c050c030d0b0f1012050f071e02030d02161b0807170a0b0a0b031507120e070b07050709050a0b09011403101b09050604030309 65
    0x50303c0c90a100f000341d4002910404240b04945980e40c07452070a40c6408005e4400c40c060900d8094a0540e2602900a498040d0010030146042c280704100c10406031529507000d99100c00d400003400c08654551461161404a42da9800071b51140b00c5d0542e4200d80d000381c05440403504034420003c0751680a20703c000c0c2c08245d4040e641d420054803034160322318004c034038102040302c2c00842d6840303c0186503c100341e0514040c01e0b4181c00b2a141c100142500651405241803580010b603051200c502d402d000700c24005591012a030907500c80f43c07901ea1040c5002e842801e502520355001031183e1408101c50041c1100c0c071448002d05040801d0040c1600b089100c410107210b4441da6500c0217440103025000041200c03602140e0b4580e0f00d0b2811646420182c05519586864200420140342d00c6200754414100042d020741220790030200601c4040103c00e11050f410301c2070321a00c032030600e520b0242062031100402c124840c95915000609112601d03000380340a00c070282300c10804039510018180460f0719030b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 932237994 1250 932236744 932236771
    0x3071515290406020c130501030816082731090206090a030503090316050604051e10050310082107022421100e090c0d050d1403090303 59
    0x800c0c01c19402480c820705810280045000240b0360707000314908110701421614401007803c01c0030184102c400c00e0001a01d502002e002c10980c0c030700850048008280184a03503070030031656001d841ca00c1d03121840500100e0300ca01e0140c041508020b0044054603200101010204102007140f903007442111503020f50f40b5807202e2110f000e54507020110b0b103a0050141c00c0341c0446890382400c40d0303070354000d2844a00070320403280311856090003600110259034009043e20321306441e05040045003049c2007441000c5111360500340080d81d0302c20343c211506d0011a01c0c0c29441e483c005442850b4005c46030b10404c1c0e036401c0b040c060f2260b0010561980a02c1c4400c0002d2900d4000d5400480d1303044200312040001d5840d00d480845540d2260340240c07502204000f40700c00c000355140e001990001c03040e204500e042c04201424050303206540310325070303005420b14100c4000080d0320001420031900300c10182c0c0c9035001420412007203507008265641607000d40c20000e285041403c1038542d00e01c0300030000401100c4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 932239244 1250 932237994 932238029
    0x18090e0d05031e0f04030e0a080705010503041401020a0c060b060c150a23191a012a11040c02060c030a020a120f0524060703050c031b03071515 63
    0x41c03254440088030144260700400d1520104c481510a02030350164081050030f980750059182001200302900e0010016100051801c00191031982002c1d0080741c41c0403403000410910b500034801343c990400320707955603941001c2c0c604008080b50708000300d0a0042500700140c42a9407000500c2020294441991000035076490103440300070505841d8030f02040020000d4070b411102004505801b40c00501110001242032828400480b250b082080440c41103203001d1070502e6008040c80e51100d14030300c560401c00300d0072400c0360360080d603a030808460b1808520728022850400c0e00c40c0c0c9000d05050300082c502410000400e0a003800300510070210944c0010300111700a12034800d001c101d40329000140000110300b94944050031080b2131a51044405801c03074200001466040b0341c0940f40907011a251141c180c85c200d0701d030392024042d202c081c4002c000c0e0790855022010f8580c40e00704028040c41c0ca904251500c900381507080480c0300222402c00c8512142c10a074001c42d001191305000c01c2c2420602c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 932240494 1250 932239244 932239261
    0xf1b0501030e1e0307140a140c0904110a05091006090b1e071a07091d062d1201091506182417280f05030708030718090e0d0503 56
    0x800c1090042c440c044500b4103000d406e00000320301c25050300c551640c810440c00c10010942c2c4040603072409501400407408503001c02c85144082000d41c00c042c0c0501c100b03c0d1140003080c005001a1350400302203140800400a41da40b009406c400342000e40c1215150070341c001ca80d020807600d080001480310000261480800c00048000800840300f99181c030b6071440c001d03030080c0040e402ca1144501e1100c040710010b14401010b407000740700d501d00500311850456048001071188004840d0030f0b089481c81042210070ba0b4a07030000c055a01c1030340d0700200c0c40382e80524182641007041c0c111400010f0428030280700c00b4900b07846000c440700c0711490000d00c21104070003005225411402c4a82e50404070980400d0210080203a102d06480071811510f0780c2c801c80303a18070001c0d140e202e80c41e501e54280f165074000080c6200c40c43c5401601580880381049080d858485555005071441400b01e694961046944003184180348010300760141c04004a040343d0440a480b00c03030030483ca10410200000060045 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 932241744 1250 932240494 932240497
    0xf061909050a050a0605030a050709020c100603050a02280302040c12180507060507020105040e0925050418050d08090f1005100e131205070f1b0501030e1e03 69
    0x1440034000c10311a034108091400014003042c1d6000028508006012850303040004503e44e82c907138044010700ba134500c1d04503a000203404c80814015075000e44450400e0500d91800395a000d0f42c01a0b0140a48990901c10043d035045003400b51084a44056600001000d92a605004494050b9404205161400350840b4603400ca0004554083e140c01c03d05104908200d82d081c03503861142c0c0881c2d00307a40d15180185c8890240e00310081c0016020442840005402806190880c83c00c9080710300c41350504071400040e0703108080d005018540b0b024100440e281c0b40c0035007000400c19096801d020401a140e282e1100c007683c078400709220002d00803910b059410440800d0360382069082e1a0f90300200d07003e160103030800b0395100070707503160125010407480d07000c0c81c0d918003c104641c0302c1c400d69052561103108001c0400041400c0c00700074410b03040404d916a20400080c4c4c880c0d9601c0404e007404440880c1c400c80a50042810149002c10025404100082c24070741080d90010806d14820342d0034810b480c5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 932242994 1250 932241744 932241749
    0x1505151302070305160b0601020d0e030c04090804091e050604050420120d0f020105090d0c0f1104050109090303050901110307030b03120a05040e011a09060318010504080d0e060f0619 80
    0x350302e44050401706005420603201d015003000d03400c1d5001c2c2d008800007210110a045090341d0700d90010300071400d5034580b56000c00559813090450504060f603510061086400c0c01658059040341807503820404101c80c4600e0758002c004803010880c500b0507840d80e120030006094003c035841003503080795000741d580c09404045480418115040c0b22410ba070000c03c440031800c0c01001560914020a52221021519105001031075030345400340f4a5507154040d07040b02c100d805640b05a55000d260f50981c540340969800307410780080104001000d441d008080b5040245518416494680ea41001386c0807481100c0c0c03c40c520b480e010521824580000c0d003806d0311041c4e490091240000c0b103110140d00040a08210760560f10030b00a00c0ea60f500e100c0341000b01d11090002c40c9502049180c43c1441c0c0a0042c0d500072441e500715510580c030700c02901c0d084501c1a10305856104001c40d40103078510050007000f150346d042e5000307404281090a4071941541028141d2403060303582c102e8504295400042e030500 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 932244244 1250 932242994 932243017
    0x608160912200a080102180a1421010911120606150a03060e09060402040c0f02030403081c020d0501031b03050309040e0f0616090b0f0a0c02030709091505151302070305 74
    0x540c3d80d034030496217000b9070141200314a844410740c0940403c2c5405440c41c2d04039108040b6a20078883c5680800141113449541c03051b2400e00e206010071880360903c6130b600314510540ca0b440008ac40042003241051007030720450141d5105504110315a12040344034421849540d081a031101d0380318400703801030038842d0030081c40000032404010300401c0000b041c0d80581d000340d8081007404c52460007200c0365885102c0040250340308010400018516a00800300c44451503801d01c0402d40340c40341581680c0c8404a01e000b01a2030b8801441271000045100c140e024894000e018030500c1c0d59282d039141c2c0101401c40f442a40d4510b109190401d003804580200c3d094401a12075034036050045031a004405100040020030f82200410440c00e014211402950000c00c00e0b0304180d11034a00f2030340c906003048100d03014001d030308000442041601400daa45803103444600b0110b81070040c1001100c800802d818903560b5a10426600c94a90703514610300d200400b040503070307104403500381900c1c02c2c4a608402103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 932245494 1250 932244244 932244259
    0x1a0d05030405041103040b060103020403020d0b090c061b060a0606020d0e040f020f120105040b010e040e0a06020409290a050603040311032a281506060816091220 71
    0x1890020040045d442284101013072001034940300011400ca00481c08000d400104062407000800c420014996110078100219a909103100c2d010034280d406c1301418a00b003a4030a08030041001040c00102e6110802d500d0030005640b61038002580c0320380144004043c856007032a840035640740d0350440142070f490101c080d0350382e030150300c15142079521400c0840e0b984003000c0e0004c43c20340f41a00841d20b8505050f522007400b4840e441c20032000f42841010035a4a1080c40e015100103409330001e40b000b0034034510b00041032501141032909004020b016036071000705480929106589806040094420640300d20752a40e480d40b4050310000ca00e507506000501c00858a0070b28066540c0d03107564203014060898242d0440c50003450360b2031540c1c1d4005900500b0310304850041039100000a41c1545c0102141c00780007804111850483c0c50340d4000b500000c0d403c1c0700b00b0a18609001040c1c12040e000d18043c283d03c0d1a221100340442d0714103030014800d103a4041c0c0010560207070000101c1c40c030802000300 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 932246744 1250 932245494 932245511
    0x1020c0106031a0a02031b0f09280b03060a03062f07021804020a03030f03111207140304030f1d060307090302040f020a05030604050a0e07031103060a1a0d0503040504 73
    0x9444880c0360785840390815400c0f40004d41c5400c0b25009490003008007050740d0954911200303407442c03103410988100d02d0420050082801170f60310300504103007808800d40c1101c40b4411b01d4220428000f2280c0010b1001d03903040003801100e40b2100030160407240c20032800a40200100c40c00a180d9491304a150502c2e01e130840d1961144200000a04c0c07aa40308581840c0466443c2c1000310700781c07c040381d011f503004d40e19400800100b0b000f8646110041310307524000170980103049402d142500111004000468140208008250000514070200245240c1da03421490a958000c24042e040c6a40000300300200e000d540040061a04210300036200030015078803441e2410000f0300e000242c1c0b206a200da0f05040c0800400303a014400c940c2281c0c056590305240d40e40b400284030107400041c00030040942c0d5040061440c0d88280f115001540c0f0034030f500d0301400c80100805140050280289001c1450f2040b20005001e145c5c0e1902170161040c0c8942d40040c086050150643c011a03201a40207400c0046a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 932247994 1250 932246744 932246753
    0x2010201180501020d1802060d0c03020405061215010228030c0212060a0b060406020d0521090d030b101b050f01021c150803040501080907030515180c130e01020c010603 74
    0x5000c003070b05901317002c0001e410580c5542000c590520030180d0084000c01c440403000171650401d000e960076a003009440c0aa884002c9459030b07000a01c403481c0201e90000748500a40300c400282c40c0175009100800f501030103540030745510384000141c0c001500644920804041c080d0064003c1e03030b40c0081400d00d01d2040c10030b410381c0701e541c100c50b0040036528008070890145004425242680e640d0b80c020140c900081e002600c07140c3c002e841d0012005d41c5085a081001081281c080c0315200d40c0c8003038910345a031b040014082d102c2d003100e04c81c0b084114411401000c2d40c8440b82c11001d2404201050307803c1c03003030f0800c6418110041d010091340e5000182c0c5041d4203080e8900c1c102488003800303082108441c0d441c0500e401d0700181c095800f190700b0030403041219600c181c0b80c440d00244041e0170780b401c00d0740d00d503542c41c0b50000b003600c2c0c1c2001c02982000c1201076805000b0f003406c0780002c0b10280917510f60000004550000b11480b5800075546c41d14941500c620944c103440407052214000c202e49030b1030703040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 932249244 1250 932247994 932247997
    0x3080f0a0828020906070f030207030302060a14130f020406060216170607050a09320d021f0e0909030c0105011a3018060129070201020118050102 64
    0x801012600d401d0200303030308110078640d054645a80c80c1c40c10000003a001a20710295002c4031400d54441401d00280c000b01d1800d030030420100b4800d40041000910703600c2c02a082810050143d03820924150740b40d0139900080110903071000d0418010355240c6d2181c0b602410114a00f00c0281d081854041c001c94590b4001400301014501140390310682c3e6980e90181c4040c50103010001d03810303009500440c07025400b0b0406042001c9039070038125020303038650030106a0003400d44804515000301e000d060324501822510031190220a5400e035080b5100e44d0049013141244215910081c0e8043c1201030075030740f01d200d100c1c40703d41004004000c3c0d070418100040c0d80b6041021540304551812000050500800c54801c1210201d095482c0c1410940041d040e5510f0000c40c01c000d003425600d40c10500c0b03610345c01c2145c0c4101140f00d03c5d038400180b4140a203107002d005821084039074540f100f514481c2940741c812000d041621516045d9038420600c0106e01400008040c4408004110980000c0007010740 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 932250494 1250 932249244 932249257
    0x50717040b0109060923060a05150901080c09010c0f030504081f05060103050708010e0705131203030c090b161103010204080a030e01020a02130507171f090902220603080f 75
    0xc2c42405150348599500381100d0761185483c02491990a80c071541c032103135206c2c05074000c90040040f80c20030750b5038010a80707207aa0040302004400000a05030019030300120304541251460320101d080112080000c1c0a106030810301900b0076100d4000c5804051042d0200d038041d003404800c0c1d40741c8a103801c0c0c1030800315400c40b44000b070003401d04e80050001d52080c810940303d0740441e0781d0824280d1800c007012081c16005001c140801000b00172540e00c0c81500d5081c03d0051510619156017071589040040848241c41104810001c80c0d10081200c401c610041c0c038450a42410310303e1b034014180c6005039120041c004000c2d059400441d00141c4090b0102d00c821800b40a5110501d0f5210100d0049072203244802d00258402d91a424144102c001c41d40800e502103c2400e018010320b04a5001300c608801c2101d104c250700847c40510070006507020201402031580b0982404101a1940000c203400303410b821641c2c0d01030103000300507420901504510011504010f49903070f00e02c961074640c20180d100c0c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 932251744 1250 932250494 932250509
    0x30c010f11090616030201090b04120813050c10030608070305030304020a1a12070c0506180d140a210213030204110702131805030f030f06030d0e04050717040b01 71
    0x30008045020390211040b08030001c0005182208484c060241520080029000c40d03581e800345800240d60300700c2c4980074600909040c42ca04500c007000a0001000504222040d0030310915900081c10002d61440c0307208044550042d440c05e102c2d400c40082016603c090030034480c50100000f4070001100650141e4000d880c00d40009460b88140650301e60303101920701e0081000c101941850701c01007441038001c45285801220358000c2e88400c0d00c3c0100036528002000c21030001310b00490001c100f07000300541107042c10804813110f1540c001d0503020300e10041052019081840d030b500b6050510440390b00361036507411500d80281840703071086960540030490103a403a250080d01c0e80042d00040e5640300394028003011444c405100e03200060710080d03075036000d01c0c0e003406c02c403100068042c00901500c076003480030075450b8688001030101c2c8105c00b42511340240c2041100d250119803043c203070400800180c601080c180c030780300c2d4111200820100b10b00299405c0c1c400388400c0215800410f0b040700e000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 932252994 1250 932251744 932251751
    0x15060f180306090a0804091e0903032a08010b0c0a1b0305010f0501080303150a0b0d09021e060f033c0609070c0b0a0b04020c03030a1512140f030c010f 66
    0xf00543d003583c5565000014040240500007001100a44e03040b4503568800000c40b040007210288016080d15810b51044001c6601d50300c8002c01c200e003699810b00c2c0036090003583c25950146c00b00107004554180142544407400280d154041082005051a095400f03681c400e241116105149280102d50004841650a1610034182d60000e8003a00d416600100003451640e1200e00d1000414141c50510f1394105c13008030301c00502107544001900960715140c0740865010f51600c10001908002105243e90940780802140103407208010f40302451031000107180e0380e48901c240280d0307009020303e485505110892000b04008000c02d081a0304da00400300c440c00544502040001c0030004880103c001a201100c520100b224a80582c0e00b00c0b80d65040040c0704440d05011405aa1003283d8900300c03a0700c0041400207a110600c504007048100102c00141542031205c01c8a1105c2c5180e4050b064010f10600042404014020521004880e90880b6607038016420709074082c100034a08465514036 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 932254244 1250 932252994 932253001
    0x31e09010504081602010e03030c03040e0f1312180312180e0c1308070311100f0f0f02150103060c0207050303030103112206030f12110615060f180306 66
    0x2014050385025503840101075040c581603409110090101c01c030140d0400018034070b05141520b0a00081080c000058055590f40d4100001034617200405403900903402c201d00e00704034042c0311011110210591010003c00c085110320001c8480100702580051080166603001040021803100c801c400302c21915042c1c480b031848640c0c00e40c80301d01c6100c1e45400c00300c4c0c43d0000700c080d030071100108003018980703106030340082d150303030425107012a160022240980160035001d01032074500810003244002d481c2441e40a440614000c1114440300650000c0c0f01c0035808420070103009115050b82c0207501d0b006007210b580d4905010014151a00071013016018a582c04aa18107001c401c40c1d05807034106400190712a00b06081c01034542c00307500212aa02147c0c0c181d6203410348240201c034000d60113003413216000320760307070a104041080031036040c403c0c0030804038412130300388010038030507070103002480000385141c090804a400ca2044103410002d6680010703401085203001d80382c24050500603802c8490b03664 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 932255494 1250 932254244 932254261
    0x50f0f0f041704030615060216061d0406080f0a021e03120d150303020f0106050117190608161a03060d1401021303080702040b0f13180503031e 63
    0x1402500d00d003628019000000d0045228441d2450340d0744008440710349829640e40f502d41c1241d411442501c0c408510b41010403040e0341c1040400f00d03100318006071106003850308101502026100c850405011341806a1981d03654580e803204004094a4050351400715004083d6030300c849010000303d21452460344449803030b0100c4003001c61a40c00c060004c0070340c011942403024050300510852034a094440501c2c3d00c58000509141c40114400d0b001082d407144016001070a45800d07801c414100440c400d0300b6252003c24501b0507401284c820840f0b034035030704010200720203400d054014419a100307240041c44e42c2482c0a0500c411a4032116400031040c0120312034043c0ea01c4155022584110351314000b10205450b45400045942c10f000014039002c05680c5840300c10350541c1c4180d521403401700b181c100f03500f0680101c0201c008210ba10324500002d500004000900014000100301d640d00c0900031810003242c900041990000d0450383c480c60910084041c40c1c1d800d440b44101150074401090645 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 932256744 1250 932255494 932255521
    0xc0d15051005030703020d05191209140603010603020d09051e0c030f030906031018020c0d0201050c04061202040b030a1d1605091905040b0105010f020a050309151309050f 75
    0xc2d007000300036020319461074007040300c82c0703000c0d900c10344150003001600060900c0c0e82c1034440b072645c8034000c8050180500325002c0d200c8441c6a11060400d111221052480d0352244102e0b4156031036410016210400f840d000801090200e2000b4102d03c500300800a80801c1400750444180c002000c5a144143d400305054075408602c08858040e8414000d00d5204c0c90480040c3d6440000fa42c5a000841d03503d02c692601d0606042440c80c41543c00104011f031454280013042603007445000900141c00d0601d0750b001d0a1060344100380401c00429108800380b401601101d00421020000359101d0410f200312400511050b0246520036803264010691600d01042d02401e941940d9648141d0302c1c58075060085124000f0501d81d110080000c901c03034403000612aa40c0224000d066441043d81840005020303200102110001c1d5489a0448000154004112560b826003910500d40d00c0d4236108804c1842d00403092007942d03a4150900102d00b00c40d01e030b03000520543c1a6441c04500751030743c580b44020b2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 932257994 1250 932256744 932256749
    0x512100f060e091302220504030f0c02030a1502270f03160e0a020705010507020d0e03070e0a0f020702030703141b030a030e06130f0e010501020f07090c020c0d150510 73
    0x800c00501c00100080d0242c6500a942030014014001c06c00d94600303602c4d80d0200c281d103000e203820ba0f80d50502050640c0b001004200d0100c1e4101062a280c036500081c3c1d543c80c3d0303810001d0078a500846404002e003800d030142c070a81d21612b4021501111403840e0b0f82540d00344544400e010782c2c0c030340c02881d09619000950700107400701d1010038003609040041d23203c0c1c214802130050740e00b40d07000c0050100240091180d14420809035015050280e50b004000706406500026a0310985c00b02e10306008200204c030030b9a03040f01203408000f604070019070100019002e01000a5810700400d50008180076060030000f0141c040c440036114004a004201c411043c1e0800465805500501802000901401001c445120300401c01e50901940203080e00030131806422000c1d032803078420001c0041c007092491641c00340c0000d002821984030541c90041d6900b0541c840c0c000000e4030b42e10741248031402442044007a290203024044800c1d03243c1880710017000b8115403e4090f51030840090286503600803c50103 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 932259244 1250 932257994 932257999
    0x6080c1306060f0c050a150f060e070f0e040e030f1e040f030f05070f0b0a030f0c0e22090305030601020c0a0303140f120106210204050904030c030512100f060e 70
    0x40c00201000111341d100d000c240115802d100d10901400494000d80081000c039881e55808034100d51503140b12425100c580c0d01a040d030390703440781c00d00078283c0d0411a1030101ca403542c9414000340496500041c00342405100c80341003404001407107400e50486000502c642c0400d02c213540c0b80d000c1810500c07084c510861190714408050724509000145440720503190320b5000d502140c241d2900d0304140301c0140075940c0320034460300c80000c0c2000c40c030b81c15000e000d01c211100d501c10010071034a41c0010f4017440306903150610030188a4404161450300f10034030502000c454404221118940c50f014000350300c00e40c1c2c140e0161103a800f5945062420324140780940307615954540c04440c0100944880381c108114129a240050250801c0d03115429001402003d460f81c59a141c0305102c24081005031412490040e641d004003c00d001030f072a400e1810b80c0042c0c0c1460002c170140401d080851361801920b510080c152034076403e000f000c40040240c40c0640d0480d41c401555256100e4060b1200d9501c40340094 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 932260494 1250 932259244 932259257
    0x12160806060f0c070510260118050a0b0415060216050f040209010512100f1e1509170a02041812050306060c100b090a141323030301060318050a020f011206080c130606 73
    0x40194180b82c20003904542540004213a58210100080646905413b907042034003603428108100c0d941004000c44041820350261061801c080c082900b05011809aa000f00c1e0002200c207600e03481078007259a00060618090114200702c0d00780c00f08000141716040c524128000c0119003580c0306017400740b600c910302045494061a00702c00901d84000030301600c0c14012900d41c0003c46d00095114400c02c1110140601038842e414410001280d00926941001e40002c4000c1000550a1340302414141802e007031031612a0f488000041d201c0c403c08500c1d5030140902020b9904442094000c0342003141c040b18800455a69900d074039080f150b40f00c18680c001c10b070301800b10b00d012102d80d02d2000c42c10f00844d40c9080d10611000910510004200081d009a00000041141a03414465140303613400f00c994050325008a51030b810355540708024003038415115a850040c0790780c0519108910b6810b051001d00c2519a154030b200c2e00d5003100c594060040c2904019007000101c0341c4181c1e02541c456447d0034 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 932261744 1250 932260494 932260529
    0xc060c1818161e202d0c03190501150905070e0625050c0d08040602060c130303120e01050109020406110c09040b130812160806060f0c0705102601 64
    0xc4981160720b440300c1c0c00e00c244d50059099070090500c00c003141e40038031110040a13104164190100d04614182a201640003032842d074000f66000320724042c034103140075903007218900b44c4d0810744e0040111050307015181030a03200020b007a04813904041e01c00d40c05a25080070640030002401810720609070341c114ac044044000040c801c50098034008401e010f94104d03011503620f100441c0324031080740420703650034401140420145034100440e0741d0040a048213507081c070404414800c4190300038040201072081c4080d20110701c050683c4450811000c110013400300d9650780450b20020f40c8940030301d40024010800d600341207000000e0707c20710004003030100140e559694807030921201016080c03920702c40a040401e800304007044080d1080407142104407103a42060002d000c1c4200e40311011034280a040005c0103401d90b501c5040c0c0c1d02c4000100301656841c85620a01030800a898102a0b800198001d4030f04100340d110000224003248901007401800080c502e80003401401d102c2c00302000718002e0302 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 932262994 1250 932261744 932261747
    0xe010e0109060818072c011502060406050c07050a0803151c0308090a06020a09170d1e1101020f07020108130b1302010e1002160b0c060c1818161e 64
    0x2c2c0d480c50120074007030360415604d0f04151b00c0512020615071191001e021009142c0d180d04035603050060107140804842c8a402040c0651140801803000e058599030f1000900100110001c403119503500400756000c902d05868507440503001584c090300c419000241d000801e060074299a444c0d40124004d00c048020a5502101c0c4614000c01456072409a900034100041190014001103029920b468851074144000c040311a81340d403d4407652580991450103205400890752030b03501003d00c02c82200203d5510342a1440e032540c0b1200d00c1c0b00d600c0005e0940700c1d4002c41c0b001d00640c2d80300b6a0740c809180c0380d0710b1092015001744080981070406035800320320b41200080307004e03081c0e61041c1861541a40e80400080d03006007403030018000b503003002024680b60700e01c05083c50040c00c50042e1050803d03031000300e8182d5070040104403402d6080c1c00241e040c0c080d00046e004601c3c07904010003075000c041001c403851180682c01c0e40c0c0141c00030780700228003c900d4000c90641380c1e032070748a004840300e80516840 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 932264244 1250 932262994 932263021
    0x1014060919210204110a0e010c0809121b030c030723090109051f26010f020f0414031b061303021c150b09060d060b0d030e010e01090608 60
    0x4441ca035601c01000040741080300744401641e078075035469540200103074018441507500503104041003038801c0014580c129080303120307148400b0080c41c001c83c0140e0240b400441d1481010902944480203041c26588040d000410b8585400c5140d10052450310f81c000740b41c3c0c0c4100c460f1401d50303d6040803c0910603840a076520f4000540c9064404200502c0100454110365080c3c000b4106207440c0d03810400300342d841c584d80c00c0306240504050242a0700e040120740f1800f0980656402d00e4044000c081c8881200750012910740e646c1003030865890f03000d000c0c2d14400e9842481100659a0800261840d610b408602061101c408190580480100c9020462207600021918011046d4520040056241c04505080c2d4800c2041c2c1182e0441c046d0400c0821140c4200e282403a2500f000f404902d50b440b00090503802c10b80940e084000c49c0c0d4140b6029024007503500000b908400481850820b0503405880288900b10a880300854244144011210700c26680110004200f45a01042d1805245074 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 932265494 1250 932264244 932264269
    0x40308031803040537030b06060d02090307090c0f030504080d020c030c3304050304050f03030705011103040b0901020c0c13140103060f05280504030e090f10140609 72
    0xc00b41c0345400c0d11040095400c036400f040c4401003801c007200c00f60710481c8a40e206000340b0381c9034812150044c5569038100e480507000b42014094440494804285213058056a100c400006c06440000da103581c080c1e001040c3c812030744c2000a2203034480000445c042d108a41c007881c0c001c2e06980c9001a062407060280d8061030354102580300410105044140c14400600122441070030058841040e103c02d080c0d0340b510441c8036000c1400c2109010000f0400000c5600b140c0b815502c0f100d00b00704540c000381c10f41c0600f1202614650070011075081681048000710722452180d0445003540d10740c2c03501035080b40038007400714200da400751040070000e01d0005520603103011071a2000c030344408080c2007208095001e0344202c030f41603141d0102e6060f00c007440c021f080d480b40d0000001485165542c201d0410402100c1e545055640d0700d41c0071401f0f01d84100c1010a0511020b04201c200c0d084c40000018041800c480b0200100d07850b0070b0208042c954819078005d44d100007401542802100400c01c0410311200 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 932266744 1250 932265494 932265541
    0xc3b0f0f04030c060b150a0305190e060a0b06040308030a0608161224020f0c1e03040308071514190e072304061d0106080f040b102601060b04030803 65
    0x3541c03104d9400c0c6a40000f407c282d0316994010440b030500194182c4034258240c13444013454240b105c012a03000002032225030200c00c0714000f14490f030307100d004500740c1e116a400240c08240000100891041d441d00f15400312440c00040f90480848040b9402c0e509486000c0c2c4040000501d404001260700001852040f00072007407504901c0502103e000100c3c1d0200b00c0d12010400d0108118103581c0040c071488801030381c410340c0d610490405415807600c91140d400010301c40a004502c2105201c01002080301d16005a2005c003c0700c0511000c401000d4004c4500841d074402824464a6055207030240003980d056120041856900b4444044450036240c1052011840240540340e1266200e02944c0010b1260307100c41c04010340038039001c0c414560160400d070140505c010030300c01507108401245505c2504042220007944848842c00745202c40e5a01414034070222001185445041c91803000c1001d000700000c0103107c0e550109100140102e11000e041800c003440007564002c1c0310002c02d0741940e0300 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 932267994 1250 932266744 932266759
    0xe070507050c060a030e060903280201020705030a080a1a030705130f05041a010b09010804060e010b040528270201021c0c15090c3b0f0f04030c060b 65
    0xb034a011640a4021a04d80000203440d880325118258082c4140c0e034010403020080c41c034002502c00103150881d44180a42c0a12203004020443c6520030740c1514130b40c0b03a01c5000d03242c0d074514091009041480946483c241d80c1d1a00040040c4004982e540048100b0050041c24005180904125500c1700301104641841e031504079100c41e40000c4d1059501ca1407043c890210b002c00d01c0e015648203040140c21010851104004500c003582c2c03c1100c907544240d0110000c00c041c0005101140508502500590050b0400052082903078594080c0d282d01000c402c4000d00280d003202e03c03201a00c07841c03a424a21840307248003948055a01240402041b401801140d4121031740070505d03c0403440c0068007400245041582d4010010024801e00742007041c0c0f0000c0c06815056141d42001341d03042e2140b48000000c035522403a800102c103140104960203800d11051000d2110b11000403000d089072038018042014001840721039200c03c00303900030342d015981c2d200740404565644c2c00174291410603a0707200d03c9 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 932269244 1250 932267994 932268013
    0x1080a1109060705010c020f06010843060e0f060306040914032205010305090c10021e01140609101403030d020d1406030c030d1b140307120305010e07050705 69
    0xb1658010b00303142d4441d4000091064281c1e200a0519060075400041508018010013109000160b0044140c084158100408440c0c84040d80e24401c0f0318192120070700400c940d01e540c20404000a01100d030781d9140c40c91040300c01420010b2090200d00c1140d400141440402c4007420f0076400fa000030343c80741a842c07500041010f150342c0307981c1002110050010146040e58002d8041c1c61090700100400e0900780a43d0900840d260703299410001000d000e1024110740c07003061407003004003280e40e0500f01001c44451000b0000700740a003042c500c0382eaa0500c200710105006050a00f00a48100459007440c0070b0303141000c0ca4141755210300e801072549403001340049561806a4170090041000742c01000880a0400d42000200b40000b00458400d030030003500140c850302d010031008541c04507403410500740d00502003003a0b180740c03031000064804094500d08603461000040189030381750140c210400e852000c04000c5064030024000e441540e4118008141c0e850300410103403c20511560540b808000e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 932270494 1250 932269244 932269249
    0x20706030207110a0b0406030b042c0703060c0207030512090d021002030f040e090d02010507021b04060b0a090e0a02130902160204090501150602030c0642100e01080a1109 75
    0x741c0340c010405d00e0400003002c11030302d0340500c2045000e50040e5002e000000b40750010103950040c1d10f00d86241054400000386a5010500c000300155034014810030188401181c02540c03013a6070300044480d0310840100740b000388224003e0340c4070910010300d8041244a60b43c2408650302c902030a01003903100500004c9102880708020b0310203411040118002c6240c000c540611b40301c1c0120800055903d004c0901541075404540c50345200146045445480c03444000b0600a003400e40c0900085c2d0400300c3c800d0007a40e400711052007280c84c5420701e0111030316082000c400700c0c851448041000314600c0405c00500f4400e4001d41049603005840c40408051f50300400c0c280c1e8080c060444403650742e1030411b907000c400404d400014000c280700440c00e00d0340040b61155544000340c80400743ca0030b04005401c070120031171100d480161002c20030006101d580142c003c00714003080e80240c81595070706103c2000c0e41c81011007403081c2034140e40d80501526a442441c00a00d100a81d440070000d042041c0310254 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 932271744 1250 932270494 932270509
    0x6060a050f01090b03150f190306110c031b061b120a0608011a01021c141b031b0606010e09040b09031308060406063f152a02070603020711 61
    0x5901c110800304086c4190010410304640c281000c610070494030990003403201e00800250140d0b40c2c4100c0015076921180440341190140c41d10780f20040c880020010345402080d80c01d41c2ca850442c0b0110340050304d80004143c00c01130040c1000d50820b4052042c2380304d21504012040d040114013000207201903e500c969030a40f4500c24032850300050103603880e012541d0401c101002e0f5000f400d200e0b9403081903d14000d041001c40512840d000001060140d101e070709447c0f00c21412032000c801c0b29130700c00440541070790071540c1500c8420f20f4069030002401e02d50213000f000110740401000710000e941c8565a407031010001800f106460b1005103c00b071485c103107001d649800340a00800031301d40e030301c5c0c50324101007964032a800c2180a11010a041c3c100041c000125580c80d0301c25955040d507034a0146440c0a00140c541e0307015049980c1e41c049844000b07070b0341c1e118104800e20a5800442c80028011a80026110311161401688024002c00180f4400e80c06081624803c0c035403040410403110019140 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 932272994 1250 932271744 932271751
    0x30f03100f060c123b1c0c060302040608070804060e19050c060f0f0304030c171c0c0203220504020408012403080403110105070501092306060a050f01090b03 69
    0x11894101440c400d024070460a43c1c00b03a04135140440042501900c1081c00e100199000c20079481241303036500711500541d66004c20220003800b2882160460312113107040035900b1505503007000300c40f040810b545109000300c5040e210b03180c031740240c15182c401088402480041c01500c0041e61f414a802c50031106206804040e0181400764085032020305149080030860304c1c2151240400300919001040b030941910280301204030305079120340c1c0d03030304003694040c6092000800106000c2d0b40d5500c0c5462030400741030745441030b0340d40b100e400c0c0e103441d040c80840d810455414050381c01401030440076449102052058115404680c14031540e440c0850141c2c0c0007508580c040d651120046a07030036500c02c2c4a0000c010808142091491030750301d40550fa8030441c0800703000540310402007a45a4080d5040b00d4107030364000700800c211801c1e81003180e00d099414910f03400d8003251060900c0220310000343c182c002d100c000c0c0002485442c0c24100100000c00c0d040c402d052150010340001d0003140c08016611 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 932274244 1250 932272994 932272997
    0x27030703030f030e1f0e100507170c0304030909051009020309060405010c1b11010c0519030f0c0b0f06010201091e0b010501031b0e0102070902070305040e090c03030f03100f06 77
    0x3203203540369001d01030724802e00503681150701c515520083c0079080c400e0b07072000c88005103000a6405429040c82d040c06400c001001490303041800380301d20326500c000003c0c240ac2030b981560040340c4800c0030801c80c074071054902038000f82441c0820b01c00600c0c151b104030303040940c0541d0031060a9450782100b090b038004603807440c1e098101d02d08002c2031000038021200074a04600c0c0c101c01c0504490400c0307880000c00351000d402c80c500d5030400341250340030319044450250403208507507030445094805030200c40c412104400080c00c10340b0340c111170b5002c2d030005030409911480100c0c5e01c0e40c6000f0481c514940c0108194119902c41d42c9032004150b0005040e00640e45c40315046400403003d01309920b030404181e00445c105440c0c980700c501100b8564070002a114114580005420b0340080100d00d082580e40082010b40d1000030042d00300f41c1c000300200112640c41801040c5a900c01c0c001548410880340c1d03290300364004103c0c544005154034003c1d41e0020324000c115240c4d41d15038144c94885200d40d0011070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 932275494 1250 932274244 932274257
    0xe010f091b06050903030a0302031b16141f02090d1b0303020d08040f0209070c2a09020903120a090b0f0a02010e06070e01230307091d0105062703070303 67
    0x1008180c00001e0140515040c110702e48510b10010a56038814601d02c0410541d0100200f01d1400c5034001d0a00046a080113168684525081008528a58000c111040850325640d40f01140001c264a0480c890301040a030388203100d081c100000e54001c0034042e0344141c00c5190400016a40311000c038050030406420400f5030f080d032401901d13001d2114141d405000d01c000030070000030700c504100c0f0318495058503040b000c1e856541c400d80310405100030003001340c4c20b02d510144441c0c041c483c1388007003108010318a4031055a00c0b85603100b01e100b461448c13034164124640101c0241010710081c061020b00d89041007481d55100540b05480d04026003c0501140010304124141d509002c0c0c0140d496014010740550709280602800d1a50803080c00ca05216800c00c4800154600c1107402010404906803030b95203241255001b402c05506005403221040000c07804111103807802000b0b4180c1d4009449145030154858248084611a20080c080e210b03400d010802262414441603000303621a44400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 932276744 1250 932275494 932275523
    0x6122a020c011205100320210c06040803040306050606040b0f07200f040c0e0a0e0609010f0303020c010503191e1a0a03140106050a0e01032d02040e010f09 68
    0x140065030303c83d80e1428690910b0184410400708000010031640d210035075034280d1804032401c20400c4000c480003a401012035008541095058105c0020321b0000c0042c2d401140003c0304001c1c1c14052401032240c00d0307006110600014100394081034000d080100710742d0a01c1d40d03e100c1940c11b0b0b40040301c4100300b401c2c0451024208803024108a101c01c80c0c6012203280b440d031040c04074824454030766502d03110700c1e10b500e5581f20040c09081c01d440262030207170074440d0303030f94840d4400d00b00c0d142c0698410380140c0260b00001460044440f2a40070f89515134042c00300440389c0001110190409410320700659450002400310413014420b1680080020880c0d0754082442440b1a04441110b0380980c100340c800c5c51542440c1d0740c0da895540640b0b50100c444c82c401c1207074a8440b80140310b560001900620191404074049000c101600c2c1203074400c10b400c0480340d6010484004003481d00384010145000041c4c41001480c083d0008440440d01e100001002034450060b501559880c00701a207242e000740010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 932277994 1250 932276744 932276747
    0xa060204140409020d12030605041d0616020a03080405070e0414100c050f1606050c030901050702150103080901020f16080c030601060507150b0d03050d140106122a020c01 75
    0x401184000445042000c88044c0d004910a091144402849180b14012400d0203070300a5214002a08019100b0003640d0041c180f8030501d10b102010501c0240705880004080090741c000303800041c0c0c41f41d4040d0021103034598041d60005d1001c0c0044495001e147c0c0040313001c1c41641500d42c883d40c0039400c14050180302400190524507072140c0d445200c3d007080344002c0c500381c0110844039a210141d02076030707665080d8503145030141c0e001e060040c0458104020720a03407941c118091400746074080f008000035165100103a03645c0c14441180704039414850010804151420060f0840010600580765881e4807a501b250629090380452840010f0000081c00144000c0001e8040c01c82d0940081199504000380039045000d41c0784014060007102c862290420b403141c001040240010709040d0410b4101d29003e00941c0099078501c162a14042c5050000d1540040c082c1c100c0b006512858003100300302c10131001a06603071800d02c2010144440702c2c05440480102c41507543d0256020b0410100941d00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 932279244 1250 932277994 932278019
    0x907080a140105010801060e0103060b13180209100309020d0b010f1505210601090308190e0402031b0a02190c08070602030a1d0f04050f2710020903010b030a060204 72
    0xe4216001d51048014803c50744c00c21302c2c6905550483c00c103841c100c210000100e002c6d111075041201141c40104507001d40c030101d001c6042c01d49941c001401844a0040c941c0002c81c0100d0300e0b280d40c4403030454022a40741e4000d40c000c0d800305002401c800000034150302d034040e0003c4280c0c07143c1c20054890104014060003c44841c49440007480e026242890411103c0c000c110050714100c0002c08040c0031a001e68025142c08000315403000105854403141ea04503070703000780840c0200000c6145400ea40801d80380a10840b0701c01c41e0140c3c40c6c0d8480031807144840e001740d0070040340d5400358402c441825000b803c007603402c0400d03244281c442d0307200a810081000d05005865100c001035600c103000072002c083d040a00011a0302c020b4502c040e46c4840480050010040f6120540d00140b60405001c0f100304000c0030181319117900d00074000000995074001c94050314410080c0401d4000c22007125040c0740d01c0c0c000705184c0c1d00007070000c078070080a0300000341070800c1c140003180c000d640060104019094040d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 932280494 1250 932279244 932279261
    0x10807030b19140d0b04021c170d050a0c08070815120619050403080f06040603060c020a020307081b0103021809011710091112070e01080a03090506041a0705010b0907080a 75
    0x104d0b21215245295103038100180c0241000740b185e140f03440c0085c810f080e501504462690010040c075510380c0c41400c2d61055900000181c814a400c110000d006c01019000c1d114400909030303285000380c1d85404c01210b00c0d800103480030b041c0022440d488603c1e80d44d1420400002c003213241c003034015410080070070035200151211411003281000100000b10390080045a0f00404225400078956582000280185655000213040b24600340d510061188d0000ba0000381902c03e80c00c6550075130700e80c40791690701c8400d148110300410002c80c0303003243e551084c0c02034030741e5940c1c00c12108060b031035160001c0c3d040b8030260007146440d80103500303666182c4010002241e00301c1c000481040495016201d4110046411425074000c9244081d030302c0218900b00128401850341c040000c0c02561207954294407501d8035a030a0300004c1c91300784081401c1c9040f07421142255005941c141d8800540c495581c550b4000c61419070342c5550b1035031086607d40310704803140c0c86030440355034030000e80c50071006107012195141d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 932281744 1250 932280494 932280499
    0x9030105010e090c0d0f0b1501021006150e0109030210020102030403080c07120813060c0504080d090b090d020d0b01120c2c0a271a0c09010807030b1914 67
    0x400c20b1142003d40810f0a40048800307031005c000442150819103019964008020000640c14040052441014404ca10810001d90076201041241202c507000d50340d00d4081e02a0700082d1304505c0310440d002d09400c0140c1001030500c0076102e07035250009040084610f00d1140540d400104000403d40d02c0000302d5484004000711030308085654490318003400c101c50000051000d114003207100751160300c0012155030790200c401c2c003611000003c001e10f150483d1185480390300c101e400d0940410702900494058500304160142810a01420412404c14950083e41c02c0460a118030002c1244d48110a0203043c1d00d021000100c84103203441c1070720800360f078881ea103540d482880080302c0c0040b650001448901040c504c14840c0c0318028000c009064012144500010b103400d5440700060703000020540d5401442050f40204070b0b510041541a03040712410b4482d4010007007030110350700444540390402002d140020740550100702181820704141c0b4140c0300c00400910801c00f4220340070b040605001c05 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 932282994 1250 932281744 932281769
    0x1050108100b0d18140706030f02072d051c0914090f0402040e0a14071e0b0a0207170f0105090d140f09060307050d0c0509060403081b120903010501 65
    0x410407034804034042c0a210748100c035150001840c818a0132141e94100030703044015200e00d036250400142d074603100c610815012a0615511240b842d0f0140f00f5140c0c00e0350070400902c00201401c034503005051407091000840080141c1840129408000d94092110094602d0080d0050749001501d40c60b1a40e000d02031705a2900c0c0340100589079a4007241d0000401d800e400b246444d5440090b015280c88050058644030781519682800a0001104800050382096604c05078646c10f0314044a03192490440d0b0320080003200300242500c40001342044021031050b20100b0b61030303e042100c00a003401c1a922031744d2284c4540e00000f50280304031a04240c0000c014141d000303001002030308085196a0754040c40c0008034000410301c0c920001c84014010082020b6900d1418220192454002d02d1140c0200303482d04e400d003900306000304101c030403c0500074040c070300b458076503a5001d00030b038050810a08400c20030000c030015201c00b00112901099249005034448080700c3c241400c452050b0300040d1707402003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 932284244 1250 932282994 932282999
    0x60608180105190b0301110a020a060b09041106071506060504091a010207140a0f030f050d0207030f020925080106111f05130c030c03020a0503030c100c11010906050105010810 77
    0x1070000200c000e8841c3e440d021070581c04284c00a0300500319011b11001c90280002c03403d1989501060f04611203100d0f03071040003403039405800e0040342c0a080710010010310b006202000301d03242410191644620075070269003080220307aa150207039112503100401149001c141071190301c0c00c500400700c1004400c0021402480441c0000b560398a052094582c201e010b102551309a8451100da0000382544a4491010715564940030303071402c6035038070180c0d0140161b00c1902800391001c103c00003100d4102042c8070892050360200300907424080c1480320a441c0f064400798031120b0709806240b2040312500c5145080d80b5041e405030a000c92442c441d40075410014080d440701d40f92241c03400342188100c0c0005003654404040346203a440034800501110303c1003a000081190840325003095910940d5000300d45036440e401d16942c2e01174559004110b41005080719501507050b800001640c07901c1c6002503044c0a540d00382c0d0300b1519520400c2e1f030941c2c0ca5100620295802c045099008202655520034507071 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 932285494 1250 932284244 932284261
    0x10303080a09032001021b030c191203051306140709091122080a05010e160e040f0302280210020a0f14161401080a0209030d050c010f060608180105 65
    0x101d94000140c9642c591341100e24040c07a095054a6240c00b085140d0100c5445d8142c686030f1303a0b005095103c00030b1154607901c0c0c4030307002011042c1040c01d138003401480309400e400c2c20580190200414200e0320004042011002c16018000c0d040b01124401800742d007420204001000829680c1000e204d6904150a418803e810304c0b080b40c4249244401c00e0040060001c44c400c1a580d66500c00d90302845800e4810b41446010740c02030b03940010307450407240900c1c801e03c603109400341c2d103100c1d83d118028400c00003808650b004c560200c0461091040d2140c00002c0c04401d0340c000c40d03400c030002d1114540e03890501141003d0a00c20b860000c240000c0c400a062541d50451500b84004020141c186480c20700404120812080c00e001c0710420300c41a0442e290350340104c000502c460076500169084000c21200c043e14400c03184001c00c081c1c040c00100c01880015140c0d90f00003040d0400e20766980c01c200d212307a6090301c200400381c00565141100c0d4201400c488080302ea40495200c55645080103002424 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 932286744 1250 932285494 932285507
    0x12050909100503031204050309030f03040e01080c0907050c0c060a0909060504020412140a080d05091e030a0c05030d06090b100314070e01110a060b03120c0c0603060a120803010303080a0903 83
    0xd00000c1d000d43c01e156211f190241c11400b9144003039030107101d600c1c9100903000000c400740080e40d80c3c09403c44100d0381d0707400030f00ba034450f0348100c001d4000320010f011601c1d041c0310f40020003142950100303e40c8080c03c00c1000c110103a001804000005900f81c90a2150b0710203806182c0080c08122019410b0504040c058824034007800f030000c0c001000c1d0b11200c1c0e11102d00f444210101c40d000b801941d101e0282030a05000340070100c6010703509019040900540f4101c8d01058110034045500850900b181c00300d040d21100784450040c1c5417444140625500b080b204d0141c1d0002d05000d620206038090114140f1101d0a900354021040c94244441e00b000501a03040095114801e8940050f000d81030782c0c0141c400070b00184246445014599800b014842e01c0d410100e002c0380c0540848280e0310f04020201002e018291054000e504840c10746030151501d00c01075030b04007200401d12258035a48d200d01989125401804685580700440100189034000c0700550780225451018000441c2942c1c00030500d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 932287994 1250 932286744 932286757
    0x1d0c0a091b1b05070306091202010e1f02040506160506060a06080c0a0c02090a051b090603042022060506160f031b03110c150a080703091205090910050303 68
    0x20003070180005038020b580c607529009100d8005060ba030742c25071a401d024002d0000a802545d203800d0300c0d5000c07440c480c8144201840041c01c580a040844403011144641a1880020380702c41ca80a006c003188030340d1035000400700b003040700c0d44800d050a21442c000c1d060400060116100c1e0140c424200030454000341410390091040c840340745e9588041005032410501a000039402c00d0a600400c031500420740c1c0a5801500200c940001006001c20390502c01d200d15204c9030307000001880130600107030f1480703070411800c0c2c2515640c49801142c203002c41c584610b80c40d00504100c02c0c9940b8590b0302c41440c030078100034210a4540034078005032404903c1030141054001007101020029000515202c0d500b40c42c4d81c0c190b28800000d07000300604006015880075240b1004601858242090f1403801403800d01304004548007090070b26681407421703a195040107000780141a01d4502c407100040d013400c402c6032079420740d0321000d84a43d0800300340705030600000c0c00300442030070b58602880305503800002e9615 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 932289244 1250 932287994 932287997
    0xa060e0c0918010204030c0902090f060c100f0e16030308090321060123121501170709080a03050307020d02070e0606070309030501060f170c0f01050309011d0c0a091b 73
    0x4900002c030203240203106030f510190900403214000300c0c08084540017440784a00494603021510400001c0241ca4441e04042480a80c40004854142640c5422802c2500c500c01c0001425104946415003000c203503015424015482500500800d504901c046402001030707401982810110072442c505000700305200c01002d02240001042da0784507418210200c01080c10201d081d8901100da115140c01a030400c0301070709108400985080740340104a400c1020594400090341e41c81c00395202c40000c05010b80301040314107100400c0c0c026007005444a000c0c4265141d985e285000b44009060501103450801150441c0d4001c00c046018003200715000700f812213901d6039030344161074252050b0801d640010540e500b0100d0018010300380c04049002c0b61031120100500300044203c664881c00c803c41c0080e4045940b45090030035521800c041d55100c4821030000504002e48a4100107940c80d102003101d0a500c50b0005407414280f01002d2002001120300c140240404030a0100285500c4c021590 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 932290494 1250 932289244 932289271
    0x70819081e0a021e19030b1c0c08010905070e06030c01120c090503070806041719140702090414070f1409060103110f070c14100e041d0a060e0c09 64
    0xa00040b03095040301d2000014001c1c6684007103885154402e20303044044c800f01c2501d00d1401c0503d01901078020b08800800c001c0403030310307140e402c41c42d11a80c2041b66101900e9661107810040740c0100248241c92005014a0090149a15000440a844900420030343c00303900405988695640c0120300c0e4555040c05400228100d140410105da04003d5a4440d6501d4416018001a03010300450701c03502031030041c805028280d05ca514507020610444541786104421200b491103c3c80c0b0810b404042900419219440c000301500000e14800041d182076500341a0320080030016001004400300800e84034031000d8500e0724229030031003841c8244401e58001c04961002030902e030312a900c20728140002d44d800d01d0302c600070a6a90402a00510300c1151230f5100380c1000310700c114001c100300c000b0310030050008410000d41d500803504800c1881c0c449410545802c0e802d40c02c00ca071050b10204080180e0001c0a03141c405040282c1647c0f011186010305401600040b81140c0342c03030124542c0010101e2822 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 932291744 1250 932290494 932290501
    0x901020c040f180c08060c0702031c121d06090f0a030e0604080607230f090d02040b0303030c0c1006030201091e0806010b090f0a180902060c03070819081e 68
    0x164058000c101c1c41118030030565443d001002421544c800c00c2d00d11690403a2610390311070101d820107120303a18010b0350540c04401913210725806100c400d040039072507241200100c186130f082e07081030340c2c010b08480707489a601c1083e003a00b4a404200303581e401140c41004000c14002c2c0d10130141c03100304015011341000b42d1000c5d403002d0303502c95030b00301c034010f101802c00c03120b040c0f50252004103010a101784174903001c000340c0b00482e4150f290344e00b514984142409603d103000140320030442403030b02d50f0300100d070016114141056030340e40510203948944810504103681d41124000c26041c45106045043c202e40b0305442800581d80c400c10403401e441246902d41e01c10116072000b103104065503401440d030f80c400e240c004601b8007220720240510745000e580440440328081c0400014844900603040328002284600842e80816003003403441c10300140c002c51500010a4209040d5800000c0540c0c3c090b03c00108150090420050311400b41a58a440031050030103555054005440c90782007040000b549010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 932292994 1250 932291744 932291771
    0xe13020f0603040c060f1815110a29040804051512091b090405060a0209040e100218100806040908160b040201120c02060c0f12010306091101050901020c04 68
    0x260038580001c15198407441c0a190116180c080e900950001850702e4070300e44000c0e0300601d480a91010034030122102c03d4103100c114409040c84081c4501000031240032070408003000e001c55101c560046480c100c81c000320078910703134100c1c0a2141800748004a07004200c0032070f0551017503a090fa24115210306a281c900403607522140680c80000b0014800703d41844200d000014015111184441441056a00801c00c101005100303c0380540103401680004018587c103900905800400800000351102c1200520346030142040540380c180742c4c002690306030024560107120301140e0841e00c00c0c0580200c0c01000f024520086d1096004684034005d00c42004034003020741e1210741c0d00c1200411003001074141600b80f0f0344241e07030a0f0f0104442045107410381394140103000200f03e041d0020b20050710352141c40c01041e4095541007600103003e000c0c444c540000c041c07009000b1401174201003442803040c240341044e0151103119905201c0c04001d91002660045080317042500700303e40010303120034403100 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 932294244 1250 932292994 932293009
    0x703051911060f0406091a0a030c20070918020d06020306061e0304030f02030c0a030c080714100b01030603031d1201050a090303060e010f0506070309240e0a0e1302 72
    0x600d42c01003021429520309902c06000c0d1003201d046503039410034079584000200e240395200f8400180d02c030301045452216030182d00100072030707141c2e441d004d02210307103040516009402085407074003203030080c40080000e08801c0c040c0a489014200c052101040164001902c180700300000424840c0c0210010700c1e507549800a0b5600d501400786140c526261801c017601195004943c1140801c4007601c25800700c0b8400400d460300e604100b0002c10035030f061500c040d510008584003c40704c1304401c21030b000000e0345044039100e1700240070005000300c2c1d00c030750503030000d8514408086040614003402007021a0740810720707204260f003400f40c0360240c030119804200141c8110781e04c20015800d080902038540c0c0c941c0c0c031140c1858003035030702004030300d44480c40705808010a01c59007002200c503503070600c0203103070000042c05541d11a083c0002440d030303200c4881c01101700d100b4000e0704901e0402d848884103500710003000802c1e070048424402503814070108004e03851014002d841d580c3c56070301c1107104544a804 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 932295494 1250 932294244 932294273
    0x27060809030d06030606210b19022502240a0305061305040302070524040b0c0a14060a050a18080c030f07080301050a0b1207050702180a050405070807030519 69
    0x400c10b000090310707824000c020701418131950040c841c800403c00140344007d00010b11856018442e22800e440d1203805036203c0d44004155180254208103d41500c04003614503540b9048025111056101500400144907150204003149aa100b00141891300c1000c08581c4514181d040000f0241c454130041520b1100c51a001100c1c0384c6002c082c8000c0c1600007039004200d0f00122044040310b00401e9401607508180d2030000780c644414441132200d4081a00545000108001290394440c01c81c0ca072072a030051a038940e80c2e01c0b0f800c00c806000c040142402550b6000441c0b80301440b6078511070b000640a035052003400740000344045445040300d0818412116240090f80c140341e11145ca5044c0407140c0c0d802803052501c1119034643c006420541d00060324107a03c407407141080d0641d038444080e505507203d220120390005000c07009002a80700707200042e001c1e07200f1140004040ca4186041c0349048070030303002452141d00c501e104000003000010344140019440701090404c2005242c40c802c19100d84 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 932296744 1250 932295494 932295517
    0x1207140d05090c1906080c0f0c1c02060a0504050c130e010c08060f04180303020903160b07050c0a0f0302150f161e1119051e012706080903 61
    0xc070901080c0780e0300050601020303200b00c0d02040a00501070240c603012100d4404c0303e01186049000814500f0580007401c850036610061510b004168901075060100642041c0c56611000c46508035040d410808280d00c084080810469401d02c1c1d1265550350100e011250320800c00840da03684502801d42102d00740c00e10302002031007808103440c00540081004c0702e21502802921441d160180303030901540000405002e82e8044550198804802a52203200c160303400d8030440e18070b05d05c02e901e40307803d00008003002011a900c51516203441400c001042d00010320071110740c0c4041c4145078a41ca03803c800c59038121002006900c010048190500441d0740741140700d0700c0440c0e40c1c282c1c00b03030004905151510554081203c03005041040d01d2000840030090020a607038480c81c5100d080c110007144501318010b07841c8106c9607555002401300e040402221400c092000b004403c0d07560031078158041021031000c24885554007220380c2004c410944a80c02c1040748000101c1e17444a000d2046a600c0c2200 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 932297994 1250 932296744 932296751
    0x6030c181e01080f040c2c040803040312110307030e10050f0702121806090f0a09150501080103021507020d0c090c1d010c1106040509131103031207140d 67
    0x1000d2110141c8080556403a02141942c1c0010302c90254034501c041c421341c1d0000b043c410303a90030200e240d03444299400742e00c2c540002140b01d000a040290703005501c524032885c01e0903034170314107440c000705a000203521310503425080400101140654505070390f84580346140006803007014504084c80d061849032040640c030300e0a01400340312f04000c0c080d42e12402c00c5070200d4160846a603060304480c440d055114048241601c2500b0040ca00000103110034080104506a5104000e00044010070301e0ba00081205540360002805540c0c254001c1008241c2400c01e100385614607008500c810024a80c0b4101583c0c0018100045513a92442140340b150404166103106031610142c50040c480c0740c1d2410b02041c950074107444d04210b51219440c02c1e00040c0d40d44074074404966100c21001542c0581e170b6920450600c000308240c1c03500c200545c440c1c42018003000f0135013070034240441d0b4548100700131802078001b04100300c000c0151001d1590010041d00c0c02522594450901d080680035a030201c8140300c2c06d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 932299244 1250 932297994 932298019
    0x20402161502030103050c010906020601050f0a03050f0106031101050f0702060304020a0f03050d02011508031e0c10060e0105040b01080f06220203150105040f0b2208031e0906030c18 80
    0x242c0c040c41c1a244240d084a0460119000544010301580f096000590010005103c0350070180c00418411201520209445440e581c1c2c045c1044890000040e060303648a408100f8010300c2144480400d800782040da15003540ca4070346000600c01d04001034000c1c880003021404640b02d03103440400400c0c0c2d8036000c81c1215240c2c502103480e40c120034001c500560a0101c1040c00c000d05852500c210342101c4020351500504202c00b4140e16803409603441090400c0c0203066403620184466030402580d020005039050400f403201042950681000c0d003e20302d40100080943d0300801d606030480d140c04018241075892600207410b01d80c0d15605500600e120005c0028030148580107103015020940e6401004116100115414040d9106490300340303900200c1040f00003c4a0014109840d000c4050500c41d84800f00154500c1e0307069000c400706900010300304120100b00328603d01c02c1e01102c43c0562030031103241d00240d0305005c0505442940c0700002102030754030307401218641c104030010345100516076 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 932300494 1250 932299244 932299283
    0x1e080a0b1801020405090106211503030908060c0a050706060510031a09070f1d10230a0e040b03100516020f03090904140a060912030b0d0b0402040216 66
    0x203505035007220040c0e6550100c058461410300954003680d4000d00366075802d07846d0000032110100c5244020014002d6030f440c609080080340540c81c24a00c90080090f071003032940c50028007d07100d07a40146100c0d04000203101051581c2c90850f40022043d00e40b060b1680090304140d0010300283c1d2129501c0f4040003600380d00942c05410141c070040100c41042904003508040c052140f400f1920680080c5240000d2800d140c0a90300041c0341e8444050815000d00100c00456030a0107207400700d20100b0307003003a048811044d19007266a10354030711600030b60038000005000f40001e00c44405091049440d040a205603071000c02c9220550001d58006014034241400c1c004010311410070603800500034607003680c141c51400000c446410401401d601d1140e5650b884203201c54405640c06401c0f030181400c0c0710041900c501031051082d004021000340300002003c040d007103542c40c0741003d0080090b07000940200e0035101c0d04d00c0d48550191009680c5a00400c00c2141c0003903101002441682007107104244030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 932301744 1250 932300494 932300513
    0xf0f13060f05070c03020621010311031905030f07141b0301060501020d1205040819020309011805031509010b060d020d060501050c0307200405280203010605041e080a 73
    0x541690321040700722a60034400301c800e4812044040c0480c00881003c00045c1041c900601c180d040c50052056680d00072000d001d00a542a4000c0d60282c180b100c0c007501c0c1d46800e110382e034108103031801c1880801a2595a6948a000d40b0917054601c0c203000c01e17000280f00c0d0f1491500e810880031070079240904021aa911007061400983e24001d62038210b021031194000907102c11441101d07219150842c54400c034103409050020411603a0f06414444802c0c00c0804090300000d2042c0342d0081c1d612459410001001d80b80c0e003014448101122042c00c008a48010030b0f00180211400b02d04080303962054080d6014001d03004110307410040015480140b49190f030301034101000340c40707c02d100c180e546400449003030040760f4008842c0e810411803070000400d17810000700d6944000f4014100200500e0002d02110350482c0c240c001d210f943d054650519003403044000038000da0070400c508650500800030147c1c013940c05004940308500c0d05501211104800903801020080c0c102c8804184628228040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 932302994 1250 932301744 932301749
    0x11180c030405100b0a090b0301060816090c0201020711060334030b0405011505030a0b13060302010305090109080301090b030717010212010807030206070201050706020d0903031a0909060c0f0f13 85
    0x28051182c0581c08a1804d0180e802c0c0c0031402420a8041410000131000405030384109503819980c1d1034000850f200d00340305902c0c2c0900b20030708829880d450201c119003036501c0c1008280859104010041c00605d14100100400740140c2c0c01a440340e541d01955200c08203823803580e00c04030358200c020298220380161200c004019a642c1480300b089000c050100b6035400380200340650729020100140c0500c100f001d035500000421300407495184038400300c1c5240c02402640301d07807941c0700d40d03090041d96058042c8503009040c60008000c0c0e000d9545800ca00c03170006001300407203da190340d00d10b440c9940810070200602824203a08150709640e841e168000d42c003518500d0f0120a070300e130000032403620208051080300d4000e4110303803070140c3c1781c0d004640c69480508219915582401902080742d81d44c895080003038441c2d10001010312a200c03044040402c4000418403408025080001200c0003003903040e00541520480d030f448860411180f503c900894854620b03981001c18458460354a50120008 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 932304244 1250 932302994 932303003
    0x10b150307091a090d0c090903050d060b03040c0302270c070506071b12051b01140a020c030d02030604090218100b0301030816050f03130f05030d090311180c0304 71
    0xb0305580c89051480c40280c00c01d0820048406000c015a1420720418401d195442441c400c0f49003512a500541202ea26080070380000308042075004951806201d084060840801c0301c50030340c42e040e070310303007000d42014000280030320700749220b00040034115480c044d0803200301c008001c401c0ca041b50f02102c05421245080e03503144180008900d90030301648101400c2c2d038403d1054000c0c10500e4403003000800c0102040e4003004010055070032911103142c00d1110a200980010481e00700380c0010200418001e40141d103c2841041482c0040303000004651b000c1c8051840907813a40d442c0c4000800818500c00065000041c0030825401e00b41e40c0e4580030300c1001c2c291704000b1066141c05072a0035501007408001c00c0d184c000c00410140503010500800000d10500440d04144505034140e411a000b04003203400c003090100d4188402c6010328140e4020300004d4005207040c0584100052060b00703a40700142000c0810079041a507511801c00100c5c21000505100025044c00060400d4950040f6020703503 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 932305494 1250 932304244 932304257
    0x10803031f1d190b21071a03100b0a0903140a0b04231f091106180307050f0661020919020705120a11030921010b150307 53
    0x14403c20203109207084004082c148401c4081d4070006081c96220702240c807241841140d80016041c4003202406c4034110042210036101d00b403504440c11803131840c1c0c000c00318205041c805039012941c440010b4048980052a0044542642030b070341c2d0802c214484c018010a07071850400c003c0c0001013482d50030700080140006c0019298510450315070131820040081c40c43c54880c407004040c2c482e00050016030007110041c079842d4500c00002c155030720204403101c5d0017155004d0b640040c41c050000400030310090700d000203441c000c6800200c0920580b0081108811410080302181c1001070300c82c801200349121440d0010300300100d000c0d61a9000c0e41c1c0f02100c44400805d4900416101c800c01400d03940035040450a803905548440c41c5074200004a501c66420f0004d400420010080012455a002c18a950341e00e000d05006013404020100046160310800c4071500035142c0d0f0305204012440c015500f09107803050030170940503141c0e9110840d40103000744405544d0a4400d401980031714402e8a412 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 932306744 1250 932305494 932305531
    0x2040908180f10590f040e0c0d060e070b04030b220c030f02040506012d020a0c14031e1009060609051611161401091e0302010f0305010803031f1d 64
    0x10684c0c00d141d03c0310345c0c2c004855006502d0603007850f0b04501c003010038010540c0d0442c0c111070080b4041582a00d03094503139946071581c03a2210756090141e00003900c00342c82c01901c0d00c0d00b1611400920a000b0700f4141105242443e001200301310150a0b4445940c01091000743c90303942d040c402d0060030781c10800da2185241c02c0100700a98000c1107026074039525640d01080c070f000f8001015401d418204c1c07849065020304103800c0c0001c2c91800b0343c07502400b515410707510201945400d051510305c1c06a01881716540080010900c1000000c258021b140c100742c010a50740164948003000e0111580311021650804e4203014590bd13805403101c0610403ea550742c2d401c4a1540f107a83d0341c8100104500d101600320342800c1c44400c04551034462080c03010b0400380c2c6040e0b90359446444a48000d81401c00202c14031009004543e400041e0007a1028240380911280d410140ea01d0307180e200140107010304100e400090313403120110700c0c54840107040d50b241e000303480881d45070010702ca00c0c022180c4240b00f01e0100c904 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 932307994 1250 932306744 932306897
    0xa020603091c08090a1220010e01060902070302070e150607110f0103150303121d03040303080c190c140f010c031b0207061b02040908180f10 62
    0x3c03842021210014281000030b03881e40301a81d91038a82003003c020a580c100f15218041c1c14003001c050074a03000001c0c846078800010b17800c603181d50b00640901401000f043c00400e500042074800e40d503081d945108952120702040d1200856000d25a41105011401d0300c01d10448121402c403d0350152118203600c2180c000440441c0d0882141c481c40c0c6108103c14130110f88180186421864118030000792807514419107000071182d101c1607005644005001e104040c4c0c0910500c0e041011680000e007000c50150b82c0e4151000c2317031080c1200700411000d01d5814000d42e00081044101414140e51809030b4000c2582d01030010340c0f031550b01081c20710741c0002c4120302c904030a50205260340d01900d40581452411110306581d1302404c152101c00c402024056640c0c0d100e0340c08040e10401c245c81d0b9515418000c1558203203c0324130a8880c00c0300031400d1143e030b260251101d240e20240e1419041c00030100382c1c1c50904000e403401041d0b54049407402d4190803218907000300b2050004003401c5072038500c81d448 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 932309244 1250 932307994 932308007
    0x1608040305180409050109050102070c0609030b0403050904140406060f0b0408060f1e010b030a06090506030a060513050a0c050102010e070b09060a110102160209100302010219050a020603091c 84
    0x9009000580400452054100c02d52040315030040c010004208904140c413805d09640103900103075180c1c1d500240e0380d81081400c0d82000020151420090003452441e00c880140c040001c0000c0d080c003c0008081c3c0040c1e075558009510b903440c0d00800165803d103030030724200600c03060284a04100c1c45110100f0112900303815501102d0301c440050800d5943c81d82c2407042880b0142c0041076145d40d0310404080030040c0d16000d03010b0b04880640d10b460380341c080c008006031107803940841c0000e8034080c02d1187c5a14041891420305812820210306503c03011304181299101741005040d5001d958800ea0800c0311018600d403c03104240e000b482400380da50091900c440451207201d80341c580410460800f1300f030110107448184003074200140300c5000000340d04d084e60710490014020040d000c0e40002149420f51419810039480030701085114210b600203035a80c4004402c1c101c941e00052801d00400c03000304148080540e025051640385d040401c111613440b4646400400c01c040c441c024118010311449 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 932310494 1250 932309244 932309251
    0x9080708130f0b0c0705100e030a0b0702010539130303031d030306010813020301060906080a17031003082a0a06183311070212070e06151606051608 65
    0x805800300c11b01d000704001502d19020520f40a00c0b03014810420310380c1c0c00b80540c00d0f003d0701800b502c040501e4041d41c001d08441000342100c02c074210244070f59031a00e461820b4507107084d600c0e000b074034018004500300c5041405000007422840c18840804010035605030816002240d0b8104141c1d408403050401c41d450340801c03034031980040c01d82c1c0e0008907141c0c00b2000182d034440c009400014200c0c3c6600c038030401d44505030001c81f52a0300c0f24802504200f000c0c03503c00b81d012070500c0c400c1d0079410011000265008a0320026041c8040800c078542103044102980360001d104a003003048d0181d5071004035843c2e0503205000e4031074900e07043c11484441200d04259410580c8010f036245550141e081083c1170481031789040346902c02d001390741c502200b40780c861301c401c030062031140c251100c1c143d204002d40240900c44c1030520350001c85c003c21184000030030f0f032500300d80c040360282c01c00c104044203680d90b401500c0c50441351040c0290043c2c10701000da400607002e035001e03100c1131422401100064402d0306040e03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 932311744 1250 932310494 932310517
    0xa0b010f12030f122c0105070504050d02031606090e0c040e010302100e1519090f090b1302030c18220c020f1501090b010f1209080708130f0b 62
    0x15224807001922400e4119800840350500244403403121600e0310448502d401c10019008400030720115141d082844941c0801c01e62000348018600303a0710040c0f03903002d180700f1907004040d480d101008640e400d01c080004059012203180c070341c0b542c4850061030030340300d440382c036032160f503a107000c9805845460116000c0e41c00601e158040d50b407a560078885600300040000d010040d601812446070399800908070340000801c0603c3e03464101c030754100302b2403122900c551020b100005404100c1595544240c0703040301c1e82d0110005e600c8802c40041408036070b520501c031440510000800280842e40c40c0905103003003500740d40c0c0c41c012001c2020f200e40010020b0080c485c6400c844151104819182c20800304c101061043c3c801014840d0340c40c910b40074501007403a00c2c5105030001801001d41c24420380418250907e17021900c0c444400028218850500c4d06407107030f64840c0180c0c01805101000c0391240b59010819590b10902d10100c00c01010b180e0140f03404016040c2400a82c0e08641c40545903100c070b00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 932312994 1250 932311744 932311769
    0x20a080106052d1204030e030f010902030a0209041a0108010510090203010308030f0c09060a1110050402061918140102010b100e06071a070225030305030708100305030a020a0b010f 79
    0x30b43c80c40c21004240039200056800100300c11901e4402e068001405503210b0340311a0320140e4036400309401d2101c41441d6145680c0b414082c1805039800017060014244c064584140540782c506007000c840280c0a880d00d001d10580000061a81c01584117900c0b82624003100b010541e143c04030b8400fa07100030320000d08011010300208402041c51131500b500100002403040c07074440200c0204265401a003015008504900080740d8482401d100118904680c100d04004500e855400190039000d1400fa00018004c01002021074034061310300038030548410b05d401080b0690b01c07450038101c0080e0306e0001e4015402c10f030303450301982480500950401c895840d02c0848a0151003400300d203412045094910a00342e59034240f050000500c0180070f500c03540c0c00ba10310011000c24403140c070170340b20298a88070001040100301003540002940e821201c0c07440c001a85031295107100b004050240c001a1080c000000d40c1031540d078001901c80381e094410300c401c404603030740c694041510342035505c14140403068 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 932314244 1250 932312994 932313037
    0x20340290c0415020a1205040905010902031b0d060807241d0609061306110f0604020907030b030c13050702010b120705060901051204150e0a2f04050a020a08010605 72
    0x2290400036107400110310460344244178075101d90440b0b4940a0500f00070032030008050240002d46e0184501400c42c0b2a000c1d455410244060003a05c809044e41403c00c0c0310108000001e4640364104c48000e10440d011102c5103074403102c0b5045045101c02040d031390042c0ca00b08410501d8041d500c072441a000303154140000c040c409050103c2070f4070960415601003400c12124a90280d003c0360304011300b090b42e4a01c1503896144580616142c86c0c003034060029403000d4100401695284545039100d4801d180100e2420209000709207000c010703c22040e4419281c0c001500c60110715404075210301d81d242d000744131018a04003403014681220820324065003000a060015051840040c4240d02d07041c90818503182422722034111490003510100e61200170b030907030b120600f803c0f4068000303140c2d000d07030203011841d03229503503140c1c1c007a03030740420400843c00483d2140c601d1703e40b01d041010500010380140042e00c1c020705913030001e40c010650700b004a01520004601b891042007900c07604200b10a10110115 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 932315494 1250 932314244 932314259
    0x406020c13230c0c0601120c06020a0b04020d02131b0f0e0d060911030f0f12090d020d0501060801090b04060e03040803070602090d0c090b03010f020340290c04 70
    0x10001420784004400801c0030742c4c400802048460b0080580440f8034040c4941c1d80350049520303036564012011580b21401c6100401c04c1c107a800c940041d4121003002d219141880450244510401c2d41400940380c2140d08a506140e40f4400802daa41544c5034070000c100d0711002d90341800100c1040750001c220740740150008889a100c2e0716454010507401c40d21f01d02000000f40f80110f1070404890b5034100042c0100011030420402c0e44075241440c0c0542080c8001010410815507c2d0b00030388240044c80d0707200107101003940800d0280a4007002400485140d0404a01da0783e401d030bc1c11a0114603003541c80345d001c6800b00503a819543c551004d54034100da540c032050b01941141c1489075011000d4480200095150b582c110001c00b85481c000c42c100c18400304250031034038007120300400d45004208001109404414401c0403560903c0084198204030050003504441184144a0b0000b885024400c1c080b60820110502460040311802003204846102103007000392074184640f84180020b00258 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 932316744 1250 932315494 932315561
    0x1b101704061b120e1209061605100b09090a0f030f02010e030a0c050606010f1e030b0a0b09100c11011b120809070906030c0504020313080406020c13 65
    0x3401944041045411418110070b510102c0c070307402c2e0204000d89281e00381800107014400030341c41c0b0f00010700304014401007401411300c01d0003920f91203030000150002c030b00400390800035002500441100c00410787c007000080100b003445070181c030554000c00082c496880004105101e660b1041d0303c402d4151045e58251034866404c00240155522000640600e8408001401f6000c40c0d41c1d4a100c80c1d042241012802d102000c0c0400b410081102e940490068010100840541e076a4401e00307555514030b20128000c0c46c00900c40d6602440c91400000c10440d03000c0501a0403504079034000d0009940032047c1d40c0103031424001407900b4006480410190700901518420764504a83d612481340f1550343c2d48401c54844c00000d01240004041c4041c0d40000c210b100084c0240b8601081502c2c2507881300c480300d0a003031144510494001001611400e9401e452044565201ca440340d00c8070744a0a0194987d0503070000140100211079001d050300c1a6400740c6000031071103003c0301a10244515016442 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 932317994 1250 932316744 932316751
    0xa020a140c032d070b10050103050603121c06030609030201050106080112020d06060e09010509061e0a0e1903030506013e0115080a12090e151c03021b1017 68
    0x4412401007010740302d201e4001c2100c11710520142d001c0b841c000085600038019900518101884c04041240548001070000350f18458194400e4546415498403030101e98501d4802c48040d0400d5400401c000240c0c000d00c0c507052007a002800580e0720703500100d614010900c500c8441c040320b0380d07001002d41409420341c4800c40c02080d011600d0754441d520b220501006076031043d000e81d5100304010301054180b102e0342c1c1046401c92910480a0034000c8001941405000030303414903a40c1000d500b04c40820040301d180c1041e0500c409000351800c0c14090002c1504a80e6540417444101b1412004039604034902100d402da2086e1000c1020301a5003000c4400c14203901007020741d070365100c004901c1c0d440c1d5050b800030251a0000c0030110801d18200710445940c0000d401800400f14040c007010b01501061544030b14907498042c120881c01001400c2180d071070140c4255000105483e1090503404100c1c5a14907601881c0107148001c50000d0198859002040c0800134080000c0b00c2c90700b821091140740c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 932319244 1250 932317994 932318047
    0x1b181d19031404180e0c1305150d03020f1c050a210204080703110f0604031205040b13080c0d050d12110307092d060e03150a020a140c03 60
    0x4604525608a081684144c00190001c140250344025404241c081c9a1051071040d014018002109002c40c0d44040c15136803104085032a400040c80011030208940308400b001407005000000320304000c1e481d069008102485801285407904c1803034002d02030a80e103003d00399142071401010301c0f01181c0101411808444141d03092101c110512403d0001c0c00c041d019800c0648216451841c1410303a040e1440c9280d8040c252080f80000190f407145d0a0b2002c494010100000d0300c4041102110b1901c226004200c0c1d4080c08a1501c0111072060802c1d0107a400e50011121100342c4241000b042c601c00e000010003a5001803001e484e41c510a500b070002040e0101000300e02100c01c5010440c5a0308202c41c81ca002400403031081020703016036007260485102004211310904950ba52504001c0e0f400e021307003000e00c0070000782080303192810811003501c150300c00f00540701307814000111000b940c0304001640003c1da0b800711080484960313030100c542500191004600d0125403c20f5a541403000c03099a04 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 932320494 1250 932319244 932319257
    0x80a0c0504051e0406060504150509010b070c170307110d1211070306140709060c1e080c190203061008030919030203240a0b0306060108041b181d1903 66
    0x490f0b81c0000c041503008610030400071a490307080c041800b081f03955041405a03025079510081259455004005054407094681190380c1d01080c10500c400c0803a83d8003d1140d0026400d1030b05448002002a1610700d101cbc600f86143c52a601c020040c0f079600146004c0c24018142c450640041d0052480c01d176440c0850094441c103a81e662a2071f0103c40d03581050b10400d42c0c648042080310b550001c0e00d00042c2041d4202606a0f601507200d80c00f41000f040301206810b00100c4a542c203210240041c0c80c400c414200c11030700c3d107150140c4c000b01d80b40001041203002c1d100d4940440d070700d4200178000300161510314005500749007501d000c0000115281c000240340384c10012011016880500c600032001000049120881184a1400340401c0c0300070034640c40301d46090b0040d0525600425082e8000030309113420760303a40e1991b05003440c2040040000b0604008018400140c24601070301002c408800c0100401ca036055401000010020191000c00c4681001c2c1400d4076000c0b942d05021030050080c80c0a8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 932321744 1250 932320494 932320531
    0xb01031503060213151b0609020d05010b010f020c0f01030b061306050a1805010c081305031c020f0d020703081b01020d2a05040909021207150801080a0c050405 70
    0x140c0440840e0410b80d080d80d00024074001015030848410020300040c0c8003581005d0035203000400e15841c00d120301582c10382d440d10340f00a0001c0b03a040302216640062030701e605030904c1c1c03074120700038000900190701041c8130048102d821070020807050318645000c1c0070b02800031251801140101003280c5001c1e881002072149001d12034081c01c154001d4101c6407143c41d910340c40d0b44800b4002c001a032007030b03100c10380044030140810f9910094140c0c2d02e59100b41c00300d03191105a040c0380d42c0341c1425089181c041c850aa50804544070b003589000c5901020f40946844d03012001940d41c4a91003441440c015920040007000000c082000408500381140000c00c808005158180e080e03921a01003001c030381d9200d1201c6000104008d04100b1080000401c45004007090748014005005d10b10070343c0d410300d130307600e12100940d1201c6803445000008081500c0945031a140001d0000300c1584200c00007620801c004034800780001804401c994210040102052514080101800000789404040180844078 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 932322994 1250 932321744 932321771
    0xa0b0a091208031f030c1406071b2306121305030a0801140108090616020a0b0109140906010812070212010e0d020105220212030f07030314010e0408030a0b0103 70
    0x45441e002d01c20310140c1d0740ea08044070700c280c50328402034104021200a02c0204006aa08060b0720102c84440c0540c0503110400303000501e0702d010741000508104000d0120313a401841315007980041d518a071101c17240368910703519403a02843ca00349610703400442c10880700120802e0400c549038080e00100c48250040c0c600c0c0c1d2002d045400030003003207010031501c000612481c0056400003000c00070a10b4030074494a4002e00180d941d04000d8640c00550b0a48414035030300c1d900c0ad005800056411440346811942d40d61130070303c002d055102c0382c0700c4080c850381d000c01c48408022070054100c0d00c0e00c0d4000d00b036507120395001c0b21465100302412603000b12140860f5094210a020f00350116480f8000341a80c00507070781029017901c0008003000c00b40c080c800840401e1401c04402d182a6a80540c2c801c121401c440100e185584030ba900e43c1c10079601c000c01c1803020540c1c5904a0440031740e6591862a00b40d03a10b00300480d01e004195401030410805100151031042ca40d8802c0310440d405241c00320700d08000c1c100e07 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 932324244 1250 932322994 932323019
    0xb06030c18070201050a11070212071208030108010e2121042301020a090e09030c060f011508060108150307050a0902120f090304031401470a0b0a09 65
    0x4001042000d070010095041c0d028881d096015003600001d1054560080c175601c1184120b5500170f218400c034038100c0030403150800c00c0c00098903044102c04c620185605111030940c00034030a40e802c44d0b0a00c0c51a6041e41da010441041006001e20150480707250040040c520345c00202c1a070000600b00ca48070781c0030820a40d00640102e000e50203c90440e403000b100103240d003000030001c2c1c0392a1300400c6455440d99010a4003812540c0b28802da4000780c442c81c100c1400c43c4a0801d46409612402c2d05002400b00a170054504071a0070380e1556001c41640c08041e03500e920300315019400704128000240306c01a810f1690b4100c41401000e40c2c007440e4880001030410300e17a940041c101c2503808903280714a00d0f0006015034200b0070b40064200c640ca045042250b41e40704a0000800395004410b82c0900c1c11401d400100c141c43c40070b40f458240110000f01c400c002000321050061005144410240c2c84140060704050f1036000380000074000c0c01c010f8011510fa1101c0030700d004102d4034800002c0c5011002c034 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 932325494 1250 932324244 932324269
    0x120210080703110f090f181b09040608150106030606050f030c12070815030307050c010311120412080c190e031915060b0c2a0d0302010e060c13030b06030c 68
    0x1207445d104d107101410721501e04030030004030340244400c0e041103030701244154440380d01041c44032042c00d00044c00c0c0c804a0590151078401d9410500f05080814409404a250b401403051540c0c4001c40b13aa85040c100e06651451080d84013041080040311001b06005000b10b60010700c003a601490080d0340407c541903c0360403942640000d0741c0000380700d98030201e030b10010445041140298182070180e06e0300f68403026110f80c61030500d40d070340402214260510080ea015034000c1d03000d0020502d4141400c144044e49074004030002086a4006602580d00c2000d45502c403003a0b807208285030007012020742e200c505607030086a06100303a10796038030098012600407584510800c45451640e4002408400381ca20b190400031341f10310b051001c21420440020421203d000c0105103c0500343c035440703030300c0a8a4841d07041c01e8100c28851801c000341501500600d40c41e080d40d01c201c81981c0eaa0440d942c07464024050600d94944d240f0f4010000b00e000041da2700e0b0480d40050680390b540c0c02c007800003040c040d840f0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 932326744 1250 932325494 932325517
    0x4060c0c150b2d15090102070e040c0b1b0d05071e060e070b1809090d0323090a0b061e0111150910060501080415020a0e1507050712021008070311 64
    0x141d00f500520306040204591114060324024208408480041d4840c2401d00402d408110703000000b40600130348102d013100602401c040150344000040f50303078081150002194410b442544540109544500100c0d0000c58022111900c0e035507111440410501484006640f09512a0740d070350000d40091043d4401081c0b01154556500e14010043d400000391542e8607120b4140042001504c2e540030130765130020a924a070000c0c42c0909001c0d1091041c94103081c8142c030078003400c100305c9450750014480114a000d00c00303c90f601c0e500c290030004009200070600640768440e040c1c0040550203400d00c2c0484200038000c0d151010952254081e03009800c0382d01c10115448007070b074210324040605c1801c000d80f0083c80d0031544d078038180d2604000214029400c4103055400101c54902512403801d41c5c01408004080e03001c000b03840c85040c01e0f2500295415516401780c03034070010340a2610040c9500d0507074013509030344021489440540c2e038010001c0000d01423649800301c881d4801c04640040030400c001 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 932327994 1250 932326744 932326819
    0x18071d1e19091a030304061e111609140c09040e070314150a02030c03191424061c0203060a030f05070f060e0310050a140a020304060c0c150b 62
    0x740c3c40c50303122031110303005800b1341c0040100b4462507034070005503500190350b61080014a0b40300300741141c1145c904440d0648038054540c0204980c800b042100c000c6920300601448091080ca0480c00240c50641d5541a100c13410081c0354003505241c0c020203c9107480700250381a0941e00c0c0c03106000511401480f00035074000e601000c510303410004c5120b402c4855044118194505402151881d200c050070b4425200ca03112011000743c038960300509025100b1922402c0c55003095040c006440d24582c40348104e40306424003441643c1419800d070340040800000411000746256060402580058002c1e0b4100c020400044003140103d118101440c2c414002050424a003184289080030150880d070100310a02c108480c5070303500002c041010183d19480060541c40381c080d01c400400103d1828081060b9910410480c0d0865038055881140601003d0007941c0301c6a108a5001021210007410340d80e046409044902c1c0c0b42d132180420b40d2000d443d06500c103040000800716000d804005642d407801 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 932329244 1250 932327994 932328011
    0x6050903030a240e0a290109170c09090307080403050f010501050a152a0614070201020306060d0e030702060d0905070602240a060518071d1e1909 64
    0x40c0304441100d020124800c55207801d0201403410755180b4420b40b50441400b801161010100758007810485a0450115964840100d006c00ca2040c07035030021408030b252000300040c040c15000d818005480c0b81400340c41803070200000c11502080103400c00300c0c0c0340b0040c40060001910304001740051801358006028804c80c00b40c030b81d0f0955005802941c0100c03005401007021820241a9010003d110b040c4903486000c2564540382c0491289508224409156505001d014603a44540172119800b80b0811050740c460502380d090784003c0c0d03002500203000700490401284694018000048c10307400341c0c0d1920b07074540c0010384140c10460b04100f0040d900c0051004100d401c1006a0040c21140007402c491440d15180a460700f445886010300394888200003844c2d05805da0009020307290042498842141d5100401c40c083d400311070b40c90100d80c0885209810041b0604002d8900c68010082d00040c01040d1105104c900740b01c5040c1d130004d0a0b90803c07120301703000204410150100d5903002a10a5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 932330494 1250 932329244 932329261
    0x503070510060504060311131b050d0509070608130c09020304060b04050f071b02011404060f110a02060f0703052b06140d060c02030c01020403150e0c03100c0306030605090303 77
    0x14100d0380400d2244d49012810000240d81408402440c2c8003101c1d1782041110840100c0c014084201514502400b4505d0038680f107904400507281da1444880100b00c40d9941501c070641d5040d50380110305c00305192000181c000170041d41c1080d03440707200e60131204080d83c0d2200c2c0e6100f07981050343c0071524103855645101c4181020b201e11984019200101c3c241030400510140000480e0090100914a42c04201041da4010a03002c0000140f0302611661a48e035024011301c441c7c002845400010508101d15408400000b801c043e41900200454a40400442050240e40c080d14080b0140801881840384200041403d8083c020810b8400003402d900319030b01a0480f0060341010f01140c8d241e010b1110103407100360048100d550722800000d00303203201605c1a8918025511711411640c00040c003c000c00400b061100001c2c1c503100402e2141e045178807503890f25403001c441010341641c8550403010a4015036001407103501300c0ca060002e00c00d9200d0300d0f020203440003142c6030a402e5000205011292 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 932331744 1250 932330494 932330501
    0xe0a02030a0b0f0a03060b0607020637050a051308010f0e070803041206090c180f380a0b0c0a1b0806010308030615030403080403110f07120f0503070510 67
    0xb090884103030b154a650b10000403090700c118080034052a666140740c94040c0c0341c01c0204e591680d002000c0f540c85a007040d25400083c0340d107111041d407920400041041c00407411611035021342e829144d10b030074400a1141216950005248580c41c60703954503001495007030a1207803605140104001140800501008910340455030b88400ca003680204800c2200461006c4910b031090341c001004a1014202d040800d9212502c1d00203282c1040b01d807020342c400d200c080d0f0100d03101250121041c000001c181e1480724080c00940320480c041c3c030f0803c444a0814130030414090002c0f01c0100b40442c07041e04c48060328519080a0312142c0030b40e01001c005800e103d0a08070391050741d11002400c01107141861891703134807a0010311008010490100c00700b0000c0c4e5546458201408600c0344c2513449241c5420001c00c650303403d803411781c042803051070345000070000840e201012802d144014401545840081d560318480d158040d0741000c038228030f03000001c4041c00145052409400188407080e95103110a045 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 932332994 1250 932331744 932331761
    0xf0305150709081e0102040b0a17060d0b040204091406070f1b050705011805060711040b040510061808030c060609131e0807020d2102030310140a0e0a02030a 69
    0x10302a5080d03040150500001e80b03002d0300c24084080000301140240304501902881d00188c050b21000708610384c14540c031007501e02c041402d007544000c0c01c2e240c05081c0004042504005040ca44c002c0000170054205900805001032103080d410856400760399207281060401d5a60b000023540034440651900d501c010360441411034440f070410590043d41d039031a6602064403030300781441608550310101740d0350021306400030880500101d946050b00d18190701c0c01c20341108882e1185142100640142c1410701ca07451003074036418117420324241030460a4070101d00303282111486201d40f100119a40f0070900107072014410150050945081c100100005000000d2201d00a0070301204101c011442c52070301c01d11202c021004030039280c412800d01c03504620840300040d400c45114554041003082c80c010903030100d00c5006004541c440005801c030b8880c802a104442000107118051050200707840440c1d8403060010400070381c40c0d43d10403165070100b4007161b0b83c4841550100411a4049a6001c3e42c8003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 932334244 1250 932332994 932332997
    0x70f200a1203030c18090f180b01172d2b05090a03080a0f080a020c0604060b010c0b0a05061c12030f0605040e03091201020301050105030c03100f03051507 68
    0x40103801c103004005262911400a420962101a03007075106008841e107004609401c011803400584403500c103005001101101c80300a4038042c003096031100104441130865610104504803a441d202810b06901e881071030000d6980100b003000c182c3c8444441e00b142c0b04009a40d800b154403142d81c0b020794205100900a81c46d0010343c41c05041044252000d201041c90381d0303080590300c6881c24404920f0003c0e0980004011000000740158450707000100c07084441841e0391107510036a02c0404040c01c0e402030504008044d80608040780000b00282c000c0c4049440600d440081d507d45078440c1341c414001581c0241c505a503880500080d401d001410741c1601859007940350164013256075415221070342c080010101030360b0b842000c0d40a070407030700aa0f005040c0180280320314110101103d032a03602c444146442440c611043d86844401802500e0413604161121821a138401341d50715202d92000380680c4110f8289640403034440c54100c1cac2c9401840c01030008150070309090124044820018080c2070 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 932335494 1250 932334244 932334259
    0xd1d16030206190201060f081b01020d09050f0f0619091a121519080715090515071a07110a0209151f0206060a0f080601090e03070f20 59
    0xd070302c2e85000c07550002c00f50410060400e1100d04100d00401403a0411650016003030740c00034001c00300007031040110151030700e00e40f036101d001c2c030040e82d4a20f0349103608000703d508900b00b00494580f2040caa25800800b800780e007030301e000c2346000814644c070016445070048124421102c00c035a00c211181d003d054502649031b0a502e4050025a07070b030041d261482c42c0d500c26140081c00c010207003410641900070182108124000010001401100500401c01a48500c100001d00d55003039141340602400a41c842d070080c28146800d201c84129100c99030304503c0010004200001c442040480d12080784441482250800c0c0b0700061042116000e0441c43da8000c0c502180543d840103007250308500d0b51510076030003003403c4020545104c202641c02c41c00840645185049540100300b0038411074084503242e50300341d211945c0101c84910381c003031003070642e00070001802035020a80c0b01015580e0481d0480e400e080d19030340c0c0c0700111350351042e088030300c03041c0ea58218909891001310296040411103904 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 932336744 1250 932335494 932335499
    0x21b0f120304060e0124140f0603160903080a02010c031802090f1314010c0e010c080a360306110a02060c07080c25090203090307060c03020d1d16 64
    0x6030140e000240018148039038a000c451400308013580010b0880c28401511008100983c8481911420310321405003000c06c0c40c000017009182140d041030318520000d091604544400811101c40810740700d1023000e009400c00080003080f44c0308083d11020000d64008520b0004801d0000c09030f5010915840304204071040307070001666003440c2c0d2075100782c100c2e5030f1491660310b40d0b0b46141009a501c00c050f100c0c20100002d401c2224040d08642511000c0c0c1d1110b1a4540501004451f4400d0200f00540b1059080c00641c0c00c891040e1521003180d41c461041c0c00013142c8070204140d003514194901c0b60012100c0000b08100040d071700078000c03400300d9084080c2c00c10f42640e902035110714009000210280000411004100c1d5a805550051804908840c0300c100c90303000360403d203000da0801e40e40303100b00b0000001e0b4590980c000c50740729030181ca02450400d0350b182c0c6c506019060002041041c140c084c4400100d0404a1140e4030140c43c41d16070380c90501c500d03c5102c905000307007010003100440c49000700303 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 932337994 1250 932336744 932336773
    0x70f0221101a030a1401060f0e01050a05180f15040608010e01051605040e0406020d0908030714091c0501140a02091309080726030708061002010c020d21021b0f 70
    0x1002e0710300c4c0c10513850302080c0c1800b0740c1c246c0105440c1e005442c0e07841070700c2c0021401d4071318454801c0c180c540a50712201c1031500c92080040c501020300f6501ca10b01509800605c400c0c0b030f000e00143e04a9004c1407080c00002504c000038094400e01d0304292060717903403030710f00d910300c1c0409004450308036189480514540d110040010400c0c415405404145603500001c541004080d078111101c0031000c600400204440385040ae01d5580103564103000540424507041c5040d070003400312140118000c09600c198503681c00302c0030b0600300c40ca605641c15543c074402008612a00d0108601c00c50700d45c480140da551130503040048199915100c00c0242d442e051310080010711000442d06101d412260007003481d1240c4416810000e801c03660402c0d0184044140071320365401c807021900942040b10b0856030307070b246100c6c224201c0d03901c4101640160300c035604042c0360382d000e034442a2400c0b040d007140c081c650302d0981460040c1c0c2c2c004201055558800e8090158101042c801100042d44400c00740581050b11082d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 932339244 1250 932337994 932338003
    0x1140403120218101e110a1101020f1e070e040b06010503040f050706050310080c09010b0d180b010911030f0109180203150a0b0a050105070f0221101a03 67
    0x5450201c0e80c2c002481c0c0000312500d03050305108940100b041e42c02c1c1065480c02400781d403000710000d50003406000303e06445070140c04521640d000c000c3c0200030016042d15020711652030070510074158022540700b40144a014054012001c00094104002541496080d80303059990f5000302e107410410f000f404001031602d00c0483d0004400d18010b5141c3d111401c0240d014030f05400002d002c0d108044001030265044030103948550521a04003034091350759449182c6072030821307849550004028005204018000000d001d001969810000361034044007001d43c1040000b5600b601d50000741001003080031020700403d030303031039006100300c0e415130030071001c41c40d000c4806000c2d01d01d8540d02d0b1148054050313a5800da0f07203c0103030018100c40800f4022400300c1c110389400d8454640701820500c28413094101540c1001c100c1e2810380d540c82c54a04943c40340c02c2c80c030300d410800302e0b408480300c28401d8541101e9444c9460854a0f00041c09207080c07a1091002110038486440a07845020000d40e91181e50214 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 932340494 1250 932339244 932339267
    0x60a1509050d14060906010801060b0c030319150803030a0509010c020616050d050a050907050102030a05120a02070210080a0b0405040c23060a020109030e03191403160b04030201140403 81
    0xc070b44040b040e01d43e152050408044002d00892882140b04000c240e040008616040b5500c3c600204805900c0b01d02091482c40f552050620b030754810400f01c6d408840300c1b074240a240340400400185070200f0168003100b4411541b10276034561000c1309001d28042640304058110300c540000300b04144800710003940741e01000b400c22004100700002c03031400314014021109024000d00040140746000e840c050300030082503c1540c20391207400b40106165000204951105196031111801c0c8030f85100820000c100c02030581d090f00c0d0302130002c2ea0058842e401070f06252a010740350251107140900c14003084a4400110034030035030034041400040f44110002505440d0b04860407945956a00e040c4410901c15802079904140e001922640716607040d03001010b424841e80d140510315454004045d61003000c040140c4c45005030f020b4800020308005100b42c5400d0302c6205890030008481d05640e2114801c107015120440e02c80f01b0001015420f101d42c0c00c1203207d2001041c06420a5180102008200c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 932341744 1250 932340494 932340499
    0x810090515060a0b0315060a1e0c081b01060306050103050106061107030c0e0a0e1203060a0b03060a0909020a09020a03151d07050c01060810092f040903050d0e0105060a150905 77
    0x2184802c10343d2221b054400344080c0c8500d6a07005030a000800841200b501e03c2184007504c02241341051145245100e12500300c44a141055028040e1005c42c80340040500c4056690342800400641d150140324002c50041000049061a0807409003410044001d034041a8011803070a0000800c014100800d850585c88540000c0d580c03004030800808110032150950700c1185045c00034100e500005602c100b505507148100296509040701803400103440b844e13803100c0301600c14410000c1b96441854054002802c001511399112607000807039018102c2440042d40311100c42d404204010018001810b10108440315031000345c4c1980801d001c00b600680c100407000441e4107040c02f00750012405401018107036030380f915038444260300400c1850300841d401c00402c080c0b20380c980310048445403141d22510b48104524002d00c200402014800310440c2402401d0011030b00c0c80000d481100d1100011350000030302070400d00d0800074020782d1680403448a202003003104c50f045600640010885209 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 932342994 1250 932341744 932341747
    0x1081b03160e1e221529030f1b19020d03091a070302121003050c1e040f0609020c030903060709030b0708071b240b180c0717040311030610031b0810090515060a0b 71
    0x3274035001280d107409084081c1e118080895685011070042036080b00b010380701d40031500b820300d5180307040d070940b40f070414003a04a80b130060801001200600382c145c0e0104aa10f001440c044110a0350f045842040d00d480c0ba502520740014002c005080099140b48002119080038079002301482c401040d100c4104540290f48904007220046941e8200340081d041d880000c0d91624488544290f80c0e40009000324424420130000c80c0c150340c060701800303060340e0b0490000d06d001c0d0360b03e110980b10302402501000421406840d07284809a005520314001032090140b03e42649400c0071102c041604a0110031036a071074418000da03107913501e02050340001554103044455a0344d4000030f540364001c20310090307c421070180380c03001280b401d10010010780c2c0c810844400510300b880e050541ea802d0440390740440700c101a0041c40801e543e040b103100e41c4415000040e00c22615440c12908001c01c0352300c0380f00516203d42480c400c00c102441641401d00302d01402d081c59180c0744000502e04891413007803c040708030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 932344244 1250 932342994 932343001
    0x601090e010b180a1203030609141303020c09010b03090d030c1b0f06060b0919180e0f0d120f0b0d0201081b03160e1e221529030f 57
    0x4041201c0c8243c0d80e0002c01403880700d540ca1a07042d03a05030701c60104500003468003001040940c42c81c810125002c1c81140c4008107540d94141c21961402c26400603810752040c411600d06a82c0c6400001d40a0010300c03d6650b16424000f400b1450007942441c01d6050500301031009800b103078402c0e0404500d005811508644404a0074485081651250050703c454100100841d000104500034100c14a0a5441c0300002c03442400071403000c1018000e070390107406c07034100500040f15a1b40003038a9140440065070166a450142e9030700c0e0901d0032503110080f03210365050305801c805500c07420305109179290303040c043c02c0075100001e0100300300480000c1c1403005270404242500740313048204140003040c00e40c1036940e0a000c03c900901411082e1408006105500000d58034200541c0b400c07400040c65800100603096081040251480c0c0103400700b00e0004001038a072034078514002c00084882c10090040b5030341c01c001d10b03204507404408000031800e01380740903200000c5400045031303448420007183c141c042d00c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 932345494 1250 932344244 932344267
    0x50f07050a051c1b140a08040602190c0b010602010c050318030c1002072d020d1e06151202130b030a06093c150b0918060601090e010b 59
    0x403484403424910440781e60b0b258401140e03200a20b40c00200b844c01900d020456800c5030000c00d44001c540c01c001c002c1c0701802d401c502484040382c000e48607540c05414082d04502d072608011110701140c000070485944501448802d8101d10b001d4401807000b480030118068000d00584005404114004030b003040d0030a003000280241c5000304a5202513032040702c040b144103006034022510582c1e07640c1d080500c00b0380e00c95807940000905244030f4004003c86449070200505000419400c0c0c036440c0004c4010080349045040c4482c020b481580009030384018142d100351451611340100c4c00d40000321860b0b001594448004140c400f0044102060000c800400310b41403003000d000040c005030410b03044c001003240d040c4510110002001d0a06005200c00e80176098003181d03410419619000e08001c4000704d440341c0525841207031500760200d001d880e40c802280183d4000ca840c541504400c0d60406030320030007441903135000002480c100d81c01d41e0030040c1c1c406020f08184688010400300048420415 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 932346744 1250 932345494 932345497
    0x5150f0d06061e060216050a090903030605063708040b1b0403030801030b0f04080f090604170303041703040b0720060114150f04030b06011b030207030213050f07050a05 74
    0x6054008803514400143c1203401c03c0403486000307110240c0074020510030b8009800000000f21400104201601e900c7c022941d0024000008243c08150b1985e034085005d45600c4010f2607060103548007090800d082d1100ca48030781c01c4800d8080305290741444105680c0c0d80c0316440a4000c0c1c1c20141062090f2600a4a10490010071180c449580000704000043c0340d080b52015040301d000781140c020f1580c07401860103000604841c0185009820300060710310390000340180041d402c0240036070b403402c0c0e114594144484036102140406a10000801080068070b080b40034180000c003001c603017581415681e444490a00410100410400750a00c02a42491a002600c01c441e01c40a4450558450ba20105420300403000240070381c2d4021807008036903d20303c00321801091b0414090342041d0440d031362800c031120080e000504200b0034a120005d101c00e00903a0302c00007071081d001080c1881c0f4520500c1740d040500548803038264a448100030709201790360240c50780310540389441640d420650340141d400c0e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 932347994 1250 932346744 932346749
    0x192606032103040213140103082208071401051305040203130b0f0703050612030f0a0c14010522020306040f02130f241d091f0207020405150f0d0606 65
    0xc01c0303008007490090302910002140954020340380c2ca01306074403540d444800c1d11865421500c22484000040000c900b1410107041030390202440c00640001a092900d00d20707205400461103600420300800c460006000030f81d420720f40a090250400c05050110485030619200e5140a40d40000c00640020054180e0304074680c2d201c0e501003014101f01850b0500300500701d40c039002107454407001c01c049182a550591840130100021440d00d000c9410100b0b580c1c00c02d00e551404e01c400381955200207034408100c4244502520000100b82ca08482c00719511101003c031072030f4203001803030440c01581700421081c0c0e00580110f8610502038041c40410788102c04190b89200180c94820540c1640c0d20070380000c0c2a00c04140d0825141d070f2800311544040d4002846001081e0b00400c07031481640d0421a50190712540d1030050f140e0003c50035600300c001d03210b00d00403108515030004407202140b0b020f12071190442851307080081da0740e403094085080300074049440b921420b000e0403008200021604075802 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 932349244 1250 932347994 932348023
    0xb31060b1b07050a03060906060501050f0f130e070f02060c0304020a05090907170304050906041503021017011d07090501050919050a030b160e030a0222050c19260603 73
    0x130b4441c0e40c1c0c1040c2009103014442107404904200c40010158400c105a414443c01d41c884103113441640b030704140d103581c050092000c601c4020130700010801c1c0d03c112480d02c03442c441d441300c1030403c0501c0002800e1040040c100d4010341d40600500000d40c542035188804d648042d20000702070b40300c8007049441c00c4811f9001c054103010b074101500650f10040302402c1201c1c0241d07012102910b850f400c00065500b402000410315006140c100050700e0071850110340c0159600b05540c44200351050f24030201000d800200000c0384911030060751040480a0a0303002029103401440a0705020000300144078080081b40b1031000c00c102d01807035056080c0703450000c0000900072100380369285094180c0760b008039581c14002d045040c900a4050050a10010410740100503254926a941c00c1080110700300c04d0320300c4402481e501c0508003017010311900380245000318113546c030b80080550000f0b40100305a40a8100070900032001812114604e0746084030b18205090062690f0b1080424600941c00c2100304 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 932350494 1250 932349244 932349259
    0x4150e13020405030705060301050f0d0212010903030207020a050102210f04050316030606170c060a05210103020a082404080903030d020a1b030c1101030b31060b1b0705 74
    0x226090003540c0208111142a001c1e1107096640e0f40800c240c5000c24400c540d000300c0d03a402850028a400c408181031035200406c040c04143c0701c50321560071208000022008a540003412609528190000000901d005d100401f6a02203058004101c0040f040341c0340c00e01100840e010240079298000d40c2d0160402078100c8100403000196504c05c0b19142c0b0041d03540e5881d09001103a0100712410242c1441e104e40010421440c5003010300c05103500403a200c60030440e0034000c1d01180c99291a2020810440388001c0420754114010800d0b41c010542c09840ca5174401e0b005189000c00041c500c07a08084820f80007a5181d0303c0d42001e40c018403c41910070350600001900c100a0b180d55406042d00510954400c040c1280e007404d582c4003c20300382406004640c0f005051400600d400529110403d03040c0340215495201402081d500c007164060b4811000d5545402000c3c801500c41ca905074200c51704050000614182d14043d05114507803072512155412585111025010410381008150241442 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 932351744 1250 932350494 932350519
    0x20f12090f0f01060e1605180d0b0a09020114131a0c0a080d1b09050d17161518030f0908160302040b0f0603060607020d1205030f090d0504150e 63
    0x264020035843c045c50104103004808111600c017440e40b8429510b8040d224246401d6004a06110501e0042a4540d200151703054580004210301c2c0c1c1e45000e00d000c041c010a0b0752081e0710026015050910b2004038411050000482c20301240141104441149403140c4480150b0b6060480c04d2060001540b00c03071040840280421031342c40c0003016a440410740800c02c15118000300d180009185400100090f81680c050000c0c1c580341d900c1f0284144a101d02c0d00e000c94a0741d0300c0c42c2041d08030f02c0c068088801c83d203010b1130030322050b01994a50300041001c1000011401c1c00414500d110450002d010450211040d45e10b00c0e0054280e080a095180e084a200b0205841c010008040601007240070750300b0b00084c0001414040b00042d0441001030102d070640d511041442402c0c1c1007030a0070307a8003a01c8910302e1004034120801464800b0181d82d103540d50f0340740c0154070003074056001d08108082d50000440328400380d40201910b05640f40c582201c2064a80d00368100c881c082c440c440749a0189000d03484 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 932352994 1250 932351744 932351773
    0x3020f0105090a02011b150b040b191505070b15030f15270606040e0a020a120b100f1401030228020d170a0c1403040f0b0604020f12090f 60
    0x600d0f01520036611481c0100e0010140e140d407150400300200b1601d4502d036900503842080e00b0403d001c41015000281888848002a0b2070220918952081e125182030071f12107840700300031140740420107050207450101e580c0e07140f842da240000c040b094030307140504041019030740070302040c100703846a0400c807203414001c196414a0848140d80c0c0031542c4800c003014440c00b01c28000303000964407840380608403941c0c0d01801e05c0050680031600c00402d024040b8581c0060351405110360141c1006420007c1d06400c03450700b013140c40005080f00c3c151000c180300030440481a4465038003500c4100040c40724000700030307005901902401e14620104440c40421200c088109030890881038410f50890702e29030f66200c002d5030843c83d0008e0782c04015500e4000a2154095508000d030782c0581840c1c0500403003580d407103000c0c1c5c5400c240c504680a4007005402e03418040c5208444d13400c24011503085107003e41005101c081441080d002c140080c0c151000606980014005103806540d08070503217001d14210002e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 932354244 1250 932352994 932353003
    0xa0c020f013507030905150603030418051906080304060c060618090b0619290310091407080109051819030909060f1205010219030209180f06040903020f010509 70
    0x60b02c980300a085070006403058828060b00d0041a0408013400940d54888900f60010300000c2c8100d0701440200070000f51034071000e203011446800c0400004440c01c0100103c6503042a00c4010980c07141810414401070901108131400c0324400d081c001110700d841e1404c20081c12240c0d0000120441034101c11081c43c5076034001c1c00c4900d20811030050075564000812445014064004004501c40c41c4280070b241c45c0c1c02c041d0050022032580c040c4068080c0c090710f41140d0700861b1604803007500c2074010052404d40c0c4c0182450203503419207200c0b661503e104010301da248148200c1000c20380341d50110341c603070aa18007101140d4001c07100380e5a00b001d04010b101d00801141034103c001400c900b0000a20a480c0e04c80c02d0300342c40c001c1d500e10b500c0e00c0c9002c20030079105201900a4a281d582041103c0d400b11440f115105203038190f807030150300c440c24030341045845a0510308941c0140c0e865000c201c2100c940842030b030381c008000c0b100095501d00c6030070b04902d02950707a01c482400750328160601040301e20006 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 932355494 1250 932354244 932354327
    0x307030c020f011e0e0d290c03010308091c0f03050306120318040c11010e0c040f0b032d030301290f03044709030a0c020f01 55
    0x2c1c0c0c1c01c050440024011507400329222050101c02c0c811902c48601130f4818682e003054040e00500640c0b990340d80d51149903d05c0401d4580c1d0407151020202d007056041840141584030740c0810819003590314540f5170910911807400c2140c03003545040188880100c4103407808045c690031414210750700c241d46c41c0280035580700b95105403081d804c40480344c0d5410400004c03100310b0b03101c61100c0342d001c00c444c1c4148000f80018012150604c40d0541c04104056400d104408a2581032801030030249424001c0c0022100317507120940485040484d030304126240003a1084030513141c9080480742c0036500d440c04005403404101d0b0704070760000000000d0740035030144c5001c00d1f64114800034610460007030b4022109128040c01141c0b8210f00740000b50100d012814440b41c491416460b501100c03184480802604020030040740001c003203040b4050101040192041d4440641070040d07151021a0402a007011031441c0000d22810258800c0fa0860f441220155490040c01c0d10620031014800000040c112069 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 932356744 1250 932355494 932355499
    0x61f0e190c110105010f06021b010e13020a0e0603040b1602160906090c0306120303091109090609100b011704080919060e0a060503041e322e0605030307030c02 70
    0x41c0002ca0f21031254846c0340c003100c119800402500c5c0a4502018802409183c038a060054840c41c0314041d444c0c59074610220fa168403001039581041c400040c1580f520f01003058040c10092041000003401c0d0740a46402031040072031841d42c0f80401034204c3c64410100c0ca41c0101014002001500443d6500241c1c1039a0071003030709100307004d1003000880403034400e03104204041c2c400801040120380a603105980944c003400300b144004034040007040b04a5002d403007483c8254003010800c1003108080c803000c242500700e044280801410100002d01c040d8120b402d17511000c1140004c1410000802e00305d5924090251400917014090380d01308414110a1152030041a20040348900610303000d85010152030340c075107506007943ca8540390b104000f541c500341d65010a0600300400041150402900550440c2d0340844051500003c400d070240002e410280b2070701d038000c500500140c1100030702600c00040601d80f2071844841c0d0400d07031010741000e40c00540c150200113031070414103030701c4101d2505042c005e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 932357994 1250 932356744 932356751
    0x608010614030109081603021005010f060809060606030a0c09080604050a0302070f050d120e090a020405040b121506031c0c0611090a090509070f0b0309061f0e190c1101 74
    0xd0070240340c00d803400740c20024003840040215102d03110100941c0d00d0102c4c080e1040b45c43e03200584640e201150020381002a80700200301d81000103991000180742d012041001510079824641d000c110305020150807160080d031039151021120744514181c0c0f000704500c504844090400c1d04040d6282c40047e0f02c1980180500c0074041100d64900440d01d044230009445000c44032a940c0b20520180800708c02e031030810100c2e0944088554840f000e041c0140941c550041e0f449180400b08000c458940009a00880049060050074003010503043c11280a40707000c520359688034400a42403151154258403424404043d81260f0345d880039855181d2482110200209040307a0304000c45400f90b2144107603c1a00200d0a00248406400c4550072403450000c482102d81c41f0003020701045010b40080150a20120400400c0001000710715040b9041c9072094012484079445982c0290300d6001320811140303040041219007500c0000090140b2101504001c100c84900000b4000b20524140c50810340c20b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 932359244 1250 932357994 932358029
    0x4060204080f060702060705030703092a093305150a0207170a030c2d020901050105031b090109150f031d1015050a06080f0705120c1c06080106 63
    0x2800250180286413070f400410342c81d900c0d510111842d5000608074030401d515807040c0700002d41051910a101c20384030050100f190461b10700c41d000803100307610815040d070a0600c000d080f14481400c401d03802802c85024035491071201c0d005d4041c01000c2c1c0c0019002005050700780e1120040d0000361100d000c150f8250342e07440d076881900301070444040c003420070640c0010514030000390040720f04082c0944035008400402242c4141c2c9101c4030301c0365420607000c2d2425900c2c3c000310b10380412000c0c0944002d003015800d5050625030006180c00c1c0b00d2922804003000110310790140c1c0940504002001040e01107201001202001444d100803078000c03002181c109020200c0c20041c4035841a4898101001046844187c062030310290405000c4a9817004900c1008921600e4070815200580410740702c0c154581801c0c00c00c071400d16002451041003190a0120a0000210121041d0021050f40300e40d41c8488242c000c2d42c2d0101480050079800c94500303000020070000c19040384045420713140c1c030300c2c49503030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 932360494 1250 932359244 932359273
    0x6100e24120a0609090312020c0705031605090c040e041202010f060f0801140f071b020d0609030f030c0c02100203091806040e1c0311070c0315110a021b120102030406020408 76
    0x1000108000c020030710000349444901c0062380a015501004003c07195010f0351000441c3c207089040010135901e950901c01071102e41040d41d5116040019400b03081d00c0c0500d000000003c3c0034000d00000d0100d0618000c00401c1d030b1003508107132201e0231440b81c01c01c46c403a03840041c4003802c51903104281c40342d401d052448040185071200c3c00c1c4101007080c0429600ea03185e00c0b00301e901d20080c815142c02c8035041400034000d0780b1807048103032445111340d4001902e446181809458500d4035031300c0404040c10180340302080c1c0d500c4022401c005905980c0480781c44640c0b80103034154010405820380101c0d135905a20040441e204040380250b5082c0d0f404c011741090120469180e240000c2040c184508407012401c02900c00d50244011504071011141450040d54504c40301005d664001da8284564100e001d000104520841c1c0081704140400e51420b038002001a4880240800003101c0120746500d81c00c1c41d40f0380340c2420100c019100c000b103541e450285048002500540100700d0a803151248920080c07 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 932361744 1250 932360494 932360501
    0x906060414060f01051b011814190f080c011b030612030534050f060f060d0303200409150608010b030a020304020402091201090b06100e24120a0609 65
    0xd02e0060000001c1071081001503c1a600103d081c04006480c0c0130b5401100a087c441c0d4940300200d0400d44403c0341d040d0800e4900e4108504481d80c1030741004000c080181c4008040c040d01700d03400f2421302441070841c14800590300862010816550804400b4100d0700401c1012089004c000d40b400c00c80a40c83d00c080400c0f0804030701d07004020030401c200300c60b2040054540900161103031030380036040c00c00c2c0d291451700000c24014121025404114480c00102081c4610303507000e5510400d013001490b20900103021803d0310f800c090245503813070214801c0240e03200f040e406004400041e80d81e5460351845414010a0b0044003c0082c040c017400c0418654400c0c9a0a812034954651403411600e80b0800d002c0250710142c0103da01644c02c120013a150741742c00750380c0030441e0001400010034500f503007000000018014409486401c004601c1d18502d41c02102c82d0f00010300950b2205040e0a040b10458407007480c1d6004a078180e8800f061440707505083c0040b85205044102003440b600e580c64282d0001d4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 932362994 1250 932361744 932361751
    0x50304020a140f2413150305041203020c0a05060c1c0204141002010f0603060219020109030f0f0210050103140717030d020304081c021803030301081c050409050906060414 75
    0x40d6090540c074149040840d0350100001e207482a070280c2500044d002e0542d01100d4400704604104004102d1482d000843c00c02c0b00e081c6050502003894182c2d6203078140c1c810015a002810f902103421444800704100794400907074040e04403515400d095151803600c0d002580482100300d052055400310390094001d036002c5803820070161900009060410000f9281f9a01900442d0340e0341110340c040e41214000e95008501030b0030010303511a010107034407031748810021480095a040c8039240e40020752040c00c1801e481c40906d0811181c1c0101d0104905040c500c01070216501d0a0000100601040c1016610030b800400112004550368040c50206016030880c80881b0790414061441049040d40085901c2b92065060754030b044002814002d100611110031003215501041b00030104065000c6042d01c244100c000f5810342d0700d041440d90f0385805a03c094440000801c104a400c3c0340030303105481c0a0a01d1100502007480d2085032103544800c2203a045120b035040c1004c0c6a521140e5003400c0f4007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 932364244 1250 932362994 932362999
    0x6050a0b0f0312031803030a020702040f0c0e040b011407060b1915120e1501090510030f0206090301180f02030c0108011401030b1f0306031103060903030114030a12050304020a14 78
    0x644401101058000d030002041031240c0b008454140710740e0a41800190720623482e040005889450070300501c401c49003c5000002c10034135151100710b00035040b8655000d141406c460100720062004012500c0300c11038002c480001401241480820200e90056040404180d03900b10400c801c5480400c0c8103c100e1040607250340844406403041c84c42420742008901c43d018020512070308081e520b03850000340d0007030192a006980c0041c411011240101508039190180c1ca050044c1141c613202e0490800d0783d40248074000c001203203034840d1029049416607031034010a40118098a04104402c0040c00d00206d2280c0549090452650300420560f81601c841c2c3e50703c1001c20003a4001580105059051350b584092910003410201c8021380020003202410b69000c500a071071450310100081281e10051710070b4028000300400080008140c13030449407440c0000803500c0c2100f000c40c1c1014003402d40940102c882c1500c2c0181543c000f0000c500491080e9036400d209613545e1a0190060716044000d035 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 932365494 1250 932364244 932364253
    0x3021e09060d05100302090103080c0d020705030d1107030605010308031602030a0903061503210905060403050a031d03010c0906020d03060305071401050c012a023c06010306050a0b0f03 81
    0xd45001e0703030701c030b1913000c070812460b1801151240c0000320a00001d91044030a5040020786600e41c1300f0510503464034540303c2c001807002908100c0000e4884419018010402c070b180c29000c0300e003600403c000c01c000e5030408000c00c03072561a400d02c844030b64000c60702c02c2170346070218403c0c030007a0744000300300e0302e444c600740d07503100101421a90303180081c0c4604c1580144035514034030040041464a10b803500701000e0095100e02159280e00041d00e052026071025114041c10301003000450008a80102c44952514086020702d15001107526403280c0d0000840c0c0541c41c003a5001c0c08290002c40c2d00341075a40799000c80307108652010048099a100d8080100641c10040d81041020380d80c2d0410f8480000c141060382c20208000502400c40300c207880464100320130303107203810070310302c91040302ca0802c40303007407001d40385905e4241d003120148412680301d03000b02c41d81102c51446100030300d01c4040c0b420902d0829a002075a403420a24050300058402030040352a10444c0300480c58011841c0c3e1031404040c0151 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 932366744 1250 932365494 932365507
    0xc1c0519150915051501031505090406050c13151205060a0506030c0c250e1015051209150c040f03110316061e0806010503061011070603021e0906 64
    0x10003410a0b2102102c5407800c0c0018020640480d016030b5100e60b0314035900080c4034448130001070a440708003024003401558604240440e8980b440140c0e4820340005010030b8035101c200c140a418840c0d00b042c003042e4650842c000c20f106020f603038507031070040d06070b41c1c1d031549500001c01e81d100304c6806403490b680c45022000104850305011001e1a4000c542e00300c2c5a00300102050304500340500310000301400042000c2d5015030002c41000704010741818602e1052900d03012101040030101409035140f1188010520035425200310116150030000813100c138100d00303020407071598a400c01300342680610443c0c9d0004020300120f0041c0e60480340000d007000c401c50302d16200c03601d0b0351080000c015014081c45040c50911100c1c1240080103088580c1c0e40703c80b441c1d0f1014030b0781004441c0705060040020383d8044c4501c50f0791000640f504250120388085030048025000e0313a2040c20402030f00040d006812001440075055805449041810f1068840001c14001000014810502c0d20b6500403c1403126 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 932367994 1250 932366744 932366783
    0x91803030506040b0a140907020118260f0c01110a14030c04083301141210050109020703110604020607140111122502030412050c1c0519 60
    0x590046005000041e84ca0b4800c000300741508810b80100c0040902014038000340d050000038603900c410184000c11540f1003404003485c0700368242801400d06908400031442d03200002805c00b0100b90601440d90303071f42d5100702c0d0300d84094120074a4908030754a0000310342c108208020807589401120b564143c2a01214094101d103900040c1170a104404180300c0840c0b0300c1c000304010b8040038003011042a102c0320f00351030342128580345401603002180d03210042004126401d948800640f08680a0101c00801da0f455864800384002e1100103d061a000090900481c0d00800e50140030f903444001d10715020035415030754003054600940242040180e01c0c04512712880401000c2c070040c001107200000480602039980144081c0d550032121300e010701c02030555290300d001054890340180c002500b100d14020351240618850100804465170380c503803c03c28184049070740d01c2c0b80104289510540d640003e52405448030048403144030728810380800140a00e5451183d5900049130080c002c0302c0e404 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 932369244 1250 932367994 932368001
    0x1020403022110020d09110a2d0810020c0d0c11060a05090d03090f050102010e0d05030c0d1a04051e0103120e0306100306061703162f0301060506040819020a030b09031309180303 78
    0x803027480d0b07410008165050140040e0080e00c0c0c900c030300942c0b140c0049010030304181c251102d81040c0701c0e00c400a2030000785462454210007d0403600b050300c0d6600001c00f075510348107485c641584502028100f90400d43c0021110095861244080b40318540780c2c4016800c80e0310050200c02903034007104554a40b03510800c0210343c00000004818202032a4001c1c25007a83c00140710110111016498000181001e2040e1a4056520725200522103180351030300c034042006000c0035104041c01c07401c280e0480c0c040c0c0308041c0d200c1c4001d0221000c0d0314000300c840e103090a09000498041d400d00c03a000607600e40c484030f0009510240c1c4055807402103608001080541d01031000c603507140413225542011541442001c0030240854406000c00c101402050f007160301ca9040544074010030700044c8001200000c541e044e00914100420295041e0b000169224030164402040c002002042004210003c006840f2036152200110a180d0305c511094098400701281c0c0e401040480307064402182c460341 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 932370494 1250 932369244 932369309
    0x2070f171b01020a03052206051f0f0e06060a02061f1703030709230d020a050603040f212705040f0605090901020403022110020d09110a 60
    0x40d518a001003a400a00340d0301a018410352880c0d602040039942c0030f4140c022140c1c40340d117000c2c1400210901d001841d403903826085024002603911000030f080919803070020200b0b0440740d044000741951700e01c0d40c041011480d000ea19074101e54807010980c2c5051107020f81c0d001f1020703a0003411540d42e40b5500010a40c64100d000b002c0c00030b4900000483c2000461b031140d86594401c0995500d140c9260003404c2c0003084c0c0d02c84c825a640143d0103410240c402e482a556509003254a540d0305109030002400e160600c2c0c100d06c2d070100000041c4401c01c2030407161412580c0c852031a00c0316000321014069005a91a110304011030600c15440f040d841d17580c003400b4211600f035441e15140c0380e21480442c040301d00700e03101d9208195aa040500013450704103605035008034080c0c02545802e08542c003203000d100d816403441b240c00c0a040c10b03d481004007481b000d01011901031086490398803011104000d425104010303502180045901002800c048030316000b070b11000980c0f801d02c0c5450705059a00c800014 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 932371744 1250 932370494 932370533
    0x9040b04080f070b10050f030f07062304080c1305090606011103070614090f0c030a03030905071208030103020a1508060907111606031503110904060207210207080102070f 75
    0x4110700800604d901e550a800740181e840e1100c699402c043c1401031655044480724420381c8101d1401034440c0300081c940045d00ca46180049034800121400110204251207002072118080303008505854009010a640c001c21120b108000718440c1e01c01040320f100f40c5210000740c00140016003154042c4494100101c111002c8a2520074603032a424111a03070b40400002c041000800e02403010810402d200c0ca09281d800034005d9a00e0240001e075681c8840d4074002c0c00e140c1c0351860030062290502114004007a140040700c010703003141c0340246055009000c101d11440800b003022901c241c0c0303000340c030480130b4140e140d40e0083c3c3c0ba08001c00501ca04000c20500400c540c030640b40940c0c03881440000290349207400311948250915402400703403030b4a5103c0c8180101c00590800106034054a40d944104c030a64046010352070b9420201301030310070298081c1c940074000c004220310744c07405800101e0481c0141c0c20358000c1520380c600b80f8242d104002c80505500d0850340013101080300100241001c0050 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 932372994 1250 932371744 932371747
    0x30206071707060c081501090509060d121e0305090c041d030f030a060801090314031e040f14030f490b0d021806040603060f1a09040b04080f 62
    0x200800e05000381d01c0444119400e644801ca44c1c2c4495130004030a0ba0440d0a42c4a500ca107031882d800000d002c00705a2144a1060000714040768a9031101d8264546c22504142c250003601c3c0c2080b00907100400080c600c0c60404501d00420001c503110741300c0e080c004c01d80030018000348000e04003044043d1030380800103d050b1041c1c0c1c456000e806020070060502d031b82d44403541522442e004c0801c0088541c15270001000da41410b0450f0000b0b6400a0325a0080c020601d1103a20ba2b1100b540c154142c103440402030481c0d00140f0107000502580e100c1c581e464500c21400d000c4214244000b90b9100e0003035030100640e21405002620301d0034421402d45400c040c907103940d800c0c805040c40011141c103000758001e8100c007078240211001d13081c2c43d0190001c1e10710180c410526424044d40071a01d601e040c100340c41d08840c041c00100d10a55602c1d0409001190480300c18820240d5a0081c00b00821102401c0c80d08018550b000701e4245c00c002c9141841103802c1010814103541d2340e100c665803680009810301e4007000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 932374100 1106 932372994 932373023
    0x10204060e0901051f0f114305060d020904020f09100f0807050a0c0c06020106060917070303050a0513030501050f1f2c010905070906050f0403020607 66
    0x403484c10000384000114103d075038851013401c20080740601104040c0c0303040d01044030480f04c4501d0407a6000d6072001c03402070320008996401032302683c5110030b0800607403a0002c0034295071701d00d501d009443e01c00203a000804990101102c1604517801040060303c80c00e1500c40003860f00c0540c184035140d0100200041e0460400401000801100203034402500b0301c52410000c1d0282d002c042c680402e1344800019010304141c0c094580025205100080e02e03505204944d4078000210707000d04800c6085460403601070b44003840510a010007080500310007200c80c41d801c0011801a00005281d051058110200e9800078101034a81ca41c403008074041600035298481c21940d41030721560f816403101c6580c08084003440d50780002511300500020380000b00e0740140b44200180d90311144600d48900007611603008008400d000c4035030500007480103007070590040c410140100a400356515 = true := by decide +kernel

theorem cover : BRFrame.Cov 932194244 932374100 := by
  have h0 := BRFrame.cov_init 932194244
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932194244 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 932194244 ≤ n) (h2 : n < 932374100) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
