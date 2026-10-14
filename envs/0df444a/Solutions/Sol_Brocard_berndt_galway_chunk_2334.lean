-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2334
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:23:43.651118+00:00
-- url     : https://prove2.me/submissions/a9f5d5d0-fea5-4b68-985b-1298ef9a933d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 419604316 ≤ n < 419784172 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 419605566 1250 419604316 419604331
    0x10605090c03090601060f02120c0312250507111009080c0906010804150912090906050d05030405011110051e06101418030105090c01181a0a121509060509 68
    0x84561b03e001e604442c0104d044024078190b0051001003501000c10000410811003103e0013107965008021500e100d10700014200340302070800c502010fa44041099003002c200a29181c00b0751a212981440070340702e01001841980302c404003aa03066502d4015207010212034106044ea4017903540b8600384030040c0f000b112100c2c0060322100014001035052458165036240d0005c001441114680e07030020780e0340d001590311000c203402c0c2034200404902c44c064000504401d440c0812404480d80d15590340340624090a410b00003508852285c024007040040c0700c0355401c1409104c0c80c24000d01228403d030780f5000d07034641c41c004600002d202d800c01c0c40c1816010081c2d941c501c0201c2425802c062131641209001100042c418130584540e0343d0240035050140c034499004d0319161040c8000585001740303800304003503080c50103042000700c955030030020400e283c960b2400796030307508060710100c0301c51845c00d640c104014a0f00b8905980ea01860f000c91080d2400e6030380420201c1e840b5030401c0403010342100c11b078 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 419606816 1250 419605566 419605573
    0x2304020604050108040f121e090e0a0c05070503040e06040b060c0706050a0c050105010b030604140c070f0f020306040b0f01050d050a061a09010b180607030e041e0e010605090c0309 79
    0x2c00007540700b9a03d07144d015019401c582c803944140d03680c0c0c84034064644458800640f0120700172807001000d00e2001184c0003903041c14030b00e40e4540510350128203001444803010301d03521810301250a0281c1f0423a25420303803120540b40d840b5241c1c0d00b82151840180c0783d85005a01e8021085014149501150260700380d1500500c0b046141200c2143c0c1503126121000c1007050b206955000103030309010f01400303011444015a100d00e014400d00c0115039040d0642414031214034244980041542d00711188190000c403034510307803042818015640756017004004d4151240c1000c2009110020480703d0040b600002d082c05166070f1070701000304418034044c020309150489040c0c200003600c0e40e0b03c11404082d007400880c0c4202074500000340b0241d0242d01070340030b807100040c176414107450201a206d100030048520034140505518020b200d449031100b42805141d8491860011004424409202c82c0d03005200740219544c03d90310301d01901807485040e0144110801082d0000411070999100d01840c6004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 419608066 1250 419606816 419606819
    0x108210906070b04030909020a02030306102c1f020c01020f0106081207060b040608340e09120307030207031b0228030227100305030f0a050c0708012304020604 70
    0x1c034101c0e008013030001c900b8840d1030400000c0b810501d002a0044400310b40141d500c0b840d00c80d040c00702c6405006c1c41c00c002c0280f5001403048081b04074480d14081c0300e0450000302100044008981c812090704602d0042040904580304640c1d40028504540e02013a420784440c54000c01d165400d0390024040c0c1681e5420100040e032610700305d5409002c01c980140720100e0001c001c0400303e01201c902c0d07000304640f41c100b6200001c0540044242c400241444418036400c48901c07000300780032603503500804419448500205469910402c600c111080c1c6101d1050341c8c1c2d04044030050000e40c01468103c5c00301d420901c0300104580519070324102d29402a0030718111107110091802c0f02159601d80d0f01081c1340304030740800540c031110011301c0031041e110004991300351070303c0b035044803003000905001e126220064144001140031007a1500c3c5841454595146d0107402c01c1580d03240101048440144641840001c0762a415040601041c204201002961142c0404800c00e0f0404683c0a074002208000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 419609316 1250 419608066 419608073
    0x60e0306090d0c0204110d0510080604080a0e0d0b01060207080717030711010c2a0b09010c0b0a091e0b180a02010c02010311030405101d06042603010821090607 70
    0xc3c030980f0328030041001a80034504a0188000d030030180344014059a162304010030129039000c40030180c00904001c000d00d10341070b0341c0c24040744169103c10041003041d400d540d515031120308400032800d9001030b11110942c2c5840c07000b96104558403801e0b22900c582040050b07203002c94401511a0f1802501a510301819031b254010050388140d0303414108503482d034012020900d104418007090880300300744140b6a40800038542d841101e5000410000c50800581c1c03003981c3c00502240c0140da00604000c0950380e8405030700c00511082c24040c7c84002585442c0103500034840c0800d5100c0c3c851607407800700b03840ba442c1b10000c005107442b2030000c0c1c6d03001c41c3d1602c015601034100101e01c203105160115041c1078074850403885403c1a5012a000d078032156005000b582c80d401080c0d4a444650280203203101c0104000c1c2c0d07030720001740001e0200c0095112160409445025540d05908031440407696960344112507507480c021084003881d0002080f00c0e25074842021000c0380c60b0040000c0a250500c007a644 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 419610566 1250 419609316 419609327
    0xa052418100b04091b0e060315031c020c03070801061217040906030f150b0a050909100203041202071d070e19080307021905092d0f01060e0306090d 65
    0x20001500030000000c000b409000190041c400340022074804141201139102c04907103542162040300520039843c01044050b100c42d420350350301c0013002340007400b0703d02d840c00400e007002d043d42800150881e642e01075506041e00014100b902101c140d00b2200016501c003091401c0314401e000752180c0c070803202c60110100e514260341e59a007245030540140340c19034903417904045800e0369000700c0d44504400140c00601c819403010840c6d49a8941048c0700c0203a07000b0020b80041d1850058074410110440032414020080080c81078942c200401103642c1d040a040030300d0700309045003040006220703550340800c06e0001024180c04402c00107a1611080c0c58003041502c010009030500b43c0c01030220348000106058006500b00104041005907640b1109030050003510300d10041c441221070200c800422051f2076a241041d801310b0300c1d4074407080102d29001078110035a11101c844c00300082c0d10742401020801d8102e100d04a591a445001d403000128041c961180806c449180c3c441e0094050314660f03e000e103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 419611816 1250 419610566 419610571
    0xa03020904020111100912170c0306040222090203090708030a12022118010b0307120f0503130e01050a05180103170c01050f0f06010c080f1602090a052418 68
    0x48107580450812506031700445032800b43c01d4072410710308046108840e8104000b4400e4960a41d600e5002d80383c1aa081c88440c0710180500f070003a5800645200614652054400b00c080030300780c0401e01c1d541d1001448042d400580e2080d85502903014000340d0040c0000440d0090741040c2c455040d800b0f01c1c6001700300203410071008203001242c03070540210790f54504400396205400b01c0ca000381d10408d08211583c21554034140c0035000790b200302d40901240c0212041c114400d50b2010001d20031010321300d0f0079400c40c02000c1d04000d000580c290045140000e044d202c3e41601c2c81030360081035903952a001c102c0304100050480f581070b122440188086644030b400000504851600207180071464000b150855030101c4983d007040802d0000e00441c0449255210b8100030246006222420700d52520070492048803801190444002500b507847c11042c0b032605e1b441600105422110701d0281e0010300640411034000c0c08024021035407441e10480c021215040381c101802580301441010101c443c0d50a02 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 419613066 1250 419611816 419611847
    0xf080f0f0c0d080a090302030403021005160c0806060429010201060803070c0e0f06010906030510050604060c17160308040512190f031b0c03030e03031f050a030209040201 75
    0xc00910186421010080080590070402481c0000325804000d01199000c0c106a84442c01d052000011a6001003510156034040302c072004a4a03600e8015201d41c0b144401002c0141028100101485000c070440c1d001c0342c0000054441caa5240c0c01040f0840d0254010060007000c1084880103140e94a90007078407078801070000150640c3c90ba2141c2d451078015103802c0301c078400b190805100341c0000004150b040104c00c941d49403103050850000e07086801c140168800c05a58000080c00c082070560144000e10010307202c642d5494a800e0b00604006070140d042d00c0c011042c0c0d9140c608912138604903100171817004000008594156400c0b05c0d400301c00303081030781c16200e0a840d200070380002000500526511300503c07104440c1004010300b624680d02008800d0500c0c201d86c1c00401710454013802a00c0116103040c40b200041481d040d0b006085203041441c0c140f1000c010088a0140c02038201220b16081c1c0e40c05920310f40d182c08121852407203003c005d4200380043c011500550045101c42000e021 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 419614316 1250 419613066 419613097
    0x100b010801091a0a090f2007020108090109231501031223030115081e130f0f06060906080f0304060305040f08070b04120314070806120316020f010c0f08 67
    0xe01e00001655013845402c200e1441d950742418540201d014800c0114901c510304002e00d20841800c4074940302e0041c0c510107414041940c0014404107401e5000c1c09041c1d60000e100c054540040500034120962a07002901520070724050800e204c50b004521070480ba0301200380407580c0180002190300345646c42ea20100341a101d500310b00c0d1050100042c40c081c1040b00222403504110000040442034041c002c007000101b94105c11600407a0780380c0050384881d101c1902c00d20840035181201c1042e90341200a8255099887c1c010104201d075081a0100c1d4042c0b441031081a445105207505c0d83e0708002c605120f54001c00041100f90f00a4000c00d074042c0c0030740f00e0580c580d05a500c921919500290046031302c8101c84040104111340d80c003072035002080c40e16081207402c0c180040f07184945c3e0007070213610500c1075507000680381c2c0e6160044a6802040e98040e0798403059040d0100c4103100c0360807401c03071180d49201000300d2694858203011031100e1300000c0900d98254030b0340303801986034403042030211400d2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 419615566 1250 419614316 419614361
    0xa06020c011508030c06071803260a080405010509160e0601050c0d030903080c1920010f0e0606040908030a090204060e091e010b01020d080c16050601030302100b01080109 75
    0x280e10303000ca10020f08400c8051a902c01100f5652820214010508030602c0400d1000b20b00500c42c00031101c090f40c2c0d0044110351600d4094203004c80490131071342408042d0344001000401c940c1d02826450243d07118000900190b125484100d841e26180048640e005801400400407444900c440c0341d00404181881781c9172411980315a810101c10302c4020000c039444030013410405a11107022503011480d1010385003004481c0c81028410f404a404c00420042c00240d500c41e56081c00f03a115036503c6141c0e008000d54035041d0351300005458085c60030b01d250b0007800300051f107605050041d501c0090b801a00c00c0c0c519a11580020010540e91000ba41c1044e40e908010070303150b03ca50381e0280510900b00c01040002d86400015103040502a1501902d9050980104d1181d80015600f00302e001d6506181000b551a00c400c00362a0182c114040020302100240c4410700c4000b150350741c1a640650309551032003640303d41520644072010308030b600042001004028046090f880100380c070148200c0d4a5111 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 419616816 1250 419615566 419615591
    0x1c0b030a0b0f01080712030e0414011502010e01110306120c1503011e051507030c0203190201140306011b02120d09090f050402090601050309072309090f0a06020c01 72
    0x286000c11201c40c03541c48144506050112005401051084001c0c4a818140b4290054001d07a000000303040c070a0242c0014034940d120342012401c542c0910b1520007039039407845809031501040344c4170000b5518104080352064018002c0003440c0b00d440d1112461911141e051024020721032400d0100c03802041651000c40d40e607c0d0f00c010844000440090f01d079410040c2c46940e0203400c02425a030013006140410494448000132042e0103010322503075032200d03410b0806907511007040c0701c002e50501842c0303001c1603013030320661500920314000c0e42c5000d64984a48541a45032009448250101d20901054111203083c1c03281280c40c0c0e032000d40011a10b9001616140c604004800c0c03540205402060a01c50311100c0e11610140640c0f1090030f03c51800c050300480d06026010300a14104540000010052201000520010052a500311508074010014080f0f04034203880c2c40c92145560201154041c44000341c45815003451034090500d5280756607510f002035000c18401c004075502c8590b8030856 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 419618066 1250 419616816 419616823
    0x90304030b0c040609080a151a0604080313050a030506060f04020d1a1c0b3709030909020702130504150606110709050108210403020d0f0c09020a051c0b03 68
    0x2c503042c0740d21645680c14940c2c080e000c07041c0e580000260381e101a0059010500c1c040034005400302e5424006080050020b0154107032030031036480e5411441c006000280caa42c0080201190114510303011006600c440402c075800d065440058125802540400c981d450002209800302400610040c605172100181ea025078a01c0031f0406d0381c40e045103035010a142888241582d10148030740380365902290030750b1649610107029003454131120319600c10f45806407402c0d000c0c9540c0341001000c00c8000d0342d001c803484050698484200d00265038104001119038250082e0380c3ca40d036004051184c403040400100006240040003901c155101c3c8007001d00340e06c2e980c030410005c0c0050750344008000c1942d81d90189030644a07800400310a290800400100901056041c94462000c06010b00c1c03084c031201403d9207000315040a98031000c02c001d003a0421002d18011303010940b013210190460340d40c5003080c1e0300b00d018590b131960200c0d10800850b050008050000001c94030340500c0092031820080101c0d26 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 419619316 1250 419618066 419618071
    0x30717070501050a0b030d08040503120c0a14180103020715021303021e09040b07051e04030302010c08010b2208010e06071b0203100e100f0b0a120803040803090304030b 74
    0x111044000340e2481030041c2806002e41c40718200c201031146040da500800d039111049802001000400404241040030510894410034404002d03186141014401001d060f8002c0c010b00000c96480d08150a5030a55841a51402c410f05010f00d21500709a000560213940303c0c0c1400c8447d40a609a02c07081d1040610140007244080c000d4030301800d00314418813500e01d04402da4005d4001c10707024040010c0d6600a102580158480c207810b0080d254280107a03414042d0740c0c10380020500703508909034205602005002141e0081e8024028511850b40540b1114021300581c2d815007820400243d0517428401484100704000c4034040c10560782d50001c03803c41d01c0d0394401281c1e9802090034000c9441e8466028a040401c0505010005406030700195882d51000380f961021a2185d0b40c12800000a10110960300c0810109200035400d41244100a10301c044825210f0801303d00003081c9a403080a5200c19540d0105145240d62181c2c4c4039040c140d000200846801c0c4010440031002400e080d00e07050 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 419620566 1250 419619316 419619353
    0x2505011406010210051303050c030f072919020a2d180807120606030210020d020106170304031104090c23010503060303120907120c081203160f020307 66
    0x100d0508003035000a0402c080c0e8403000c8151030500c41030115503002c01040d1001d603a4181400d56540022120047c00c41c00364100742802c500c80418008280b01400314420456084c40110314080308a5450b560405001641c143c0344003030b800c07600c003401504103900400b01c00c1464203240601c0301d140b42440001441102440304007082e000381e88812150001c80021602c40181c0095001c0750401c04101e54031201440707801e40c03021114400f0001d02c51281c1c06003001d160082c11110909035080006540c1e0200704400c0001586080720000c0c0745006060a14034506102021f10f02c1d041c0f5644030381116000c0c034120154800d07a130344500301c0000e40703185280c80100a13070020860892046200035030001c201300e0340141807144c204100101c0e0f42e400300449408090014140c425500c0d0a00c0300c80c0741000503040340001074000201d09003401034414250040391001e40480d507040c0c128400c44049401306039081d0f842905171b1901b5480c1c2e50b010703a889060098503403040380d080c07815075100c6591180c09101c0c2c50 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 419621816 1250 419620566 419620601
    0x4050406090b0405010506070203060703050a110301150f0e010e011101020c030a1d0405010f090e0708030a1701230d03031404080a08100f12030507051002220b250501 73
    0x5402c6410180106401030400701c8200d802c00e51181c0100740c948070020280300805654400003848101c0d035a101140030101c801c05280c6940c0c54001483c6d8a182200100c4049100c070203c0013842446007800d10392407001a910380303082000b0540107458224900e500c9403540e5400740302c001c3d200c200800103400e088007142d88030f0400c540036441f01d040d420705800305c00d07018074100001444285040c0011320100d031007042c4002150118000c410b070a188441d0090f952a00002560750b40041e070007508034a5582130110720082a92765010301080c1d00001040b02310b90381a0346081819a131425120b4146007900a0401042c1c101e030841c448611140115411140c004011130b81051455004680ba0741c071161030421008814209504811032183d1441404400881c41e104030081511607400d0b01e04442d0300ca4215a00e01040c1c1c840c94000c6d420100d20f0b008200600150303202425040240101100c2510444501c1e100266050003511502680c06c4006c3c00c80c44052140046d0303003440750803200240d60a09 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 419623066 1250 419621816 419621831
    0x307050a0b01080a03050307050901030f060f060e04180803062e200c0f01020102070203030d201c0b0a24090f030c0e1f1403100513170405040609 64
    0x100145001c10b8020074010360003003034844006504034080f20b4000710607003441360b10740c250003004074041c1500141703803030480b0700340324001442030780c502e280c881500d0182d1900000004c002c2f0902c41120724045040140080c5001d0480115035000000c5412070b0024080d422480c200f51140ca10409400142030403001a060600400701c0d4411400540b400001003c0850814035500580d540d030b95103404d0500c1030010b0b1248403140d030300035411034440d1580036058035102c40090162000a000d85142c0b07103110150403034038200c0c0c4c1000c1c1c02210100c080c40300c003c0d901141848050b400030300c8a80d05407504000c0040740496608503400100c00c040c0c8412007031001e5140400360040c854441c980c8070968a0781c0d0b45101f0300008400300401000d461081d0614001175544280c07511202c0303403c0881d89100201c1e42804a8503010107800c2c1d00f41d500c0280d04541c0b4611030424003400b100c104a603c0c0d001101400b1440001401081d134404142074200b0b41242003980b6a00018100c030090b038400804142d442d043c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 419624316 1250 419623066 419623073
    0x30a02010c08010302030c191a0702040b01090e0a09020406050411030703150b0406180e0907090c2a050a08180102070f0302030a0b090313180b0405010503120a0509030307050a 77
    0x26122400766540781c0500b09524560100b9070b035080f0540351038405c0301c42d010301ca1064062104c54000401d03031510745240c0910320b45425155588039041c168020340c01e01e4008103065014203100400c4a154402d5941c25a4400d540200140b192a030120f81c09601c1c0c84000840759120300440f21100903694410380c0c1d87c281081c018007112802e20b0300c111f601000d010200021510001610101c5580b401d2250049501d07202c81e5800803c2034104408010400c0203200750075400241040943d41046020040c5000c0c0b100c06a48552040c140d041b89031442c010980007480f04041c840f0341b00d505c540200c44104840da51280e085030030030100c3d5428440302c1d521120300d540e410044100209181c0007000c42860550300425203808044502800204000e408201c41c003800300704441c1d4440380d6665208d031140c0c545200c41d14140d802c1200341210b41c02c01b609001e03e03180a106d602e0403180000c0c02005d69070944504ea1209801007413095081c000d0502c141002504c0910042c000300748030340c0252a100e80303d0324 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 419625566 1250 419624316 419624321
    0x51023030114030a0b07050c0a020909030a1805030606060c0a0506010603150501170601050c15040c030c0509090705090705210612030c0d0810090c0e03060a0c020307060906060e0702030a0201 84
    0x40028404c0e440742003103c000c01c010401c0c0d641c208a0902c0c00c07650724005400c0083ca44540120001c0d00f115009003003008036080030019160800160340e960042038011801c50000d453346d805a5681504413402280e40362404800501c0100d002c6020360b0f41140444e11140c2c10143c007640001c0100b51034050b02c2d030741e400d1604055805000c0034205a400303034203880c0034206007440003805181800070002c2e00c0b0083e40810007990980c1c500d6200606441d19141c50904101040c5120454091500e401c010500e440c040c140e962150100500821900b4940360810208000c00f0b0009014818204500851180048101a032039406803a1031801030070300c0001d1014001c42c4140250f1190828803258809000100e82c020782e00300c042c5440100780d21501c0340320701500d04661040742164a0040c400104c26000344468503412001c4042d201030fa0b46540710401503548054101c0f0050304204404000600c0540c040d1403014010000040ca8684804005402e11815514500580d0010a910040c0d56090 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 419626816 1250 419625566 419625599
    0x9010914030a0909090611030a0906050a0b010c1b05030a06060f0501020a080d090206190e150a21020c010c020f0c060f092413030203060901060f0510230301 69
    0x81d480d00d00012070050505031a0b004000d2110b860701c030000c06205481d00961112800c0d250403d03035074104042c041c0001c120a113400c4542d00d0400c0001103541e000c2c0d2143d0302000e201078603140c0e502ca4042d6600501b11501001c4a178075001580e07004105a1020403008505501c18400007481508040c040030300104141d00450442d0302440d014800600071605a800c11850300401044440482c800659503001d18007a00c164614a01c0080b11240e90200e075618500d0020384e2620001003404c0f207420524420b2140900c00308503880c000780116484c6802d018524504240b005007002e40030f180403403d507500c250000c0010fa002d40103000541206000b204c0c854481129000c2c54510740d04c40d022400c0c004c007440700d44200211042d04070783c40c4240820103000041d82d01000c1e55580c0c1e00703078614001000c0d400142e019100303030310016901402c1485504290795103640858125850030080000c40e03426600d40d64100000f030310405039040b20107500d42021071441811b081c1c4960403c0071395003810182c03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 419628066 1250 419626816 419626853
    0x5131703090316110616021008090d110109080406050408062404051306290301090b010314100c120c05090d0b061c05030403060b0d1205130e090109 65
    0x30024845a0300e0000100c03035160010804800c1009000e0401c2c03070040d20802c10994200d000020b042c2005c404201260103500d1085075400c0d0418460f0784225803e260881d0000c45685c0100c82107003041e8001d101d0300b060f160100b070021490700e51503992606250040c0d8050004510046024021070b0710602029901a1901c04420640c80c41c0c1d181c190005120b07210403501940d541c0340400d01021540705003420403900030800780810003010042e4002c801c0e1007840201301c070190040c810381a1806008490140b0380041210f044c83c1d003141c6502c0869040d450b00070125200f80120101000b05a02901d01c0304401034440d10001d07110403460000b80d030180c480301404c101007001880050798442d1408005650001c181741290f030303101d0300410340c454000030b16600948203c088000c1040300020080058a108100a02000c407080b4280141c4a01c50600100300340740030b030501c1000521500107403000c030150000d00c45044da50f9140e0401130b00016649c444007a5125040c03002484210092213807803940 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 419629316 1250 419628066 419628113
    0x6031a09071a03010e04140105090d0f02010c0507080d02070b0c0a0306061106071116030b040203151303080604020702100804050610140d050a021210050c040312120f0513 75
    0x1288008502d148414019562201c0c01d4a0129007170002e0558010248080b0030000c00c41800c040103036660f13801c5a2401100000e0030001041d5a091041c01416242c5140c0c3d11580e040c50b225613100d890035000342a80101d62a424042600401e41000d0100e001e49800b140c4c40d0782d80d01410100606840c17550300301c0740600c4641000027030784440003c0c070190700892500c1c01c44203000d0841c600e0341c00c05d20000e900c190008402003011060000041d2001c1c0a04e2085040340c01c40d0003803001448101104a404018800e4144c489001090040c0d05495200200400040ca482815400142c1454941c148040019075000420080140c1000125040003070296907a503282d14008256950488070903126001d12202e41c00c2c1c408001c8200b0034042c3c031603401000c20400b5030340481d1182d0303140407000401d5429402c00e400301d030b006038030041101c058a800c400f940c43c000501030000c0d25541d20080d1000405c0743d403410f00c1d058451580c4074050084020041100c01d0300380c1c504081c00d02d445443d8200c41c2145 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 419630566 1250 419629316 419629349
    0x8030705030a0f0902100e041e0e06010504200315220c020a0b0106030b1c111009050319080c0105010602030406030b0f0f0f15030702071805040309090f06031a0907 72
    0x20340f00100c2d0841d14016181040c0d1001f800c80c00705000d0f20025118603d0895400d076907044030a966009050340d031990130211002a030343c0d03c0c100815034400b02d01c03800019000320000180000404004e5130300c000030f00c050f03001d42171401010038402c5049107140030004440640d001c14400442c01100259040c91000305480455900c0341c5081100c10704c24002419940d614600342512440c1504a03580640c01c02d08090083c5c0b0700b0a0003002894200f00d40c801d80100d03050900103401030003040107480f0f0142c02840805c60300078010121111000064502075424002d0488148090145601078a080c0c0c2c05140c403030346007400240035202180c4e582440381c140e500e0b0b0941c40b6114080c0400c0100012107465250180800200d40c4083c3c04101c0304a40410000810421a8000414100f1901802c40c000c6100003180500000c40d10152002000a00207040c10021070300c140d000441000300344a00000c03a01e9517a51076525070602d685107a15000103510130824101d0051014030f00030311000c83c2c0c0c4125030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 419631816 1250 419630566 419630569
    0x290315040c0c210c06020309030304140703170f0705030705100c090e1605070b0103030e100503040525180603062003160201060f12060c0e0609010309020d08030705030a0f0902 77
    0x300c401e402c202c040140c4005003c200c00e1080301200120f40d0000411542c0707080101d0704545903801102d007500c002040d814810505800002d40c04122a0000c0c44565011155084464268003040c43c90100903010300034440400c0080c0000d01c4c00c0c620580092419043c101005070a40f68120304000a002d00000d0030459400c0c00084990701929590000310400b9421009485500031a00054040e00041c0004000c05401103101600e000c4116543e00c44043c221038122454031040318024000d070003c1c09603004514002010050030140c0e1009d1200b115103076803010305041c8070380184104080c0c460204009000711740c03082000f02d01c0381070162001149086001103103480054007000958105102e00300100d4408c2d07200202410030448413044981e56003800c414600c41e5040282c500c60700c0e29520003079540c0a07290008015401402d2141810301000042d07006000b0004240d0700510114060301c0000c1100005521840440c0c5880d5128105803080504942542c1c100c2d101c1c4a01d0b0241075800f6 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 419633066 1250 419631816 419631833
    0x605031c03090206041d0103030909050c09100c02130b0f0d17130b03010603050106080601320d050c030106020f070e010512010207050f1b010305010f290315040c0c 72
    0x4400d5800c0201d140d0384188007140061107594030135801c00465080740c011000e01410640e040360700a45c0c03440c940d80d481d4412081100e10544500c03a0944e0104044072503424049034070394203027085042c010a141c0071034011861000f0141c5020b044241c3d01c08a0545900d00200d04c5a00c3c1a829601d580c518001551000c025170a403098030464004003140042d4190340c0c3d810240044c2500504003070b100c2d6034406016003d08000e00401010032003660000e105940320303030b2400344040c1c0031080c15455070200515000620012407140f40301150100b150204490715030182c00d004948544240340d03a0761402c1c1e0000c3c2048840d03c10310302c1d142c11240e0204410f8059640980c1525070403518040740d0204a00884d0080c8103010b00140180107032050214801c2c0041402e005520004070389070010711411004408507002401041c00841d00d000003440f00c0034025800000d1112260031400081d039401c1550202900216440131314620b400120681c039041c00c2c00b400d07082485905122200da1815603a0460 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 419634316 1250 419633066 419633113
    0x90f240a06080c0408011e0c0c0f03050d0e07080a02010e0307080d08060a080f011d0d05180102010b03060c03101a370302040306050711060c091906050a03060503 71
    0x810039800042100803683c0c07801c660003050100000c0141417030a008102d40c40c100039010380041894412a0125035004031250780f40a50722840401600701d0b00d41e0191140d030841c18080306415614001b5500c812020000310010380b030100c008058450407480014003999080b0680c501a402c1507400f0007140d03d000541d0740f004040c03402c09030000e6440780c020a1503a0a07030b81c045102c0b0312840780c9065840c80194807103696030000103410b802400c403403004141d880c1d406c458464000780c0d080100303445805809102ca0440c000520003c9080750250001a181c401c0075541350b040c54900005101600254003444401081c80120805440c1c151a240b000a07006821204203d15440d103004904d5007240003c0728641c20a440340d50301546c00d020130060082d0000d0000703d039440d250102040300329002c0c00506003402c0314480205250343d5494180607998008411181e080113205842000311036501c15080d01074401c0340d07103151700e03848401c800400b0740e25654481030003508502c01700b40c003c8880214010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 419635566 1250 419634316 419634329
    0xc060103060b030a120809060c1e07020a0506120f060103090c030b190218010e090411120304080d0e01030f1109041a0306090705180609060409050c090f240a 69
    0x1510081c92004a81440c0244c40c009240f842d51030544e00201e600301c01d0300f60040d2198011108140e03180355032000244130b1850b2110825840c5090b86501c01c074542c000f04901c500c080c0501c1c030100da03071b80d0100f00c09402100309665900000e800b00082d030909118501da100c2000d180a0000d070905803a800380c0c400d11801702603d5141940001440501454080d02c481240004119130340e100005418416401880c8031900107419095202d05c035241c00a4401d0140d170300248071040c25090030040010f04a00050800c2d5240410b0000284000d0240080406000c0d15100c0c0702c00c1044a800060445281007020034005140026810722611100207850308880c080d1030004002041c0d0040c0d14200300c3c8101499403601c104010440760840c0030074200d040f140140c3d200d26010958202604000d0300803030748250890022400a2158581074005c1064580214162401c02c0f8184001c1f07506188200c440c12805400802072241054524921840b80d00c5076002100c005080c2d140040c00d107009a12484 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 419636816 1250 419635566 419635571
    0x1303020114090d0b1816060315090e0106090f0c020a060203060a120c091407050f090406030f0308061f020c06090315182e0c2304050906060c06010306 66
    0x3084010450216405903400411001e20000c05142411303000404403008007114502d401c1005101e00006080714600001d25403980b01503003820012401420000e6103122034007884030300054500507911603448816001d500209034a03040007078490076a0b00070004001600d11b0400c03221038071580443c1c000d182560104000d82d0781d0f01c610000403c10708164008035070128500b04042c0400c81c501d8500030840d11500400c1c442110844220307100240304444c0034001c00c1c0100030b0700c4035120482c8018280d0041c0200006109600c0b502e03a0f07102e4842000301240851600400d1203e2494058025103860164040c03821181180600c004c3d02c03a074000740d08600603c80826800c0190360188004024080c0162a503559460141d0002c6440190020055010300941807581f822080311b421080f100102007803c03803245541c0580030b2009140500001c41000038007416828080c911050b0050a0350003885000e440f01e003003c08200070810003800380c47c0301e1082040300074031070040841e00170b04583d01f10900 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 419638066 1250 419636816 419636837
    0xa0f1b30030306050604060201020304050d260405031905090a0503070f050f0402120c07030305010503010b150304061509090501050105040b090610050706050c030703050709050321040902070606150513030201 91
    0x82d00a8803258001c2540160b0100d03000c2085035056000e18402c501035011038103121018841a01c14503c240c02804512041c3e502410000d403108405603003061046040b80d10b005100c007074800898090080c2000014070000d60000c640c54040305030300c0030b00002c5001d040c116140c8441c610465004d8494240504110242c0d071520b07558a50558030b0140d401088403059161503114050241d2080a0440c082850140041800e003014890a000c60300b001d040d400740c2c00c40071780c202c0d03995030030081c4126080c0340c6440902c004c8211170303030801000f040e2103400810f600160785401403e548050300302c50301032490181c8400301641c034009001e1b00200280d84c03407428030000c00b1088038503212f01c00014010a040000380300c0340c04c07070480040d4498503440e03804110b513840300380040f41c16040a01c50594941c0c8982e82e0026082c0c01107071088c484148403031141d854580c3c1c402c1039500b40e820080c010341d0b54a594078010000c5034800d180c090524802417030300360f140921800b0183e9a103c19800081d042000148a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 419639316 1250 419638066 419638073
    0x13030c020d11191a071e03050306010917060606250f020a0b0306030604080d09140f01140115050d0f140703061a090906030a0f1b30 58
    0x410009640103450110a040d0780d08102c05003a0800c44840d020741e03481c0f103c0c02200d6900000e4a8251160031340b0003440e00281c400c01e1045900322040c2640c040310340114003103c4002110f06804542d200c0c1d140c0507200e00d03021001401c0010701e079104408c000540996184003c6000c2042c5910400807038a2684904103184a0903030341c0c860010301c40e2808144100c070003d2007600400f2192280c4200c0c0d45404041c0c540000c81d0b031a002c142d50803900740e4040e40105000880b0000580941c4801e82c48c00202d42996846072240154403e007602d03c0b0343c0080c144100250f00030f002d554680641384c00144a0380d45840760500b5044d40c1c2450400421502081540422055800580041800610511042800101d80011a00c2c1980c000f80801d140000001b0f604443c46040307032030100d100c6140e5040c20566014003000020003012258140686501c010005400c050070904441c010050092141d0500720800d0f850751a541008031028468004540c03000301c8058801e058440070b000300c9008590320b19 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 419640566 1250 419639316 419639327
    0x90501230f03090604021005070f030c05031303200904030c06020c032b24140f100507030f082e0317070c051c170706020417060a0509061303 62
    0x380101d003180e1000090280340200000c03094050b500890b00c90850500b6082e0a85582c0300d001002000142070480000109000b903542046d460b00038026030340b9100f401009044400c8140d0412200e2005400d5506403160700b640d5942d14503c4160f0300d000841c1015140036000149001000744400e400103440c80424000f0f000703403000c0c643d003624020749071242103807502c0c9040b680c104510511840c022020200010b20055000c000c80d5940a101d166400e00d00e05d0ba000249041c2003a80010154020b0002c0341c49140d6503102520065440e25103c41c140d250013004c000b0118921810002d0640911290580c102405040b03859050454541400a54002084d17a052644064801c1480d16002e4140141c00002041c4907031048451010305a10b400400c284a091000309000400441100300002940303544c00a18100341a80c526050030120707520030050740d00940180d0b0311017000040c02c0382510381c1040120303040780a40c941071243d031074074103025640c4440c01010382c440e155026061409060103003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 419641816 1250 419640566 419640577
    0x20a02120c2812031a010c05030708030f1909080306120c030d0203030106180f05011b06181505060d03031109060d050708180318120318090709050123 66
    0x400c00800c124801070355108014188401641e80d54044440003c010b88030344160001102c40c952a59034114040b8011103980c3c8080c030085030780340703c2000f2200c04030b1030ba60095071003a840f4000b41c00191601d604141416110940500d60f003904002100001a00207010b03203612000550742d001c581a100400c0e02e1500911804003500f6000d000c2c281c14903d0ba008c0000c0d0b0589600c0d8035420358080e83c601040710701c00f209100b0b000404910300e80c2800070b584200400a51403a000c10728000f83c1d250fa403901c01c11110410300340d0f0090b9803000103400400941d00c0e0108804c800d00b04c4100000e190a101083c903461707040c20020308255603214a80754120b03190043d1140070710302400c01078031800c40341c0018000f07203815910400801e818000007a40d60300c007110501c100d031110700c0207107040151840740114403400e81e0f60000d5101c902009030708102d02041000c0c2041402c5d0310441644010a00c0a1042020019107910108a1050418402e50f41c002a00a40080703005c1031a081e07129020080014034001c1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 419643066 1250 419641816 419641843
    0x1305011704082808100807080a020607170408030405030114130b060406170705040501140a030b1003080f03100923060d120c030f031509020a092408010801020a02120c 73
    0x40c907030b84a0000390301c444e0780d0b480340407003402c07aa01298440c1225540c840041c41824101d80c0b00c500401e005041101c090500b0a02c02e034405600d2005143d0305090a0700250090611640040b80401c454502401180c6001c6440401c0d2445420404070700888a074000c080a084040702c43c02050158030749071320840c000c04514105a1100440d015580c0d00c40c141407203098030030340c2820004a1018074055004920450060604902c2c038a103940304030840b08000c1000740280340350440040400c4103000100800812500d41981d41e00d031460401e1442034003900003a07403282c90322102a80c40d2105000010004001d400c070850540d40781c00c0000c5900405200043c070800c0e12400d50714040e5003012404666030b20986a08403218446502241210003072070581c0f8040390034141c10000401c655009010391503a91426012840d102d1b8a602510b8a207200e003148003000a47c0c40908050340941020302410080d402075251141182c0029070710900e401c46545090320006645505075400c000c00c8000184 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 419644316 1250 419643066 419643127
    0x7140304180501240c031e030c0f08271207110112020703080a110c010e03031506040e041e060905030d0e030909011424130501170408 59
    0x719095581c00c10580341c104040064101000841d0b8643c1da00012000308144c4030181648840000084840700b0410000b40c0a02100c1180000e00300700f06c0001c03040380070407506c1c04034212a00290080208405440070301c100541c071000c0c17010084444d03503040c5024588800c1208450040040d90f030078440c0d18280c0c3c0f00d20702000242001040380c0c3e49c00c5940786040980700d10b1290700184000c403050340f082d881c0040004010300005140110242c1c803503501700c0703200700c2c540e414030000100950854a43d0f62045003164004410440703c0010040004106c0074141d5074603017011f1521310a20041c40e0003610081c0080a0f400d005140d42c0170402d0a03c0c1083c1d000b0005100c0500c42d030400036200c0d880310b0410004507045c03c0500050110000c11031f08040340150003140168600040862054220500309501c1000c295000d55004040c1c414101700a883c611102d0f5126907004080340c800d411342e402681880300ca0001d46041182d402142a80310340c000b200c0c25034030360448030400f000c880750b01001d044411 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 419645566 1250 419644316 419644319
    0x19030c0909050a02220f0602070e0f1503060405010605091e0c0f0903070905010608060108040f0308071b0614090703050d0e06090a031b080723040b180403030c03150501030207140304 80
    0x1005c1900011605642840c400d100c2c2c481031700303d8644001d40030310b02d4800c001c10b0125014a143e01d000360340c02025140c2a00c0ca001c6603c00190810005031810380e50340e9140e500c01d008900d0f0852550381c008044003a1509504c5515a642c00f5028004100300d0f691500418807150b00702800303084800d0b00c00002c0c00d803200161144d4103200144000e01600e000181d0440010703e055024032051030007103030050b0014190b0050360380d04841005009000c1f000b08458080200b80784059600306a008a20801b804115400107507040c48070200000c00314202030f8440c080400c045503010401c0d180c07206135442e1024003e6500c0d408206ea502c00c2e2518540c01c074181c14000014400d0711103418001c5283c0b5642040c446581e0352aa507a205124020600640000e01545002c515114806e0b686c0000c064000b1905c0f401200c00100203032014511110900f402208100070540d2620031100c921035241010800180038904107040004180500d0b81450f500203030702c03001e11407a00200401d4804120880760350380e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 419646816 1250 419645566 419645617
    0x3071505040303090b0a09150c060609020403050f0109120f090b0d020324030303060d060615080609070309030f05030402040e0609010c0e030c0306060f1201060b19030c0909050a02 79
    0x6a010784803c2d800200001c1c0040f034081e1a410440780005000d5030b81c40c42c4941840c1030003500b24900000d80e400e11840c1030105002440300d008580051044000058070740e450b5003455400c1084124005e61140d01d451220b200040c1c031114a151107030b00c646402e5800c94081c500c1038501401c0d5400210b0700f104c0105910b034180311550021840755072010040c0114a0780b01c0b1507100e014a80d4900c0550580060000811a040c410000544507004240110707281e40d84002a800d007a507002c08a80024101804020302410109100da40050f41d81c07508001038400e544008200ba8141c9602e9000c0203000408174003590b81c0e94208405031018203003501c2c1c3c40d08203c01814000c28030701c400d44002c1000348120074010318001c1313000c040028014001d0441581c0d040d00704100610045841988484460b2400141c10002d02c602c102600800482c0350f0740750200e030390f440124881c801c04402014101390700c40b00850fa02c510041c0450324810400b2880e5120256100c0190040402c01240006040c2844614 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 419648066 1250 419646816 419646827
    0x905010629041422061a120103030f02010b1305010504050c13050f1807020a0c0621050705131d0a0504020f010f110d05030604050702060c0a0e010905040603030e030c090105130902030715 82
    0x125608881189071810aa03071810780c0a000301380d111f031915448a401080401c2c0210828074851005200002c1c110112100080c84400c0c00c016102146540d040140010b040a10690360007204040006043c0807801d20b0609070f0100174060940a07814000c801500c0740c80700c0d0f030f48800d03400103031000000c076140c115402995240403503810344112050350000695640101c0c0040f101c0e403440030b0303442001c0403038000b20000745c00c01030003202c01c110f000c00c52420010078071651240981040d0a644405511138100d420360000050008c804843c03900c028400141e84015082803118401c1c00c007500040b5603100f0507504500e580305065514081c0b220070307080c2a035100005610a04046404101c581c450350801c9a98580888084140540c1040088441400351210b000a00300514041204c1915a00440c00795016a4022008a4034280e49a0f2062405101c0c442c4580340503100e4500035032400c0300044611186400301c0c6031050340d803e042402c2d921b0034000e4a01518032072a00302082c05524100506 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 419649316 1250 419648066 419648069
    0x105090a261209070501050c2503050102040b04060810060c0b040c0e16270b0c1c080411090907092a1e09030f06110d090501062904142206 61
    0x20f15014482000c07030b4940c0108161240c01e01e0150060018038801e2610302c850505403540c8021120f428000000054802d0000f1b0010300b80e41480c6d15200e900e0140d0240c505a40608a1495100f40785001d10813140c6c0008a116000d4004c0c500c22a02c1e119420300390004002e9800c9070004c2c0d0724420070803202200403d1580c601442560381e40311212811070f0305200e501e130070744c4090450b281c080d4000c01035030000b01c000d482c0714100329099070390741684402520f0180080001050100d0416001c11050050f801380d0011842e01c25035041d1080d01d440b039216620782c8180e001e00381803640c0d22a01d510f00b0000071031110060f82d004c1d081e10140c1e03488000c805450144441101c2c3e859841e07070840007194500c109220070850303502452445034400b1654544014007809551201a244240090310210610340140715805005500025034542044180000da100c1c40c42e108000308020300300c554284944000702c50482d48078039000d8400d800c1c01c00008100c20800d00d52031041c0e560040c10982c0e405010740c0a40d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 419650566 1250 419649316 419649331
    0x20d05092202041e031208091e061519060540081203041509050a03080f010906050915150414090a0c0519030e0a06050411030105090a2612 61
    0x401c0d608440418003074141c05800300412420042c86c000d100e0500072a00c13217420000f601c041d240d0001904095010304407419101c148164414802d02c02000d4030425003000401c400d543c011000040c0e502012140c9549120713034410044001900c50001e41003071070242000701440841d586800051400c0102070940b110150004011894002480c80e4006094110301071540f110310f04558850b1a1700c20041a800280c8548688400903c4002401171000300d8400b407203602c4e10b25550070701c00c81c0580141da0503040302c00c00d246031040620440d41d40e070010580c085c80140805a440c02c40d403020560701d6021040a0080c81004140031a808108a00c0d030300d03c80c00295081501f983e60610004242c458001c250004185c040220503018007050710081d0b814201810003203181300d030b2000168640000303080306a0707410b541c56060200b000302460650f00181001c400a01040c2403072603e2710b8640c10848001401c000d002000382880741c1810146034030110805040b55100d10400354051004a012601d0b45c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 419651816 1250 419650566 419650589
    0xb1515040519080d03050408040e070809060703051003140f0102040f140102010603150f150b0702040b0a030519030e04020406050406030f050c04120201030e010906020a02120a020d0509220204 84
    0xd030101c842c0010510201c0c0d4004000341640d005000d4160020075001c1c20691301c0071010030012441c17800e00708030607000d6080c6980781d651620b0892145401d02002908000400d410700b8140030561085000040a5030781000b0303004405c5c01410359031460525049070114040d400480c0020b880081c01101000311018581c4030179807102d031200120308a80701408020023038075001c0903a500f201d0180c1d03c812040541c925001079510f0340022561700381103013544520080c090000c2e071001141040e0080800c0440b043e540014064115038030580c03100c074040741e90001280c42c00008018503204400b030104041f0054000c41d565a00e854005040e80d0250082101290511140c400e16407824071a140c415910311941e0f60805041000e8008404980f200c1a0b04041d11450040a85042840740701c62042c803600300180d0701c01442c803001e03061005009624050440c05e0010071718154020498109240c0c8a1501d40d0340d80b240440042c1321800c2d121340000c00054034000c00304111000f81d0062040e2007070007144 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 419653066 1250 419651816 419651839
    0xf060703091a0420040f05010305160905010b0415020a17071205091014040902030f010509160f0c02040e030a0903031d010c06050a06050904211403040b15150405 71
    0xc1d0001c21809590062104c040303010f4052401e400c050102c0f0004400400c0490381e612200300c564242c1320280c0007584c15420070074445002c40340300ca00c2840249003c0314113002540c50410358200700d00541c41200c1d1304c00038842030203400038424421510550b51101240e10032280c00e444400298120b10012100c0c40003000c02100194001c1d42501d00341d440c001c0011400104825080310071061040e1160103502e402d100205210740c450025510403160310041080c950700d40b4042052880010b020f03034040c0c498052403464059480402c040402616007040a003940140c070200c1c00400007440d00803168000803801c5c3c0816644101c40d44200d90180d65100716504103400c5a00002004031b502c079021900038903030b110000b0400d8020640c40343e110f0784000740855540c0301080701e07008205c0d0304640c0c1d0b03000303001507103811700300b280820008140d02c0c98040300d05504400c1c142c00e640b0000e40040c010903120000a6401c0c070081c5c0340100849005030094008540910004049030010b010b01445003996901 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 419654316 1250 419653066 419653103
    0x12071205070b16051b0309041b0f14090402041202010e010f020c220203070203040305060a05042f040c091d040503030103031b0206040e0108060f0603031b0f06070309 73
    0x1601d00d036603000001d40400381c4801540a00d22082d0101c0c0009010007400300c10810700221000c010441860350255a032262004204402c90364000c002c00e84182e54141643d05443c3c1c450156072806d0103508209510a4660380b5109050042203031103039005000203001b2440003030301d05104440c07070f101381c0714026209610320055403540355510882c40140c0c8065044d008514084102d1001d001c0b8402c9410000d48848080100360b034022100d10015a00014040003000001c00c40c02c0e40c05400203031f0400c69800c0542d51032601c50b044610030841c00268072003464001d01d20320001140b8400c000e004104a106403003014100032001d00c11200180c02196408150390001120306200d0740c0d006000d50f1860f03007142c0e0151240241113880c2d00401c5000009080180c0f5a01c004101816048298030581c0d0300d0b03d4203061030300400609445200044400f0303c0f40a84000003501c50032441c03000004600e410300540549001745880c590540c0d44112014400941d42680c000c541e0701307002d405403040c454014403 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 419655566 1250 419654316 419654327
    0x21f0e032703120d09020d061104050a0b0c100209011701030b01080708150c070c03080d1d0a03090b0a0e06070803010815070c1e080a09050406091a0d020d0203120712 73
    0x1140c406410f420030801c104024264040c541d298402020107800f101662103200c03c40e1034520000d102e18000040501c4103160000041004100e2102f030390703141c01c42c0d0052507501e41950301c0100003400d03004103041526a004204284030041ca0b281c50030b01ca5a521b0800f11a00c400030302c541c00c220300036000302140510700860340d04010410101300300590384406485900c5940502c0050b02e41001c1d07a41301000003504c400050840032804000841d98114010403c05c0e045031a031b4001d031035644080c40c0f2000080d0004c1014007201c445490298445044480640d007020724405c2e95644254000b1341e407410080c51a001c2e40c16503000740220b8481d002d10422840700c03208161201c0002c5001d09950030002603158066480e504d01a41c0d07a5181886946e4440d0400c0c1c22007407880c00410b40085c018000d13800c080c4600310040040359030030312000304a85400d89181e544c0c5c610f1907005020380302d82001035440700045181090f80c09011070f0381c04c1c03900301594001900b002d0b100716141180342c0c2c2c15070021032141 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 419656816 1250 419655566 419655583
    0x10909020a0203040b070f14030304050c120a06110405060c0a0611090a0e07231206150703050d1127091501030c02010f0c0c0b1006021f0e032703 64
    0x380c000714a407904003417000b101a04030000440340c0c0d01c042c4402d031000400c41503001074030640d090021030712410310b45016400d00c080500f1490241004581f100c603002c00010b00b1504498212034009101008040c0c200300b1445a6041030ba0070110029440d0300006000a406007180d0294004112500f884806210b0303521605550b590300c29000e60060003441c0603a580560414158107001111500004c0c503d0301c0c82e010300c40c00c03518400303001c40c011040c04124000d0701e500510864003c0c0844201001908981c02600d00250400c00040f441411400c820ba01001c080e4004040c4262101d5043c40a150400310310301c900030640342c40d520300907158280034030458020002c8030115006180d0280046005004280c600002c56480e0540f41c000381165118629a50505980b04640b402c01070138181103180024040f134400c2c0078031343c4041100c80c0c0d01003100154801146412a1580f003600c103490054441d44084040d03a02000440038180040062001c1903e0030030441107001640100c1055155482c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 419658066 1250 419656816 419656837
    0x108011508011707031b0312030c12091407080703050d0503010503030909090a0c03050d1d060702011421010e0105240912010609050618011d060103020415080601090902 74
    0x30041c0810118800c0405191a500d0100c9000c20b580e07460302d15a64041400c05406e05000d01001c0c0309109484010380c4e07030122241000e105401c2c1c0c002000300300510040314005e10310b0340d5001d803100f00841e4007801501043c00c081110016904c3e800c0c05c68503a41c9621044409120300ca18628001d4004d805590403500d000b0051400c0036203034001d00030006001819003609000d0700c0078034000182102882005540198020a034900c80c0500207041080520b800c00324508035040710980c603a03128001c40b45a40d1342813804000c001e500d03c3c0c52003414040c2c00803404180704440201401d094034280c9081c1214030360390b21303141240d03039500902c00004a0300270030380d01c016402c103100050521030710f00810f0420070144c0307402601c10321031550b0303421241c054000310b0040d80c62750140411b41c508403081c1c0c80301c1c0c0c0912039a194030b949402410780c0002e00c2e066070000d00e01d8040300002d520740c1c02541500e00412550003280c41c03003c0c0d8a80c0040c0290821584a8086914500d021962000390300c2590000c860 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 419659316 1250 419658066 419658077
    0xe010e0d09170c040c050f0d0b09070c080301091808030901091712150102190605010e0a0b0d06051f2601020a0905040f0b040e100e0309010e04050a1b0e01080115 71
    0x50782e801d000c0600801c0d220341050000801041005140c1c0d040100b140940d03808c000141c0d010740344200540702e040a08000708000d0710f9074440e0042030302201203034115050240300040d203405d0f022030244c040d4040704014005030700100030001801419000407503201d00c50940201c000c950085a10010301400d0a0568951a4400014210352028503c480140300500407035020440100110b0015201c7e0103040f142d1580310401000719140c83d405482e0010300700d0350140048a85100400c0c0f50402244011382004c1e10380002c03814002d06006000089103070740c22881e0180c0d44403200146442587d000354652001814800002c2e02010703c01d8078000201540c0b18122945001d0401002d464000010200d10b5a02c0054402d00e81e21351107000c144070383c420060910349400310b0540044410340040c0724810340041020030301503a40904542c4640404441c0004e81e40c071103244100003800e00840c520503010f203516800182d580c11a02e07441b42c20409980b13541c1c03160b032243c00c0111800403a202130300100e003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 419660566 1250 419659316 419659333
    0xf1b0911030c0a0e041407020f010f060302030c0105031b0301030f050d11060112080d020a0f110d0f0815030a0302071404090221162304020307090302040f0e010e0d0917 74
    0x344204068a04c0700030042c400b0a010b9000d44018022240988104000d6800840c03c90250f04081c06412035582c190b4504000c158550f8010a440700070348003100d0f04005000000503e4070680300c100703140b258200386040c0e80320340e12440c01105a90718640269418130801140f2541b0500c40d000072616000c1d84400740141c0e91900ca440c21740040c0d17200c0c0031241c0050900450424101d28030150401903420750760310041c0d1030402c802616640d41169854255007004040107074082c3c00c2184440c2c81441c61401100c41d0b03551800701441402503140e81c079454060108080241343c1c0c0020710748141c5100c41024002c000103013040000300c2c3e01c0500d009400502c009000f030f60390941070025881d580403500544001c00079550314200030f04219040000c0b1486844408540e042c42c03158030985155054404500d581414680a4401c1005110080c801d580310941c2180b421203e070858805030040344024000806050100b07a210300000e21030303000107501180c0c0050300f0041c00b40c8181c003010028000e0304000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 419661816 1250 419660566 419660587
    0xa030809030c030619060e04030c120e130f0f14010509090f150702060609220c0510030605091b0f13030f05060f010812160f1b0911030c 60
    0x40d002111059854001d0b10141c0c0d4854030705000803441001182c1c280ca43c1d070001000310f08212074264201c80c0d85a8001d030100000a038000c2c40030f000c001d800142c241c0340c4030500322040354404000c01c0301d40d4010a41921034040d883c01c0b608500c032280d18840003400528038500ca500100ca034403440000004401c80010411410308408558003c500c040649124025411403103141910725034041550b00c0082c010001c0c040d41c14000700b900080d08441c2c00e009030600c03520f400781e05860410260985200d0880c00e01c10461076021040c010800030b0070500001d03580d4030b0040c00030b001602c01c40d4020b4010900140c001000c02d40b02c681108220880c0a003441d942908601c000d8000d02190040048a1900800440d0410881c02c40c144d210300d00810480c50407150b80741c0b040304180c0c405500c3e648940106c01401144100fa03400a44080c40c40d20b000c90781c1801c220f40500720301200a40212021440d044210095503200400d07a00b000344248105100c0b90b071181d00912044074020070759078043c007111616 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 419663066 1250 419661816 419661833
    0xb0603090a060e150c0a0306050d020a03020f0a080d02010b120109081903090f0c0512150c070c0b03090703050d0203130605030c1306030f0f05010f0510051b010c090b07020a03 77
    0x406400000c403071300032254000785003401c502070301c6031280b80101207501e0303004a41c903004100c0644000e0340c03038200741030040e80801d00050361400002c1c0300354450a8201859202e0394290030081c030381071048403e40e80210b800a4001c01d002030b880c03401034020110f092030061050046207881580300d402c1610b401c1144410400b1201e0362544c440c10152501010000300300969040d600180c01100c0c1c07400843d140030b08114164010145d1050680c03ca03001c08607000b1070f509a002d501c084000305181d40ea494501e00032101c00440e0704412007030407021003840103038100010350f4006d80e84580222000c0d080700c0082a682d07405000a42100001490401c7c00701a20450145402a40c03c540c280c0c02c1403880c3d0099040c0c282c0700c0e000078001a9075401183e00c2400c06001c0c400e100c01c0b404504110a50412481482003034040c0900c90050500c9004600310350f21038000c458444241e404e14a886024000096010f005c0819982000940207480400c0203907082c0c04079403e0907030040541280c03610796a1260340 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 419664316 1250 419663066 419663081
    0x10605030603071205060f01050906100305180a06061e0f050609040b04050a0f05061c020603181b1305091009060605270702010903080a0b04090215030403030b0603090a06 75
    0x30507020f54207001404008030300f100c602d40c43c4544007400b001d1819651002e0403c0059000d584507454900510100d0749601000f841281c01c0e906c0c0119260f070f2910981c05070300d503803201c1d19403c1d441001ca05109002a6601843c241c8120f0705c640340303085000440c26a400c1940303010303200024205100400c501e1614600034030040c040a40003080d820135402c001000c540e01182c13401050358586410b01d86150152040940c003080484a8003240003100881d50040c1c010348100900400000020480c0c19401d400125030101162044030b0080040f0040401d0038038100b28810700400a101c1210801c480c80e0160510901e449030040403641030496215002d0701c2c5107102911003964440010507151550071240c900c3c0b000100c1c191401585081da24206101c2c010300450440e450304c0c0302403000a62000c0b00e5034101400300b8000c600da81003c00050018403010000035400b02c0c0328400d102545401e840035520070713030003528204401c404017401d200c6a0300c0211082003d40d04046107460000340c042c2d21911 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 419665566 1250 419664316 419664319
    0xf1e03100606170c04140d0f020d03050c010e0118110a0306020a020102090111010c050307050309072420061305120c03040e0c180906030109050d09060f0c0b0106050306 74
    0x40d91048680d4a400484000e0340003000040d081e8807003004030741c071070240309900060303003000e180d14007443d15095041d07035a007003040b16201d41000410311041c8a4500c450941321500140000300e4128149005056a8082c5200c00819400c11100b081c0341c050601c55066030020782a509505800242d0f0b4600c000c0000d86102175200c01e01e0312021000c00c44610203410b00c81c10a400050303555900900250094095080100a6a040003516940307254850f050303c0c0c1000c46414804d84a0312a659114103051064100c00d41000342018000440042c0501c001d14016030398440807412001c44c07440e544a04070404040509034001000306840701e00f004080c9a0560144003540c4100d034148440b40318551040580040987c000b1400380007a0100d85030054001d0100c1140c1403070320f907000c0c08403040384031000c0d15244641512000500151001c0d081211901d42c40410340d049800c0d080c2c00034103410664050400095403941c1904034003801074110003100340d0030200c002c50342d0303107011412203541d48020305a5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 419666816 1250 419665566 419665573
    0x30f050c060103061a04051506070c0905190e010b300a050304064e0c030e0c04061a090415270b13090804051c060b0f1e03 54
    0x11069505000751800f941c8074080120703400d03020314050203509041c016094070403840c01041c48489140e6144030070340c0301401d4032425243e4609040c034600440190303001c071005c0b80c1803804002515062070401c82c07c65407102070410100f400e103102c503801c83c0d102841040e04040401600c01652201c0101e0360010394400c160f0200c00c148404a590030041c04c003900300e506074000b1405200780c40e000070754070003441c404101d400800d13802d0380b148200d00501400f844555160604540041158201c1c600c04401420703442485240c801d040e0040c010000c901c51401c19000d5401100303901e241c2401130314100c3d042640c54424020700040010025071081c0002a8403d40e43d55042d0b554403000c2003864010301040c4c072075100c1000c1c0c8401700e17600302181200c1c11856034980542c0d0046607554130551046c401c0c0c83c010000b0440003500d080c080d41d1083d03801842c1d0040100c10700b03810703d5070402c4051000c02d10408003400f0481c4540d00b8450b905100d200590351240c50298403404030403881c040146240401000c4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 419668066 1250 419666816 419666827
    0x11802010206061311070807021002010e070b090307091406031c09090e030c06040b1905040206030f09070b0c030a120204060e0d030504030b0a0615020606060d020a020a1403091c020607030f05 84
    0x840345191b01c8480d00716681c40d804100070741903240c090303140c540c41080b80c0000c3c090480112210340e10360707003140101032182d0740129081d1602e031410030580c03000c2c00100404100040341c032a4001c40c1d00c04100c4a07a40300344101c0005002d10440264094204800c40c0c498022580c00c1481a00107803050842d940d40910051042c11424642002214011401202000c009044c42c045461042c0c042c0110481c11509000902c40142c4403441140e902c2040e00c6603028460721100c02c06428480c01e54801804810b01041c0c1130201c0002100410505066495100e085125050340e0300c280c2c041c620854000c2540e404650055050a44044400c02e2182c84c00618294890740c0d075030810b0074150740303085101e595010240000c0280b01c7c4050340c85078150005054500e8690001a8180b00d0008030001c0250003148000b0300f580200001c40030503074402c02808010480750310b800c1d520740081c14440d00c100001c1c819041440c41051110500303e03009000e00d07190044544098600c4850b80d4000010400308012 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 419669316 1250 419668066 419668091
    0x70203100c090806160302030c120c0a032a050c03070f030305041106032806050d0b040501050606040303050901080c091e010e0402120f1003020d0501020c0118020102060613 76
    0x28214158a44050019903011401e6008003016990741000f50340c2e0f806441401018070303441d05110071400c801d290159480e524020423081030f0244174000c0445070403120503c000300013020060003100403995020440000c4504c003a02c51007240d0808114520ba00b92104402c50b4070034030007844480030200440303141410903500c40c070710002e88040030b5000950f1803007440100b008a10052881e00011500c060850a00d00201c1c1c076a500300c0009480041030420140b25011410b0300a2802003000030011140c0e10068100307507a448004a50898041d40b80100054051414409880550b074155032880d0601e9007100c019100e01c00e003d000c0810140e400c2c002c4180541d58000005915140851849c0c4412902c400162a2001110320a4840ca006114008500340341c5804c0c1540004401040d01803a241c110066143c100f4540020b034110003156a0503052100c150010040840c0c9240200700c42302c07155903075140d24100c04c88002d00503080386001c0742161034000c11a06141701c0c3c1c8100000c0700c445180c0c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 419670566 1250 419669316 419669323
    0xa170403260702011a0603070c140a060203040c15020607050c1f090b01060323040c030204050c03040b06030303060604141f090317040e01030f0f020a09052a031b070203 74
    0x1107038204030322601040241e081d6081c015450b91000d08080c0752903103040440002d00340d02004090008004444c1c61100c244030180c2091003054903c5c00aa590590181c24044041e5000315015184c0c0e20001c000003c414260343d4031003a0382d581c503501504040d181c0030f2007111140d005115a08941c801c0070300da61040c00b11190b00c2c0c0102001c1d40030020364a0814641642d003854141d0254090501e0300c040403c8621505481c800c0c001c0203915070700d40a1340e541c9800441110603410203900203203828100400e9100403801580500e004004c040c60703e650768401c15581c2c3c881120714540001c410310082000c0018041c0e15220307910018209020900f030002d801d46152200080140060481c11041003484940c6140640c0e05550318103007850981009404040c080040c400200814115100070040c00242510120b2581e4001c1000e0404c5a4a02809002e01000ea0b50410b2251408602550072000d03944450300401049079400c1c00c5954030410040d25017000c5c480800600020010580183e4060 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 419671816 1250 419670566 419670617
    0x601300b060c0d32030f0a140114010210060b030f1303020a120c02030f03130e0402031905070e01091b0c030801030308181c08010f0b07060b150a0903050d03020a170403 74
    0x50401c0e00c2e86080d81402c440e41d6006403030000510308d851480580070904180c12815505150980e885400d0030800403490150035003002d881403840c060f00400c0d1644240015809400960814800c40d02c50440e900e900d120002c1c0c00070050ba00400080b00001d0b490303012160514854100403400c407c00d60003082c1040a14045d00d14150070000c4e01c1240b40a840c01000d0140a01591100071460140d000c240d50b158040041a440a0525905401c0107401c10080d8050458110165900e5a5915840c0d000c0c08465501c0c082c0702c1489107842161364407a4450030b052641540d02c0c01c0590f4070316201034a0000001d00344940074401410f40d44a03c0c40300f04802054207000305140320444103401401006600c042c5c0021403800302049041004584020944144580000c80010f500a40d50001040b8141d600710340466200081421094190000d1505081b60700400940780e59110400c0c0850803480b4001e02503000c2801015844000c4c9540c40d50315900a1283c180101051407000040320158031a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 419673066 1250 419671816 419671907
    0xe0d0b0f06120a0b0a15050604030818040c20010209121605030601180506010c150504031d13020903030c0a05161e0603050601300b060c0d 61
    0x4030001d0041da810000c03814418410351402810041c1c03000e0795480f061250141000c5181d5880ba4070080d0b01c10101c12001d0b00a01000b030a49035175598074a0103854a0f0850184021200032a511329001406d042c01281207a070681e0755815200b07100c00b41103003000c40c1500e038824040d44d03081c040d40f600e9440c0c072501101171007140401890303101c1010f03944000281705a00103034000e820030340c010400400c4d58140d440120500f55000b06460b07a41c01d00480d03001d5800040600050481e00309082600f40030380c400e5006034041d50321340e22032246000440d80100d400d40e160a4101360307021201d2000705229805481f4a50b030040a6038034025060b107280b0300d04101c000d000d86044d00000c51000c0070400d0b00c3c20b05401420081018007001601020580c25081c0b1845040d051645680008110317038446c039440303082c007180020b4080442c0302000c039a1400501c0601c001100500c0e19110304640d203007a20a544591080b600100a40342c0307002c204455400320115075003500021a90742d141d41074030507038001110201 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 419674316 1250 419673066 419673091
    0xb031b0406050d030f050c0c09070c1b0302011b050304181d19020103090f05010606050406030b03010207050601051c0b0a02091005090d020111031b07031202070b0a0e0d0b 75
    0x20000100310072600240d0041d4400d591604070600083d42081140034802141d00b03201d40c81e0b0b00c103000224140350107880c1700380e0f20010700002c02c0482c98100041c0006107000c0c1500d0404049413072903500c003218090001070301049145410300d0940c0c4042c611030450520031000d880c100360f9101c071038220002c140401d85442513159aa4070811110000c1804e0035061080010007020026050003c6c150740155000b904154032060800280300385d8024650300b80d0343c03000081101540d107001c0200260000c3c02980b0000382080c2c50341240b40703014000ea4840035009009490315900e0081000b0714400074000241031510705c000d0603400300d8540114036105506400b009a03640c04078404001f85d1907143c0850101703120301489299000e0722018607040c5295030a01b03010284900001c0107a2444c01000d07008030041003820354510f00300d00f01082240c2101d00c01e070648050000e25070304c00d81e00d070680740c012030b00904024041049034a00c00e0005068500c4050000700480c43d1030344599405270012200c0c1c1c0f26040c1e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 419675566 1250 419674316 419674363
    0x1b0309010e09040b04020904060b06070311060105180a020a0c080d0203100e190903020309101d040e0615011704060c121b120605090405060708070314010b07060b03 72
    0x5810550300c18501c00202d40d500458502030755003020350400a00040e02410010340004c00300616070744205500c100c024030311615407100e07140044c0401c02030b15000e150340c045c5200006940c1030401da0403240000000440b212590744280c0c1d036009402c01506801041807140d946008510401d009010f50f818860000d0ba8030320f40940c060504c80307010340c850341c500c001d840100003081d1200d41110311010090030000c5442009802d00301d1850244034500f60340400c0c001003808101c1d40008044400560306400c10150042202c20403044440802108026800040005a85998030810001c0d40e210506021400c2e10300908a0001c2c0c40040b5402c4a01e956284a0484110b8001c0c50001102801101c00d03c50140c48065080d8109001c0c0b01d01c0c001d1020440201c0100c44081c0c01880c0a04800381580c01c16190a0030565601e04058550030089114413011441e014800c1c00342000703801c3c14141e40e40c916441c121920031554051030040c0c403010307500c0040a545603408c1c0014108519a03145140449 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 419676816 1250 419675566 419675569
    0xf08010605030313181509090b0a0b0a270204061706030c1509060c01020310260d050306121f06080102040e0601030e1207060f1419050c1b0309 63
    0x40d400c98210501c40d5206005200c416245422450280c4114249400c4a01c0b02c0c0d4090b200034211040c40c0d1079010070602008240b050041c1d0100c0c3c24103000d0031900f0754548440c0c030400c00b21030501e00200d80140840c0320500c11440f042c00400a007045100c80306481c008040700342030807604141c010a0000341d54100710508038029210080d0041000c81c003525079107004800140d07500720888400e82c405200032500710120303900e100546d0941e20b10030380217641d6444c200d40d03010100c3c04e40b401204441009516084440c1c410340307003420b035a954403a004014840650030b05603259000108640d40c00300080d0901c200c051824084250200300c00000f280c6115900079402c019105990401d4905078414002006180819071840c1d070880070a0800040480038140f0160a02412203118030a29030b00203050705c00c000301c1d03500919980880a004000d0751154144c0c00f00b000d0000e48110a103108d8403410300030307080040c2d4040c136040a2040700b401c0c0780091012440412164040e550030729a000031036041d219 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 419678066 1250 419676816 419676821
    0x50c0d05010506030721020d060306050702070b0705060a1802121c050705330c090a1205060610020102041d010e0a052502072d06020c13051f0f0801 65
    0xb4010490f041c2c2d00714035207050000c0110001d000d81d01510500c00310725a00f600c40d02e0f0b0403170b808840146014001a92a41040b1014010645d0180014840c0b02da0008081da0103074141c40c0110360250240449860f2031403c1000742004c1c4c070085014215035507000380145e551580c01e00000301403d001e41500d00c1c0b50305601c2c00c95a0030310400000d01c04104400303c0010700200f20b403901100300c0c04d4010206180c42c80d07a06006201903001c0c01e41100303118240441e0204240240c04180f20032100d0030000c42c1c8030301d00607084802d0904010440c1e48000080b4400e403034004500104003070180300040c18542d68201e102c00210703220804880b811580b00050000804000c10030368000002078082c003c50a001c2d52108020783c5010040d1402c0e5007100c14048030034030038130030034000b0010309440480c4003000303114440d41c0a0381c100501c80d29841e003030350002c1c0460001c0b40041081d0001040504560040000c40c4044d107801000720007041c25208101c004058071362003020103050300c540000283c50038000151308 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 419679316 1250 419678066 419678069
    0xf040311010e092a1201032103140a1a0a090b040e03040501021f0e03042c0402030c0409020604090612020a06030e03040b1c1b030c030b150319050c0d0501 68
    0x7030a03c0400c000c4881003400440190030716211401e80c0c0304100c03000510b540c4c00f4245078880c21400800000007030087c994006800500009221405203214200540c2101c945480600d2a400b080e000281c030111140d010411200c4810285d01c48088007400041c4061029081303e00c4160b962800c805040c1040c0c2704c2d000000303500c1e10085162906100000c0c2d6079500050000e04821010411250102e00c6030300140100150071044030345641d2a11501c400c82d86010a0800c0812401400220412001449a406650068040d0000d020040b0912001e0008010140d0700f2003010480065412018459100140041c0d015081854100d01c100b10b66480198000000c042c180200d680c540a40441207e04494450380040d170380f60442e00508200b5a100100802264906003a091100c1c0030821980401d008941d42000100b512400540c2164041640c0c00d40101080380b08450070048600115000b00c1c5a040c40b07455601080122021f4072011a44001d41410209205c001981e10307004150 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 419680566 1250 419679316 419679319
    0x60c03051029160b160f17150102030403350703050313021305040b04050f0708070504020a1110090506070504030203060a0c200a05150c07110102030f040311010e 71
    0x141c07071882c0084058038030724807010700c05040c0900042c0001540f4514514000242c1d2082d40c064081c9081d415021a19a03800022004565100b00142c3c01a200301000303640302c1040e52034a515038079081c60030b10402003100307540782c1075110170030001c0007003251284200c0c0032800241c0d4010001c4101400030b050745214212002040d54244540c500103a04001565882195020700550401c201c1c0005940342501c030b40403910051070403082c00240042c0e8000d05103d680210700f2101114190a28241e68541c644907241c0281c0007028140b1851403e5002003107407c26919080d050840b0b215107450508940761038030802d00c0e548010791010044248000c640c1300f42107082890415140d43c0110f41c0750b06005018409007640c50302d11400180c0110300c8060740034a00c4200e10480000c1503e41c0c1e541d0303072034518103480030312500043c202404500b00c40c641c0b1910350740c1030380d60070300056550f0401c80841700b403001c41c158082840b0202e0307540c070f034034000c1c0000714040c0040c10300ba1002200050540c030091007005 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 419681816 1250 419680566 419680589
    0xa0f180608030f0d06030b04050a030806121504021f02030a090b04150315080f0c120c1011030d0f0603030f02010605011d06040e0901060314070806070e0607060c030510 74
    0xc006001e00403003034808907040c40d440715964002e1280804001d000300c4c0c0008005c0c000c1381d0280030510500184d601d1041e0b200b9142c80809494000402ca00305520707480803511548140c0d86040c110680c50786654101e0310140410b10b0132030f600d10a4030200810003080800681c004500d000c000c0e07600c00c03401d0300100f040e191564078003801d1512804626031356154582c01d040d114140b0300811103110303130303001e0051180e00c060b195481090801e0580383d41400700000c0c4a00d102c10400341c542100400c11008458008180180040d070500c4155840c044101d40c52596010a004c8403114502c1800b4800220542d948001805421071030041c0c540b000766144441160325061081c031299070010300c50035941c004211901d0641d100f00c0000380342c038840c2d60010b100000c03104041c800f0b045015040002964402e03951080050840016190b85110610072007110340e00040101e268a40030f01c030b0110b41d4000140c078a91800c106074842c4000e5039000d5081100103035407001040300a116003400d00c1c0140c240121030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 419683066 1250 419681816 419681819
    0x5040302190c150e030703030818030c0a02211501090c080906070e0d020d060b0a081203040204020a0c08030f040b01090c050f030a14010b0c010606080402010507110f0a0f1806 77
    0x308400031039940a544461800f4426141c14a8000c020110000e0b4000301240c0c1400d1301da1400500030341d010fa6110018000c8080203100348071010068619000c07964006082c9101540c08200044803021600c800d094080701425820b000280640381c52008010b003996104e515107514503080380d0392020302008102c0104180410483c01180c4950080d850780340028a501210b000140a84109500254803000c44c221071004c10400350404403050701c0840f1362021140d5502c98403510741d803511500750040c1d1420000140145018cd01a040501036403906c080c1020140d0390303468240d80b041c6e072294101844030701000200501f80d803810380136000f031070801d2000542c1a05c2c0541140a446590001c418020002501b103880c0c0703900103505060302003205041941d40c0d00d4092250751250608486a5003048c10100b2102d01074100240107542c103940b402e00e0404136850b04a01c50000908050744108241d42c5404c6603613920300254050400c44098203421031601290440d0450304000300880715040400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 419684316 1250 419683066 419683073
    0xf030209091609080f1b0901050328060504030c1b050a06261303090b1e030a0603060c0504090b030a210207050a060314070801050913050c030106090504030219 70
    0x107001d0b00404800d440c003400310940c500503610341500341c00c1140c4910907400e500c0784030040020800d0359511940250341c4400e21000501841d00d1090164a40540c0b00400038480b45803840c20191036811050b01c0504805016640d81c0c007540c03001d8800341e0020301c00b00c26880a0140c024505880d94040100b81d1004d03500e000e012600c4480c0364401c4a0511142003406140903034808446016158507140d400304900d40041910300319684a2010b900040b66071b10086000b4000400b110000882400502852051003a4aa54a50000b842c0e1086161101000000240e071401038052074011901c0745525242440c0043c41101c1c2051001882a44000000c0740400c910401a11100c6005807056120f1492400e09034905001a0301590708200d9248000401a9240d4402c00b082110b0320401c0619454003181111944401e001e126400034020010501050443d1048a0030074410000c1c4c50b69540d1100c0040e0031070380703070384c5c003100381c1035261020041015414810751003142641004910301200c640c5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 419685566 1250 419684316 419684329
    0xf030b0a0b0a050114130f0608090c0102120c011b05030a0c090e0a02031b1612081603020d060f0305030a020c0607050303130804050d05101811040f0e1501060f030209 73
    0x4501c074140a00980d017400081c50110480c0c1801003140d40f0918420740e91444500800a18403980c00001c0b070030310109400281c04030b121a0b2030b501c140c0c01001c001042800300b4080764080003a010142d9030300c0240040308184815103480116490f22100c0d00e80c41e05d11501010303180c0244003602005031003c028011a4104c03c50581c10000410300140c40b6079801c80c9400300002807940002200001143e8591a10002d40c4041c9c08541300700c43d60f0b038259000100a613000e4a06513501202001c2004110841f507100b0f501038507140141040209130207075690415031030b08201e60026101c503003000030f4220a5980410424500711410f40d0050310b0400c59494080c1c80f404050141319884000030742b810244883c1c0d0054401400e40100380180b034010307030300e40300da9504003482d8841d072030b181000d40c02c50f01c1c1c420720010b1030700098100660045610b0311a04000042002603c0e01292968481c0c141041d003100b00322080114041302d04640c002d50424801400e01c0e00c52200000401d030042051015640307412 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 419686816 1250 419685566 419685569
    0x71205061306021308030c19020603130606090e010e010c050331061d0c03030c120f040906080303040b131a0612030315180c0909090a08040f030b0a0b0a 67
    0x1e40440102081c1440e14101030f1080201030018201010300c00301d0074520100081c00c203409901c0450301180181940c81207185020040a54051021f00000315800d800c5011510300074460b810001c2c80584646070002160003018010000c2c2e17550b4011007110034401d109031640c036a05404c00318114940b00f000c1c180b5540d64000b12042d4091418143c2c895028202003180c143c560203035050001d14001d80c01d81d00800c0090700020a24891800d021a1604012084807890403890010703098040030100120b0440d8026034100395201e0040100080c4010b1724414440901050f8025540d07a050504101e13845140c0a07201c1a42c6240507100358001840c0600c141a030301c0403080b0400c086948a0700010400c000603848414240000000c0140c1c100a0305803400550000706c031201c81c40d41020b145400400c0c02154000c4140d04108001c90161030401120f56000050008031244541244e507201da460f005a0b0101e0301d41c01c0d400000b4020044074245041d4040d81000307003040030700d92100000d1000783c0c85 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 419688066 1250 419686816 419686831
    0x1d0303190e10031e0c02060a33030c090b060702010f1b050313090b0d060504020a0b0403060501050a121106030c070618031403010f1401050408010c02010b0307120506 73
    0x200998400341030041031980704200c401042040d021114820180152403026502c1d000300400c030007401088410340c800c041c015502540202416960304209000401c58003a004a6100841c03901e0340340305500305444803030388120943c2c4c082d80c6455860000d4203a50941c0020a00f00d003441c5e00c1504a80f1141700f41c8900d950246081a0303034280380b0a0580c0c0c1144004011810b09100039101c9090000000043c0440e182c9000fa40c000c1554030351001d0122603086041903808861904028045441900490781146c002010b4100840eaa21041030b015442940110b6082d501c4400401c5145485109000100202030241111140603950072500c1c0c5038a0032032520419001c00880c40d02c0c0110025620000e81c0b0000c00c0000007201070382c6c0007085108000c1200040c0e400001610008035400a0340d04030780540507010f1025043c100c00c19002c013a8103134481d040000610000900501c240117028800805800005005180e0014107003086015003048039070b0080c0e1809840040c2c00040c81a0303002a0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 419689316 1250 419688066 419688097
    0x2120601080408120a061e030c09060e0a020901020c03060f1e010b071218140301050601110604200a03030c020a050307150503090a0203070f09150b0a050705210a1d0303 74
    0x204c04c50440c0050a25400c0180791f00c6080c628102035899040f60042a00e001e03902e5081001c1e5910498815a41c0c20302404400400c24404210840c1603074014144864050043e0746038440e00c003020910340f243c2258945a90280d1200b0301c1518401c685842d02040c08601040072958105030b07101500d441a01002008007429804c4031400c075120322022629003c82c0301c042402c65075102e9941a116005201252080d480d04010460642c0500780321060789050602504041d5520303201c000816640c1c008a50003c50389845104441e41c035a502040070750b2007510340400e24806401402010800703904818001d501c170071820320091500c03104030480b41c156842c00c2075880d0380394664ac5041000c007100081d0940305840b8007080540b030100e016810382d60f08071b10400003580301c02c28103000108103110320181d01c8410801c80c1c00c414482c600904286003c0c00440c2c400a104080840c041c040c243c1180e1018400480c4050b485940282d28150906801e03c504009080c04c038002a160311030080f07100708248 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 419690566 1250 419689316 419689321
    0x18020f06090111030307050406181202120309150406030b151902101b180f0504020a0e0901030804080f07030b0601050c0a0b01080d110f0601050f03031201090212060108040812 77
    0x20f200380010094004982d0035291241806080500380390494000c040204000c002c140012181601c032000480e0303440410444041d6058003070045d03a0400844001035404104211184c40d21800442d10020030003001c1d54bd82d45e0304e4030134018112a0800c2d4564404e003540603840c86581c0521040e43d180b03043c0942084299481c1030026840c3c494042d566090442c2003241c000440003070700d90122a0b410032500c0c0c9900001a810013212491128040c1101da4015040c003408a0f04050703000d0032039050700703003080c005044080d800113491400076403080390007140009003840200340a1140354011213554004150450130342d40d81074041280200303002c1c1048004603008031105801c0000100385508400c0e11400ca584458046482d01c801070781450100d06840d40303483d440d85001072100d416040180192a035039003042c0c1000482c4500c0040035515100a0020140303038110000e000380241303110040186d48010341242e514003d54003d14080c1072120340410400450107281c11a00180114801010703075a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 419691816 1250 419690566 419690569
    0x291003060305010e0d09050105130603020f0c1e010c0e1c0501180b0717010e07030c020102091509090a02120c031f080a02030f010b010e010e0411071518020f0609 71
    0x20a50341d80301801d158240700c0c2401181c1d9001c50b01c0c07140000250f440225144e115001903640d84510107402c80c0980c5040c00c20840382e40329501031300848410305040c40c07a01c4209000d40313180c9026140000201c0102991112400a09105410404203982042c929014481c00080d196442c40070f141e40d1300700f510021300010402d0a50144c041e58908d2301540114500701e05003090303400011580f103c01300300300c10550000b84030300603d40303812288403040703a00599503120340c01c0300900310003200d01095640034060f5000c6a82c0e000700b124980c5101101141c0c0fa20428030810040c1c40c40a050150058410080c800010002c3d036015688101c22180d02a500d444840c48801c2164494001403842280c400001c00c0c0ca0b030000c01c00300c407154000c60071038081c002903041440c22140301000003804030f04981041c02165011b2a540300040b940200001081100d481000301070350312194007101e0484164000b01c10388500c912520002007075010b142038a00c0034079408600c0b80030b540040188a00d0000c213603031029 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 419693066 1250 419691816 419691821
    0x306021606020309060103030905150315180703020915070b0402090711015601030f05010608090d0f020c060702040902150d0b0d020a09151e09291003 66
    0x280360720000441d0b0b00e00c1d06205641e240c803400e000c1140050010140094189003014451086c0507030007003030320300e1034480711809030302c04818030180c80d00300400e110307282100c9a131403414901c40d08142c0c801503510441d100401042c54981d00d401c1d04401820301c0030a01080004006a034805c1d03040d03501c116545c48079282035078600100301804211358200141c80014900e2040014040c2402d1203c240003104030200d4145080b158000c00b42880c40c051405030380300c043e1035032041014941810005410700510b031a07501a500244c11110118503081d051001c944810080000240d04501d40010f025000d600025143d26041d04030511805000c200c003000c4d03580b554030940c0d50503801040c5070380f1850b2002c0c00c039115402985440906500d0719028a07028180020240403ca50080000c00300c9401c0c084610003d1148200c0c0d0700100c0f0810a011451a14005c103002d60044802107100d1214502a019002e90380140300105030038a25441060504000740001054030703204503100507980d203405004800 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 419694316 1250 419693066 419693107
    0xa150305030d0b0a05061801120e0109050c030d1e03020304060e060a09020a2c0c160305070501051008030a3615030501030506040807061404060219030e07030602 71
    0x80d60200094042c2500c80e107500c034032078000060b2884580301d0340d03500c2000580d0090045480100740d40682120355580302d0b07401d28450a207100000901800181d862a00710b03100c2010440d0a50300a030000201450200030341c0c40300b010380d03181880718813200340f81d019005032945038100c0915401001042c00c200c07103a008400443c0003201111940c3c509003109e00d001e00f410755001d07405032420242c041420312072002001140e4510704c10004d01e680100d00d0386900c6120040184000c0c00d0300348010001d503003070650780103151030007aa01d5035154401c60400608503040682201c01004028070108110040441034510103407040c200304030003103070b00c0c03030300c0501d0310509241c000d50b40300c4d0361280c481a0712400124600350742e101c3c0f14943c15040e46400590445100b0700000c1d20950100740001c000400190003022020311aa1020a501c004040c02c20035800e0181c030b0855045402007140d2540e942c41031486081d0440c540750a003c007144a0b0706d0141c40d03080c079000142c441500000c4039000301182810704031 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 419695566 1250 419694316 419694323
    0x810230903071709011e141605010e031b190201050714010510031a06010c0b15060a110c03010605060a03091406130c1401080f0703181407080303040b0a1503 69
    0x10820000c2a4501d20390303200c4d0b800c030f070701050030501c03030301d502c848a80c941801102d800c2d00c6004080c1c4003c04015400c0c0c010b009400140f080c00c40c00c0380c1c00a8000e000c0c0402444421008540f100c82e41400906500f030103801281d10396112301c50005614207503024045030b113602030038100c0e42c07070300d2906201c504040c0c42c8038107195540c2494188000d05c80c1c144c81410849004603444c03482c1c0090b0200200c0100c00607650f450000d1a41c25a100104004081440e0081103002c0290740701c90211000c110f894000f492000c0102d02c0755002c030f00101c1020310044a070300308114000c1000e00d01b0305001034014010241daa40806680700100780070080008250810f45000e0b108607803551030503045480e052818208126055a20300c500007401464002d5440076005058651b400c1655610380001800c05004006804062303c40c00368500d403049100c0000e543c1402101c0e238021100040582034609511544040c509500800800020071002074046402c4080482c003c901c2242c00100208a4402c1d5000903 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 419696816 1250 419695566 419695583
    0x818030d0908090a06080613020f0306010e010c0b0403030603110916031d060f01081203090706140405040507081609081c0c0c08010e07090209031506041113081023090307 75
    0x17280341500845124410b54049400884620f03060b03036440144d0103441c01c81e400000c001c4c00460110360044200080f810010f1600200c8422241c0301e10300c5060056400f60003103aa00c440c00e0041c00440320152424200640c2d0604107828500e4441d5207181c0404030241c03c26540d2801102042c051840f586092641c0d201202c5c2c083c20700d10400482d56000784100900c2d8840e010307203111445501c5066921a0165401400d2128075207181036550f010b21110800200104010100d03180c0d58a02c034507809804c00da5100c000c14a0041c40c00000040c805440e101032041d52241006407000004000c0410084400f42c0c82c03043c0c0382c410381910201c05040009010b41403204010404200c154405001a440e5900310303113030a6074408004003244201985103030140c2048444210a6580c6191140c000e2009000000c0e040d90b0300b40100701075000124400b040c480200c50420480f9800c100d000b014130040c6004200d4451500c0c1e41c8030007070880003202014243d56030300246105c4c5c82402503954103074028400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 419698066 1250 419696816 419696819
    0xc040602060a24030b0906090606091605070c0e0411010206060a03060902040f0e030a020c09061807020c03010e0a11150318030f070309030b13051b030309040e010207030818030d0908090a 82
    0xc014117100131603002e4103c0c441d070703070025078003000000d4043d0080501a10707000003a00d5214a0544c849178103042c1905001003041040009401d84510000400702d40c0080215030400b403800002c00191100c01c0c070704551100b010300c40c541d03480c8102041200da1100700014200c2e600d00c08280685075804003100d4503031910b246140038140c0440205081d2110350b00f651012803260b001c0240205c020380300c139078015410400360021126400b602607080320003030045600c0032042c6000282550b001c401c070511075801102030790707040080180b80600008012600340b8200c002c000c00c00c01041c0001800e0b80d0324180250061150712400380110b91a40200700b03030241c0d881c049814007500d520b400b8441196400540b0000545441d40072420703401c0f00740e01801030050584000410100000c80d003480560600040041140c4c1d070343c8034402c2c2c0003c00742030000035880309101d04019019800061002071501c48481d070700c590785400402100e81010400000084000e420708028170980103080a00da0007000d034260 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 419699316 1250 419698066 419698073
    0x308161b0305090a0b0c10020706020904090309061106091b01090b0f13091e020d1d010c02010509030304080a03230f060901170c0904030c1b0501080c040602060a2403 73
    0x4010034031043d10310f40130b0140e5502d02e9074070a104000580c06550800840000e400c1c64a0b0001c1000721b002d801c01508052030100040e00b10b803010705084021039007600d420013009420008409094402c07101824061401000440c2c682402d068020840d6040c602828480c1c2c0c01110017001404074210040d80b503007109142c05036158040d51220f0381c0c8400e01e1a001950503d28042d10307074442404200354160701000024000a1b41044584502c80ca031a620500c2c91541c440d180e0783d80304070600001060782547c81d5000780c02c480001c0e0194150350420001c0102040090b070881c0c041304590310300014407040c85003440040599054046040c141020184451962094001d0740200300840d00d41c00325903a07507011518000c00c1c100001c4000d4002c580006024500b24001541c405d000b4104119480340e1035a501c1e440750009100740a051002280622055074002106071b808176001d500f4501e031500b0454041c1d90f0b1407005102089207902d486034203068980010b03821400a44003001490915183e01c5c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 419700566 1250 419699316 419699327
    0x1a061215180a020403170f09040b061c1a0d050a03230d02070c0608012706170a110105040b030c09010c080a09051302030402090c1b06250c0308161b03 66
    0xc420341b018605900790518100120701268108808000700074030b01600b010510000d0f095050344c255008a00f40060b0710f0011a140c0b0781045610000ba001462180b095116902004c13101061400364500001c0c4174001480000e2003541c590b0141030105503c8029000050380c40398805d41e42e0082103010581401c1840c294001c1c0040c244101d0280440c20703100d810446203410300344101c01d081c4480780d0405030340c11404405001c4440c1c440d5030100344180c81d0321841c0e0302c400000c038950a0303540c0122006414032400101c130403050301c001d1034024a8246080d92203170681c0006401d54803030701000151407a180c0e004a03820900203510500c900e4a4038280c1e070300504070403141d200e214024110101d408011011501c00c9a1213154018906003098403440981c180300d82101402080b004001d0074070010408040040c58840d09041221440c03903a184195074030704a24240d40f000511000c0002840060342081d150340d800394441c0d0300690010721101c1c080718100d250520070007624410801c240241503214 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 419701816 1250 419700566 419700569
    0x807021c02131b0311040b041412011103070806010e0a0308040914130f03051201080a14030313020f0105130806010f08120313020f040e011a061215180a0204 69
    0x2c480320076080d120058010300380d07203410b1a00c4196465104034001000e01079404441418014018a4105a15540800030541c000c1d080003e141050f00d004c1c0c3c00c549010040410003805010090004e179903009610616804040d2a500c280240b080c005003443e40f1070842c5420441005000e044840d03901c0c1840d000a40c0300e80282140d46041101c00802d2a03803c10010b40200c0036109030248107803107a00c401f40f442158231380840400000708036030440092003842c00c0b4064011000600502603c81c601240d400170401c032080e201e90000e00030040070803036405480c94166010364845240c55803441c0121070510500e00070414030006208007040c0c6180004215044e108060050003159807501c032450707600c000c542820450040c040000881c0e09070251600e0b00c0b1a4400b0b055003070944410b0001a041c1d540a80b031111650795981c003807910400004080305c080c2c0750300340d40843c50724002007420320310104010152041c800b45a001c4525549540c81e45181000360300c043d01849042c2030080001030340c000d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 419703066 1250 419701816 419701819
    0x10021507121b120c0c0503030c07080903120409140f0a1d010911030c01051c02130b0705030901030f0203090d03090212030c1509150703050603010f0f0209011d090708040807021c02 79
    0x100b40c0104e50640c001c00008281503041001542599079508921501c0e5210300e4045070030303007014000007907661000c03c6609130484102c500e194903039080421580488501c10344641c0449549814400707403100c0c4a0495030404250b02e00030801d1041c1c040400b101d0f00c842c02405002e5840c04140c001400200300302c0c80320780c11044041e10f4019509400444040c0200080200d400c01e00020050a802059000f03014031000c4d42c1010340d540c2c0d81c2e0100303440f4540000005940c5504001001c040542c0d00d0720402c141c0b58ac585408504500707140da4119034801d51030354450f0a141d41ca0303544100399038a4070901a0303212460003c40e981c8521a80d1419100c00c0108540c1040829241c04500180e1002c0f031040c6a4011640d07103060707503549076001280904405002c564055580319055100c10240d4050440c2c0d112800b080543e965001703c000400e95030340080b00d26407800810610340525601c0741016600405503140c031542036116420324414510a20b04000c4d80008440c0d281100424602c010200c00c070300 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 419704316 1250 419703066 419703071
    0x702060c3c0d1416020d1223041806030b1003030f020d0c0201201005011518031b1707032a1815080102040510021507121b12 55
    0x72803165079151145111100415101d2400d00318000024001c1c10014840d071540c0d19056010340c0120382182c4d034100054584a06440c01201c00c0c0d0f82103040c1028401440c05c215600006154407480c80d40202c0c002c90f5507410344087c09100310f0742c103600030304043e41d04100c0007080d0b0305004201c540f040d0503510044020440f10000000031a0010405141d91141c548078840c0841480c1c1c011188200c40c82c41d640d04405200d1190405500700b0801c9107490744440c000080d1a504101c002e40b03c1343c020000a40c03c101e100e0715070b0801003403200705039400c40e07a100703100e402848400880f414802c3e400e40c01c10009101c02040040d21408002050000c03280030725408145800da20525131402e00440f0032002c01103140d104200403203195128044011085418001031000490100e400b00c01640e91001d20103030340100701480b89150032090b60303880c0e8030240020201c00c41d1410711a0100c48008081c0014820000345048540550342c00003691185036200828250b00d04440141c2813201ca0211192200c1c0b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 419705566 1250 419704316 419704423
    0x3010e0c090906130b04032c0103060f050607080d020702060c0601030b060d050303160201022a150415090303020f0a05030a0e030307090522060e19060b0702060c 71
    0x40e0b01240f024040c54407560484400031540c1c80309100b2500c0a04218100049961444680341713640c65142080745041c2c40066074082c050f0f0004044d250182c0141c0c260f85c4104108204540d610710490301d0b502e50202c406916400140e5503940280500c1d440a504640c000ad030021044070081361003070682e48500381c2182c65032642c1d018130114001c0188020b0842d0300030804103004c0b007245c60b41c2500c07540e690320025241190442810764600d030561047e112190300e81d0950080400b05102c0a441040d4440c00c491292074135446a9107040c0007034405200302962480c40c0c030305051003034044400c0303e60a215101e0780d400d18690020200d500440303600e090145050302d1000080004400c5a014509641d41c0c00081030404082003c40001c1150a6407683e45120700140842118004d030001402c0c040354034120391820700c4160420181540c00b0780c6260b49040c03028001141d03d50b0136104280d4060712255282c00082c072045107065025039500b4400090100301c40d48a8134015017280e80c08405214140c4103c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 419706816 1250 419705566 419705581
    0x1b0b07200d032a08220906090b0f062817010b0901020f010902090a0c1107080307210f080705070501050c1e040b0a2102040e040c080f0706080c0903010e0c09 69
    0x1d040e14000101248801c014201105c1440c83c1c1e00760001d241a00410041070707841e0515001c84d41d103640101d084540740d08050340c4030701c2d01c40b0711807481c01c4064403180d14200b15018618412a1041c2c00c0c20480034a085000c0e6440b48950580c000c0d54810150741412540c45911404040c0c010000e07560051040101410030b0345010f01808034007a0303000d00001d204d41c0355514840c000d0440c07860000204039000c9804014401d040040300000c28081c1c0113950707034000728100340729656812405903c403540e407080781d00c040c5d640c030000c00503031602103280075551600c03102c1003290b180c452040041c1c415130910003031108816a8070002c1c510003001d4010410030900c0c03c0110310300c0d07000303a102d01d1070b0310141844005603c80c0100d44443c000b424405010101e80c0d0040c0d0382008036001383e04050200da01140401080003403500d182c84c0070303002c000010301641544440d107030303507d11040c0181001c004081012072421a6014160703440c0c1e46009000380018009501500e94070f0107521600c0740700c0d10208002c560030b07 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 419708066 1250 419706816 419706887
    0x301603031a030c1f0e060d02030417120106030c0c0506090625090506030a0908030405032d09100306091d0d032a050405060a0302071b0b07200d03 64
    0x2881d0f000d040245001002c01c211125503c0440070314080c0582c0b20003100c096526500282140301c50030340c005071641003506061521404c401e0912440d0f80042100d200394940079030740e40e0f04450640c038001c200070700d000c00100c44510602a00400902c61441804890440421254031032252801c00c1c00b4010085924990b042e03c1024091001c1110020280305604041c00250740c403840142000c2050010755441003010343c02260143c2d5a078001143c9494030b841c810b4030801002c1d040700303200340501c1d1880c6007602091084c114201d104244041c07600d11002d020360001002024031480c20044c890310044810b6000c0c280f00b02443c030600071103c041c40045c1c02445110303081103180d803180c06130f0440580030b0040340790f24071400b106105061000084076a0ba5900404003c0c001c1d40e80503071141c0302c40c9418504d45482c1c205002990f0340000c2c0601905d5216829900744c680c11081f180e0050034000c003280e0340802d80650094000204034411001c0c5500807140d00603000703824417549149200c1d0003c0244 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 419709316 1250 419708066 419708083
    0x7020d090302011d27010902070c050108060414070201020703080a1b0c0c0f090903030b010807020d05090f0a030b1e060604090e030d060603060602010c02301603031a03 74
    0x4289603000510165100da030b80c500c2603074411a020341d05806200c0c0082d10b1001100340b042082080400c4003030b8101c0c0d82c12603041c0100140101581006d00c80d668142d10710a40d80900350400c03210400260303059945400c001c18000c0162131442e041c1c00c00030002030203035111a40c10b601245410002c982c118503035210b581c111848507416100b076201e9900e4115000450703403d0545100030b0042011902c0e01492070110014510b24000152200711490090f080d030f5040120f20381448101030030403084c1e030740104200301c034800c441c03031300507034880741072001a084052800f005a08642e1504000c03080000ca00c9105006200b031000e1841c0c5c0c0c404eaa040180303555401c032010b81d00720100b44002c00045500d90480002282d02c0001d403801c280080081c00d085030481e034440f4000a84550041050701c1e0203104110541040e0310141c80d4910001031000080314059074003885d00d2010902c030384128180d07101030740e054103c400d00c0003850f51120f04005000d00602c8611410006105d61501c9061130005407003030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 419710566 1250 419709316 419709343
    0x131a15040308031f090c1403100b03100b03040605040308060a0303090b0901090819031d01091701060803040e040b0601030c020c040902030c03070f0312030b030304150c080418050702 80
    0x914203421542d502090350000381c90b0b4803404c0000f50b946440c40d601c04100790041c00441c00001000d0340d1003070780284800501034558000000400600500f40c07040d040b040c0645210320340d6142c0c0e0f80c031114000300c01100c06030b000c4489024084188000c20907a41c000c280140c1c0030343d90352895519000b04000c005605844002e000c110314020400030001c600024040207401414880e010b00d9440d00c0c894102550000035402408000080308201500104100b529a885025241080780c11000180c40318000c0c5c01303207003000d00211034480765001e03003500508094030f8020103494881ea901c03c2011024076040d102150610480c2001811319442407040e5100041142d00030030100b448a010b0000410481034180d8260040301d0700c0840580b000c01c804402008204800c0701200d10b5070600f506d00c4101c0b5813240c4105401c002400c00f407035800000740c03030603203040d880c8154000703102070000c2e1000700d403400c00100007010110740080c002e00ca250400c1801d048284090003955203c20003240ca610711003c0c140e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 419711816 1250 419710566 419710609
    0x120c070b090d0b0a2307080c16020f06040803120103030f080708060f1f2607020a080d0605040516030b010201061820070c17060402090a0b0f131a 64
    0x2000308644803c0d5541184080000058491203a00303011310100d440366158034800d10101c14411041d81c0203000603800440d21040d5400c10542d40074141900b00350300ca0213441103021442406203903864100701d6005202c42e4045980c3e45250080c510015103091000b900410100c41d121443d250040808601c1011580d803010510b0b6100f10801031030b0028181040d0b04503e508591100d0600c0451800d100d03041d0944503006184510300a60504441e0030070041480c4440c80140b02c202600018415012540320b00349544407045448804e00515081e031000d544141081306000c1211311010644201148a60381807004080c01001a800e8905030b20610340079510a0781c000c041450303207034000c800c048000306200700804400031841c1015044814252140c2800c00010003918501054080d203400b5030381e024011914040c1c0000300b0041008000101c007a84074185c502d03da070b456040c6258042c00c000e03c010307501401e4420200040c6409a0161a03c00b240e00c81d184d9989445511048200b142c059803 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 419713066 1250 419711816 419711839
    0x120803060607210929030f06061215040c020f0705190f17060f16030b0409050d02070e0a02070f0602090103090b041209060809030904110903120c070b09 67
    0x50019582c403420b820703102000600c40f501c000c80c00d110070f030032000c2d6403560342c0c400134600744048a00781313030f52803469030040032502184070040341e0a41042d02e0740078507014030b0b900840d550342001c61510310500c24400b829810440401c0400a11000c1c81035040d101074604200240450806a0b5030b540704280c01019a800201d08024a00c1c01c4140846039140d682400038896030341d10501ea40a4140340c1004280c07140c15005070711442801c100440d4403800f940340d94141810a0300d04800d8218910400100b0140c0340e213851007058680f0b810480000ea4030204840440c0c0e03085000a44610b014028000403d408901003101c0400030300030754040d030741c005403e0615240140e59a800950040e0142814141c90301803050200d44000301a6115900600150b004031080b100c004101083e42c0d00110144000c11080c42541c0500100396810310806840000b69003d0352111000c0c9800341010580d03142c442c0c00120100c082205004d000030310400e0003112515a101c180001450080c096a981c024002241 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 419714316 1250 419713066 419713069
    0x610050d1202070b0c030414180705031e15030f0105010501210b091e0705040b04270e0d030608060106050316030e01110301031506032f031006060912080306 69
    0x1a020740e40340341e0044074079a694841304040c068102152510703850b00041410040120136943e2202070700c1c4101c1c2d00d0885103810803101003001801a080c0e03010050044006008101401c1d00503200b403440c2c26a0020514200e1140050512070b1031201d402400f4648101d42001700502905050304c030142c55900f243c40001d1610140442d152000c00315007501d9040c0b03103400d9100c120a40740244908000080d0054100064141da000042c06074410440c0c00c210030421380303484030251400e4555429003562040104084c03201012008901c401c120340c034007800c0c2000000c000800a8003100035840911043d50389a00d0300340c640074240314400c049042000000c01c114079a4010f0032060005040001d155a440c405e12421106510390210580d08004011700034070607800242c19030320f000b264060041c0c42c110365408080414003040c00b41110007071900034021514000001c403a424015084450b130304200d00c403481c084d110b5840b0380400315080d2000402c0c01800301049001c03007a00302d0300d0325103540c88240 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 419715566 1250 419714316 419714333
    0x501050a06030b031c02031207090513180c09470a0f06090603110a09060e030a02090a02070308160e0f0f0619020717120a0302120709080610050d 64
    0x8020f9605024140c01000480d040111010100c0300940c01192a030580743c112101c021000380c1103a050100713003d41040942c0d01d011400b9400d588840340860040792100700190701d035018400c01001c210003040c02250215480e4000c4030030b45050200c001d101c030001303401c641900000d151070172201a19010564101080b4114084c00d000c800b80c511624581c1d90b00b501400da94150b0440000501102c4003040040c4d41402000c200a0307405602502d4001105d0010f403c071481d920902d030500104080c41c0d481c1e0b41d81444003041041e005001e100361703860900c5072080294095041140402d0702c1c41c021402d404603c80c980d24a16105031602d450701144901001409050050000c1d0320090303441545c10700b07455a60284c40d01282012005903a034089500103410900250003c054460302c180c4c5401441d000016200540980d805085030790ba00d4440d8220041d12076206100401c04800040c04a515844007000c007c0b03905807000d45026444088040688003607904c1030b42d501c11560b22048002c00c0303c030f0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 419716816 1250 419715566 419715581
    0x406020c0703080705010203070f0f020d110106170708071202010c1e12120507051c0b13110403030206061503070e030c100e0f0303032512140106120501050a0603 71
    0x40c089a0505640b90748903885940301041c00c03103150350003000f40301c4913a40203180d11989411504012070010040c0344001d650742040746002c010400c200e6248072241c40294406c3c0080e10341114000c12840140441c00d41e0785c0b01c117100d003019910544000040ba401007081e201c01207541656000304031922911030780002d400d011440e51000e00c1c00074034000040c41090000b0040c0310b07183c40750b41080c0e14000d894011181c00900c00010f0110030084e4040c130000c1440301d40340a036007000d00055040c00c0d60010030429040903100c1030042e440c0425007909003c80b04040c03c1241e00c01d90845030300e941c0350424091107020800700184000da00b4401b2440c000c0c0140a154118030000c0c0031603500214450004d00c1d03c4010410500200d00e81c0085a501410074000c08410f900d0140d0081d031450a10317001200391040f07190103907413003c00c40898a9117403034841c602c11039103543c1c490004e0000420184074250310030303401c0c41540007281400020010f03003440c0307000325170417540001e0861545a1034104240e0262603403 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 419718066 1250 419716816 419716837
    0x50102300d0e15040203151909140709060e0c07030c1e0204050a0b041802060405220204060e01080603010b010e150412080d0b120606060d062115090209040602 70
    0x81e010380c0821004100030b8203c440c0c101c1c1d10304801a003040c0c014182458061006501d24600c26400c00c4907407024408403101d822400b030b100085146890030a00310198580d01a102e860040610020f4146003075003002c0140c03903c1c2c03484c0300c1a036104c40e40342c2e2260f4800c0b01d400038042a45100b503030740070030b0724800300b100b100740200c8540c8020120b0350700040881c1c0048920707414056072102d92800d039090602c078036074441a4211600b8800e80803500041c016001d240f161511403d00c2c440340c4e5203031840d101fa60018510002a040d911507482d21400b900180c840c524150001c0c0c03240c030004d007081c81e05004620583e68180c54106c03108200744140320082c0841c405410b0b001c1e104000004441c1207840040740b04a018018480d110004210894207803814507040e6841581500c1c03041c115090041603250b003018007100d1260355800705200b002c002d80015031181e0440f4803e24140303504512681301c1040c41d00d204450881e206e00505160204541405002079084140d80c80000c00203484c5600411942c2c04 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 419719316 1250 419718066 419718071
    0xc0f010f0210050a020432010203070c05042706060305150103120e06130801060923071d0a06201c0c0f0f0c090e010605010507061a0a0f050102300d 65
    0x11607c910892042005e11011466513241c203900c510050740312014a6040006d1018501c0c0c02840c0e10b84800d056568021307944600d42d10b10516022481d80d0000024482a0311500c000b007a425080100040840e884251074a003c2c110824041d10355007503105068980c8081d51490222040604552910340c0d05406500072400304210a46025007050038401081c3d80b80000c1001402c200c1040162040340b42940d0301a460710205280ba41440f0b24481e80c4080302d807600c07001da02e0030b1808800301c050345180101c1d0810300d0303a00007041403035101101030b10313046140d0762214506001c1a1015510741482140048001c071b17800b084030525128941880d280b6010303103516000e03070b8403a880c2e2003d40030242e04100d031040b420741d808001d174994500a000724010a0720003041050715100010f000783c0b00c0c801008046c0c07696981d440082401005a00710600c0700907007914007094607464410601500e501469001d131107420404140c01e440840e58030020f0424070b401c0c020401c80310201811941000b44810000703034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 419720566 1250 419719316 419719319
    0x2010603080f1e18060c190b0f1e061c080a0201020301080610050f0d14060a0c0e041b050304150e0c0a240509031207050c0f010f0210050a0204 63
    0x441c0342015211150300503141e01d9071406090b103607865490060000c100c0305501484010142d07806200d12440d00d85066509603079504110b140300e03041500403044014880400e003203442c20301602040c1d2902c83c1c81e001c4d046585903114072440700000106454808008007230305000034041c2c1810082301d0000000800c0603003200c1d80c255640d1000d50860707800d010042c0e60200041041720010043c0c7c130780000c3c04040c0104000c4c00c0c10082002c40c114648900c2c0503100c0710010804010404d400050460f10b1036007650110f04054003424040d02d41003500d5000181444080c081710b1a261003446000c4901d080303150a00c90240e001078449030001403050303500544410803042480c0c00c40c010740c5041c40003d000b800003501c40030b08104020000390000b0a210444500f120f8031849680e8001c82020803604105481d107140000091805030f5480b403060b4400400309006080041c001007140d200c00003202c0c4e0a19051207000111040682c0205480c010303449007c030085085003990203d6008825072001600d000d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 419721816 1250 419720566 419720573
    0x42003030f0c010506030c1801060305060a1502073006110c03040305010501030b070807230906070309180902060313030207031a06031605150d02070605040804030c0905160c0302010603 81
    0x25080301c9591210b03a5143c00410542c1e103410f2101001250301183c40140c11510005d00125010050140b0740a1541d03a10200e5195a07528020340d008007400000b41e0f00d0301d1f800d0300009450b01120301c10001814030041014080c40081c1d0150326042c2414003905068201030745455020706003803d441110443e04100e036401c1c5440c00d20040c400f031030203440040740a501d58905406003c030b004050408100c4004103100c200d0380c6c0b218400f06c2040900740d03180390140b05050045040d20401584961089000488008068008428108650004220f000418400c003981402d441d0f0045000354051001c000050000c8244da0700001c0180c020b00c1169855600c03507030b599205181e0b890540898072804130030811f0303510b001c02030f0b013100002c11007042450030724140114205030401c82d08002a08008550885403403066410350b069141c006100b4800d50402d4209014640d10a00003500c503144402c07404240c02c1e00380e0150600400c03000e203e115a02100020865021300200b90840c03c42d521000e000020 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 419723066 1250 419721816 419721847
    0x3020706110412050601050612041115040920040303050901050f04050301060f17151308071e140303042d060e0c10020714040203070210060b070201030c0804200303 72
    0x1504824000555880d80307030030480e1170309005074802485182c08021820410704203100c1581c00c190710041e012080a0303a50001100148055100c03403524401080020740911a90400d142482040742e41000c510380900040300b05108501015001c10020801095954842c800900c040c007102e40005042c103841d04d000a00351909a07018a044c0304800d103040c010700210808265002074000014104d0410000300031195040040587d5500103100003440700740500c020458401035448a14030b41d0a06440e21801403182100f5070035030790003441c0b03403802d80840c0f0000704070303809a40c0140328845000d851000d0300042100540c0120701c030032101000800003400500030008903115210141040300360410500c030484007001a25011540115002c01242c80c015022884040040e030307016940740e03200c0b00c0583c50705859422800c885490090005881d80d8014003904070360703200766814488014100e0703045407404405d840150a501c0b02601105100c0c0c5030000c21809540e006d015682001ca9941c0443c90 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 419724316 1250 419723066 419723069
    0x6180d0507090c0e180604180206161109010605031315021c0e0115170c09180714030d0309060e03120a0c02010501030f0b040f020a06020f06180d030207061104 70
    0x35403580fa4840e420703000e0b4120284402d1150241c43c001d01104001c804450b02c1034014004a000b240e8070701040d4190000030501c10306003a0080d007010b64030180d10741600020358113000301b80d40d80f5007100c510020300c2c90700c1042103040300c503641d480c3e5003543c0760000300d4140d0f0801d20b0b00485805d62241d15400555800380040d2010b85500c040690320703120020381060680781d80742d201511030f034034080198008030001c0c140441030f220b88940703080035107030f520b500070b85040b200041c0954044d0071700c02085069400c14025903070042182041d0f9884c03d43d0303821803422500c107014480d507240c4c1044100d04031061085c7d10191085010340804100580341c80c51550540d4408000c1101c034200740c1c0d0404c41f4121560103003204001c007a2008102d550b1454441c0807482900d05001415005607038007140500c0b40f1400d1f0300d07581c160002c140a40b85036031210007a40e280d1610311a003001d0f00450700003030741c05001000c1080e80000103c010700080300c6446001c400a5000440403103204e55280240e40c90008080054030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 419725566 1250 419724316 419724329
    0x706150f080c01120e030a0c080717070618030801050108070314150a050f061c0e0114060405070c0302030d0c021c030e07152a0506040813080c06180d0507 68
    0xc4a03401010004082d8030f5002c1000441904002d00340f21030005c00800c55840c054a480c0c00e04400c1024070b001c4080344074450010740600400d6011444001d0410028807425204c4ca2040241468804a00039901e8014070b0150118440c6801085036500440c5074691040c611714000510b101c400c4a0508882d609445110120070304410f020f810b82080614040501400c6501c421403403104400581c05c2d110311400c40e01b0014800540c80c0c9110038540141200404010081c004200020a0f81a4000f02244da01c1d01c40c0f8140804110320901034040c0c0e4401580560181d45080700051215010303003040c030401400c62085060f0f03034458044000d40340000302407a81e0049260300000061504d001e00540100712462032011a28200c0d40d0800419082055a50030145050b00340c040392010032020464080c10300e020b010104010081e0781d03001808040142714102032010348442c90703140e4075a100034911380c02080c100034041e0b00d10358040f02d034000c00c0c0b402030a0201201c070f40d5a0b00c40c100040b0b640882c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 419726816 1250 419725566 419725573
    0x6012303160602071a030a0908042103120507080105010e010e030105010f060f020303160309150911100512060d110307091a0409020d02010f0e060f0405030607050f0706150f08 77
    0x9100683d4107006101c0103010141a011100780d0082090981d88809012014004d554050322000c00040c0404e440040400d8041100b01140c0308a6202e146008181c0c11000141c1946801010340e442e485054087c14030750341d8000b103a80c2014015602d015007448254141b20040488101d41d039024082c3d140a4003210454558203840c100d005012400100410425034006104110103140340c10380c00340705500503113000b00ea2240d460410400480d050b00200071900e04114007902449201c070905001c40b1400c1d0380805005e44600821100c50080183e400000003006021456918184540500c602c0c02502030011641040300042e28003c982e40c40000c0d0329454100c2000c010512600b0202165415981800f1800490380007407410681c0000003410300040c41620140c40380301c3e01004507421030141003a65600103800324000660060f108061081c811200065030003403240d810740b038100c4a00e00400742850076030740e60140a800c01070400280950b403060b0000c3c00f2822600c100c8010110103015 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 419728066 1250 419726816 419726819
    0x1520070b250215160b07080709080706090e15090403020a0c09060605030604020309010f11040e06030705010801050d0809060f030708060f1e010c080a09060f0806030601230316 77
    0x2031020001c0c49116840001c816003180002584680c0001a54003c0407403005039149078540e03040b0340c00d003003803000503080d8491a4208907802e0b4000156500070103203030b101c42c001350390b07a080b0080d500c1c1c00500481001440800080000c0c8901540743c0360800c019140e51200090400f0108201c4102142c0550050b48801e00c0383e802d01080f0308012003d0071000c034007401554107014000d0014480640858096907001002441d4101c0a42c4200c1e1044d40d003680a1190341c5c25000e0700b42458029008640e01265004041004c61500040540455078103841e50380c0309a280100300214070041101c10364070080d040107441703240e98541d0010001c04040840d01500ca0500c1807000f0308244000344207501403100640403001981e242100c2c11044090b0f0582525807040400049403054940d0600a00c80640491786c0c2000c203030442402c40546071280d9072950401444041110135460598800d07406400000041c40100f480e21b416800b4040c2d200e007004200b01c10071010901d8001c030303106a56140c0d03110150 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 419729316 1250 419728066 419728087
    0x20c0a0218040519050a0203060108030a0f03020c0c1c1a04060c1125180c230403020105031003021309020a052d01021c080603010f02041520070b 64
    0x1a00d20038203101e00d251106103010742c1c82560300c800600b0324800364034400b84c0303020030004100141201c491340a4107803501c40d6510f11040c3e51300d8001c1101c80000c500c005800381c143c0d0348240b0030780746140d400720020002c01c071550307060108820204035550035480303440148001052203806540305030040d205005c150741c50300b0306003c0700f141d250422203000c211500e06c0e2100100342c00500c6003104030382e8601a01e542a090580042e030301056920011100d8031898003191802c6650388000040d00c0c031901c4060994051800c520700044480c658002182024003091015510070005194004000120812000e4a0b500001c900b60080821441d47c10f403070f0003883d400c500f4105882e07001058169100c41040604d44200e900c081090281a840903010b0314004246030b10070411408484112800c0600c0040c030400d0040000c1d5046400500039030811341850a0f6111038402c60307003100c42983d0142008102c004046401000c0903c1c030361220350510342050411942808864010a02602290740e03074100c140 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 419730566 1250 419729316 419729329
    0x1305011d0c1008040218060a090e010f0509010608070306050411281521060e0f070906050403020a0603020d060503030c07060905091b0c0a0b10080c040c200a0204020c0a02 75
    0x20124000c003e000e9040c80016151101503004a035000178140115a46800c04907001a55581c050f010036810424000108001035100d000400d808113018030595a51004041c00e80f036203480707584c11540c4940e50402c003003100c03640f1007900180304944110b08083c101c00010b0b46183c400001102ca4020b20b1100f0000445089e4520001c0000d160380614800f805d03200949003090300210804a44044001d070034100c0030382c5d84900094000d903d2038030002c1c1810401c072075400008803010b802260382c005003c2982406803003510212580144003c24031414801c085000e504105401c0c1051600d0303910100355664240080c00014548c500106261450003800520900842d03014501920f45d013818000d000110306204100f4206001140707a81d603540d50f4003a45041c080100140c002640380c0c1c140322642da0018841d4048900f46000c81d01030136403000070402181d442001d002c01103440300c228072001d8002074618161181c6810b0a55107002c0060300814103a034044448000710b60486206c0804601c1d105 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 419731816 1250 419730566 419730589
    0x20c06010b09100207060509130b0303070809030709020313060903180b1312051c0212040e0117060601021b0109030209010b0409050705040b0f07080f120a0509151305011d0c 76
    0x11301c0101909850154041c00e944141d4041d0b07406454608401282c1c0c0c0341c00d4101302d15090024003103940c4d66029082510f50341d040400c10510030702a40a00061416070750094070f0040455040c00340700a00309940da03400a01c44400b0440c2030140e031120610500314a0314100000b403c08107400369a9198000d0744c01750f000100e4101200419041c09080c0104a0000c4c08509802400300040d5800d11102011f929000d40c603030114000d03140c00540807a203039940b040164121012407040f80d540300d07007031340c40c01c0d4417000c0845180d0f0060744062020030954403d1003110000c09010306000c0321407a26a00402e01200090f002128090380c0040c00700810303582407090a9024013586401800c1034180000920244900c000181d88500c012408030140050726003250502d409010b00584d94003032a1901d04402c2c2d8003200c8545016143c0070010b458050081a46e035110610103084c94640d5035611403d0701051200d01c0103072420341d0380d0040036500c02c1c840300950340341c03d88960042407180c000c04208a020441d130b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 419733066 1250 419731816 419731849
    0x141006050a1802030a0b0a080d02060a06030b0a1e0c02010905060c03010608040b0910020a030f05010504020c1f0f02040609030b070c0305041503090b1e150a030308070201020c06010b09 81
    0x10107404119a003004109080010034250001d40e803510341c0c0c5841c60280200500541d44030103294400034801200040b5481500c82c0d070340030b075005591100944011030350b06220260046240e400018040700d425840382000c200c0f100003c00c40c5e00350089005045845414403100980c1d900ca0200050001c200955644540001040ba1071581403110042200b07801810050003110504042104150140482080a51030032800c40d11103500d158000c01600d0180300c041011481c00001050070b0419000302ea44c0c0691002c000e00d131000a08080c000041a070b520341404456480b00b41c55030300c0800b400200001c0c001039a80b40a40341c11420b02d2981600c000e009070050200081075203000030340000c00c0d0340c21030340e5042e8450180d1000060a4003c0c2000c0c0800403d801c2a0500700007180702c00f80300220b1500122840401947e403000d02420a84071603e285a50040c029881000000e202d1002c055103d2120f10001d0b0516003060100c61914200387c11284004902184840c0681403050050074a07054 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 419734316 1250 419733066 419733079
    0xb0a050c100e1e010b03031314010903112206090c081f1208090901030c140d080f03040f06020301090c17070f0806180c0405010e0910091814100605 65
    0x2000c5141d40c2d098040030081103910143da4044000c0c402c0d031102090310009800e80e0340e10203035120039804a00060055560402c142c55520700154411020081030320360182049a030007c0d144100084184058850b008800794a45121150601c42c001c110080560f458081080c000c1a80080e004030401031401245000323820000c9442201b002030784046560724140c2068641450604041c28801c11026680000c03c0c0d8000008100c1070980034070454840c19122481ca45c01036041290074103405502030300c41d080034064400405000d400075034000d8861918911103500b070b0340d140030680e0400d910016040c0d03600c036218160304c0c4d0424800c03090300035090702071306103450003440281207500c800d0303135400c1000441c1c6d0025010303458005400d10708848801da000c0711860104114001c940c49401158005804040c40884508120b032000780255010780e100c6090310f003002b2440c001403407403403c90580c0305511010384012a0a0004040000d03007510701608200074050f00e0282070b140e4031785c40280a841c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 419735566 1250 419734316 419734331
    0x1805150c030103020f01031119020105090c2101090f060b03010605010305061e0f06070b18070b030c070f1403030618091b060409180b010b180f0a0b0a050c10 69
    0x800000c11207043d603504a0f40800c00c40310920048004140c0d00c07440c2c03103610703000003a401e100d14456013060070998503c0d4000c0c4040d9950005603511007804003031141d004001d20380e0b030400d4040030322040500c1507014800090003503020340358424000400e5400385c4080d9030381c04503002d00e03040a018040140c0801c0c2800e000d00c0c141180402d44024405c2001801c007400100903003500d940d8111010800c541c010301d210707103400541c1400246120700f81d9036090744121320b0012107800380c2c002c10414202e0708408501d5003903955013004144150300641c002c0b1507110002c0e03407050024009114118201010340011a00c91500d130090002900144c004800308140c0c001c20046c103003000150051107413a1414410150340c0c03144001c61418003d40d004000b1080c1050b001c000600c101c0241080503900945200003540d80e10401e06000303100b80381170322040b142c000941c01683c0c00c0502c1200c10418028003035403d030b42d03500c00c107080d0590001700c49240080c60001d10326040304001c000100d084890b2a10070032069 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 419736816 1250 419735566 419735581
    0xb0a020c0306041e03030f060815090a0b0105120c0307090204050f0406030c05011407020901090e100209011713060c050c010b06040506090108060a030515061f020c120c04180515 78
    0x6112048510507003811380b04030410144203401c924801e4024020510900c0c0c2c980a00a459100024000e900da00c0050005008000005610401c45401c003a0034401a420401030020f0030010310f0045429100c0c14035560840e403030800400c00201840c10006840c6c0382488100329a1216419003a48a10f0410708280041a0180c10b914101e030000d00b032000900205500456247c050000d001c0d520030313641000059200e00340d402c030100c0c0ea000c0760203485460320307114205400ca005080e511030001d500b50079640140505101d02d03a8015171018880009105a551400c080c2c07450301c410b07d000620003090050015a0034081c00c00300040859042c0c0c00c0074104008a6002d01401c0c20f00742c1006030050100300280c44110045014541180a5030190310f103a01c002e03241e4200982d1164060f502941000540d050079441590702001580d015103140c0400300100000414a40041e0719140160408181c0565541c0701c0c10122880d126136101c801e285906000382058000144c01d001408148c0412684 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 419738066 1250 419736816 419736833
    0x801080312011809020a09020a230d0b0402120717060d1505060402131409010f06020a0b04031124150105070f030c0b04030c0506091903110f070b0a020c030604 70
    0x1903500e080c0d0a10300c3c0c031002c6002100070f080b48010203900300900310008034807060307940c0081000c1e03121a01c40035400740700c44003582c0044060800e6680b0420040c0145844880f1070b4211002e008070003403003d030408040304e0817103120100c181e442da400710706058403075410401e0341e120155000303c0460318054403003d203881c0c2c124840c0c0d800c07645199903070b603800016038075a0f125030607112a015105003480000e5180e040c1000c2254421010a10900311000006406401402c2082c241c4000d41d0143c0031400b4a9a03d2040d0400060800c0b41800242400c61f40280030070015500148203200c50340c0204240c0c1c0c0107000f400b007000b0307001d810303100304002c8500c603141d80003c115040180c1c0700b50300000101c410b060444a40307480901c002d11800c0c41c003051206050344091610b05441c00f603c15901c0ae511208405070f0795402c10266944014905031611001c2030162060a070105001b50a80e2448260704a40750306060b51078100d0b1002c0240481d841d0103040d410440d910342c000059006012604142c1c071008507 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 419739316 1250 419738066 419738069
    0x702011e0e10020714190210050703030b0303210a0603030c0803040c08030d320a0f020909040807050d0327031116300609020a1a0406080108031201 65
    0x3502510340d0700c80600c0000801c200440070703515200441d19a10ba62034406000d92140c0d481002030b200d190026070088a02c100c05400c0760344e000700420005184041c0980366900035070404d4061680c0c0e1a0584e0366910140300801c3e02500d000310128030f100d82d00840c5807058001801d46103029140410500029030090000a45603401c84070594503542c540c900340f05902c405030401c0c512800086080c03605085681c00540311061071407601180070003036200861800003080036603041441d0010110301c2c55005903000c40c4000c221071501510740b039200c1011505480341628202e031710550001c2c0202c184001446065912501444c1c180b00990b110303e078900160445c640b84804440071a43c4c000c0806000e8035598411200c1c110603524502d8840180150f080410321803000c032925070761505c0908004541100800b08500d11201601c1801521540001e100e074890490700b01315080e00122b804180c200904002c1481034940940d1103041a03c000c20364041a44413511079401800711445e844001590b5a0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 419740566 1250 419739316 419739371
    0x60e010332010204090b09010503030c1b120304380f0d021b0d0f110303010b180901180c0e010f030e19030804050d0e1f03060e01120b070201 62
    0x480d100711400010420400741c652400082d0701c0002d0004410031070360401406a41c080305d00d14002da07a5401450744900c41c080601c0811780007074000070150b031400980301c01c0321200a002c000542481ea01443d256602a400c020704080502e4806c40311000d800d048813280c0c42440c0e80d0717004213401b0b402d032044890050301c41c015580c80d4003041c1e26150a120b941900c0d01042000031243da0042040c1c40070380c48105011b000b81c0019038107802c06000300c1c00b4451711941100d14a000350f00e181c3c41d000380c0484582210a45049410150002803480c1c0d5450207010701826042c042044000d807034010000884803501c00715414408200e5004605a0f008203442da0040440d00340405d41240d84080d043c2001501441001803135001d02b010710626600c0241c0c10320075441482291162100104251460541240c6281c0d1161300c0c02c001f02c8440d040c40c5880b002e032820030306004c60050340b500d1618450b0070098102d11aa03801c0d03801c111b01800080f040035904958980020001080140900d110702d13440a03000c035 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 419741816 1250 419740566 419740613
    0x1124060f0a1a09010e090a0c0e01020c0a05060c010f1b0306050d021c05011407020318040605100513080a030e010e0a050a1a12070903140606030d080702191104060e0103 74
    0x2900b82d01810345e080300a00010240f110a28022440a005110415aa600050708021201e0441d400000c501c000300d0380c001c10300d080e43d030301c0c0100700308055202051071101075480d410120000c810310300440740d02e41d0507442c0a200d02400d00200404482542c0d10003881480080900b04c050384074804980c40c100c0f010b0710355801e442c940c0d0421a01611a20b58514003e04004080108030f035404070241c95181070b501201003915085c20104415511070f40160380d030103a00e10010410140c010380c0200102110640f404480350390380c107541424070b40500c405501148000c9401c122942e4809015030b44c036003048516590711420030000ca84030504a004420240c0c00100c861607615030360f841901c02079402d99031240240d00e1300394001402c002c0305200440c0d1044084414800078107011800340c0c414000a4000c203400d201100c41150750680180070300c0154042d0340c28003000300c0c603005110480750f40078403003445058585030180012148240d2140611010403001400050001e1110f4580e100304070a52 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 419743066 1250 419741816 419741827
    0x501050d02070b01300c0b09010c0b09031e120402060f041e050a060507030e0904030e060313030908010603030210050411090f070e0f030d1124060f0a1a 67
    0x8020081c481d601010700f20380d000800004a8168018031104000c0c3c801102440040c5074002c1903c0050300850300030700c489514a0240310300820310010300341c95401450807850321041307038540e051134180a0303071154055080041c1d00158079010200c058544141d0742411032401c00c402c100401c6d02c6001a0000784501d4000070704024800285081c2e402802c40c0001085216200151010603064148a4107018010189000422038002e030241c1e00d165805440b5504454003030030401460960040045080c40105000010709448640c007440c805c1081c04902000003c1505018184489952140d4a80ea04240341480044e90118005103c40440400030505442c1d40c03038202a400360b003c00140d000120101001440d890f08800580030312166100c5007111580b6005029a0940c0a0407594042e480b090120a10a10405c07a01c2894514642594801032140622a01c1355558904040d21403d03100284089454040340c8415110000c4507260841d82c5000c008e031041da0202c680300c88120300003144 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 419744316 1250 419743066 419743087
    0x30402030c090702010e030a0e0f0114040e100b04030f0b16120f02160f11090f0c161e0507290a0c050d0c0308130506060409021f020f0d05040609050105 67
    0xc1b01e0342c0030f0000e00580b521240c01c1d440080008a4900c9aa80f1580c00c100c04030b105035000b600440c064138400e40a443c509400c001001c40582d1000d070114003a2109000d001405007544406070000e1403140d0038540480085007040c0d02c1d6994081e00c11401e51300c121602054482c0c000001100c401c0c0b061001191095415116000034000c54032140040035080381ea00d001c0080001c9041c40c264801d42d801c149170f80c2d01d0010300c2030700c1400b15a138020348610400880c0c40c048444020b060350245160349070781d102d43d89540d2410b000d40316103000554441d03960040c0e001c20100740f20217030180581c0d4006004544000800c040380c01005c00c00c8000341034000541121052103081c1c544407103900700d0101c5a90003c992001003403010b1040007030700041e803c0004280c4100c0203183c0b0010083d0800300411140d154001000000d291684089030b104c41c00140742034003000c0d2400380c4006640d803030700501600145001a01d080811024050041040810041c407040e0b8100f90400240da000b03280581c2c42c0d100d07001 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 419745566 1250 419744316 419744321
    0x3060126190902040c0e030f06150d02040e0106090605130207170714030c101404051b0301021c052706040318090203040c0503010c09062a08031302030c0105030402030c09070201 78
    0x62003e500541081c0390300481c160840c05000307841200740c080750106054110100d0b1510804d86480003a00b95465400700107281142d40100c8050000303000040c0200080380290840d52a54040c10586440da0020042881d20184905018103520025440c04a0315503032400c6070070400e15121850800484e140d401d02400f422044941c8114904036580d5819107030009a540c84400300f02c4405d141040c18444980c0c100c03080b418000d40e840801080d0008841c8240c111007805c4082103501503500b40481d00d804084180326480d0307071007018000101400d1040401411115130174140b00c400a06411034102404005801a400b5406181291410701c00f41031984407141581e00003882c560011082c00184400d00e1a00c204a4604500800101d05811410741d15100d66200390b0000c590380d0031104910166030400c00f00340b141044148a400041640c071070f40326400540f18510001e85c142480380850800b00184000d90300c0908100e8198901680060b5440c1e42058440b400383c0e00340000314140038002d4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 419746816 1250 419745566 419745581
    0xc03030a022803050907090b090a0c02030f0403030e1311041e0b0a080925140a0306090503031f0e1302010e090112110d08090d0f0203060106050306012619 68
    0x10100c042000c102c0e888024040d241c29240d0a2640c012001c0010310f5003500d114110091801501e01c00d01651440c01c0d00000b002c442c0c0704072055000402401222088050081014511981b510704170508130300c00340440c202c154215800c0c1a1302e0030b20b80c045070900d00d80a4504503044110a02c40320b0480742d10a0740c0104031a4003042100030041039044205801000c124802e12a02044461014281e0990002c51071a816000d2040d03060040910440c10f0319100c0d8404200c000d0068003405030b60390b03182c0d421a1a0040d05a90baa0408401d00c131109180030300351802c00440180105034542082041d0b10710b00405441020051880301024086900464215a000d031004010b4070310741d80c1d03644484000c40c82e000c208891503440a0025540b5240c120840c1c01010b80012100b07040c420b811007480f4505801480951306180018032080c010381d0b0400031240030b03014a1b91800d40300e04020001604d01780040c5880c0c100425001d50503201c00d10070144007941710010400700a450003405e240b00e002014407 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 419748066 1250 419746816 419746867
    0x3060302090703050a0b090403050a05370212130b09010e0904050705010207120c030b0414010203040c0f080d080a0203060604260d110c010825090303020f030c03030a02 74
    0x700801c4040b50301036200c0703482401890070078011000440204005900d0441d0300801107082840702c08907a42c030400c00307041600450350350f50b603e035650501c1c941034008003980e00000c4440d062040b0781c0007590501814001d1441e00c80414180b0001754003e560300d84c210f0103600112007003c640c3d10816072150206002489016050603042e04003070070304503103c08403030088a0140c40345800005540054440031340055070025042054282507640d02c50340b4000c050001d07281c401a00010500e00070b8284001c60103503103c0c0c41d051101500e0841c800800c1d0000c1e40c00b00f1450340082645c192590f400ca1007440e400451142c0059595403a8000182079000303940040380c0040000d0b040820800240040b02c04130351444044440403511901f0480f0350509141285809810040b61004254010800150840944041c810002e02041d002140114030700300440002400590304006050301488030b103924041506c0a07500c0c0500003120150f40c0d200c0078050101155000a5040500002004040c1c2d03c400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 419749316 1250 419748066 419748079
    0x6061a040510170a1a03030403030e100203040e0c04060e0a12060b060c03040b09040609060302060a030b03011409060f0c030108070e101d0a110403150b010c02100f031b020303011503060302 83
    0x201300203800002e002110160300050014440d40200740b0300001503804030790303250f55459440000c150a0113502154040304c1340640c07005010200e404c440070340c00c80e48100111402c3c151591329149004041e9444000380e00d000b080e010f0424840d41e4000ea412040180c0c108101042694208002c100c851058040241d030b1400702103404180703414403000038141e02d4004c80d010f100c59500c8225120842e915440003d41c40a0104005103599020340c11480c40c000c4002c5c00002c4000c0d26003507001e1440e03070481d0b15064503040407081006180d04042e0150b006602c204e40d40b8250360606c0c004a03039944980c001ca404000410000440c8005461100f001030000102d18024640d0402c0d036800d900001500d520110301d0a001c0303001d00b08100101581d0480347c000341c1c04c2c40039a42c1d0b050000d0061440c6281e480c104906402c42c000580c9400b0511210380042d035950654015291100070211680c68800c10040e01030008003107400790380017003940d0641d0b03d85070210106d030048101c150010078040d48002d41184 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 419750566 1250 419749316 419749321
    0x120f1b05090705040306291909050103060219020c06090415030f050c010912020a1a13060206061305041208070c0501060e16020a1716020a09020706061a04051017 71
    0x3c1e40003001c1c00817a4440d00040c0602ca410001c4d0303101910b65126800c40868845428042da807500141845803080344d4070044613819180c001038070594000b42c10981c0e0f400e400044c490552070543d0151f816401640c4003030000c50b00b2041c00a09581708502c1028821900d69252098079a10408510300469105504140c403440034640719813600d098802c5039000c01d0440c00c0004142060030010114168010400311000e8181a83c19416003d203034015800c81005000058981152100b82c4001c0d2140360001c02540c9001410410000f80c05032008000d0340c100410701000901c140402101d041b880d0526119036600c4c10301c1118503605021340605958200b20000802040b000c1c441d034045ca0680030b00b858004820740c000d80c0d5030002e1303001c01002035514000192440c00140041c10700360020300d041075030f08080d51700080e00900f10f50300468952a80041c604040000ca0300c100c40060a54007800e001540000280c1d240314001c52050b41c4c019258101aa000d1078400c1c81c68a184440c8000100401e0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 419751816 1250 419750566 419750581
    0x3040b0c210901150b1c0f06030213050a0b01030b03030d090f05160f051e090c0c0109032a020d1502070605070809060121031b0218040606120f1b0509 66
    0x20000d5003804800004d041002099104100045450034800a542c00d8941d000380070400008049041040854580d034110220042c0d03940d05668a0041180001042a06060303840c001141c90600e4603e051600e0072441040c107440c0803054a00102c8a40d000081985540c01e04144101d0f503400024640d019069020507030780500e40c41c0c1d200b607903205100f200b04107840d0010700c83c001c074011880030040201404900b0a0303241070303e002c50f84112038448444c102020000d030b582c20348100100c00c50100300754082c450342d422114001502210034034040500303148543c0e0081425001c00729000b5041d07001c2111008042d031000d0f0100c0e408154416400c004c20314210100a20b000015141440940103020000402c450702e0400415540d03110340a0142c005030b299020360b01c0c1141181d410461981c0310010902680c1c0344140000d000c0848400c801080c906454400b00b00c40c9903800c03010340840000c0c10b400100f00e640c40c0ca04500740d44043c080c07510542a101c00b091003601944a5039210082804000a4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 419753066 1250 419751816 419751821
    0x1052104050f060a09020a03200306070e030c031b13021213060c11120d0e030c071e0b0703110c09012706080309010f09180c09060503040b0c210901 65
    0x4a400c401c00f03030b60264030342030710306002d07240000070280d0701005a000900106068440304100101c44811b81c24407003084002007810000c04640103404035030240f9048440381000c0c4a92140d4540860180204030310f14180d81c422100300e461645e02800b00c008a402c5201d000d503044450321b5008443d160700502d03145000851085500604588442c140402041828010340409030124440006048261913410040125400c070a1a80406170788510400c2c0340d00006100800100a010007d01100d9003070580b02c3d07900b02441207050469a4041e801048001c50040c25501c002e0703414501444034040c1c0300c5283e89842e0030a000950b211000c8000016101c00d0078404914520011041e0780c1c291032800720a804581030307072042c03090302c1e00204480320340c540c8503401d44022034001341071444180d03031580c04100e21800b2040c8000790b601daa17204202601c0f504202268010515450024594a49507450340d1499602401c0f4103ea40e0300800c1c01c08040101c1900742084105049000c412403a018032107501 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 419754316 1250 419753066 419753083
    0x27010903080d0203070909050f011403150a050105030f0307080301140a05130b0118030c03021203071a0105130612060e03160327060c03080403020a020a081e03090f0105210405 77
    0x481d40e030700c1b8000342480d0b00e8091148209000025000700c1c0e840c0c1615145040740391f000d007990600805440c0f48080c5502d440303240c01340c001d60a0018143d0704103002c0c1464903045041030440c1d0750007401441d000901e071904980c10368295188442d400454030002c40d10345c0459401c0694005003100300c40c051400d05a01c4242da01000b640c40701c003840003039072481c604180d1a010241410b9900e43e000d0015041030924081810071107401c0300d14001d45510342107401c940b02c43c80f4018116101004002c245011895080d06064480080002d945081c0000348480c0f480341004007955126801e01e201c200060041c2e8050300303a61655642e15100c07520340103182d5283c040e00300080d024003080c9030703580420062104064030f4040d12022810010703a281541c494400800450461007101c2110740107131206100e40b001031080e8802000c41032604690380304c214400c40d000109503031050041e8202d960b500c400c07041c501c020a09015070394207810070701062203010404244105074030b0b013000c0c402009000190502c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 419755566 1250 419754316 419754331
    0x903050a0206070921020a26060a141603060f060f09081b09090a05070603090605130804060f02070e040f0c08210f0c010f020d0b0627010903080d0203 66
    0x942d039a03140141034a088255010b454400c1000800c442d108243c0303622800303031032030000b8440c0e04811388d01d50344c12010209400f001500b841d020110300c00001401c000316038100141d80c00900c0074203a07034101e030761040e04010b0038803400d01e00070149200c3d418020b0380220041c000c0b00940d0600d040c4c5440c0060300c206417082c0100300040880c2c03000203201c400030403a00c0400784032120348003030312524408000c24001b0107803400c200f5005604080300090420031400f40108042d440120b15001c40b410100c1c1118001451880020400942040080d116400302c40030f98541e41007400400c0707100d8404924100c0719811001c04071081030300340001e0120803c82800f02500c152915801c5548945800e9100d400c0c60072940c080070f4048080d240030381e980801030076042210040b00d605202d080c000050a6406100d0221200e59000603a44059003c0340203443c40f503401030340c2c0145480520b401030440c01070300516813100300e95a08017410203a885484a140107541081c5040e07251090708400034000d520a55558 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 419756816 1250 419755566 419755573
    0xf1902010501050a0e09060c030603072103170702061f05120604050d021609110909040b0117010606020316240c09060f050a0f09261005060a0306090c090903050a02 72
    0xb000301d51791251500c01e507802405040c0c1c0b070711030300004081c3d908044c1416a00d40038001000c2192094003844181c03070301144d4550350200c0000d00340a41260003298900ca20001c28004001783c903a0000741c15a0003200d481500040c0440050008012081c6a00003c1e0b1045000d40c060840c1c190020310309000d01d00400030707142022001c0d20103a0f82e54064007030b80c0b801c9444440c0d081042e86d030554403c010448040b1001031400341401c00090285004a604a590b104c0c040300500c145010341503c141c15800c03510003003220504220307010f5581c0c0544440244642c1d030203d5400300b001000f5501c00c0342c200c14521003001c6200001045000762a40550840c00542c0316480041d1051044000c00c0120000d80c658038500405a04100d4060856001c40b40903c43c0d0f8110008880801040c00c80d40c10b203c00300030100060341040a182082100c10703000c0030050401c0207004044c0d5a138041e6000703d1b0384c8100000340020315450f0004268010b58411000149005900310500d6089001000030ba2029400d5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 419758066 1250 419756816 419756819
    0x906010e03030f041404140c072103051b0f0d050408040f0b0a080601030b0603040201121b02030c010b0a032d20240a030f0207050307050a0c0608090a0204020f1902010501050a 77
    0x522084807c50100c21355411425004107a03203901c403800070084180665001800c0c0f100300140484228440008400040d50303c0007084480c803564182c0c05003410b00c0c054444d103003080000551005003d03d480502d2865030314000705d01004030381340071a402014101d902c50003d40e03443e60400c03825009010580e002c10b04000010300300350304c203104540321007000508103801e5481701d400440c1c0031803840004c50300c1169034001e1001c02080c0301c414402c0389032072a4000c5544230020360303403a800d441020542c0e030f005400d402000c1c00000c40c0d601000711030508001940c07641d030324405220b407080200b543e40540100c44000420000d0304411100c04907e01c0e05890176400306090450704540c074070200103404403000301480005099440381d0040054a0391000b009424580941c079114210307809a4401c84203944a4083d450410420f5070000000344072030b0600c40642e180024450351280351055009100e15400030f034a0303c4081051041d2180c01c0e40707120304051021032085010740204000e0003154400c01300040f0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 419759316 1250 419758066 419758069
    0x809040e011508030a26041202010207050f06010501020f060906040201030c0212071104111c05130c180b1009060e01030609090b01050f0303090604050405070516060212070c110906010e03030f0414 86
    0x24882181b940d5071030365070f50390390399281c0e0b1041c1c1030800804c10455408001e031501296007000102c803154004000340c02c1c2035242100191a00c8109410303020113801c5401001090741c00480c003503a0041e02800d01284032a1141030490420030078444000c116003010800f64140248510b844400c1842550304000e40021a6158a041e0003020740000c0d45850300c40c0944040d07109a00030640104183d12140c00030101941c0301c1c0c004078040e400c0802046154404040034103014080c0c032150080c2034451144240c0b01d071344020005823090203000140030390a05c05c945140d1003503015038001c1c000000100300c00031a51600e041024802c1c8502c904c10745403040000301910700403080710780306003004000702d1401d4503003010b0002800005081a0a1010522014182c090b520710300485251103842c005943d940494030350311080602406107230030040170800d03020000e021800d0f000654070080f50481001d43e0350000488464002104880c0c26002c00314461402d0b00c14100a402916801ca4215070311402c0b900 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 419760566 1250 419759316 419759357
    0xd120201091a0c03040f050705040903020c0307060c1211071212020c030633100c140c0a21020a08030405040f1107240203040f0b060103090809040e011508030a 70
    0x90790311603105000c00200d8005880000385446c030390b106506844100d592900058111805401c0035805a00a0545003602e45814801c081c043c2c107440c00e00f506801303460388406603420303081c25144c41804606942a00b031004104200e50040c01584000d1901c22951f28125005211400c010320161040404c56001845e0200d4050710a05448040c1190b10f40000c0c08040d044903184058150455510f42c000000c2d204e060b04464500b01d5a00c50003007000f2203280c0010341c240708456075072580c2c2154980d48000e54560390380c1c0d0201c81c42d0140201d98803a0014881080d011040d00082d03110034107e50000e2030388004409401202c1044901f0800b03501c0a03a420025034a0715818190345102c10841000082c044204450280380440da001c10050554075282040342d00590342500c0a1042c24902410001114900c0b507100e08207180500c400b0050baa6620101d004800805100d1034407100005a111800d50081600e0a08420f041880b140c1d1046660740300e078840a40f4900050462848400580b00791 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 419761816 1250 419760566 419760571
    0x40507021b010c060e010c03140f01052d10121512030309051f0204051c23030708030a020a09270510090f0501180c1d0d120201091a 58
    0x440031051007022900c0115038184031500d00f1514180d036914605071180c0244a00c030100115620001616104200034040501c4c3c000c1800c264003020900601094907541e0550342c503100d603241c450458589001d46000d9003125201420381200c8258150488640d01110a1501c0114000b08203c2d400b4404088075150644e4007941a211418014400010703100754010301045002e03205584520400b062004415034007014601d021580105003031002d450010303a03980707a1400600010b401008660361b48100c40090100342c64107452100d4120305483e4061084405045d80202d1066603403924203070210094109036001c02c0003e0342c021001c2200500007444945400319008100080445000c802c40030b07001c0100704551448817102d0002c0c106000e401480340244a4030710210322507060106440301c4071945140f210f441c60510306c00d401c0254002c943c181c41400c150300c100a18407602e80203c0d0150480c0306000b041380c00a65001d464456041d4020341b010703403203864181807030074000c1076414401c03100703 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 419763066 1250 419761816 419761843
    0x201080402060c1f0e0607080717090c030111041a0702061c0f0219020c1c03050304231e0105100506130803030c04030204050903070309051005040f0605070204050702 73
    0x804041405858060050580c4030f00c00340440740c0003001115030718002d4006a00c000803080e1141d1142c48006014065076601c8641442c140500b403402420003012022034804242201224101182d04118140064805110064001d02c11102405400e120561107441034901030a4490150f028060040702110501c03a001031145080242c1e0000310701c0d00070070070a8a84042d03aa10a00c511840c0424009403a400d152410501361403007482c800a0b04011001100501c54200054860800c01d014600c0441d10364040c9007a40d03c0741e66920341b000007100e0307000e0103420721100900382a00c0c2d071500061142c0b1501c40309684040c40c09542e4032150984600396803001d4025600e030317802c0c0003030305202000d01154000e1040703680070b5503540c005150030f5600a507909402c8030320001d420710070350405000351a0400b40c120001c5252007081c0d10002d1442c105401458821085c82002524003845141607501400c005035200301e84680e2100d000d8515409000c0881c029802c000000b0a01400498000e07000000c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 419764316 1250 419763066 419763077
    0xc100902100f0e0910030b070f1209020402040504050f07090e070921060e010c03110906030426030a050412080f0c03091005010b070219030528020d0b07030f090201 72
    0x500328002e8440e020030740011410011203421220180c1e4600318000e01036400b000701c410300941035080281c55140300510701800c0c010030314800780015500480e844070b2001c075107500150001030340c80010040d01c925070015030f1280c188802d1041102c0d1501c01203001d0442500c42c0303026259540081d00031140211032013400b15070780c2d101c00c01000340b40345511400045069025800b038012540d9000494010040b0803601741e40d24103e071114650584103a4024105074131003c0e00b080c6003040059064480241f00070140403040782100c0c080200d4908464002d0314089840361a480c04844010003070008071400c0e60840182d81b10b6082c42401140564020000c9211035541955191080c4e480caa0019050401c1c0384210440502080040d110302806000c0001e1031306d40c0d80c0789a004101c9940c000b44c0c41f050300f180400d5000c01c0042e0b000624813062030308907091075515a08200c03204541c8000c0e007c002c0d40155100e5921400c00c41c4d4a81d40c5032080413284c0382041211460802c1d4003c544c82d400700207000c5103 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 419765566 1250 419764316 419764339
    0x901060912020906040f020304030c03020717060411030a0519060506150702011d060a0804050706080c0409050405030d1e05090c06070303093f0216061107080607050c100902 76
    0x70702c3d20f801e40e4401c03000340010404c91190381074501260b10840c1e041e00041e5192103503208043d410b0040e41c0c02049201e10040782c02e040c250f1090b40341d420107800100355401c609100a2141c9051000d000c1046d000804d0311812300c403211a0140400b02c1d0802118410320b072400080140c500002400010045050030906121207680190341100c50f001100000c65009841c1324050390740c20300140030305000c039034640455081c54034209251800c00e1708600c0034886010100b2000c88a59002d5904a1f0210b03840445c450310385040241c1540300d03295248a4040c10030b0301044040f1640c1d500b0415484448204214a81e42c90702c029403900003c01542d80d01100030811200400c1c401d81051011502410240f070f001241401c05101d90300c030903441c80c0245495203950079108581c42901c11030403c0b1a001400c030441c40084480340c101d045004000901c031111707103164040103082014902070a0b1200484509080c5a10041d00b0354200c0703258000c15214403895032110383e01e24010820481c0e40641444020f6 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 419766816 1250 419765566 419765569
    0x40501060f0e01120203010b0403111f21020415120b0a06030b0a1e06020f0a050703020105070312050108010605100e0303250b010e04110108041104020c030c01050a0209090106091202 80
    0x480c000400c10f040103c114600d98801145100450003488140b90f0650b50b00c2c5503240c40040c6c2d0060300c1c00140319500a6801e901f400702ca000045500114614110381111041080103000d62816506c00404900c04a00400e41500c0300d03403818440c0d0240c0d01d0b00e03440403891a00d56020f552050b868590000e40e096800c0200502a810085680c0001000c104040e5222070b0b800c514400301c0400c1e000c110710181020801c840d010b1000580f18007030312010301401c1015444103640d54034079100c02410010f0000d101c0c010f040c4200f01d00701490700b008000703010360b5a5912003a4080c2c18030f40100c038440c10303120100540303560141001901e4041c010b80a0360406060400c84c0c00710342d200000c903d11342444500079500003180104c4480c040d1000c03954180c41c5080ca070418481c0a11520744060520031100c05010228080c0a502c401a0108072009a80d82203400003550450182030821078903076003803005002d8034502d55000342444100903100ca40c2c281c0c0e80c2d80812244001240301745500d21000454241c0507 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 419768066 1250 419766816 419766827
    0x50a061d07090c030603080f0403030e12060f13060e010506100f0801090507020a14061b03070c020d05211b030a0912021f1e02010b010f0c0f0507030305030109050105040501060f 78
    0x510303c64100051415500e4071645015840360181e241da500c00000c0510401d85c2000940510241c292010150303c2130003000980c1d50800500310400c4e100c403400000e041c0d8104000101c0c4803607800402400181d980441050290005450983c841d601290000318114403811b00ca141d04400c9030b0f500344240e480c0c48100d500901000d4192002c50041910110101e98038810308103490040e136000b04294038094031600e07609011410a004035200c10414000035990000303440e640181c0484021440c5400c0d4640286403c44000c0043e42115050300340515802d480c0000d01829100005d0400d5201418130030142c59115400300b210104480d22001c1c40140080320407030b420781348058500705103c40c1e9440d05450440c951310110700021885041155045448080e40207074a420707000a00c030100281e4000b1308000c100310043d0080201c90880c49050114400907080f0a5810100b540c80071512810002e183c0d40c424000d1030203140c100400050316081c203108a5040361481d94509000605640c02100c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 419769316 1250 419768066 419768081
    0x708070507061805010204061701150c06020d140109020c06131205030c13090504030e0f1c050304051c0b01081209010807020c0a0b1903050114120712050a061d0709 72
    0x180384080070f1010018909200801c0600207944a40711004070311861401841016003000b1002e01019640e409403d4000f030b0345259240e0711036009070302d940d031920300359000307182d0006200f400508180002808005940c02003c012850000360b4440b0f03511000300540c1190304020043c01d01c42e07040c4a24042901c00c0c0c0285800000042c0441c1c42c1c00703080e203a1a6000b070040d41014030b1442c0d640701031100709508003800b0100740c103054a4420030588442d0003e901600d41404000b241101503591000b00503060086602510000388220100090060183c1c82800c04400450345041c0d10800410580b0000031161452410300220620f02400e5500441d0100401741043c0d00b50f10960041040d50350300d518186000e410b945800d0342e1600350303001c0b0380d410b0704941ea00081e0505103000010300081d1450f01842e201201e0a4922114040b0a00780e40c901c0d18065501003000320603076144020801a0114a0055850040d0018809034020344440841108a000c1d000c5003a40b00141c20041400705421502 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 419770566 1250 419769316 419769341
    0x14010503030a140f21010501261f1d1f0302010311070b0f07020715080a1107020d0812010b03060616050c0a1d09010c020a031b0f0f030305070807050706 67
    0x1414402500b9004d8807a030001898a80092540d18444100c41d501c044428010704007480e1408140c060f981600d411298504407100c14010004000b80080b036030214035034440880100300c0681980c0d02d9103020004c107042d07170410910b003281401040960a81d8503440400b030300c00305c503218030b014610350040d030042c40d0700030b591901104103002d10000710305401080d51265001d9051026285840b4030000d042056940140444280c00074071703d03102d594041d03410b59002100d6031000500329490700e090f403890700074a03100961004070030a125080007401ca01034041000784516031070b0f01e6600d0315004072103130000725145900200d0078861640031a003d00741003010280144280c9410aa4490200e0951040d540008544c8944403403d503042540e030203805070380408200c0003000140d001900003500c0702a07401c80942040600b1802205070078100c003400014583c0404281c509403801d1501c03988010700d500d000d40101785400001641d0f00e00480340c941c0305d1109582c43c2813624095580d0b80000b40340400009 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 419771816 1250 419770566 419770607
    0xc03030a051f0602030a02012406120912020a03020705010c02060d090204110a050c06011202060f070c0f0311030d08101806030f08030615091302030c070c0303090914010503030a 78
    0x403400402d241d01480c003422640d405150b8803641d560020342981c006404400114508800d0111800c0c60440c40005580c05441c1c191f10201110500502074911040090091044202046180c5400040c0440c0c00b500c241c0941d600b42ea915001542c80c12a450b60194007c4d10400c4003100c0350304542d10544425100401c00203c0b0500c503034403038245400c21a180070210390009a405040c0000f0000c45005007002c41c10211218140e502294141c0208981c100003a980441c08508215003050f01001a100907481203080d50782ea410800c52810907600100e009010f222903111b4450300c1140700318401c2c40e0102c140381c2e4881c03804013903610b101c0c00c0c0d0172940c0c1c405507961008800a5040c6081340107580c0915442c07074403410301108220460307482c0d801c0094000e008029140c0e480d214150840d60540c4210001030712581c0351405d4042c54450303008014401c411004000c030405030044a201700b170720800b28041042008840d082c500029007801100d50541c410b10040002502c625242c1d2003040008801 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 419773066 1250 419771816 419771851
    0x1b1825021603060c030f02030912030403090801111309290f1e0913030c0312110d09051002040b0d0c2c010201050606030c031303051b150603030c03030a05 68
    0xc1c0c5056410503001220340c191584d000320351466150041400d1a039030703440d0840c40c41c1004aa00c0750707151405000c5944440010000909060142018800404c3d40030024415504288a2403600d9842506c00c41021180d10401054584580c404d0f2803401e00c1c032402c10341c207441d9042d801c0480b030303c604100075501c0440900340d2035070341d00d640c2950100860740c03901e62034001840c4001c200c040e01000780340d404901c440d501400c012030b903c03c1e01d4070070094040c2032248603e810440302901030049003c401201203c00150b4201a005a6001100050040c41582d109540c0010090160320442c800c0e884440070500640c40c80c40103561101803c00c02905044c071880c14540040110240e60360340c41f0201d1840d0f0b00c01142c09580a01800340d02c008202c80c07032841d51420f814030000b1400064442058160000c00150400d4041c42c120341c07110200400c0c4590b00b01000006a41e6a1082095801a020030802003199801c001060350a04560407000d1815503071041c80280080c03100034403050814011214 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 419774316 1250 419773066 419773093
    0x109180e0d0c1a10083009010909020c03090d050d020c010306062106050301180605090303010302010804080904061a0c0c0d080324130b0102011a0901050112020c1b182502 75
    0x8040402c14546102c4002117011b0b1400c0c9941750fa51210810700e141c010490200302c0e0380d108403039034241c0b5200f4000503140d0b410751202d03e1075401001d000d10f0b080400101c000090140008921901e1a4550b08450703002010000440c00d49a0038414a00400c45407280c2010340e018a1320842001c815070721002480f9541c55000909454101594250106040c2a14010f0014a005190313000c2034000055295500d1a03000804100d80204040c00c00400480d1248440c1d54540186008100c2c0a400040003240e030318210280b030f48007000b40c028600ca10058561942070011041503c1c94000202c02c0c2140d4030026030791400c1c00300426030001c03009510726005242c3e4070740312414401310881100040841c490000a400c5070310740968100c100da070007210651700740c0e103140706181581e0003842d080c54000064806a406805200f10600c0240210f840080148000d440e40f501c00410449038400741d08500700341c020700c40700c060720040108480862000052226410701c20101500c0c0e20440780ea8040741003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 419775566 1250 419774316 419774323
    0x3020a020f1204080d080c04051201140c0c07121124040603020301150309051b041e0207120c05031905040b12090708120403020f0109180e0d0c1a1008 66
    0x8191441d04900443d003404404c03c1040002c0300164241011081c50038031070059000c2d4001c612074984521079160045000c510700307402036000c00b502e850800f0342e20304201038520800e412071868141e10b403080040000b254007400100119064000d4040e0440c0180707641440204001560303001e0301c103000c0c401c456010200d45001040100419500143c4030350408540c60740da5928410711b84101800c0c00c48400c0880d4000c84d40c4045115480c4031207410313051100c0460301419584002012011110042c0d01e0010602d07002060014030a21040500300512642070b51401d1915002911a0b40309201c2504020150300c11304d44000c0c510f00300345040070380e10740806c3c48580c00030f0342402d8085041024025155410000c40e0058408007001d80358404248034088128019403101901c95030010144001e00e90194000c9000b51141c039030802482c0484585500241c01c3d81407040b800c9128103440ca01680744214200035403183d01c44101d6003903aa42d0000c8004802000d404ca800c905003c0c0c800107038100040 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 419776816 1250 419775566 419775583
    0x260312091f1b1101060f06030902040609140c03040203121c0b0907020a08090a050a03051c0801151d030d090608060618010f0c0203010207080405041d06060103020a020f 74
    0x1000415450803444908156000c030850100c05090400501c80322200d10030080059000712440c3c007044000c2d032003100c1c40c0546281da20441c10398188440114296038190051b01415000340c0b0f00b440015564001031048959055445201d102c4500c0410300c007280000040d504940010308480c0e4201c210391040d0b21070350050115a4a8000705a550361180c040c034091035001c0d02d002c41701d20001d4601104065116991400000c0803190001241c00e0560b886042c80b03005484040d0600d41070503180e1604507542d041499075204030307034501c0d107084d117036248907e0509040c0e4441c007410f0300c500c0c1181d0314260b0303580421202e02840707000511700381d8020713407020007041e44190701590710842060b14000e0058820310028020354081c000401811407a5400c0c8007410a40340d000703103400076585651440840f454505910000d40c9540001402e9050011910142003940e6003100c0c1084010002c0000101608545494603419000400040c6440d80240c1c05442b065001d40141c85010fa1111441030a00380d05 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 419778066 1250 419776816 419776831
    0x30f070c150f021c09020603190e0604050f1507050d0504030e0414060a0501020109230a0b0a0b04050106050c0703020f0607060510031a010f15050c061005120106260312 74
    0x844d11310000c0840c041c80c00d00c101109102000580426000f1880e43d100c002c1c4246448003500c1c000240d0b903a00c941c0031014010f0140b0503503419080616041751500d1240011280520510240a8055954881e141e000d9270840c0c898900e042d040c0c0c0400806000010401d800303201d05082d408805d41c43d140104412101035000ca42050b02d000800c004840806801c40f504581c905401c000004185020b05d10180c0000e10107114080c029468503031420810b031400528244184c0144402d043d01340d0014041e081c41120280b02d26031b25202c0c1102c0c14002c55410020303a91041c0d200308090f0411b0014003046071ba0282500e890490542c84240a80b4030580b4038950300c82c02030200b0000d0110300712030002d0400000003200055490302000c1c0403484128016010311169940c0700f448914050740443c1c0180c40d180c2c0941d00c0d1441c0240f8849600340042c490030340602a4140c0302d00f444203041c8905010f840d0002c6031003d26aa040c910342c0d11980e0070116505c807510040000c500d8a01400900c584180f84 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 419779316 1250 419778066 419778071
    0x3201801020105010b070c0b0921010605030616080403120f021201031e26160302160f0612090501020d1404110d03141303120e09010b030f070c150f 65
    0x820002801c40c0c405920a040103d01841200c000800300f844610486001c41481a04c543c01c940c0000c40480c000361a02c0d03610b800fa4a07142c6621941074000e5401c8070422010344030b10b5500c00c8da580340912160070700700000681080c0003c000a005090107040c0844100000400d49086c00040c4105d034800c003581c01042c6040c00040007000f59840c0704018408100c140c03500c1c4903a503079441c0740300318041c0040e4020035180107408007034804049041c0c4040100d0501c0640071502c07503003400f075224964030400c040610313a106404611245010050f500b221000e503034084c00b150029181030000c050000781112155000c000d6800011043d007d103d01f0400070a4031100c65090900d064041c0034441c1e007805001d68102d1241002180d08031121610102030b840c00c940c0d03518080d01c5e25615500b96908010107900c0546034005505910440944200c8400d0300e0304162640c0302ca07a80503d82c0801c541c8201c500004000083c12540718907184006039114101e881480c0150114402c180c901c112243e0b031a590b0b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 419780566 1250 419779316 419779357
    0xc020c0913050f070311121002040b0c0d0201110a030c0c0c0305060f090c090c0306011b140c013f1107020a0509150603090c03120a08010509010e06010320 68
    0x5003030180008000f00b800c0184105031940d03030344020030301000d0030039071280a0120001840d190140401c2d0540c00c040701046603544c0c0c0740d03004581c90b5040002a200365104001807800c1c83c90051140341444400742c0360b99420000002d0046029003210f008220400c101c110701800041d12070740000014520900113001d0500c0c101c0da00f1848203400400300d0074203511081c2800d030385840c0c4500c0c940d0000b04418030150f90f41d84400060f1180d010440c01151100c160b0803020f0240202801441800000e560503103803c07038429401101c661401040c01d11044170300d01c65182d600c4503084c00c4d45070308031110050500c1001314451a54210340b945540c41030b40c010300290400c2140307003020801d00540002c448020060400052450701c145085444034010840080401c1e0015020403400320340110086c210b440c1c60b0703010088041d50341c000360031003008500540004103082c07509011050580c1da0603584041140d841c3c100460142c042c0e20030f8000f1801c004500c10340210215802050141042046009600c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 419781816 1250 419780566 419780573
    0x305100c0813030c080a0306080a03020607140418050a1401080a03021218090a0209150403150902030d080c040e01120201081012060b030102131706010602070b09040c020c0913 77
    0x42c4080980800703261a000065000428482c0141e080041e880c1c9600c480c00e410f0703008180710382065440340318440301403082513030004034144030f0541c1e5641c01001080c0170f05595114012070103800d000f14006a5a80554400c1d81d1001c5d503c66040703c00415044428a00000d11070707407c1c1c2080407941c001488400c141a01084204014040310b0001d502e00604e030702402909000b13081ea4644071b02102004203002c3c3c4c02d150140c0390702400040c0a80e6400441c11a0710318254000d220441d507400009110f81032070100741c070400c07a2051300503015214504507417000700e48401000b44005a055070a120214541c44c001003820302030010440301c80044043d80c0009801d054005009940d0070076041001c0c841546687c000091455220708041030010385840000d0280c00703040c170402240212030b02e0000381e54280940301d418a03207064080e92810b90b2191170881c0c0310800381c05000f003186003c00030520384d42842d0340078034844503880c415180808250b2000600d00081510052202c4030711003204400e0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 419783066 1250 419781816 419781827
    0x7051c06090c0828240f140a020f0703080408070b10090e0705010207054f0209010807201002030603160f170f060a060306111c02090301060305100c 65
    0x9260402003143d90003090006013030305182566802800780c0035a0002099014601c8001d04090415140621010014030180401043c00c0d004098100c0e240b540400c0d50b082e81c0d48220345944500300340d03940c0380083c0c940b070542d03030608090001c84154108001040c00301e060003d0681c040c480d001100c61a03189040303400d509a588801c0050000d412020741013080d607030002141c0302103030410b840f10101d006846148011440311142e80e00050b0658203140c100b4200612806c0003104804d141c2110000060401c40049014800c1c4550126240c035011448080c0184100b951540018507543c02c1250038218071824446405460b244043e000b105000180c601404007249410120711540c520300e1400074901d230031010a1248a1a18101c10901c50f1001420700c07422281d0b191740011a4800d0415440c100014070252205590f26494028500e1349615100b0880e07049941c03c42005400d81a8030301c034000254440c0c1282c0b80d0544d610080040001c070280051028001740030f40020f1071103540c0401600 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 419784172 1106 419783066 419783083
    0x60312030f0601020613050c0103090f050d1205060f061215100c06110a0e1905041103010302030601090c02030714160314070807060207051c06090c08 66
    0xd112546501c0c01c0c002c080a0707007140e0071941c0b03c0e0705082c1c820345080001040b9410240d1064400e42c4a03801015616010707800070708500c245a680e031841d000c82400407101091480080d0394000c0c0f07051090980c0064140c8500400084450004040d882a04022805514208041025200301d0001400e9000002d002d101d040c1c2a250b82c09452503100b00000c8501038145403500f60511100b200b52200c0d000c25413200c40b1b002844008104220311181880c0c0300801c0a00800500c9a90718052189001c0107490f229a0329415401407608000381608540107890408040c3c4084aa0000c121207c164000c100340035446007035580181046407041c0c1140c45880000700100502030815100c010b0425071200321303030190783d0b2044140c1c3c1314259031040c0000351700460410403407401c0103107100114203d000c50740c0d28400c0c10f42e92520200da08101c401c2e0b440d03e11942040c411030508101014 = true := by decide +kernel

theorem cover : BRFrame.Cov 419604316 419784172 := by
  have h0 := BRFrame.cov_init 419604316
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419604316 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 419604316 ≤ n) (h2 : n < 419784172) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
