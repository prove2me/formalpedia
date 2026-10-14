-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3474
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:46:22.473082+00:00
-- url     : https://prove2.me/submissions/916455ba-d018-4b8f-9560-a3723f93c3d0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 624640287 ≤ n < 624820143 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 624641537 1250 624640287 624640301
    0x105120103060506041e05070806011412043810240e130f050105011103040303031805030f041a040513050a1523030313050919052e0612 60
    0x3d100186044686c243c0d00314402000b24042071031b5988400704500c540c1c01100040c0c0c40310003440c1c11100103095403554082401000941c1c01c09155020010303003040280998501085d02c1ca82200d120300013002c01c0e861140c2045c0d40e154100c10300b5400882c6980d0310710b824801c00d030b40c00b103070704a04008040c1d40c04040001042a020003000041e4441600c86d8403080180321075151014804100740e0224010f8105403001070703102030304001c2d29100e05a030301c050100c1074a003901d0341482c0c0410703503001e40040c2d01103180c541d07000500140130010f8030b9148030307080700b000300210b4104004424064000210791889070055106807034010001e045610300311585640b00b10382c07243c80000009034100c043e50195440400320b4112003c40d0700b0192006e800c040100c1030214a0030b800714001c2d49007003108030307000541078002e22515024110b1200030807564031240c0e0108180c840d0071082005203140022000d05800c001000c0d01c4e030b80468004508600490003162401a1000368591119a80704840c500c4020164 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 624642787 1250 624641537 624641539
    0x91a01050d0906151d0105011d01020a1415090307030c0b04060f0906051023120a05160603180b27061510020304030507151e03060906050105120103060506 68
    0x610b2020100160729445604012040c5812442c00c40c0d0602802940000c00307610002d10102c20070004000f5681d0101980c2c008420f1100342c800f03001e05150040c0d1a24184c680300400840c4030441c2c0c007040715800a0b04080350040c0c40c1c03171b107c1d040e201c2800e040d45134400c94601030009059166510302003038402e0300f503070f81243c0b2a44000501d402d100002008480e01210209d40359500e5805000c0c0b101100680e18010b032a0304c004001c00c0c41c4401011140c288070782203026019034054118031701c131041d040c4012003000d60403801b82c5003c00010391142c50110031034013400340401d14000511034500d031035050302001a40d0052490b1100d890705240025048000400300e0010745d00d6078603540340d106040c040e05001d0940343ca0508403012821040108410360b041001d0115402804204045940003c82c3c50454401d0b200f01020803101610031140f5042c074010000b00c008a6030009010340c1c2c0d0560108041b141054420449a82c07220011a0541325908101d084c0c0b0500100500204042d0740c811608800 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 624644037 1250 624642787 624642791
    0xf0f09050c09120d08060301020a210e1020121f050a060509040f090506070302090d0206040e070233061903030c0c05040c0f0507030e03061906091a01050d 68
    0x407042c2c001644000100407203511600001c24a55030180c0200c061a003181c0c0c114001c0d0305104207003c009080480d00340760a90501340640030602c2c80503070781c0d00500e28100203801356085040c0d890103d1000d0495051612850040382e09100d08800780c94042c0c072035860074080c00d80c480da290220030108404407440e044004120300040081c6507510781b1003040081c611604c803da00c551580c420041118114907440044c40d0901300b8850004101240090340310807181070050312455000085402c100d1409802500703e000098081842060030203200d04c80c0d2501e40c22613003440c04ca0701403400311850761440440881300032400c0c0340c220f580d200c0000f50700c0040a0220a520301e0140300800042a8992064001c00c5104024009020400c8411006000140d406104002e1043c50007045442807040c01070030001c0100c0e00f070040511070140368940d4003004040ba1075608041940743d410459007a03030b0390300003880e050300009d40c100d00e03001f03010046002d441480c40244482d8019120359000c6c014540c4026 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 624645287 1250 624644037 624644047
    0x20d060903021204080a05100218100203041e05131b1407060603030302120702010c08151206010f0501020d0e0306010b09011218060c030b0a170f1203040c0f0f09050c 73
    0xf0394107801410041002c4401410f030450741c0d007480d0b400c0c00005c9020118081c01000040c1c442001240340c5400786100b9030340b0480c0b481900f41b00305e0550003030350000c10300c0c001604400401796030700300d8440c1c040d505d08031a640d8152001009660031507900816400d001d20500400c105443c1c064048141c0300420021103d11f044420b40e02c42c2c00312002038004a000c03990205002040700b121a1200e9885030b25030000300721002a03034402a109007801400d50b11031510081100c041c1c0c0d00c48040c2c1c26000d0540c1021181d165844070409520b00c402d50058600502c1075100d0340380e00c02d110322b440900608016020381440c1e4240b844803015680448540b134188410031130008011030480c440d030446912014991010712290340b90040941d865224024101360900c00411001d80d5801d444a003154106810100c0c42c4004400b01805c202c00380c0d5440205002c0d0369803940564503824001c5114510034030561558948031032541341000c1050040c40c0401324540c1082c0b049a040c0d074041500301c110901400c1c100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 624646537 1250 624645287 624645313
    0xa050f0304080c0c1518040902030a030806030115050603010e042301050402010906030c02030d0506041b081f060203040e09030412140f030405240c03041d01050607020d06090302 78
    0x25481510102e031454400103280c03112500500045051000890b1004c081c011600d42943e940e01030003600600e42e070351103040c0c1801940e55074424034400c0d60190a58052030a80c0c00d024007011000ca031381c00e0180d4244a4500400702e0079409140580704028a034a09607400d09031048641c500040080711001070b6442241a80c40010700c0d54200301c2000000130030207161a200042c4154040d0b170200043c94204140c1c0340c0000c1d008415103046002c04403002415540d6800020040c1c40202c9213440e118241c0129466003662113a01984150a0100c04d85100d4020041c0381d0011501442540c005030000e000901182075492074940d00040740104403401c15868150b4007810b10208031007200d181000c12095403141605200014840c459640514103152038000840c0c280070151048041c8901004200311769506090299a960307a8508220303925261581009200310140704803010100d25402c0001074246031074800c45006036805040c190b02c2103141d030b559001400310000200c1c02e50280705c501002e0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 624647787 1250 624646537 624646567
    0x612030c082b061d34050a02070b12070f0302040b0d0902030d0c11190e0708010503100608030a0c06180503180a0b070b0c04080604050c010e01020c0f060a05 69
    0x240e040c142e9501d205014000303035500110b41580c1e01400c00f40d0154180d1407000402c441d00b0662014404400203091141c05680000c80c00c100b000f00505404c098604801342a07104000d0a1998640d8084601254071800710705028051492507691000f2207000060a491240e050302c4e13100303001c60030702500b425112011104d8503001200584055541c882c0b540c0190319080080364003d03140c60501e010107a000347c556400400d40940b43c1c0f4052410605415010420400c1e0f0000600e085440d48900382841e58004203840b1082c490284a8410700c2c1303900008450f40e1181d0800c0f90301800c01989040c2203504250b80c100500101a2400d0340d40b102c0c0744412051000c3c0001d51244204055650343d000d0007032000e20001402c03c030901481d203080d0184000a04641101d4105800114141a65035211802403852080b03412800c050f000c0d040c14407040050002e05d55550300d800341c880700301c07241259004982e1181801812a40a080c424100d411801e00714001c102054451078480d00d0041850f0100038 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 624649037 1250 624647787 624647827
    0x1e0f060408100c120e0102032e03081821060c0a02060a0504060b12070609120b06040f020c0a0f1a070f0e010201020c190b01240e03010627050a0612030c08 68
    0x9802e075000405c00c0545d40c0303418270111200c1c012101da803103600c0308142c0e00c41480000340002000b204001a203c03400f503284540c1d480341e1810051541808241d481440c5000c03205000d0460100c0c40b901c1c010030103090002d02542c1c2c8141d801e5004003559a140820b64000e410041c005681880c1c0e5039a0401254403031a04d03501c481d04001000b09100b502d0030b00700a01031201c503407010340e0348180600421b000031080c000e03443d00444102c0c4d001c6190040404148001d104d51003065681c1d00c1105510003c100c416005080d0781800f1310b01c00000303080000002c186920781140e0b10b10024500c2c001d00b801443c0600350341c81c0300c9203040c400141001c000c00400b034a000354102c8460982e100e84511b100420072100a01405441c059845004104003800740c0741110001c5803046040c048514050b100e04e840943c00b100041c2140258003a95011031a608650b081c0b400c1401000c45041c8000190b10303800d01c0c015401162003175045114404001d450464200014020440d2185010071110900b02000c100c03503c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 624650287 1250 624649037 624649061
    0x2030a08060616140c0a080d03092102061b07020a06120905011e060803122a0a110c010c0c15090f060f1d01080a0207030e1e0f060408100c12 62
    0x3203004d140002c655803800001299045c03086200c0e403001e2169001c0440e0240c490941410301089030481c6d4a003c012566a5550b0080d000c0000e80e8001d25941e800142c1e14003a007600c0403c0045501407110410a031b100e0000060b41058500300c040107001d206100c0101c11031041c00001407100d070300b642e80b00c1c20340c2c0c641d09603c000c48010700c080e07603040803e902c00c0900501e4804004c40c40c00f0400400b0215450004008440d104070850840384042810308400310010070014903265108941c0c04003401c4140c80200c1030007107120b91000c03201d00d0350140c40400c4101d40c0140c003042d18140b81903100341241d41c41420b00b83c104a212030700001d042480c8407040011703080716119800c0c80c5c00c141034001c00f013003081400d080c2d413100940300f40c40041c0d80007040035070003c5180700b002da9240600d05003910440c42c1621103a0f00200f41c05041000d00101030401d10400400702d6601d1100000c2004005481c007490054003c0340d00305a0b5016a808013a0780900781c0c030304580c140390714201040300b000811911420820 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 624651537 1250 624650287 624650303
    0x140c090135010b093d0e060a0812070b0112020306061507060608061816121716050618100c0c121d120c040915090501020408010e0307020102030a08060616 68
    0xd01240d01600e074240300f003817501080d1810341810500f03110322030041d1080075200c00703000e00403920a4643c840000040d0078240220303040c09480c0d20312105950b208481c140c5030302c1c00d640c0011a00000704802c3d600021f4004000f0202d645a204c1045030300700c402159042c10f024100034038030020b41680070b42401424102c0c0580b03110714242510050043c84410902c55541150401c1d001d00c2d80d00d1a218410390390b0341942c10104200525000304c5258860004034002c6c00d010032604095200310703510009252250050b076019844010700c4e84900146102808003c0e04001083d000d42c098690000d0311400c2517103403582c04081d0988507452075442000d5141d00080800800c0002ca031206003203079203554410f0f603560b02201c80d4000b0054031500a403450511554584644605100c0c0d113502e61620103001040800440515142c4903000750b100d4401c826041d402d241c0007481e00310380441503035181d6406801561410090210440c1e500c9001090103602480c144142008964a411040c440920032001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 624652787 1250 624651537 624651571
    0xb0304050d0503070813021909092a06030e0a210206090c010806100909320f06211006060e090105010504061b140c090135010b09 57
    0x30003400c04880301e48031030500c00700b0410321034020303400712440d940502004034074194890540700041206120210b070362a80051141c010420717540c00e03448441c10b50321800481c56a100902c603d40455210000d05404035054900e0401c1024002d400044400c031031802940d901403801e48d100880300c3c04001c21a010040c01c0784407882010f404000c0c154000080c80c0041100d0403900d00002d00f400c200619481c083c40300c805419200e10700410705400030f400c05072802c1c8800b41010402054000e0300c0c01c0f1100381c507600003000d998107e804041050088112612450143d6244000c1c040380000b100b880c50f4201621807800208250103000855101c820500b000c50031070321302040184040c14994056100c0d090fa0b400402060b0303000003c54003110000d05001c105a04401c0f00a40c0102c00c170780000c0c000e501031900b0725043c100c01081d1074241600c200e0318054a640ca81c030f00e154040024001d0124000a440f032508410390307503c40a41200003407140085003500039800411040d0405071441c0c3c00440750444 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 624654037 1250 624652787 624652793
    0x6030b280303080a0216060c03020d0903020d0f09050a050d0f06020a17010608090a03080a090b012c0103030507110d1410050912070f0201140c07093207050c070b0304 73
    0x24901c4c1c10a15169065042c0b100701800e205064145003402081070b9038804001c0702d040d0098040d220351a00e805820800b1380d201d400c02940b9070610440c0f03400000c1d021007150400c13500948403081a0383d0060440800c183c18401840f0794a5440300d000c2e2100001e801035400040c1e2180014116810300d42d0b00c14010068440c9140406c1c401a0810800e005100c010401d810100150440d90a41c00d854804419112489807000900154501400000c46c0a00101d0110700030f146420400c041403a03811866041c010014900d04e000380801800034204000480101d10041e04c2d06101150051054002c0781c856510340c00100400707512400540c000200f60360800505104603a172005640015101410301501030300e80c0303403040907002004a15262454401e5910490b206400f0001d000c030429958244101c08559550091103240c42c200d040c00001e10804070080001c40b503203180c2400c0010403020f08410b42081900080c03002c0e0410406011402424004014540061030544581c990b00d0500f41 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 624655287 1250 624654037 624654047
    0xa090503071202010c03030f060504020f030919081b070510020f0c09010501170a1d0f0f0a20030a08160b060a0e01030803040f020d0b06100306060906030b280303 71
    0x2911200410703141c40000c0d00980d0704680d01030b17580342d070500d00000c4109003d10360b00003c145c0380c0c12190f002440070480d80030051800c0e000314003035061541111018110700c1880c020b2101490002003a180061200040c1007080d00d1603182652450700c15986115180d8010504c9502c07800e0005c03006a20415000140010501c103220007650166294031301581001c00180078940d42d10380381c40c2020310b07040000303a1b2040076034008010000580b08100f64250340314905039460303010801c19809401030a90300700d0280000190880000e0740503050070142e4004080c10066089a003a01e60f415000354043e03079001a24100c02041e66840c82c5104441900b407605121045c604000d142600a9028081c2440581802e40305a41102d40c422940350341c0307a41e80e2911034031400d1039940003074001c000111008100061183c01c035104044c00c0d10072404072201d0500807015118144107040114205230010301440b4801e4200c2403044002800703a85103081c080c1c01741d01d080351000300d1218100156040500805a000c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 624656537 1250 624655287 624655289
    0xb030408070219063c230702100c0b06270412090806011202060f130b07030e030d0e04051b18011103180103090c05060a020c030f01150e0702120a09050307 68
    0xb0000810818500351841c4a0300341040940d011742280c10160f28172503407180c01d0081000711b0841c00c092444010f111910200d07008040224450f03041907a13044003152181480c03c8085030001000c2c1446d8940700d0520184c170f114240811841c4e1280f81108103442c0200105078062403080c2010440400c0c982c0b001825095280c100c000d2541000004003c004580c01c64140e00903011200c4550780c08015010326200d10030240c5101c1c48569101c00029518200000303085058002c3c0c4440c0300c0260039a040680301da0000b250740020a0900030b010300c2c0f50030030f03504c0180e000c0400c51440e10000c0c0c03811103180395500400b81c0034082c041132015125855074441c580e00c0d80c04818100560801044102214a50301200c06190400d50390740c3d60310b403e00c82c7c2c0c0702d04400205006440309aa80e0f110b0360b4000d40b690031000c1068040c2c0328000041c10355407014881e060344c0f5074024140450081c00e011070007020750790140554045100302c070120740520010400510b2026000d8031688807207454181494181002d07 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 624657787 1250 624656537 624656567
    0xf0d091101031802060403150b0a03080c07090c170907080118050d0207030507031103100903050309010605120a080c0309210601080303150f01030e0304090902090a0c05040b03040807021906 83
    0x1d100c40c0d483c010388030389042e030b000d40fa80310300591420800300d00c1e0a40203120b44810b240c0d105c180c1c000c0000622240c4001400842689000d545016449118881c00e0f500071044020000e60845040403141c013441e4041d640028140081c1ea401c19541c40665007500e03a08200f6200c468910007060040100c200058100c01e041400503103074940ca10303255181c0381d54861102500191100007800c0e100d9905122003065007100314402c0100100e1410300030700c80e4004581140b155071a00790041600c1c5404405031103180c070035400038104d80401e83c1e51000d1a802c007a60402e9244070901c03e0000c02c0d0b5500485004135441d03000144031035074003066440d14140040e0310a01040c1c10800600c8441c40d884117003810b450300b0984100c849030380441d004900400184541600030300001c035000c40c44c041c0030f8002d040101d0088400310001e885546240d000c540140c003a43c400709001300020072a40305100301030369006018a1205081c00701903004905601c20a42c400b0351041c807200400d12800e40c0141000410143e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 624659037 1250 624657787 624657821
    0x20a120e09060a0b190903050618061807050f0f0a090e06160210091406011e0f1d13050111030a0f05070f05030603010e100c031d0a080f0d09110103 65
    0x40392504c2d05505201e5241100104811814081e48480c000c400510065034000203c41c1c4a01c0c204407003440003603440c141e8240310f0140c9008036080c1d00b041e140301001d042e43c000103040c00300d24000410031801d118840c09a000040d41054110940d00c2c002900c00074409418045843c540c0c010529090800040ca8080c0143c1d600118412146d400078030481d03541140100040d902a05042000c80b403001c0d8040105503110304000801c40c1140706000e031404094842e0400c04450300c4560302c40e0000e445005044100540d100300d0b40901e6100c0e05000c0d0050080315001200000b16140ca90030360304154540790740741c00300000380035122070300e40b00f00741015100b04410071050602c51401401d81c220202100c08200d030110215007659000e41c01841a40c000e10100c60307010007242c0f08000503010307464520000c41e15128850021606070f107544030100a01501400c0303040f0792603071001242d400ad0402d401030381100b0310034a00c44618074855000241d0191451004800c00c1800040a8034103510310010300f00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 624660287 1250 624659037 624659039
    0x10902091303050702190806091b030d02061f05120a0201080601030b10080414030d0614030a080409180b010b0711040e07030b06060c0105070804030f020c0d0f0201020a120e09060a 79
    0xa070f101c410703a01c40642c111082d4011500300d10b03488500c0240c64020310040c0c0110301c203024412400040043c101c004030061203006408540805450342100c040120140c2c020320300080c104260540b40116405e0699041804540c4039800b046141400150408043e4014401302c4155a004014943d00000900c3d042c0103001510003c03501203050050114140190b60020408020b1105141484003000d8011207445580b03400302240a80030724400c0b0340c03054500d01c01c1e4a2036800c0201c0c1030000c06403c501c2451410b89000c00c250020010402c16070500c4c2019180707440003031890302c0050700800c021800e881e180c00b040e04082d146101c0b42d054a600c628505000002c418070041a03e80840340c00003c40c0c02c00f90344000110f00d0720311415442e501d95510700410400307241d420070f20241c001e40c043c0c1d440d80728019080600740d945030840e07401c41e03521a521103942030000c1c03203200324005203e1040c815a40300e0b0007160344806509543c4041701001c0b9074450b8030740c1e81500b40b12503003560180d8210380c2030640e1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 624661537 1250 624660287 624660293
    0x1050a09030906050c07030219060e090c03041403040e010303030c08060307080631050a030f0e030a1707051e0d0513140a0b0708120a1406300109020913 67
    0xa020302d44034070000d2010115403c03000d03400c18840d81c00103640151004004a0b8610503000312540540115004280404814061801c1c080ca4807032040e1504556149141c03503540f84e007600009521840c2001d44030801000c5117031030141c46100d00a510070384000c29820787d6080040c103000401812140680c6c40580e00304561900010060b400a14008883c0c052641c0220a5052084503201000c1c414a8088000007003020014613002201d000f40c0c4c800b800e007600b4080480b51585442ca41c1603155124491000c00702c0c3e20394401130441c1d054401e580e0b140c00c01654405003011590001c421240c071102d14080304a5005011740c2484c041180380513490405034002070716042002d8011803030380c1c1aa03494601905d48503102c0c28005059444811030300c130002407400b65115408821403601c5146504041350500025004948003500902c07078054603541c0351000d0200c414940d031000301c500c6004090042001d6103840c460400c10340c0708000420100810700501c4000000908080b8048800302800004 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 624662787 1250 624661537 624661547
    0x50f06130c0203040305070f06230406052104231203150d0b040602130504020319090c05120a170423010c1a04050715050904240f060201050a0903 64
    0x20314945404001070209600200320301d94003540d08001c280e4401c180d8040350066002c000b02c002c4071044c1d43c40400b080501c8001f9170301c240c00c0303007012850000c0504c0240603182c0500b02400d0107144c420f07035001c01c82c90341c0d00942010440989050701c9c4031714100500d0000641c1c030040312508403a03100c010310100034040440325451000514100c0c415444c114080f403d5540c88605445464001d0b0032000182020f050401c025404029035126500f402c3c0c50000305810700d4000c3e00c0c03013203100024065803100d2811071140501414001144c5440607100081060703511031014100c035400f09401007500031920302d005110000c4105081445190502007008141e403002c285403a04695400032505c010546001a111a40d0301c4000601e55a519048240400000c503000f80c4614040e904a6503025a1100705605c4a07180e80b20990004008000407409400c2c25041000204050805006521901052410080034036000807407850010702c41044002d90900400343c100f000c03000200300c504115500504 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 624664037 1250 624662787 624662809
    0x28020c030405010c020d020904120e1801030b15030706030621020a330f021b060a11120f03180d08061e13020c07060c0803150d0f0501020409050f06 65
    0x104000f9208425411921142540301455074088c02c20300403400c00345004101f0207a5215004001a01540c41441c81e20f083e91040d802d4204945203003116034216164458410703001001a8101205004103103003644040042c40b000388020381c1e0008456040c42c41c04800c030000ca0040c244640b40b00008500541e44000c1800115003a200741d4541030403940141c40825071449040c0c0501c200900e08aa62003074001d801c45003414925801e41d20b020040213090302c207030305031301d00c1590b044170301440a180382e6800b54400c0c8217039200880071600001c0f00101100425808502d800e240010007006100702c9821540303040100c0320219024000705292640000c00007030008211f1071150400c100e12613031a45440b0308500303940c64050030f481d040c1e0800040d90000395001d10034041c414400e410002841c107106020307a500d001c0e4032598051540d00c601071080e20b00204002041d91214400c0851b00000d0549024078602c1403064001585641c07038007050701c0c1110b000078081c1c1c81c41c1d08034000700442c55a420124603 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 624665287 1250 624664037 624664039
    0xc060702060f0903100606030c1205040c0504021308010608031216021005040c050d050a0302120a050d0e0102120109060e1302010e0d050c030a050604060f090201050708030c1228020c030405 83
    0x3e0b1581c40000003c2e18000a03144a0306607203140c4440480c1e441e0b819004800d031455140c65114520030030055000c102d03081280c1c09844114070a500f400310f49000d4005101c0344e109504d210800c580c660b4201403c40c0d0344e6502c0710045510004400344460050341b003035680440b01100305840e66a815001030344800543c0180e40c0e04980e10b00004080011030074642000d00170241c4200c08684840c540980d840d2454181500540b2440024070718805070f0100325022046d407507859909102c150700c200b1000e02030000982c00f641d5020b018504a051f0751840050003003110090200d842441d0030703015a240d48d4080e000f500c405054104020250b604401100d042c040103441500c0b40441702c0c18003a04010410200030f90501880010b002030003070010b10391307000f2401100c0170006100e10640e400206d81004a0081c0030800a2000710041440392025580c4614035a081a00d0a010a41d65440e503201c00c840803410146031060340012280c10f94120201031420380300c11480d0282e400e044594a009078480c50b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 624666537 1250 624665287 624665317
    0xd021b060c07020d261c050c04050a03240e10060506031b160818011b0b1f0f0b04091505061803102a020304030c09021b1501080c06070206 61
    0x40f0012242076010040c0e01200e03040a038a030440146c900b5640040030301c0101040c0e06082c0400c0c00b915201f070440d03086403c010103c581c8940796544d85000c60350140328254004400c00c90017041203800d070040f40c0c0c008070054003400d00801c5810a4038100c40250b04114000d030814004c0200502c01032100442c0c00801c281c903580c803046040501d801407060b44500511803400450040105144035420141c5071078242c0b946000e603180020342001400780400003400d00d1604502040180803141620000021040c20b10b400090300c40080c650311410543c4075021100c4006070400c00081c0c01c3c4070768031a029060078420401858030b030001b20140038030000650b045ea542e51070615180d904110704a1803040712074045c80884002c2c9982e8240078845030201c0c000764807110042c0c0800e8808401c4400340c1e98420411022a814103682c03030025001607120b00c5035104241d0002100302c0d007c200c000340a10720b1b64015811036061142450404040a6606004e04424044880142d8810307094505941c50704040e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 624667787 1250 624666537 624666563
    0x7020c0a0e0f01090905160902040f0803030f010303051b0a0809090f3303070e041101020607080703050a0b09190606110316020103021e04030c0501080c0706110d021b060c07020d 78
    0x1201f414105110781403414408a448005024003542c2c011b00111580c140201c050b10f9641d03402180c4a100031100c2c000c1e8019220300504c0003c0c002c801400f854803aa08101c144800e5100340c4916181c4840e00587e52a48041000c1c00d0900e48615810b520640304c0c0c00314000c900340128104814840c41c425159010800302451402850101002c030366603100904030789840e81e80d00c01d002c030340718403e40b03080d6482e2510f075030401d0030365000007251801801c1e1690740340c0ca6590380107012001420050301221510b502da0340803040780e84d0b0314407000e0f004500d800e82c0310040c0c001c5100c0701c4040b5880c0360b021000784194185c442c41d2550011090f644840510708100401c1241c030300c0120024460521502d466188d50740c1c0c41c00e2080000780152013902d01c515890000030f038a43c030041d20121811507282b00f01980c200000c40018005401c5102c070182c81031145c03403c00401200c110107036000000782c070700195010002c03207030384203010488503401455a030000b5140c00e00d81c0d0040b540a904a84010700003107070804d5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 624669037 1250 624667787 624667793
    0x50f10021f020903120a141305060406050d0c090620102903011a131407050a08010b1306111204090e060f090705011b02060307020c0a0e0f010909 64
    0x20600041c1e5400c0a488419501041504002900020700c0c0d1402481000c05810b0800840800c0300e19800340c50300ca0900c552000c801d00381c81d42d48141148151001d0100000441d1f8480c8030252010f404c164542a449041e44900601140c030040d51580400c5461402000401e4100181d04e0190981c42904a40b50440381120b40c500b00041641c424100c2c80c260081c11554282040300000017011206110710510000400d8240c5080044e04000d401041d0040c072028a080003c21410340340074640440c9c0300c07000c0e0b030411080900c102c8094012410014000c4251680802c000780586100001a0b00305920400d81d040782000a004030418400c11203029140200200604400d0424441d20750756aa0784820000c070142c140781c0c0c0214181d102d5140441c2504240d000c50360b100c1e815840090100780e103000c00443d50481c500480502000a00342e00c14056142c002c0150720450003900101480d940c03020a01501014545c0509003210350b045c21300048100e21b03054a070440b400c2d10004034003801030781 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 624670287 1250 624669037 624669043
    0xc030e06010b2a0d08180d050415120c08160813060c180b0a03050a2d02070c14091825150906080705090607080307050c0601030b150a050f1002 63
    0x120b0400302d0f00c5101c1400740c1c04e941c0000020300c01d41c450311005000008584000d42e40c0c1e00e0b44100d030008101300380130074004d44146585590441c020741c90201070b8030920314040002c8811812560f400600325808200030401260381030010224286001c0600b4079241d01003071040e0781c1a0100503c1240c032828002e00ca244260f036140044554a00301d4585255141d8000c059688800b03070907408079041034002134441c0381a00c240e406003045541d448401c003855514051480c1114014555403aa0a2040e54007007200d800a80303000e000d41e00818034082d1182d00812900174801001d48164071460f500d410181031004c03031401c2025005503408007141e0500d85941f503000c8140d40107444142031a0074028041a48080580d0403511a0717214130340c40e1f884e00d01048480f07111b9680032940241d030801982c2c00140322080150780c08185483e109081c0a0302402c410b05200c0281d00655803250460103100b022412240102c01c1c4a0301103c0e82500380b460800400c050308603a0030351610444030b41c0c10380e4881034024 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 624671537 1250 624670287 624670357
    0x20d05030403050d050c100614010f12021803060f04020d080d091208040b161d0a03021005030103060f02090a0b0d09050304170c030f120c0a02030a060c030e06010b 72
    0x12070181d1300341d4940c1041c02042c41e0041c3d0003080c4944103104000ca046c4c0c4141c4550401d81c1c0c420080390056007188401582c1000b00134034418200404042c040d8446040762014200082101404042c0d203d84641014540200603199011131140d0b80c05020050343c8030520024869400792005403900b9491003450010180640046c002c3c840096074a01000d50188041d03116a204050344440c50712004840c40110200c1c4000501182a540c0b040d142030706440d10200d45010000c11003004ca5480794081070100e501400d8510105d00003200500030000316005901007070b5640310b011400e0944003000105c00409600c2606c0411000048000040002d070f00601c100c113810000b102e540b00e641c3c07601c0c03d0340c000150103418014054150124114600419458500c034074030701c01403170720098118040f503060f406990982854400d5881c094010303241404005201c500984000621000f03950000d4143c958480e0703a041c651b004030f801803014101060549568480403403085028035071015a00700da410007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 624672787 1250 624671537 624671543
    0x30405130f1d16150c050118060212010801090305090405090102210615070804050906131a010813031205061309050f010c0512040b06060f0a0c120c0b0103020d05030403 74
    0x70441c0002030418814090b840b15114803044514070000001070a40002240c024801c10741541265610503d1040250700c3d180380c041c200001300d002c81c0240040710203002c500101c03030090300030500c0c50010483c240c445004200410091020101541c2c009200d8070607030040070701c210356840100382c1c1108254180c1c0c01504c012413040c000007036500c02944501c01c0444109100d03008080030740d80c1c2680c0c1c0d4401c1c1e4100755442900c85052070b04203020002d00340c8008140c1c0790051080e29041c000c40e959402084080c0c0d9841e03c84030b11885088000400307071100105414010321075406403100284c0d00000d003080300741d070a510000c0d0588400c1c000451155901a840d81002d080200c0c4c3e5081c0b20380400c8039000806540d0003004080321945083d2414010000141c1d603044e0504001404030300c0550341d2a40c00000181000e00d40107041803046026080400040002100c0c1c5c1c0b00001040a4111084140030311800c0c150102800350740d8220b0005c0050000901410344001c090040010403c284e40103594 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 624674037 1250 624672787 624672791
    0x90a060b03040c0509010603020f040311150f0403060b1008040b06040209030a05101a10030f090606030f1109390313060f14060f011106010b0d050c0903030405130f 72
    0x40c181003946401540313011380c91140305400e000240780da01a00c200d500254560300f00505252031912440030f10f0b20031325035107500035400e2810840400d0f52000201981c607842907200b600c403400c46c02c100c01101c0c072000c15070340952a400117103e94190400170f01540940c0c130101401c0c40d650303040d010802034090104101e82600c20710355000c0400c81d005c58501c0118407400010801c2c1040f0704241c504489010031001e40114410001440700c0740310350419046809840b00104641201e03944010480703009602c180e41c03d9026902ca6010400303c840c0700c1180712411985085c042c00c0503e0102c06c42c04000f810304c1c2120340d606034400b500109034881c059400c4410545291203140ca04a01c603071041000d001165841d15049e0102d05902081c4682c0c10a091807100c10b010039521502480086869038004d5414418904490325030b0710002c00040d4041d20306c803000180c179420703450000b100341d680240c070703040e1401401d01148483d41c400100b5501120821038030703c0601c01c410b810074001401031401c00d21880f4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 624675287 1250 624674037 624674041
    0x60b030f130b070c030e03071d0705071b080606150a110a020607030512100605071509060c0e030c03060603210c0607090f06021506130f020c0c0a0e010b09090a060b03 73
    0x940c0094591110174002d403160000c0c41545010551211400e001e48241c203403c2150030200804010348140d800945406c0030707881e002c0161100c030321825101c0c2c0d50424008003444140b00d40201403000c0b5400c01002d6030403070b1514540c4103076115a03004440100701005480b000208110b0f40c20000041c0c0260050b2040c1d641f59001d0a0040107a8800c0100205030840003000c20202c0f0b1407120707400c0448403aa607441d0301b07100850b40c411741e2419461410000e2a52100d208a000c510913101f6282401c00075143c482c03014008006050410b45540780c3c262090700254204105600c0204181c2e5030b40c0300703d8500d601c02c2e41c1c0071400034200e03004480c0030300c15920520003000003264024280d07070141d40509410071400741d510202240c3d200109188400102c40000c04100c184c108003c83c5000410f405101007001c4207c0d001800481e0010080000d166010b15503042644c20190354900180c020940d05660540c10208144d00a11520300e90354010444503000a0301300d0016800b0002803c0070441f540e43c0c074 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 624676537 1250 624675287 624675301
    0x4060605040b060a02100c111504030201060f03210c1e15110d0504060f0f0b0405090607050a0f0233180a03030e0c09040b04050c04060b030f130b 64
    0x20602401124003551a21402482c14500001a902002990f600410700042c224a60101810641c2e003034505200c018101e400e0014014407111302185d100041d440c141e403030031b130a0003400d40d581648030a40c580c9010b001807011072064400030b0340c01b4a049440c00035841030709000b114440307425a800f0f010326240031440505480344820340340f81c080c003c5071807079004110303d0068402c464030034401c00401d4500700103001107000306401003039001c0c2c050f0308000356a052404905c0103640c924105000000c0c0e449030b8038945032a1901c01d840e003040b05000200300030306d4001809002c510403030341d4000501c201256a4a8035520800000c0c04060070030a01c5c0110303242900850030859420100704641041e1103000801269025400703650400e041002010348400382d48050f0014131508000140d20b00404001a078030341c41e5a02158003503481090507010740e240c80d0400c0c0d800d00c4000c8009911480c2860700c10081d0240c40000d407900b056064102e0f1400b0345440121150100e013950340103190388111801c10001e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 624677787 1250 624676537 624676541
    0x611071208040b0c15060105030c031f0506040b1c0b012c190303030e010e0618101401180e030301090b0f0d031d031c08044706092d0406 60
    0x13007181c40c400945d0258843c140150380c0350104403000d940c03030001480095054805009601d1022450541203203140707446502107007459003d50803144e4903540000d85150b034088804681180240c984a00700314a000c40d8000038a4426000e59211001e06c0141c241d41141c00620750a1400b400d0081c1100c2d100c00001018a554100612080e00070a151080640b414a81030085001954100001e064545c0d41c07003240d102c2c40102d00529040320710803071500f210702e111244180e5500f0408204584a1076145c08001040b00c0e03089500007580c2c50031300a8111107150b000083e40d040d41e003504404110015560003151038144080c400c15030040300c5c80102014550894440300368550240300d101071482941d024540c0e10054060b04c2040d03140d4540070003441a1180400ca41c12078403c520800c1031000150783c0c0500508094002060021211328001312201e0195018030041c0640302074407100e01e0200c00213541c0142c010909e03109440080a042400c841110194880c80300d1202e405145050900700703140 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 624679037 1250 624677787 624677803
    0x40611070326191e183005010e060709030312020a2606040f06030201020303010306090305130e0f0f130f050c040f0902040c0305060d060209010903020d14070611071208040b0c 77
    0x100d2540145261079414405d0010042c078040b581c0810b0b0b1080c0c40e2400321855010052420805007211345041041040b00000079148180100004100380c1c00822130542004409040c10003400414001000060741028000041d01c608090050301c0b2206e2141c159040c149940c5200c1074400f640e091800719440c5c0035640350060406841c00c20045d908991701d80d0440c0e07071500010313000da4410301c010000200d075500001c0203180f2a18001c1d0400110a101c00d10091594211100c1ca40d0404c0800001e0704941d2a455400503480712280305c13a0030941c003140145038140c40b01500c00040000d100d03040c864204081030600303030050401c200951544410700000d1a0302070080344220f0801c0c3c5000d090074807178000c140c000d080c0203140601405503036403408002e50045100714103101c1199800000760f43d4070f8507101045402859180214641030600a00300452030b00208103218000c40000e800d070300b000a0f62019580c00b084200140c5205060007001405254441c16840f03000191b9070b01c0704600810b0b810 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 624680287 1250 624679037 624679067
    0x20901080f0705030d090902070204090503041203080708130201052b0f140f180f0111030f060d0b130c150f0f03020f0702100e040c030204061107032619 67
    0x4000c6a00c5000f0161a040a020340c0c00006c0c10065062024100e181e0040c4807061004000080030009e581c3c0c1c0c02d082d60800e038080f9250ba030b280c503098410715800c002c0c1c01c0d5000c619890601c801d494001654034035a088154060304208001c00d000581170181c400200c01c621201c40d5000d035a6400c581c05c0b00c0a001001ca0102646007018542c1080014001316580580c1248070b150000d03a40e80360340290880142c050f0780203036201d82205040001400c0c0314101c2d03800e003204444c558030b140000c5041072800016240780d0048440c01140c1000c0360300840240c1d000000c1c4921540c0182881c1000c400703150140e0048490780303c1e1041455a01504802d50b000030f0002e58941070442100d40e00306034101d0256503d640c0d0001d030200a0366006207008078001e4640380450400540202070340011a00b01c070200381d540004241d00003003c2c08100e401c860322020b0210420000e104640c00d40e5207424844407036100034841d40b11516a10300f400c00d034150680309140b01001d01300c40443c9002400504268200c1c15032 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 624681537 1250 624680287 624680293
    0x20c01090605181c0f02151f0503150c030907090e0a0c0b13060c060e0d03140a110909150303031303090e04050316020a170106180c09140a03020901080f 67
    0x51250200c000c501111a540c002c0309001c50066030103400e032813006176600a13804501600c0d084c440aa500701c0c1c4002d029103c0400d0441c250780654444c10011440ca4219511a5000d203000b440c0101d0302040d1503a109111111050b229110488220300c0d11850782c100d0384986081c9800940c50306000078050400a005480c0d50704020b80e50b0b00450054400c000740d210084030320310024410703d40506480c8070214442c190004003c0d000080650612240800c140002600c4201c0650321b08200405141c0012100710100000600c006212806200d00301e01c8500404042000841002031040d08000610018064a541c0d181140001410b007411010490100c1c05e400c17001703c1c2c51014252010310550b0302c031009603c0c101e0440340808500c0f0300420102e0340599603480c0400c030206408503c02054040400100b08942040c0d00541c000c1500c80c40d814905180c41c0d0400c3c5a05d80c0f2101b280101c41000c11000318058010002c111041040d0304042d4010120740f000103905440082c01c41102d81442c020b0f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 624682787 1250 624681537 624681571
    0x507051c24120332180a0303020a110d060e0c030c0406050109090b0303070b010608040308160807050715020c030d0b0906090609040c080604080a02150103120f0306210b0714120a020c01090605 84
    0x3041755030401c9000241c01a1b000800340c1cae000030190242001c03c40310081104040c01c0a80e1703228030039902148880340041c0c024521100d054281000300d07000c1c1d020111024419a41010002400d80000c0d200351800151078034103040d00c5480600441d143c898006e800c250b4251784070080035013026001d450480c0001c0a2000081403600f5881e0017910301c1b6103036540c01c0020f4440460031510364202d02019221031012502d034400e1445180b0090080100e81005182c03507200640c50303d0b081f00e0f42048294040c1003440e0400c010f030b40e070b82c0c00e0050340900e0440da803ca00f80c555040c40600e284042c1c0001c0c282e031040c0d401380b00c140812a40540070500e540d608585140c0a500b9009000900a100084c0f0300490b14008000c124010303070602d441e90241d440c00280340d96403907040c4200d091311a10880d818069081341d500602c002044036542c41070107400e00114120504484a00d02d1094006203d10744900c48003144248a01e034040790200c0c6104e41c004c0c000c60380d2a08100700203200c00e0390310b60000c20b034240e2 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 624684037 1250 624682787 624682789
    0x3040c1a09010219020f0d140d110706030e0a050105010f0509091b040507030b090c0703020c0603010f030f151b020601081504060507051c2412033218 66
    0xc121460110103038090700d50100340f4490100868010081203030302008a0f01c0da0040e40e00d07501c0390040c0c00d5020f0120003900c21003000b5214182851340f0907800801601c01c0700e000303c54034001203860840e42946000903200c24007100c2181480e121f40c070010500e50a00c2c0000032500c000000040913a00c086403030f51500d071100c01140d641c0c0c1da03a034419011400b0f000c040c040700d0351803d40c0c03005520824a060120f64191020000b40f440241210755003034183d40810510b0a041e410001d010701e03081c064454030301d554103140e81c003c0c500b069884001c000303280c0300704da20040104075055440c01c01429101401590b01d0011060541c4c124070001400600c662000060300840c009540400714503110b80b841115212521410041c110082008051050400220a520441007800c40b1080c2c91808009a4025502c40406425004c0680d070300c0403868080041c0702034401e005042c41032681c1030a0a550078546a801d12800124030203c10340c0f1400030030102e002000c042d500a000c0800240d03000e05c0d418925030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 624685287 1250 624684037 624684089
    0x308040905071707120b12030d0f06090b010210110d020301031101020c04020a050f0306121c0f02030901120b040f021308070b040b0406202a1503070507140303040c 72
    0x1c8101c1d002400d842c20308103400190340e001c803402d048087c0c086020310041c21130b01e038a95401a0b090f594280c0e5a00c20242020310315208034806460418024420401e40c10b000075070b285190a0941222542c0d40300241e56222900d00312840326000482c127540325a50307418203c0c2e48100956085000d40180307142d0348098075280c42142c42c0900103846080c01c0c103036440307101d40071a0001450103070004121118000059800c02880310b9a040100c882068800f84250003004280d200c1e5008007903500500c040ca98aa1304194644620180c440d80010220401c00000300686851020703041032510014a000e4044040041081034603200710444800079070b5411004030354410f07441103045801c41400184440c80c17040300c0c10304445640504245c080b010788030b40c40b8200900c00d031031010761400c1d45108084041c41d80000c4a8000412298144140310b0351010548034030000b850f040802c14006001c0c0108071b04134120035910390304034086a441e880e01c3e1500304083c0310706004a41c51542d1090344209010495 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 624686537 1250 624685287 624685291
    0x1d030d020705030405030105040605010305190b0c250b01140f03070603021608161e0b011401090803070803060a27020a030e031216020703050a020f0a03080409050717 73
    0x5526110051a00100035007065034201ca05000c204000142590b0034041c942c091405150b0004582d490341c60003a00d03164030001500d14840e415078925000c40da10345145a44441c203081c81503a21010396411034034807541d480c080044404011612014840441501810303510007030207041c620040103007000180d40e001c0e4095903040c1e20884051242034403c0c2c018040711407040c1401c03041d52034183d81e40040c5030403001e6002501e0441c0f01c01c050901c80e501d00740d07400c040070040c02007254140c5910b405800780414001d0b6424008002c800182d682d125043c044010620101569122a814034082406038400d4450341d11030341c45944003140320081c00e00140c40c00401956018604511702d8442c070069008001d4020a1543d5241c0c50b0f04442c0b0300703200800c0c042d160314243c04000e00c0c04c1c0d50450262507000200d1011075001403014000500c0000301300c021381d50115844000304191000040216071140c10080200001080c005040822600301c10302610b03650711000280306800d10285454001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 624687787 1250 624686537 624686591
    0x1e06080309101407030e01090e0105060304261b060106020c0918030f0d020901090f0b090121020403120f2f10050903070b0901180210050403051c03 65
    0x4111007000c41c5845008100031100a04000b8400c00c0e120540e4040f0360414441a40403400c2103400002640c1e100c004d61002d01180c01603404c003541880d000c0358083c0001440101501010b64041110324a0511a42c4c1001c840307088141c0d035030100002401c00442e619030300c41ca0900c84c210010032424004102181410f402500b04c803400e036904a035054405080c00c00101e4980001c006403841010440010061200e1066016980d001d50740300042080890398454000d1000b4584c05008400e91002142c04118003440d100c2059802440c01050010500e0029150184006000420810815402d03898151079898013000c050044406546000d18550b8008980c02c03c4103a03404000d0501708030301c2c01d03c03204030200c541c0660641180ca040782c20507942103619620100e0a0400c00440c904242d92288001e802440040100c41d400b085804404d034009126441620500c1481840750041e02e00554211003102c0c190060b5140907281e2401601641002a0404d0046c11a1002d0711202c2800034107 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 624689037 1250 624687787 624687793
    0x20031501030803130c05060403060e0d0e0109090b18040c08070e04021c05030c01050405100c0302070206032206050109020d0b09132603012319050409060b131e0608 72
    0x504c210304210401203400f81221139003465900800ca6485810140010314401c00340040c07076100449015280030003000d040b1003000142d85103003c4690340651144100c0c1c042d1365000c9620000c01000609011501c3c0f98002001c0c8510100070511206002c0c01c8111586903098403082902c1c0d22080c01040b1040b04c000e90044505060015580c0c41105007a044500600c252800c14036480d00181c03d59105440c1a6000d620000b00000307103040c01e1041884196107400c0851400c00a5408600e06000041415100491803500c078411034040f041070241c100d5000000300150741c0c40d0a00c1d50029041841d4112540740352204040a0782002e036003103402002d448403090048681e50755006100c059035400050090b1211603002c244840c418003a501a010700440c41b540c5840c1d100f410200034040e034206611540e510a402000103000700840416100243d4001c07032030300011b0500e00d0140c0580a0b00d00c1d0000503050504040208591041c80c0100710900c1a505046d10071405c00d0503540b00e4020180703070750 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 624690287 1250 624689037 624689041
    0xd060f0b070c12020a03050102120403090f0f09150312021b06040308120c191e022a0415080c09011401090611010f0504080d150b04061b20031501030803 67
    0x40c440a0034a6007a40300524001155840b66100c48c2a030300880100d03008401414140810550402c80d204081c242c0101450070040c44c0411294880102d071142c00040e036664010f80c60981400f000740d202079500500d9104902c2e2155070000c0d81c81894404540722124001174402c820f1805600b11001c90f42c01440d11400c04002a504851003a0f02410104e5a84410806078040b10407110070382e2000d145070b448041c1c00307100e05480801c0704e500303201c2d0340e60440d0060b10002020b0303a540c00c1e500542a070f224541070a1580d07144085001042d000032942d00030301d01e020000655a0700040d41e040c400702c068a10840383e985e00e00c0d1030a81c00103040344050200e40070420520009209060a5410045c14000443c0460b94800070b8421140c0580d400c0e00c0403480040c0d001000c2003d0700813201c4808a54000000c168503021103a10180918001c0408105802e00c0c0c41c0103028040000c1400c1c2504081c4002109403500440400ca024512046000c1e004480140035220300f40241c44d41201e805c10308807481d42e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 624691537 1250 624690287 624690299
    0x140c060d0c020a1b030303050912120702070504060b0a02100e06070c11090f0610050a0f05030403050c01060e180601050f0609061603030507110a0201090e0c0d020d060f0b070c 77
    0x41c0621811040451040d0100361010a0801801c103910f481d8080c1e4031129181141002802d44a00405460740b951061004d2100300752410103c1e82400c4542e800311205444450049081081039840340d984141032800204046041c6402060240c100d0307001c40e03070418440d01019082d2030405d0009034150300100000b884990251006071412032003100f064103911800310001b4000c1c0301c01d4030302841d4050174004004032810181c040103680c0110b0f042450526013030040c014003000741c1029031401c10030040042001c0500a10940c0c660700710980c001c2c081a0303200c1c8108803503188125005a001c10141e600080300c004085807070340c141c2c0c101810300e41c0118140c4013440b58981c014480e031a0811400c00800c2005100f0620184a091199501041508015000514540c080b846140481e0819240c1c0e100503130300034004208031103540038004950769500c0c046090724020050741580c0640001050a520f44842d400541540c1d03a000302d8802c8162110a0b08089018000b0010030f01804600c0500070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 624692787 1250 624691537 624691541
    0x140102120c1518120d06030c0f050910030816062c060105180a1d060f06011202030720010b04060305060f010e06090703020f04030204020711040609110921030c030304140c060d 77
    0x105d9401d103180400c0b00c950303903030350308070b49000507445120803001603002030000d4680b41402503040781405202d80601801c5440c3e82e0309070f00c00e40345618260f100d80c030620b908003d500e41002c00da840000c03d000489011086990b10b105012065045940c028240017280515101c0751820810407001c4002003540c2d92130545200600d040e00140d00a60010310000608400c03c0241a21803c11a0946280c900b0404005015116404406480c00740144100505c0170703480780c201d1400c0540d8032131942104866080c070a004044124800340c00034100580801400f00014010b40a464541c0712030000c0d80e6070307901d840701c1d03542c041d074210340d100311503c010a10740b1b44030b034010b00b2010300c5900d1006d180caa03803940007400300d0744081011200c00850408c00d40481c9420301c65003009082405007481141c6400e484440d80c1c0c4610101c161046510441340d9030076020241440c8042081103049a41d2a01c9001c2c0f01c43e6280c10444044070105031a0800004c01000440c450b90f4041003d0281400d103011401e000300 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 624694037 1250 624692787 624692797
    0x34203030322020d02032a060a0509060318010c020309120109050c12071d0108011406031207060609020f070209090c13020f13030831140102120c151812 67
    0xa4094850900140541d03030a211f552100d00e21a0310709410761507000300d94070000422110143c400c910610400d480b00703412104807542240107c9800799203948204561146000181c8046031642c1f03403030741c04c003900c54000000f0841030600316681051075401d0f07250303a400d80d8040c0c240101581c1007100703000d0722400e085410b100d100e0018030a84844648540f0792003503003800b136904c0d041a910504010042c6102c207102d14041403c1ca28088880b51902c84042030390b07000d40700201e00000000280f16010712806502c410082c0c0302c0c0307002c02c0d0b550703032150b8420140ca500444c20a074803624102c0301180c0d032030700300040740881c0d1080501225500000083c8110003034202001c02c1590640c20424211820424000c40c1d000c1d5100d01403450700c82805055540c0003d240484030f8a506100c10500d1000c90210448202143d0180d4125045044000c00407801d102d00003031b0080000601003407824440b100898049906030390202496501e07920020f415841d80400301704541d064008010400e0503407280c4008103 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 624695287 1250 624694037 624694039
    0x509060a090b06071e03125010050303030405060412031b0c060f021e0c12070c0e1e04020d0c1a070c0602060c0f03420303032202 57
    0xa04202141c0c850440c25500103110740d810500f070300000002c15810031f03100803404da0b10280400c0701005208203005194980d900040240040c0c2ca181d00601c2e801c41200c14401040030001508099200705140120700305803007030215480d0300c0d007010900d42400402d4070302c07468020703008050507122521402311001c04400e41c2c00c20035807503100c000800c49890745140c9041c400d41d62081601507071744c2030500494024880d900c2485004200501943c0020041c0002e091280120290349000c0b000c440c0d441c04072102c0190354031140c0441c40c0014061554004404c8980f6045183c00c255130345100203e081d09048000894039445501040142c182400f0132265248140143c0074416160039002d10f801e15100304680c122140006c0003010071200300040306c018100c500042c40142800d0790b50a104e40035940b1000e07010000440000e1030251111100c10302e04203088842c54200c0300c0c18840307442003004040c4600481065a0b01c1c020103083c000b00301e0303210380401c0031040745902d8064019040504080016 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 624696537 1250 624695287 624695299
    0xc03060c090112140f240f0307090c1e1803080912010612050c03070e04080715020307030b010e0d08041205010b090c1201080309030d1103070f15060509060a090b 71
    0x160f004401d45214500203a42c0700150001245406080240c07203c0004044103524075481051078140c074030342040344800420480d0400410b08100d004039203041540c1e4040a002401c01100c8140346802000014000880c07804102c1e041e1101c040135241e8110454407000b8410300a0010408901c200c0c2c00390505100050810f001401c692510509482c07a40d004a60710b9500c00c040402000723810800d003880c1c408141c005e404480e03e00481c40d1080e850042c800341c0382d1f14000500c2c808201a51503203101c030300010703c8115143d080c2104010010b100428005020aa96030407101c402c2c03030800800b52415500079500751070300d4104101c0d034050301e220710b0301140c003036403609a010290b80d50f10845e1846503070000601a255200072651518144060340500c2e0941c104001d0540303191008203c1309001212070401c094402080c01102e13103107104824001d4100401c41000200f040a003a40b03480b103014403428113110554a40c010031403406170603240583c0c05119103200300143c880c43c1d003200034140401001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 624697787 1250 624696537 624696557
    0xa0302130305030417150f06210303060a2115021309050a0c080906070f1e020a0b09030a200115090605010f0c200a0b07030315080c03060c0901 63
    0x24103106545540048425410204007441801648550a240a200d0740c00400c0c1480d000b02c011003100c90041c11080c03207910214002062519000303a010f92003480d55000004907181d11102e551a90810340d0000d20800e889080003a008511032503407540781d0400100000810720390358401c2a1844840d205912180d0240b0900c11081a00e0b049240202000d490105542c5400742d4503030f04a4190100c00000e111107141401a5070300c0004101c0d83c8034510341444100484221010b0724898000d00351503540c0500444001889540480c940210610031560003105032120366003152607005070b558030000070300d11041c0850b003500101054481000c10000016000f0184181320180c0001908200301003500c0740d00130131142d60721991442c01c03c03c01d842e00000141950365030b04100c1030002c01c3c0200d1105e084010070740aa45d0041288001d024005809030354400610380540601001e4820190300c002c16140056110400304140b641d00c08000d0181201e82e071550380303000c80c0e81c0003040201d04102a1145c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 624699037 1250 624697787 624697807
    0x1150e150414040c03060303020613020d08040602010f140606070605220c060206070201110d1e051303030509060c07121803030c02131413030c02040515030d03020a0e060a0302 77
    0x900181494040070b4924031042c00c240000e6461641402c4101494584100007196012501c503800242c200c00c2c0318021314990000403441041e2500203483c180000400040f220b4056002405091220201788019503d00303040ca06202c0045071069040178082002c007000480507401258010420360070f104030380c00401780380c44141d408403800f103484aa801d00144540d030f1b010004941e01031010301c02440441009401c0401034040c0745c1855038480e83b1071440025107070b02403507019a281441075040001c0e00d00a1700c2d0074070403c0350240c2500400c4c40c05022a164990103e21203114a030503040c010b180192640c2c903c00d0040d00101c1d86020080c038112030101645013018a54001e50090382c0300401000c040c0100b260000a08001d04034840c603000c0d60355500d213003150560364010343d441451154000e6a0a080d02c1482043d14001e610502d030108120b00345541c03e400d0b16038a5021380884087c1c2d0340b204001d40491017100c41d07500114100d0b80118040c2e1078110000d00204400b031030f001d400c103000c980e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 624700287 1250 624699037 624699079
    0x715050d050114031c0509040b031f020910050c03071407080d0216080307031e0c0b010902250302070504090c150809010f140f1008160503100501150e 66
    0xa0803d41046100c900e2800240c90100054043c1804801c6110075a0383e05030320140091043c0e4003801e00458480c00c106146503005e00540e10344800540d01c0c0b072465645040702c0d40081d4850200035206170703030440550071070912680039640c4106401c1d004619080e500d4a07001500da135105404241e6211b0b00300301194110050118420098241d0000c00544904041c201450703403950700000e840d075100744203190201c0c3d0701402c0a159200c030540c4c00880403ca06404407001e124070040a40f11200143c00002c052059500519000d0700e18809659200d180310001d2112016041000c0c0c0141e11480c4c080c0308910705603115800184c070034140020680c1e52140880c00380c1e0510f030410b1000c980305004104035610203001e03082c03c03016400f8080040805000c8205000c41c40940070387d04848040001a460400445248003d800b03544102d4607a001a42c0c605003115205000c0c9038000d0180c60b882d030558084901940c1d050f02c1c40b1074042c54a0400200040b11a12800a0b80b00d034048404220030703104003000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 624701537 1250 624700287 624700289
    0x506010905040c2310030c0e0405070e0a0f1d0f0406020306030c0d0506090601080601050d033203041101140304030e010c060e0c18040b13051002030f01060809010b030715050d0501 79
    0xa0404c0e06254010080040e580605450a041c1441c981070401c0d03a1111300c0400f080021030b0001281d444048044848210035440c1c0340d00506180d801140070012265500d088071005580440402c1c5c40155420806200340d880c2041520706401040014119402a561140c00a002c840d180070000c0009400341140c0301c0181c1e01900442c0c1486446981841202e0140040b00d000701400e525000210f920740008440107410014400340001d40e0103031810b0454003106003100005803d1004c40c00d0800154801e80302281c04139010259040154080c0d8001c01215070aa000c140c21a610707030b2415210340e0310340f00c24a410400048036074400540303030740f10f51400c0208070340051461b43ea000090007030280c0e490042100c02d608c1d040801000400305e550940d8044407928501600d40410710f0440c2c5024000410134545078008000c00c52000d100154440c1298404c1d502c41f0b1194644203410741c02c0340d42ca8445c154058101000602002c080c9014a00003601149000362800315510105c504585003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 624702787 1250 624701537 624701579
    0x5012003010e100b0a0e0409052410060909020c10060b0a0207050d081b0a12120b0612162a05060c040e070c0f05030310060906020a0506010905040c 65
    0x8040018004298407480c443c1d40050140b0070400c0c01410000c05160030f0250b000d440081092000c07030200c0f15100e5411041400ea840f0b822100c10010f01003840408044c00c1d16455400381201000619551030701c480c1100315045a290100d05c44e0800d400c1c072000e9404041040c00500c1640303202c000c403904d54412000100315941240ba200c3d22200002400c2c222981e21180c40780c0c0c01c400d03201c40030034520710884688030501d5002502250103403c6840c1008011000541304a100b040658004d0f60800c2c242024801c0381d101c104001e080000411007140135249070241c0501c09680001d800d4049000840c00c80c00789420403c070740407580c074144c040d50000e1440d04c00c00d811407800d001c2c0410404110b0607801c2001d03481a1402e2070304000c3c2d94803007228010b107c40c080122006000301440000c880d45050b1903004800e40350b4900c0d00306d01011007990a8400d40c0c0008088580010b40c1920104a20450320380c05006440750b6480c09070040085c002c06001541d40e0045010300085614401c1550005004 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 624704037 1250 624702787 624702851
    0x2060f0109092f09060604050f0616050a0f0c050a1d0903160606090513050d0c0807082b020c0c09040204060e07080708060d08090402031302040e0a06061a0405010c0501 74
    0x1840f1040c4161010b001d444280200814403003032205a0303078050035401d01d007402e403005602c2d501111080400390b44181300c003034000d00a199500091145248101038003d001c2d401c0c15180c2a981c009000010f003051042e00d682d00f00c1c50034040000004000b40e2a0040c0c100300c11242044c00501151616040990b004c84626076118810402000705000c0c3c613034040b01e401d020300c100c0340c41511050b071180c25a02780c00c0b0400070054400c004001250007030794021074012842d203844107205120f8011201c90349402d20021501062200b4811001d07000302d848810266018010a201031824003130240d60150049904c16110320340450045820301819100724415070317803208281014003000c2d0100030040c01c2980161b640200402c041035140017118100c12081c3c8006039203554020740c902200b0300c1200001d61090400c40942031000d80000c44000d418010b403020040740760355110407034841c2103075000c680c4607410501080000350300403640b8280c01805200041020082e050280b0310154a800a40ca1400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 624705287 1250 624704037 624704123
    0x1e080105010c030309111c110f060714120d050105211e03040b030906010f060c030813080c070605041701050420150d050a0b010c11040e0304050315041202060f010909 73
    0x302c0708008006581d08280e8020032540c9ca0500800d030705110784440034001c0e0743c0c1d044001030114010001c0d01216641154000c0d22003098183c2a006000203215881c4120386503070499692071900b03003004281201d03440003401205290300740b002031850040c2407080340780414040000c200919800947c4149010000b8020541c18094004182222904031404000f04c2070b54000c002500021090b0700603401c1c1d44420500525468204d515100380b260041950003064000180540c010b00540156401c885014845035603020f02d9501722942150b0250030040c803100d00c81d400e6802e55080740b840d89400380c824030358418030000c8202650300c03031160b080c2d804c1d90f65030800c684201d85204480803040240380416151495403035810f2340d08030f41e2900c40d2042d9626146004288030401c200c4000b04805419509440c1000c2800e983d484401c403400e55130900616000c00703100d84007240503489409120351080b00d990070001c0003130003000710a8048031120001841681c9001003000580780710021064074000305 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 624706537 1250 624705287 624705293
    0x6031005041119050f07050a0507030627080c011514101e030e0c10090e0a1401090b0102030403170c0111040506091c060207031e080105010c030309111c 67
    0x9400b0a03003070815803002440180b05507240840c000c4550901c0d13203420f6072100b460070582d0016204500740241588140c0900c0c0c410880003003030440c2141c1c080d640030003084480c0e0500d1508150514030702900c02c000c1c440f8441c0029030503005041d07016030500000070711481a042c0381e42c03030022a07004144240300703000c80070b6a42e1510a052400b607168520b42846210142da441e1117014408003250b8082c03544401319000500020451012a01c800803e0100c0750b2220715000351201805014040450303404c0c10004003c00c04074010300304d12182441a004c0c00f6864601220014880c0d81785003130450008103c00004078404800740c0394202c143c112160340d5602c034400c0300c0d4211007040d0101c641038007080c84104007a54a20040e03403203840050710710024504001c4601e000e4100601c60080c4551720100d501c006044e40040c0c04444030f40e5201002c0f2005003284d40541c0c0d00e80003441210f000504010700079002038466000305910034824540c0000402c04100064913440c1482506003210700403040d40414 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 624707787 1250 624706537 624706541
    0x61706070e0a2c0a0605041503030f05030703061220030601081b010309120504081e03030c1c051807170703080a09171e0313050910050603100504 64
    0x42040c500380400140c0c00007020a204000030b10410b91054120240300e07003048aa020001c105404140340a81c030780c941012031a00802c143d0284600a82c43d14012480340b4280c0c00c041c1054a0301601e4020202480031801c481543c8000c250108041d1201c400107110511031003909032540c8607040403500c02c600104144008120014490f12036840200108040800031030100318503144030030070106a1249400581c050460b080d4010700d841c1400c50b90000659001010f0015030710a0001c0c2c82805a680214055a0443c045030070280c1e0820070100714080c0b004401058190800110b511021041da458070084030f10482d00141c54412400c8540c003144d4003405914007400b04142c805600c1c0706804401c503619001030100401c510400503c41118600400c2840d00900c07030010403844082d03d000101340c444030010100820503115400b119817041c008825940e03400920204941240c0c500010031403036000141007001c910846140118103521340038025441003110380001a0054542014001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 624709037 1250 624707787 624707791
    0xc03180a0f0c05041103060a0303030209011b0501091103030307020303132a0611030f0403060506210c0312250201050903120c19080d05041b12050d050f0904091104061706 75
    0x105e10b0b0010401c000c10ba6540b0103501c01543e81505c1c006803642c0c010b60050354084a062401d440c251509000307101045015002140090310429400c00c00d0910441856030340c0c0004ea40b05005138000303100044c80c0c40c0c19402c01074040d078090303502d40144207403e07100c15290425807400b0382d180400c20b050a12100da0849004a2288410401503140008a184501e182e02490000401c0c943c1c80e403010070750580c0c83c002e16120352021b405020444483c2c9461a0359601c010180c142d000303004051030045108805801d0710100c412229280d1244d201039980200b070084168002c0b81031000502c00e031189500c0410000c00c0c010707003d40c6103507580d5944503000c07464200e0241c80c0c062544840401103001916200964811035074a200201c2c080d101d0345400c001c015103001c902510703607002e8200040c603035464400f4a10914001e400b6100896070000c4112010b100d81c003c8142101e000300051400e600b4140c1c89059aa402006a010039210000024007950940d41c0807444881c1030303070f002d40003c40080c41019 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 624710287 1250 624709037 624709061
    0x2a060e1b03070807050d02040204080708030304060c0f0905060a11060718170a031103040e040b06010f020d050f0f04180c0f08061807020a0204051f050105030c03180a0f0c0504 77
    0x2489501c0c0c403501075544c43d01070054a0041501c4000e1004546654042d1030107001054160380341c007034239001515640e420498054444604284041c2c00c2c81d4018032034001502a07665030502018208801e0011543c4034051060400c4918200c1903902081800410b014111607559251925800391039140d1240caa500804038951008541044001001485a26480e8141002c0d00c004440201060550089078449003020400c60204010049044006481034401341c0784d0b240000400307942241e0381c031030401012010500410000910307003c048017605000d401003640e14a0140c83c0e01201c00d400c50f50564405a007a100c100317454040d904004210400502da141400d80e0380703007a00000304500c070080650b442454040001c29840c5100b40f000e059200d401800c10312507410640c140c903c2075412000405900f004800000c40c4940c420001c9901805103c0c96007070940e226031140d408000400c0c0d600303510034480d03100b2510001d5085d0b03d10401c564020b1880c0840145000c05200903100d804141c5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 624711537 1250 624710287 624710293
    0x7090611030405090c040f06051c091119090612062307050d091a01030b060a030f02090a061203121a130e0322091b2a060e1b03 56
    0x100d028460020590381203070401c64510b49642c54104041c40107111742d070402440c0344000340020990310f401c14010120a00a403044025160611610b50100c44440c14010251603540201c020545003001c0d00d0500b1404517105680d425035200401c1c0e0456071194490107107039151044080910507984180c942c00340440001c1450040502a640041d9100404080502001207280100266a0b602422803035274021801606200700d40c5007126005800d100440703114051400081d01800c10a076803004403603002e4003841902c05d0981c02c01c014900014030810a1540d2488005030480e0301c03101c3d0b01c40070781c080d448080c64196031241c1103099034007603205014858103100a044290312801c9103041c00200f0640002502c69451808505501c02c148018403c0200c110000e0440020314406400303e030b1031440200200781d405a00700c110a8848000200818a9009074100003d034000200502188071058040020800d81e5420104c50500710381000399400003501d40c000203808242c0c0e15516100300c000f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 624712787 1250 624711537 624711557
    0x30b1002010e07151206090e120f04120501020705070e040303050702120306010c030215190b0f010c0f060f0903110f151b09060708070c0b0306180702031908070906 72
    0x520740e51001d0b10f10850000e50850f50111071100c1c0f0400340d00d0b0501032009400d02c15540d40b80b501102408c5404411401d42c043d002c141d001080040e41202c00c404030034081242030501d040008010400c0000081e80c195408104000c0052010b000440241604c42e0419429040038140201151001040203003036511030382c2a00c224144080c15a0341c0040246440c40e0707514841c1c5001c03030a20501c40c03400d1210810316010301213044158102c01c0c4124020b81402c0150104e0134042008403d00201c0107400b040001d000c1034040f0394190310b100c280901031000481c2c20025a80410226100d03860240c0004480c04c0559481b032a082c4185200d10070350000030180403000b0392002211400140c04c002194590881d40d0403600303100c0090b600c47c08402040b4648031001814856059406204225620841c1c1c2c240419004894416a40a071002a000040844840c0301038144030802502000c00d5100c2030041100d01d515040c620384501740c840e62880d10711300b00820081c02c10600764008205016a00d40 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 624714037 1250 624712787 624712811
    0x1806030c110c06070b090c040c020d0212030c03040f030c050610050a090209031c0903051e060105030601030f080702011419141204060902060408030307030c090909030806010c21030b100201 83
    0x3540c528540008105c0c3c442e44032031072a02c1c0b5016000d500707030b42c0150400204d00343d010b402044440c08056543c09580717840307503401c080c0c505900c4203d0340480715000600100e8040b071191003140a1140c444e041580ba645001d8940b20700d00340b000c4a107500038a10401c4180b0141c10724290b198010300f0a94404d504240071000040e4860050a1481000301d00040309000040d226807030020003560040c0607200079008501000940c0c4500101401c0f00b482540000191400c002407854100c90b009500f400420402daa1200d0241c0e101a4042c1e041240380c1000007040e13010034000b807000d0000b41c0b44090401c061050060882c1001d044a214889000d0204c40c80500c2c0d54000142c0c0704d6448040040d0100e00c40c40059103500490f0002e521a110210801c0b45032500340e40000d03604806a01c82d01c3d2070a0b41e500d40c10703003a100440402070000f40418045401e44d40103d288066652040d0011701107210f0002c03da4011000440103200041d4482c03a442c2c1d0141000b01001454074124402807104e580004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 624715287 1250 624714037 624714049
    0xc011b1104050402040621060c0807120c02160b071502160b0c04091508010b030c06040e0601030e1b011b1205030417070c2d060e011806030c110c 64
    0x14007401070b078450300000c0440d500d661118018080715040614031203403102d025020400c1342e02080f12017030301e816514014207010790310440c8142d181c0e5451060813211a800070300500329440d0114158428442c15400307544500303211501401c480c0c000c16884007200c0c01d0190840307815420804910b0310410041c3d03804984101d00c54001e9070803000c81d00325600d42079000c1201e44110b038440a50145001c401c060b810030300441c808102c031720801c0288520b540311000c0507160851407041ba540114100f104000c001919000c050f40144141800128040038014080c02d0100440c50f0014954240d09860707401d41c0c1000e6043d00040d11012800d0640341240d5400e40c19407045040c0c00309101e8080006010481040036403650003030b40008003038a0304030502d011940c20f0410b00a2031909161300c20303545260f483d03020350700b480600001050800c3c00c0c036046003905d44020f410100e0741085106200300d0b034030409525540d00149550355000440c110a4031000b010b90f12032000c3c828246d045030022349284e64601d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 624716537 1250 624715287 624715313
    0x519170601031806050a090b09010204140f0d050a03122004140a031e0b010918140a020303130501020d051801030f0e01090b1f030b0f09030f04080c011b 67
    0x7800d00183c40740420103031029002200c500203001c1e074201400c02081d89000c0d00203121941c40752100b6082600d40250650903809540901c00c1c044002c0c1c020b1300b0540c0f4180b8031801c0702d460003502010500e036543d201c60b810468044020b40c0410007811100084030003a2003402c0a401c0138200c00c5c000719506a0090002d4821485040440014942c0410255844401c80300041d503016900032514a40102d42020200c6410380542d8110b40c02000092030b040f09024242e021b6602c0c2c01c0000c00d44e20b15a88001c2c000e81c810070714500c0e9208186060005803000c0000b0100f6941196a0300055442e03c000240f41001c00714059080000a12000d00316000c000c0040319005024200491428142002000188413610b07004c0d02c030350b09021790079050006660032a4060007003034004103102c1203004945003844215101c010b0501d8035a500241039900403210154014800d030303042d280303032410040003070845400c076400c8020160004140c14070950b1b000031884407c00c051902d1110704c899591a0f402ea030302c500c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 624717787 1250 624716537 624716539
    0x30908040b070615060e09150f09150301020d0b03010b010f020a060209010e0a09020a030f050c0a1d0d0b0f060a0605030a020714030316030509010203100515090a0605191706 76
    0xca0100e0400006800440c48034042800c590351131aa00c1c803000380f02241c81804240203218680104440c628802d0782e0f06040e038005405800f902e1400418840c01c0500107000c1c40d041e140012200b035066400380000d00d41c0b480301d14004a0310710902e50070103085510f07034621103040c8803200304540004c980216585112070340082005840b812642d0050701c020007000d40c129840b902d00d66010440c0c41c1c240c0d0291134141b0103590b0410020455100a004440381034402400c0d004060100820462007410402090383e024483c886d00000c16070007241c96940d2640084034420030341c4041100442d25207a09d541d01c0002110410016172034820050800c0c40040c00c0b5403a00d5400040f9902400700405a0a40c1d03410708208582e601d25100c01031700072100c620b00103940000d0804000c5508041c05000382c4e80901c15484400201515000c03c000113842d445034406540035040c019003515070303100480e00c402403456480340713030f030ba0780c0700d0071082c6004030075003100308280301910f1002e2501c82d02c86c043c0b09900c114 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 624719037 1250 624717787 624717809
    0x1051021020a111507020c0d0302120a0306171b060903070906120b071407020405072601140102010b0303030105190905042105070f03120905011802010906021f05060f2106010603090804 81
    0x23080d04080b801c282800b006444280c6000486050141d0b042e4090012925910102c2502c84140300c056034807158801e071000b0f61018a241c0b00344032403a0007801010803000040c21a141c0d41c1d40d90644006480301b90f4403c001450714440c505003401305180c4880d0b486005e9140802d50f800d100121035616014040d0041d00441c0d445002030b0481e03004412403600c851044219002c03a001c0c0800c14442d000c401d019145600074070300d109551950050189001d00b00c00200690704681c2450188140d000c400b40b0b0f60030001d584400001012282c0744038840c0940e0040c031024000400f942800c400c0c18480d030407000b0801500b0420100414551703084481d0242c1d051a01d01001003200c444480a8607054201900340d52905a1403d02d8080c10310703038a540d0030f00c01c0c0c0300c41007541da817404142d8403410301c24404a0a543d00b100f50b2056070f802c1da030055500000043c04d40d1110b1000c40041010140e4030701b600c3d201c01a8040d00d2000b40c0500f00901e50040c81d040c64140000e40c4181d0742e451090185110302e00c5406 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 624720287 1250 624719037 624719059
    0xf0f030308150d02093d15020c0607030203041d0103050307030c060213060c0b0109020a05030a0f090f050d030b04020f160c1d0106090e01051021020a111507020c 71
    0x56250500c074141c40360024400701c50342c00e007400e40994518956205850f070106c403240301c050504504969031030400403079201c0c4064a00c5c0091075000210740c01c142c0821405420748840f0969618006007076098040c1d0300443d1030380d080042040f24200240501a43c1c003903030310010000588008219202c150f407500c2c14000c07105040c80c200e8043e001e080c4295003003150580b404503455610100382e540c2d06003c0d0307040f4051645e0301c0080e407040384105811040010810400a940940306401807541c1012140002441c102d25440c1d000c003081c1d210302d0448103034000820445010358140282c81d0414401c0364110302e000c1400c03528503036510407110440003410b21103002006102a42c4942c0d0018a103644448060011032100c40c9025007090107443d010038507513000490310030b94004030241600d202800000d101da801c0c8005884a4011a0703103284007280316541e01114490310700182c034041c2510340320800781c01075551400e400c0c001c02c1021004a01000700c100521141d000410401c01c89042d10140302030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 624721537 1250 624720287 624720289
    0x60e010603020a0902090f1f0f050d1b030c020c0109140a051f021509060402062805031518070c0f1a0402040e0d02060408030a180501060f0f03030815 66
    0x240c50158006540f020b4280300004100b4500d800514817000d0884480b02c07480d4401c000c0010f0003c010070840c044140404000c503126029184003e04480c0f5030601c20308200d2181c0e0780c0c0c400c2e1020a41c4403560f011b036440b0000c000c03135054050040c841d105070025007601c0304400c000074140702e145e01c1410360400c0c52072401403890f05e8801c0c049001d024094907459223401505000c4803001c600f0b43d0800014400d00c401c1010f0403914041060060b0b5102000c1c101945541e0204801d40d000080c070502d900030014907400700c1c4450280240c0860760240c48846d02d0f4a820f9040e49001c0c02d02105080c0034041803200306900911961a00fa48442c69041010b400c0780142410821461000700080c08400c105110b04110038a64613214401da00c00c0364280300d51341c084143c0c961560011489032002d640039038046400271b02d541d0061507001c03552100000d0b001c0500386000101c41941002564180d5498205008520014038424090700c00104800402813456400404190005080300c9640ba13451000f0415 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 624722787 1250 624721537 624721541
    0x629030c0409090501090b071107060f030b060a090611070e01170c060a090317040602100b01021006180c08010609210b0703020c011a010c08030a0e1c0e010305060d060e01 75
    0x2500c0700d80d000f008404901d16080d8003c0800c1d54080c0d40080900c000144a284901c005101e41d44818004c0c003840c9250403015a00d4401c0c0504c003005140d1111400401915800301074130b020001030341d0344402949080000380011503d0700c1c02c50032581000342d0070f10501056002c9641180c0c8800040080e800108014500b0251b08420300350b40040d00081c1400308540c04681102641c1c020912a804149428040781c024421403140d40050780101c102c018480c8038a0707000c010100418010780d843c2d0005016554121850b0b5001405170095000c00d80101e03000b80d20401110b801c0f1801c0c201d12a504080700540300b60f6442c42102c03070f02413000c4030302e40d11404940f404102840d400348000c20a410041c4010340a50800075910a01e50310701420504113046401c41141d0601c0180c40d001091542611880810750000301411440d6413030b50040d00042c0710400420400350006c0485107030000101900400c02c0d5070148503541014200018462680e80e413148081d899903000e4400a081e06c2c0c40000301c6c3c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 624724037 1250 624722787 624722789
    0x21203070501291e1315090c080a020918070201020c031305010e0103050613020d0603151b0305010503030f0703020f0d0e270c070c15120629030c04 65
    0x1080d5400c0039410800807403400d004030f01d040300038611036542d90410b0701800030035006402c21540340e03441440c8032101c030700b02a0b041c40c40c140100300021817a001580d80c01100d00060b41d000d14070103507558140c800450703408411507812640c111001e61410751a2800074240c0034940d02e0740002c83c111103001c44c4503103000358115440d0858082c01c2c0c80d01c3d0a130118803c1c080580600c00c03180440c070507400d201034940c42f9104081c8a41c230010019100074221800c81002500080714038004c4603518040400444c940001910443c20380740b030301103182d0400510760701c01c0303050500103038050504006c0144090b903808070a0343e00054040f613505807110340c00d041c101e107020002d413a1940180203420840c000c41e5480312495080e900c094450b640c42c0708405200740c1003603503500006004d0700f01c01da0210f54003100c864010f203982c0340210070030010141c603040001c0c040003010080c02e000c501030101000c00032009000b0203000b0000040000311210040300848081c0092120030040380340000001648208000103481c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 624725287 1250 624724037 624724043
    0x20307260105130905060a0b010c050a1b0510020703032a051c052503030e0d030e01060f081b01090f03080705070f03150c051b06060405060f010c02120307 68
    0x12410315154500115010401e020701400307420040780c000c5010b50180540f000d0030350700100805e0140e07a54601e0350003c100982d0114100850302c030131040410020812002c0c400d016025018400c581110300720f0001c1686d038485802840600416100c20f500072030070381c04032901801c0445082d80c2100407103902d002c651003021100700c06200031006110000480d081a0b012050500c0e03000e4090000985141c050018083c210f01e04401840d00396064550070320440521904005c50b00c001e2080030181846c80702d00c1c9400005c0c2d42c4010309070341070300c09018400062036840c0c840c0282e9030401c05003588231138000c1c0d80c5404d8880c0c100340c00c02190341310300c0705000103100726495456000e45a00d018071442c1c2c080c0c24151900c3c411b03007002091136072118512034120b079406491a13807226001758040d8054848821514180300c828080301c60000207603480310034002040c0e00070b444180381c2003040008555000e49460b02943d190400c0e24000d0b40c100106402003601220390410400340c3c0c280c0300d0300d5072040b41002 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 624726537 1250 624725287 624725327
    0x40e0403030b1003151413050f070e0109061d15030a0207110a0608070c0501060503011506020105280b060c010e0f1509061b1b030d06090b13020307 65
    0x100341079050b403203a409040c04a450b800342a01001c3c0c11419241c075011414a8164201d004000c0c0c3c1070580c05204c1075500c0541607145070804c81c440042103038001c40d51070503407440c108200840b07941e0055108110030000d0074201026800c04c0c40041907112641d42d01260a0070004032484103944858800703c041003c100c545940745001003043d4003a4100c030f034007128441c030140b83c07844007480d24001d0801aa003561b900c9840c1c55507001c5045417004103280c0240c64a550320b01c0c01007682c0d2804c1c007a004813100142982c105840ca8464000e0840d1f0004201c91900481c21200406001d02d080c8803400c4c005c6158804103080c404200050241e10843d081c0c00480d41c40e1075640c119850012600803a0f000041090b106158440c80382c901d2000f8041760101a00c0c2c09c80c100003011304407041002c00c0c03c402444405420024200c04107010030722201c184130016880454010a9001580652000703060720103401d10111204030007080361030279015100300f00181c01100007240300384154002a0640400085 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 624727787 1250 624726537 624726541
    0xf06050403080d0207050a12052106090402010309020d1a041202011803050d0b0a090e011d0a0318180f0b0d1e030302070c0b0703090510081609150201050108190507030314040e 77
    0x2009d49a540a145203641070142d2280b46c03030446166030004d62249078081c04030021030b40c540d401100240304440c0c040740c0c8007600d5845400441c403a240880c054120f980d0081c0b100c1e0805040100780c00507081c42040c216070400303003030b019101001c142001d0100e034541060368460a900c014100038007090891941c001e484e5a4001903404c6003a041f5058400c500d0700200011241405070845101c01c600e910020350f40711001240029100c1c0a01c0802089a298101030980d02d400364203043c0110002c2800040344c40b07034500d0140410612529808901c111a400380350000caa4644600d4040500341a102a510080420900d0f02903011283c44c9640400e038154210349417901c020858001e0301054000501c1d5200c04501800d100b0030f100c00d60515a1a001000d0b5100e20707850105001000301441003140e003510000e0b0201004000342c0c40d4034929000030030030b981000050382c0f4140c11224550b40500918111030301180001c1040d0050301d400d4039000360345440540504049100c6c0c0d80c4445426440002 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 624729037 1250 624727787 624727823
    0xc0c030f111027170318040e060c0c1207200319061a12030c070902040f03020d030c02211903050301181e0c080a110414010315030303060f06050403080d0207050a 71
    0x200400790006c24800c100540c81d110b0060004640e00c06420314400d070720003000300320320808840240c006034441e00200c4136400d55406001e206900310303890444032010b0704401c0e0040d090188800e81d01c150340507001407000c814000901c001d50703404400017030a000c1d903804d05c860040f0007180881e400d180c0060306102524500c0c1c204c1c25034030313030081041110901440c8004611142d450084404560b00c0750030820300345055800700010300480f404110b050147c00c01d05180183c4818110700085540303128101c002c180340d80401400c0440080c0c010701030b1a0140148030001390440143c07070645400e890144a01c44010a8600080148049101580b0198031201024040c26044042031000a94400b11103495210000d001d440030301005180c8100207000a101c0503c640e9001d02d0b45100524010851203600c4180c0243c94032603410640009854000038408007082020749001055545400c45c0380c58616207d00b2914050800c001c03610303d4000610306d0a01004008003240c10380c101c643c8e0403030244211 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 624730287 1250 624729037 624729043
    0x60a030c0201180c1d09070302120c09190605030601050d32030a0e010f0e0f0114040803040e0c03101a1c1a010207060804080306010c0c030f11102717 66
    0x1108040c0c44004000d00c0c2da980c5d81c80101c205002e078200c0d00c02800c400b800d50742000309d25241d40907015102c0c424860880066510044004e001e1161100740348a08008841c6041c10b8031413030782000380030b9400040108100e881d01182c0d515400d801490700381c248001100c548200c1500c0810030703440030076240080d070038101000c4000c2003030300d02c1511071019950341e5000541d011001d800a000103d8103008100f5100e00341101e02070202841490f1030580014510940b00940c0c2268000b001386900c041740c05d0185010354000c1070b4210f100f082c82e80d0300394a86016224008942030181140204140509204410b1803c041d90300749448c0244490103465904c1c5414014401240d8400380e1400c000700211007035002082031404e80342684e4a0300c2807562151501600c5620181c4040c1c10000410905008100c0804080c000b45100380b42190b4590001d060408440c0e14080103507100d01c0c20310508111443e0000940301d0b4040b07812001d40001381c02c0a071000400300345a0300584156600c0c0813884c142d11408 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 624731537 1250 624730287 624730289
    0x1030b0601090509150d0c052e051c0902030a2a05090106020a170915130927060b042d151a070501091208090c060a030c0201180c 57
    0xa90352151110343d42c3c02004280002614040c040d840d940c09100b40d5400c00c009007505e6a8050300c1800c3c1a640d0311004150b41810000c101d40d02d03285400107201e2030303100c0880c03000e04d05100c902c1d0450500001d00303c10b00c0c07840701000810407641d50315181c0b2011910f09108004900360040e43c4c00000c003242c4140040e54188202c0403c10000e100c070300105580c80d100d2901c0f41031324400e0b4010181480940d4030301c0d00c0c0c1c2c2002908030240c2e10052090342ea640da281802a40b9600200c0c0d000d9441d0020040c40f100348004a0300803682c114103001a060000b117040000e10f00254881e02c81050000d41c50404000a00121a443c1d400c541004205400c07125110001c200405600c4004501d800d100101a0119035480e5640c1001400a0f1001c00484680b09074041080d540c2481c3c103450107440f551010f0031105d4009044500c000603441e1103030143c2d08030001a9108001c84090505104400000782c420f1051854040078540d43c4d01c840b00c0f0291007580403108012803020032036814030030390808102c03400b51 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 624732787 1250 624731537 624731539
    0x5040204180b06011b02090a020415050a0203070809220e0d02010e0304050103050402011206031a1501082806141504060c02011b082208070506070f020d05030301030b06 74
    0x104884486100c0511041e040141e030000098503654031408011035042c1d40003180200144544120100542c0d9240e503014024a0035000043ea80c1d454100c0d0100454001d001c2d0905102051028554131a0080308640540342d0007600319a5400c84600022050414410f4031311004180d000d495013081d1065201400401214003240c0e00724201010407800e132074207441a5141500144010065940a600003e80041c414142240c80081c0e41b24107004640c02540150384038404444150081d01a49068940103c0c5803140100d070700301c14030f0010b002c03540080c0103030411014002c04030445a024903050034130b104142c0801d1001d030b07980d101c118020113601c02d100e070701c00c2881c040400d25620406044904464180d00e860445010580043d03a00d107002131080542066990144000100c200f0000c0c03800400f45a010310034041540140e0000c8907140c1c0188a080e4042c000511690303a481013601c600a900c1f03829403140180c24030104a111045c004000e00c0b0384070100021040144014803103100b080 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 624734037 1250 624732787 624732791
    0x71101060f060c08070c0302030f010f0b090705070b0903040f0b04031a04021e04020d0603060e06010605030915180d09060809010501030201080a02070c0503160801060e0c030c210a05040204 83
    0x289424400c26520700038800c1c140803070303528010369000450f0340c0c0c00303000f0b46401810700c1d10309a550390300464180307000c440741d040079655601401c6007406160301c11014000ca050752a14450f107450718028125100c0e41a0207481c070099440003d1042c8030404c201e8002e031200480900140d07645200d400c8594015000455168480082c010f171441e8203c000c8a00c110340007030084489980d00690204081005404150455020020400707150358600070540123510400f00010711503100e10a2078203000041c0c2241040290400c10301892180015045080d0340440e0741c42401a02c4980300b0781c005007a41c3c01e10400710301496240302d02581e0407008900864006444010700c640d2207001d5a03080310400d003c002d0200d01d2000203d080d01c207480d0301414002e41b042c800704400e5512100000e00d481304a10a151801e807016005001c04c1000b805213900500b0b1030507003980d6a0508050308000d80c0402012a8450040030414181801303242007006104a42e0848a40b2a4200001054003524084038107078080d40c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 624735287 1250 624734037 624734039
    0x3120a03050105030c220609060f03050c040911100c02100f1b0f12111002030a0e03091e0102101e11071a090304030206030c03043003110c030307110106 67
    0x4100429003840c3e03000c000302070200c0c1b001c41c103040f40c0361020200c495a400542d100d2000c42c28480078132410000c0d001d0020032131201440c40c070349145481000c44520740100d040c4000000082d00c6545810741035001180c41d0300c43c20132040003c85418106010180d4464034511600700802e8000e1040310310030009540f192042102c1102c030140c880d900b28802000b10950301e0380d00340400e008801306684241c883c603061009444043c1c1003481c0c00d5540d5122000241d002081c4140748140d0320825001c82c01e001d001d1400d00011000190b10f00e02460001401c5108110445169038401d210803001d140c3c4840c01000480713800d055000c40c081c0c4080240da0324521b031807e0840884800d800b900d1500790301520340006411206108100d500d000390517504148414070001c070042e1340f000061882290000801a100e16003410480f040d20502e20309079111240032141501c29607101c000703a05402d00c80381030208a0b9044550302c1040f500c213050010006000c044103018603a03500c001d1440128401304000c2c4641 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 624736537 1250 624735287 624735289
    0x1260615120109021305031005090c04270503090a14030601050a2303010608010c050327100e07090513020907031a0f04020708040b0d0501080a0209131103120a03050105 74
    0xa071107402511025000340c40010460420650010030603e1504080424010f6992000c24900030040c1c23503102c185a100c10401075800b908010144a81c042140c003402002c149a2810958054002d80030f42c500c0d82c1c00c440501800010002c0303d00c801d20160030b100480e50b50b94540380340380040340d1a2a00ca13000f02d000008840c544518142c040d60cd98418080d806c01000c20542e1058107020449074155480783c60006902c8028071451492202d42c1c2c0700c0503500c0c0340a4049089101c64202071501c0c58070310041c0c10f030aa0800140126541400c40b40015081e41039100030343c5089895030001c083d81d070519040003480c0019003910091a442034038100e5076910340c500c0076015134090404004d5120f42c2c01c406481d5034030b40400c0b40c1c0640900544018601062a1580201540503420400020100190001216242d803142c2401815250080d080d000c00903400100c1c100b4015044101c090051201281030041c8402c8449420701e00600321141400c0030302d4500345607003001c019440030924101c000902 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 624737787 1250 624736537 624736579
    0xf070201060504232703040e0c040608240303070c230f0d020402070605010e0610110a0b09030909010303030c110615010309080c0d09050f0f0a090506012606 69
    0x10f82c083c110013910f1845030070503050710322030091421419400325070f1030159180c1d02c1c2102c0d1480304426006581d4132410019140d0400c94040c00c0b0400d02c1e00d013008208000d580c4030742c5030342d0440302c4884913031806810b48540041c400d143c404090351501000940c88108090800942c04a908240141c401505040800c510b000312016a541c0c016003c1304044001d8034020a1414006100a200504046054554504807942600440d00c44c105c000c041c00410302d05100e01c0c41482000b03181602201480b8040700d5195092104014100d003804408210160b03230601c150f400c1004040c01c60303445507079203013001030117454021841400300f40309010550081001152081c422a03517000d50801c40c45805004400401d001001521510700904c6480105a410b010038107004140ba907540103507034141010130030541d003c428014420310f42e0090341003c2d9110000b1a00c111071100394006665036480e00140d803a000804420001c680f8158808118108074689545c020403055906541500c200c400c0303c1c2c9 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 624739037 1250 624737787 624737801
    0x105070f110a080903160e040203120a1e03090b0403020a020a0503012003100e010e09150702060411030f010f0f180b040f11150a1706010c03080a0b090f070201060504 73
    0x82e8010340407210100e10f042c00241101c42000c1e003200c0403a1307103d00c03081403801c2440c0c01c440c54040b17004041c40154501006100c44021451601c1031805100041c081c10021813a034246003021b10a48116951a00039808130307200d6034110810346000c3c505403400030340f00d22001074103e1050804407808599070405115002e0b00d90074a1182070b00b2141c0324065101641c0000b4610310200c1d038803680c08075000505000740d9001340003d0400030040d003441100c1038105005071420144070b0780e0000410400b1640014141d070003941060181d52901085000309080c0884032840300c03403035030910455408108aa41c00f001c1c21038400507041041c00c80341c9244100c2c0d141920300182c00c40400001080200e90619401614280301e00040d000c01001d120100e9402203000d00036104e035000205d45549101c0e004012042e2010300c0c2400741241d0310785000060300d0150340351406000c002c88000050460b8a140e845445072500c0140300942c1403425000c0354200407002c84825005500b0408006243d060a0007440c1c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 624740287 1250 624739037 624739067
    0x21e0901050406030b0d06090302060a050a140f0907170c0f040203060102070314010b090703140702070501120c02010e0a06020918010524120a0506040b09130b25020105070f 76
    0xe46824984034085002d08170b690b06490b800b15005041d04005106803140002d1a03220703801400c3c840c45c2800320360048400040804030002e0034040ca000c0c1c00b1610081055000782400b0641d2003503151243c810b40f0300001038010b03043c4245001c1400a1207000043e0a10303800c0c0d8121007482c0201540c1c014841a40003d80700c1f180540d010300d000340000380340d01000e03a00c2c101d06c40c40009058024500000c565070004d40d91840440d58507902e80f80011103240071a0340c801c1c8c180c002031812a260100090441c8a1240507800039640c0740740c031a200d24800e402c00008465800c0407120104014208203000394046000e03180b1070b484482c800040703c808841075034100c0b41d00a2040c84c104a8a0158078011001104c030400790081c2001070203601c4501004943c007541c4012030024091405c001888105c541d003a0a0074441e1005000700040c0c4412807580010f500c0e4001100d01113900c480c500a50459010942900c014015808020760036605510080c8600d00d01d556003141c120f80900c040c1c0d80c91903080300c61 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 624741537 1250 624740287 624740297
    0x80706020a0809102d090518010303030209060c061e091f02090d121706041a040e2b1d030c04090206040b072f0d03030c02030f0d021e0901 61
    0x140b426241042403604d0250180c01c01008803411501900030f81e1000d8069140540414100034820075448070b10391002d001b05882c5001c440c10051001c0b000d0300e0701444010201a000940c2810540b0f8440c15200340d4081c1a0490700c25040058003415081c41308a41400b6029200001480d0361034006840400003030303141501c00da41000c2004070006507220001c207540019085600c20002030070b50424078840050360f9a40403030034015100c01c1406060180100d4440c5007020780044c14643c0000030704a0b0744038211000510401c0500301c0b2400c2c002072854045c00c40402c100c92260494091102c40d4042c84503a56056443c070b000c0c1c100204d80c43d400040d513a0198008141c075491418546c1c01102c007240010250b500700f580c0d514140702130740e04c448012030301051801d00c42d0cc520251000000c1c1ca400c0100b1810329000e42c11408162090070411004e03003003548aa0030317002218028800c44090040c82d0000b183e44d07907903003c03407840170f9030100c403268803071010055842c4900d90100701034540d07080b8140d50b4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 624742787 1250 624741537 624741547
    0x604050f070804170d0f0c051806180306010314060901060b03062107120501060b0703210212070c120e061912140423120c1e07080706020a08 62
    0x704440c00d180c000d100321020a1a048001589240280541600031003d41d01281d0901c0038009101540c103807900740001e1090510109070744003138542440701c504505540e81a110300a020004944500b0404180e03014082c00c4008414059220181110448804101e580313640350000f6503400c880c424403980d10354007014408600240f42103624081a07000314a00c840700d40883d221600c0c1001c0c429170042080305051a10030741004028001d0070700078160000078904101150b2009404000301107a000c0151992244454041c1e50030740c1030381c20064114001201920307040c0805485840c50345410f490b0a0081410003204502c600d20703030150010301809c510308020404800c8001c520b41155150144184401c818080e0343d1244030300c420440c40d0728103a5482e0704090400c43c0e442d2250080800e0f0070304001002e80b039540c1001848414000030394079016910b11810b00043e0804002481c0b86008202e560850f036101080006d410702660041001c0da80b035965a40d1007665920b209040c010409031007480307 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 624744037 1250 624742787 624742801
    0x4020108070c0b010f0f0b0906071106070807030302130b031905150d0b1f030c1806180f0e0c0a1401050f0d02190c0807060908040902070606030b0604050f 68
    0x18100c0c0c0011140c14801c0c140e07882d5541e105800d0409030443d582c00e0308a00000c000c2101c819200000410301c01492500d03100003140450840e204072107010b01402c020070402040c40d02c500040790f0f0603a80100041d522817800d443c0050196001e2000003c140c0100ca0f004621002c04004403402050102801c2ca04281a800b9103005081c00900c40e2500416070403944c00300b81c03508101c2c1002248140d01b20407680c40d2007029000054034440740380040201452060000a00714100710059034001070140403170030180b444c0c9001905480d000200c1d601c0c414004000d00580e1030300400c0765004035034001c3c002400d040c244c80d42c0c5c440300d416489920140b001410404014110f5140c030600e241071410516045070409500016841038203400d11703880d40094021000f90010307200b504d01c1c0c0007501e040c01300360f0b090b5118155540603940c405018603613104001c9081003003907004c95008001d0b17503e0554981c800d6080c018009d050f0b42c4005d40b4031010442c006000c03480c1038400c0318440d651280800c1240d885281c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 624745287 1250 624744037 624744047
    0x90904020f03011b17090a02030706210207030f0806060f0417120c0f061f0303030c0905030f0f1b0d14030906040f1401090b0d0c0318030503040b130b040201 69
    0x405094041d5a030f01d94800d1100707460140b0301c910901d00d442c2c3d01710800d400041c43e080007a0040c0283c400c1e410000b01c0c02c4c0143e6010843c48110ba5141c50404024903080000300307000081100d003a1081480094120109030b007000307008904540c6611a11003950b140d20502800e17114540310700c5181030003000141724002d0f005a007040c442c050a8101c07040c506086005603c276620080c40c6126540c48003050342503002e410800d41d81d004005100b45408107520041c0e24540f032240d40001000d16840ea000c07039852521988075040141030003001c4a042c101500031094541c0c00c8498006158002c01d800766940700c2c08200b44102c440006040441c0042c1d968560240007217240326107a0150004101e21440d6580b48400760020b41694004818010b03d0004901c1d0300b00c58681c5018144144030b076040120841e014141c4214990074603002c102c14069200071002041c0321a0301c0c00c0503200340300081d8141035000014620031849150400e005403200745d5401410801c02c080102070504400000700194460 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 624746537 1250 624745287 624745309
    0xd0c0510050105061b010f14010e130201020a02060904091203060f0609140f01090e0a0213080105071d01091802190903081c060909050f011514060a021f051b09090402 73
    0x190000094200c5150120426a4050100942d00404c0040140091851101d40e22f401c9035418a40a0000556600103515002c034220064495500810030170034685440d044110a0781d403042e0880920200010081d004015902607107985003094013020604074010100351050303906030074a250764030b42040104211b50003401e59080c100140c1050000c0d0083c1c000018500410241e0009601c60322101070900708420f5950091035668104024000c082c0e4000b0420003583c80d8407001040540348500069800740c5c808c0d404204840ca4280003030141881660103031801226018800ba03450340d5111040381d00d1500303400081e002003001c00103190f4800c140d048030007844200c0040030856079520380e80a01103400c08013003654280c005840c40da144090070301c980c01420000c2e6000b2142c250910551032098a22403100c02d02031080021a654a14000c1000710014072040d00001c07a4224056811009000c096a02e600310908060341c90034444900c1c425501510340107828001303c0e039125001c02c4105010 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 624747787 1250 624746537 624746587
    0x90f0d05072a0f0311010c02091506190206010302041104030309060534030806120706030203060d02030d0c050c090c0f0915031003030e2707020f0d0c051005010506 72
    0xc54400c14056071250b41c00c401480350784804000c0c0d61950038002598100350221904004000000c2e90060351741500458001c0d0440100341903441000c400700c2c42900c1764004501624001c8080748484075400038103a4180d920070b031018080c80c414982140d4560095000040c04101c0c828802e00c4124030a101078240c0080d041d20001c41040500021110b41486500300c00c61038419a0024052640111805401c003805880203032244070394140b02500c2c2c4030280508030400d900000070512507690810801c800c0e80d00102516080300c00000043d0211a81000441d91030007030142c0500d4600c1e0040460b0312440c0c0c02403c040c50643e01510140c0e540d44544501680302c00c100c40cae00c100c80c442c14800b8600c50b10080941d500c00c40c0c2941000750080442e0108c0500c200b4188440340d0420a134080e05071400b6071a070b40e10882170f4859500c140e0070300202411054940c0314038040302c0c2e0000d91101e011034506006e070003501d001c180406012410394909000307194004000f00140030314100d03000300e00c0d641000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 624749037 1250 624747787 624747833
    0x40209130c0506040b0706150506040605130f08010507080a020a0921060e0d02010e0c1e060706110409050603030918090733020d1704020d02090708090f0d0507 70
    0x188801c0003d0654100e5045000801c001180301010044580b28080400104240240c030107850240014011b1080340240401c101022515290b101003600340d2102905c003c846000e9619185c8070324500a00007125a00001150180407078400340311482120819051341c5e858a82081c101581c5603040441c1014414010100d0b000380004241548161804010300d84050841220054402800c3d1410740a420409810809205010742d54602e240b00c410105504106e00d1000c88400003666800303444405820b1500b81401e03610100c0600c0004d100b5120f072060b041045032250000c1c90354a0140e180070a8104080c41c00044422207450942e80e0b10000e003400303d440f9161034607071207014060000100103150301d662400c1c40c81078070044031483c4580c01d6440113114240001000904943d02c40d0703104048604010003140940d25000309540c81145c0161001c92281000c06000f040400112010f1100b8000d100d2000750541000c585684040000c0e03030303511300b010b03902e884108070205450b0074240901 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 624750287 1250 624749037 624749039
    0xd08130b1b0403050105040b150102121e0705030409060306140f07110f0d020105010e0a0903051b0109082703010e030d0f0e0708160902030f130c0e010b130b03040209130c 75
    0x4c3c0c0b0900035a44581d100d894014058104010840e001c0400c0b04425419500b088407000760050f404000da03210303601024503640d00c0300008000c0400903c60001e000d001400f0001d4041480c4002c3d4200d070040364030643c404c010041907203190000c0c0007001c0c3d440c07c4080b5440c00226403464441c80c0c00410600c198400e4642803a5071112840c0b500e0082000c50000d82d450b440100440c5c01c14426155006261201c14028070840b0303600241117214000c10052164509075503c00040400d40c8066070541d4058140b545d07600c41218494513582400b40b0019480a00754010961818103008241034002404011804e00072525064000740020400000d00e103652100300c01006a0108440303401401c144000d444201000003134417030000c15030782004210b54010401d108545166600c01540400c0c050720036030100c0c2d81403400c1d41805101e40d00c040c0042e014007001145400c40100200040e90340c03480041c081c1d0380d60700050000c6001c1260080c0d0700001c00d4000808070500f80307031407450542c4200742441a403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 624751537 1250 624750287 624750293
    0xe01061e08091f060e0109050907030311160b0c01050618130f080406090501110604030c02090c13060801080c1f05090321181e060c0c040603050d08130b1b0403 70
    0x3221003507003e40182a29101d0400c60222540b540c3d44c0500003881007400145884040306070b0342e55140c80001d0400100100540b0b07070180605c00c04000080b540384040b40250394464144141c0c120082a01595280c42c010441c180341800f480d0311001110702040d80240d850305000100581048000c1d07d13542c801c00c0d0781000084c81100248040c285c42d480c2d10102c1d5044c20700040412440000020080c0d120005000c040303504000400c95240e8111040441a500d04501c1d5106005102c5404203015801901064203500300d03440f681a00d181c1c008403454000f155081240d9200d407540300ca40b0030100e050b108006507101c0d000500c1101c0c406000c03515080ae0360380e40180000001c80515090030800310b6814241e190b440c04040ca00f20f002c8403000c6201c50444180510030b50300035082c0344038040002c1c0c149400b10b4180401000008020b1003080580d5071f03420501c0c0c99240485050001500f403200040d940040c25035251405a0400903864581e500c400404150791501030a00c02019030900c800800 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 624752787 1250 624751537 624751573
    0xc020c040219090b0304050604080f09090f010e070c03051b01020f040b180d030f0e0a080d0804020406062d030609050705070c050906010f0e040605190e01061e0809 72
    0x511100b401e51400100ea40b140041201916402806030a2403c00500002c14800280035800c25000182c9642d0780c42c000c2e000b110b0030712602007665041070019040003e410350300a80c190490304c114202c54815510b00ea0215a02d0b4005e10009010030760a000c1c0c00c400d00c809100c2c2e041501c6213040010300e0110118039084850304280d00400c9101000904580c0300c892004c24002590000d03160401101400e90340682480c41081000342000b003c00d25410186d07560748050740c02030600b001a9815400034200051042804503800d85c007480c2803110001d4884e12030041251036125201441901e6282c02c4003244410f003c5414002c100b544849011640010358402e450241036140c42d02d6503a03c00c0d1340303081094201103501c440c0c4624025010062540d80001c11345c180d03100e9a1034800c49001001d8001401003210b500181e4110008215085503090101d1514040e20301048d282403190b070340c0c2e41040720040e02180c1c01c3c01c580054940c02100719401030310020b802c64490320a80308203d030310034400c0d08 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 624754037 1250 624752787 624752797
    0x1209150103080a0f03020405060d0b0a030b0a0c1e0207060507030207031b03120e01050912010e0a1a0a05010602070e0403110d23070c2108130f12020109090c020c0402 73
    0x954100c00500c000802d50066000001c8040605041d41000e1608e80010340c80d008111000c110241c0380c0745001c48941e11802502c000c0d507804400b0ba8402c0c1407291803400200440320145010401d80000a200c3c8114100340e5480c41015900800e029070074024100c0c0c958010715404c90035845200d00102c006616102c290003110b011130402805e4505c0c0d4106007000e0240809840144092195115940e9a0201c1100c1214100703640070281c000c1140402c42c014090215000c03001c3c01030842c0d40c0704004c954010403444c0300e40740e1140301d03151300e0b5003030104111390081c030400c0d01691142c3d07000c00c10000304884459108e402802c0001c030103044184410b0801640c00c080130009100703000412881c1d484a42020b001000c005066420300c0c080e45da411504403a5401001344c40381c6080b441104010380b048400b41900d50064600340c44012240d5032082c00340c40ea01807841c2d0b40c48001c9011540300c00114030b06800d030760141e45c0e0400c1d4a10300040c4000610039103940c5002c600460302c036103030b2a40366800101 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 624755287 1250 624754037 624754043
    0x21080307020c01080c1806130315020d0b0306010b0d0b040204050405040f0611120103081b0d0804050c150702190b04180e070f0e0709030606090207030305090c0102031209150103 78
    0x2d0321581d1440010800c1500800000a5540500c48164504594600300044041c107403000c07a0307a05a1400300314404c0545610003044102e40b120056003d2100390085e042464a20750140f03c411450000c140e140e00c0b013405141d2241505000a02e480c071150340000808100c00f4000500e855101c00104095410403601920510241c012038800c00c0001d12441c00410b030075410721410101000c4155551510620024001460116000b0004481d210b045030250b030004045030010b02414a0103886800e0448003644c250099070320011003402c0a22040031030004201ca1140b402a031907003003207070501c0d036104001407080000704081000a5040d00900190000c49444114031b070400c40742000ba42c80501c00804d8030b0f080380604003c8450390302c24100c1a0b40000b110515540d540b880304a0b600000e5600c00360040e81050b1000030980102c0d8000d0544038080d5800707004d140d0350a541030391f45074100070311180107900402810030310050801019402031007003400d891100c1c02100e0390502510007a0015 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 624756537 1250 624755287 624755293
    0x20a1b110316050f0d08041e080118030807050706060503060c1216051614030f0c0d0207061b0c05060712090609030c0311040b030106060e13020408072108030702 71
    0xe641a1400304680322000c003000c11101601414900481e00d803001500d9030900418a2003181000c11944005a07005000314442d1420604212604034003c9200e0784114070301035180c005010000407582406103d0180c054488018a80b070740081160b4540c0510000d81d40b1a645260110311340e0b80901c021030040581c80102a182d4021590380466800081c0510000e0b044100580c2d0b1690b070040107441400c0c001010040d070040260a148002c0c1c1d810500c5e03007040d800b0016010784010081d20141a400d03a03840201c0300c480b00b014000f642d540d03069004800104403c2c2d1101510001c201c0440c1500720700c295111140b184c1d40b034001c51301940280c001202c4c0c1b441e8007044142801d44c456000001810b071803030889507143c615240e8149540b15030002521305c486c9103284044a031a5904181c01e40d100c0640200025030366104010244800d04a5603072041900302500c1656107800d0003554141ca1288025100c02860030007003161241500b07030020804c0811000b504013050003030300503511904c03003500070b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 624757787 1250 624756537 624756563
    0x51c050a111305011a0f1b03131d041103210306121b0d02040b0303070c090b0d05100b0102120d0f0f0c02061303020705041e05070f02030706020a1b 65
    0xc024403024504400c880c80703483c0000400603408451100b642c4000040c40386607880e06404c8a803c2603129000c00c0c5040ca290340428112203807000002002c3d980500a03406455a444594050917100c4920401001f08085c9010402003100260500c040b900c000f021280707803100319906410a80d05a00c2c0c0c90300356960100c00c0000e0390034000907090400700071401504001c80c2c0c031030302011042c0d00621402c2c051100e1480610071034995601c01c0700c80410040450352101010301d003440b4075000b5030040101090a089071201c4c9424440ca1011109610034041c0400d8441d214210f4000c0088021607411440340541010302d5910310380c01450314400300c1ca4040740401310100f0305400d585100782ca00004034a0086800745c10b0b03034003080d00d5030026000c050008181459044c22441c108040d08440d0340a860420101c00c010701980c0210400d41c1c141030240050741e10580295007810301090b074400560001c2110780300140580d401003094140034208144081c2c1c07205503d1b210103000030310484800e413400b01 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 624759037 1250 624757787 624757789
    0x306030a0318150207090c020c0907050306060f1206010e091b03100506071506140a1e09020a020c040e030306031f090c090204030308131e020114070f02010f0201020f0301051c050a11 80
    0x1031f118404138030300040000c04d600f4000704802c4000103003140100003011001c03910b00c0e550078040341e1120b030140782015141c1041c07000b8409804805d0b00c1035404101c0090001620f0700b0f0034000d152282182d00f68000c1c6040d0680b0524141750700060014000c01d5030500081a11f98888020b44001400340035a1440d461071640101c1c2154000e800c029281d0038410401031a990b910b2906000381d585601c04d0129218005076911080305454000040c0c035400803405000899000506600301035044030180441d5018044060b02c070f00c0251034854050f040400d45400b68410404140c1015007203540007c5c1d0bc040340d80343c82204402e540c1202050b01d4001801708185039100303000c2900240904100343d0260110740c0d480f107880d05180000c00d0244410030b004d80540e8041c41010001e8595181415503410203494140c1940301030030f0080380030030301007c044000d9510501c29280241c0da400c070114910b0342000c040010052041d210700044401106818000880600c5040300d00380c07260f1882d100f0303400014 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 624760287 1250 624759037 624759041
    0x170f0403020d0927020910030e0d0e13090302070e041a0108010c0c0b0a020405150d06081b0f0f1002161401050d1d0307120807050306030a031815020709 67
    0x246000100030f80f0380c1051004070919901c203220800e0784c6110070245820451000040d0042c004240d81c000824905540d00326015004414250003160076588407080100d0709607080102130017070a0304103004030740150810070568841c0e0103940c0680101e61401d5520403180002110442e000c44a0b105003034481c000d0444104515400750a0f03400080c0300702d17010034000400e001400305028201d05800c10200d881300106604490141c14080c1601c140302040051204541e400010380035006403034003034001500d01e00441c40e103a0103294004030000740000c0c10300300800008100d19095206c1440d114140f0165110b2601c0a883d5190350084c2112110040b0182022641c90388a06c0e0007404940c8102c102d6030f803000890315540c18003034002034200000b95101c48901001109220148000682c81050080b03060b03010340c48201c60781d14888039540c0d081e000c4070306000c01e54031950154807244000002078001c82c40c0034101810410404045070f42e40803c0c3c0a64034a00a0300070160b00001c03c107020b984018 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 624761537 1250 624760287 624760303
    0x50d051305030c1606031a19050d060b03061e011a1606051501050a0c06021e120415090809010c02040e01050a06080601090504030212031801020307080117150c0703170f040302 77
    0x40c101044461505440790b40c2241f05c10800d148100e0364001c1408003100110401c4020b404080c01d6208441014038090303004101c02c2001600ca8441c2e600000d100d0211102103c101d9038450203001c0d0780d41d180540640f90522850280140b550080c00740940c2050100c640140e408c0c003c6030302080324103290161007040d64044441d2410003130100701c20210b00d81c000340c2c1991104d0b80620010313035400e000001410403410900240e031400b100050060300404881100c1c90045001d4100c0703030b00e041102c0b03d149080f10254003004001075001d02400c1481c0d03001c0c4003110034581c0082c20103d13220b1100252542169001c68100343c0c41a40c420051000d01c1c404c0004502501c600001004a420542c801075621105c0604440cac0d0280d0003c0028401254640c0f0302e00000c000c00025512030600300c2000d071001e0800d02511a51a0304200301e00100303800016070025070b24054000468540b40c6131500403240d840488142c3c103101c000c0c1880c0607070b900c9243e0a5841611800c140c0c0480341480d1800034200020 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 624762787 1250 624761537 624761549
    0x17040315060305060c070203010902090103030215010e070c0b0c1b06011703160b1305030d0204090e0c0a03030818100b0111030c0d0509280f0f0303050d051305030c16 73
    0x5407034400d10003d80001126030700003550311035194072408540700080c05090526802500b019220300000b00305600041c1203181440904210a81c60fa01c401000700000011a241070000d94203401c01400302d00d098420355000460108001d107442100c44083c1c4801549411581d02c95001c0e000400402c030b03015140300e181c3c1403081d0165191204542c0545e2104503070100242440003c20007007000c1d0040c05440c60041c50744207042e00e07203c500b40b54039000290490f2041e500894204010300c1180301c40400c4001c65100000c002c5503195065440440325214002c290842c0c0c0404c5002c50030f400039003008000c0b4003045096020800b01200000100400501082803001c1e82c414030070f00040d203801042d08655041a032500a0b155204030300003880c801120801100c860302c02600b01007030f0702d4030305403c0c009a030342e40900b19004590b01c60000851190728400030340090011f0242c02030058003a00180d0b00b040300d00301488584076031903c500382551b00c80322401903103620920078030103403800c008103210086c24 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 624764037 1250 624762787 624762791
    0x2d04151e0e011202070206180d02030a060219090b311e09091a07030b04020a0e010809060903090405090a050610030b06090c0f070501090605094603090317040315 71
    0x5e00c1c0d40803d0b0b00340030b042259140a90000143c0c0101c0c0c07280c0814500302c40d0001c1c01c03038a4000f12030816000941c00101aa20b8040851210340c222900070402007040f9102403841d6407a02980d04151848110400d00705850b600d0381c41c0b54103a00c0a0100426809840450000401000040c0c881c9222a01c661700c44201d2a09290f545804621028482d2010041031611a20b2079a90094114000c00290b01c0d65548036101040744085151701600f41222460281c859041944034010b58070340d9040200d400d60f03070f258010030030135016040940180b41c20114101c00c13120107140a549050805030200c801d80400303c04428200148141d0500b015003191058800403941e00344034445a40d03c0c415240400080c0b140041c1040420509620600340e16030000010031990800c1003d5580340d01039007496203094408001c103511480300d42d17001c0901643c00601c20024402c011038051140d021200400c0d400e024800d0741c0000403540100d01079450500c0d440d8480e540e1f074110310f0a0154083c85660745404a8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 624765287 1250 624764037 624764047
    0xf0d17040602030d14040309180f1d191e050a0b04030809060c0f03010605091c0501061a160b10080f010504031101050403120506030102130b2d04151e0e011202 70
    0x940041040e0305480b0f07449c2c4180001d01400c40703014042c010030301c604106940b0380100001e03078082844400a600030a4025207900042000c0140d44035040755002170075222a4040e00820303003903030110f5208828403540a442580c44a5100c221030040c08680039004540c002c02041000c0700d0601110f5804000c0c0c03d0c165082c0305031842c5282c424001401014188000050314441716902d0b446114641009080182104600c130b00e0140c0c041c181b24880e414160804207005130310000820300341c86401c4120840c0302c0c800c1180d5180c0c0002460054072110a462180c030b0302254110003440015510409280003103a0b41c1800d1400504a80800d0407144c0680d1412051000103a03110740c14904400c00c42d1000f04c0c860711168006030080c03045c003007850080c0100c03003000102c02110002801102d005a041c642c0c2143d4000040c41c08119103003585900d11500708410f018600d541d50380a400c03821a031800500700e4241c1d60a6090708030350041c04202103091140b15034401d41c0e00c2821200780b03e854035010340c241 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 624766537 1250 624765287 624765293
    0xa0816060b030f100506151303030e01030e1218060a03143106021303052a010c14150408070b100506090d06020d051e0601020c0f0d17040602030d1404 66
    0x286000c801c403401c441d45c070b40d40400c101e5510400303640c2d0040340b1528480e41e0f560004000c102e15042c2480118085603c500034240c0781d6010707100340c030391f1002d20b100034001050003140560907a038440480289410075500e654005a01d411000d8444101e036510000f40300000004265030405e0000c01098080501e2110303880000b0103030203400b01d02104c1064080550390f84c1d14026000e401194000725008054020001c1030100004d4401c10900c00201b60501c940007602003801d640044840b680c0c0402d801094060025090b0810350006051540c26280520420701818444460a0b1030917540018040780d0441401103540c500707500041c26402664600e0328020102d04035001d00c1034010b11542ca102610350604c40140c0440314540400c19040101e441e10440f001600d52000028800040403000010402d5000050103290148020021a12652083c1c10042d8040520740103c81c6000c02447d00c4003580c50603000f80004c0d0815070003450b118440702c9001821110040c8030214a880c01500344804 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 624767787 1250 624766537 624766543
    0x130c0515070201110703060510051e030303220209010b0702090708040506010b0a030615091a0309070b1b0d05090f0f06161b0906090605040515120a0816060b030f 71
    0xa81c0d081c04d180310f030514030900d11410403c156102401c0542840b0800c00000c01d0140300100380c60003103c3c400301e03034444400e88400f40101c6040c0250554001c0001c00c04800100c0b9900110400308076074071134400455804106510f10070791003107480d614040f035084e08514000800715400303c22880c1c042d8840c5865129a980d820040c13081d99402180080e0601c20103110750403003400344c00144481d152801009200600008040c49090040f00d610010000090075240c01c4a0041e031005004110703284c10071030034140700d510610301c0d481c0441201c00740442d1010300b0b01420b0410300c4641c0350740f074035034500c1d20600802000c2001032900c00c2c44003401c2c0161580d5488241c402c07d520034410350441400500d010501e0804d5001c50044949900700c00007114412500101d0036100040300c1402116a04d80521013a00d034241d411020440880c0c1c8003400500300b44060340d28054000085918102d4680c0382c800c5694030505c0c20f0006146119000010b0080340c3c0103008040c40141d0003004d1000c40e144803661 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 624769037 1250 624767787 624767797
    0xe040b1c06020c1e0a02121b060a1b0507030213090f0b0402010e09010b07050d0f0c02011d060403060506040e030405101b0c060302120601020106050a05040b0a0e130c0515 75
    0x41595070224241e0083c2004026040e040108844503810a0400c00122941c0c0c40400b481244a0b010340701c1074000d40c600200321041c1e00400d40400201600502d010030505e50400b03c61203081003d0568480341000c000c04160000600420150001c14110300501c1001c0080c8075240f6485424500401d000414a1802034030490b004552506251101d2004a0745071f0000700541383d10419040001c0303a000d01c400001c1c0001440b0340d04417454030a00750f00030b1b126140c025641102090042c0018009940035000f00d10588600b0b01c83d46203c03410302800904140c115030000d8640c1a52903042003e5402c0a200307031401009070100540c01c0600e000002840d003080504000100300e5448055132403624081c00413002a54424411080c1a407180e83c000c0080d04010100014500300c230010070859401807103000141d90016012000c8142800140801307401c125004030303080000c0038000600c10140001c040c2c00b90141000e110540c0c4824100540601c40d2908880e01c9100117828000060926408940c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 624770287 1250 624769037 624769043
    0x10050607060b0f04050708090c09070e0f04090b10030204060e060306011e050402270909122203030c030906050307051207030e0a0b09121c020f04090c0e040b1c 70
    0x10818607002004a032600c1400c2c0f185a40290805c42801081030300400a2441880d42d40c0880329400316620400207228010350b050000701706004641c0502d8180b00c8400303c00103a014101158071701140c2d4403011040c900304d844454100c234291b014000c5280a00440d0003d203c0c12074921154101400001d0b1912010300c280040c1d141c840750f4200004000384030301c100520000304219224a9004400203d8009800d441c50407190f509002e030006140545542d03004150801c000d01c0000500c0012001c103920221003c1c440705400811003c51203c60101100038520994a00c40c0801c2c4900d0302a100321703038540150043c03240a1007088071941d4440241d80e142c0105011701e40c0c0d944c440e0142500104135a00502155020301e188403002c0c0861015100d018401c8042115620300d18540e9455140c0a42c052500e405d401c44246540c80000c1038010340302030750030317a0241440c060342c5800d90804c4a0250b59400d0105505070181011490184107604180307800391081d43c00d60b0724150007001205002d074802 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 624771537 1250 624770287 624770291
    0x50a0c06090e102603040e041e050601062006010b040501031d06070c02121504021e09040204091a040b09100608032704140103050f01020a0203070b15060415081005060706 75
    0x2079040000f03a016034042e241c000300545c0d1350303581c403a104508200d00441c1e0075112080c40030803542e90358040d0a801807500e03802a01800342d60b400d020048a0141801c6901510400310002c0f0350325680091011a00815500034025503c616203400507080e00e000e038070a0507a9007001804c821283c1008038002d503011003107240940c1c20b910144000b03421111a46090340032403103200108840f80b40701c00d50543c02180200c81d107542c0510076840405408a944a1040c4c00c0080000418010f0400d608080011403140c02041140c0010b00c40035403403034000310350554412074070b4800c1c002c0c0c56205010407083d04019090500400f428114095685d2050301d4043c50380b1000900c6041407800c61404180842e003004000340403a02c044981c0b502048028042507071130f0700500c035201c0000c003014822102d211095030040d500301981d54440004501c0c00034607400c4c2507060380f00d40e0400da590300e80007000542110440d20010740e03480c800043c104807000304100745c504028101844070341d82d1041038078400395004c040 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 624772787 1250 624771537 624771569
    0xe03160f15050a020901022512060f05072007050904021e0301060b0403050606030a171602030a080a0e10140f040515030708100e0c0d0207050a0c06090e10 68
    0x200c600007000600e03142400c0c624140501c01d01d070360a5002050070b020300364201e9103c811076111500d01c1000c161042d00300c0c2c90011008210291600141c61000340c005c04c40015031216004c5c0c854160741d0102d0312000001c1201011000d4490694000b2120a040d040100200c40c18080402c0e5002c20142c8040d100b0318520428000c1303d00316615001601d040a03000380700c0c940c1d8401048200745c109000031101e5000d807d0003d00349003800142521029084802d19100c2c2c840010120001d600100182c0180b00080e000540561005c100480b10300d840f0320800c9946180c1080700030840d1000305041e0344561070546e0190740c095030111020342407640a0501f60381d07801402448661300d105640c040ea030001d1000b4001c440d000c1022018601c102220346070000d003551184801000a4154068a241494100701140385648110003030469644a184018900001c41d240c003450309482035411286d480c581c4a0911459a100c10b201c0014108402c00c0019810138a1024141c1c610500070140e4018181303078 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 624774037 1250 624772787 624772793
    0xf09010b03011a011d1513031e0614071d0d0b090a03082d1b0d0c020d030b2407150507030606050c0d080601050d0f050405010e03160f 59
    0x4040356016100900800c1144000d142c1c2540460348400d03540e001c90b01c0782240c3c083c5035215010540403810024001514004409000d1180342c0100017015480c091000c0c0110025064803118100001c0c207001c00704001003170345800d00c191001c00c40013810b401003507004d01440c2c541110824524031800c03a40520a5851880802c20743c9181c413501400f40a418014000c1641010520222a0340070b9507030a0020740d103100c88040b900e2a0041c2e84803407c1c941c0402da030384000129080641000010110740804d4040d04c04411040d00802c4103a00340a40d1740c0c001c1c013003464040000100c1c0034503e040c248010340a46000480e02140440f12a0340e4058a80703607281e030744003401c0450722420391000700034100c00203050104000b07110403070380d080209251803070208110f4014016500c00351030f5007004080805500780b08840900c8040c0145040c01024001048404558011080e40b203011000c000380701d281c1400c2240c2951070034505008a038100300041d101c4504e0080508450680040021b0141e8006203 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 624775287 1250 624774037 624774041
    0x240604050f041d070915060305010305070603050a151806050f0d06110f07140d08040b070509120d02010213090b0a03020603070507120f02160608160302070c0303082406030f0901 78
    0x2030f0356a1054041d50f0703000309803010f440d48010614032040c0e131010107040d221642036084a00030700003c0d026038041c0f1750810401d0310036004158002c52240011485c41d01d0841c00c0354a412954004404804900c5070341c40d030003411441039100401c41214014034424406011071000411844054000740c0c80b54581127606140c20b04442400b075200d0300480c0c1c4ca0746603003820103400a10002444003400f4cc402c0300003d6501c201035084c000e81d04800c0c2c4001580781d403031041d03c2030fa01903580030f500544003e81005e00c0d0032052020355a00101900096910b0701e5601940081e1081c580118140502d0300c0114130301e80d02c407184c1510640364141c03400c50381c0c2e440e0400c1c02c0d2418001c2400c010300c10308000810005c440e030301507080d140c2d400c0585c088603031240c242c60358186414501c1c01440c00140c44135000600407490540c440c848101c0c642801890491603803034507040500310340c0040c0c0105510310b00740520101860000c0c01e0307101c80485900100346069000a0040c03101030b000c2c0c1d09510300d80d00803c1d034500c029 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 624776537 1250 624775287 624775331
    0x90c09060c030304030302040e13020f0405150d06060f0503160b09031504050a020a08010203130b070504051206010806130b0a05061f020114060409020306041401090803240604050f04 80
    0x81c4101c035168a018a00100690b0250190400480400020505011b2103001420010354000c211a9810403c0c00a100c020100140403100080d03607090a0500d80e1a079244161403036000709004100c3c01e0904040448811150348018045e40c045c1c5c1d60420254402d0303412105595400d10a2540c9030134180c0001c3c07074003000c804070082c1c80010100b403104000e00012018403d52080d00c8034601c01350b0314000702d4201e000480700b502902034080076a400250000066981c04541404c00070304154403034021034085003180c000040b26601050050107101010429568000140c1d007000030a10017990324500140006090b400d10143c0342c00c04101c5030781d14500c03800c150066030708003c00941e29803940213000e0440010b0034015030b00d804010803100d0406004040742e003600500244010748440d03666004c030b0031b845a98480c40303541c0c40740004001030f80b0f00f0045020b14007890040307170030603444009954071240c2ea04001d4844d000800042201c1d840b8002c00608414007100c0004242d40c444d42c11043c00c0c508 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 624777787 1250 624776537 624776557
    0x9020c1c09050103060b030c12040c0b0c03090405010e04051c051902160906050a0311040e1c090906030b15010c050d200c01021f0b090103031e02010b090c0906 70
    0x10312824198a2903101280c40100c5909a03400d03c949662800030051302e00c0203840414035400300700040e65141300100780c541e41140c8a8282d0983d2242c0d00e000e0420b1a40001c07404003010342000542c442d5618003402110302615054020440c0c0381880d0742e80955904500724810900800c21801480345800f6000361b40d501001d116000080ea007441d00000c1d111840e419113204c2016100001246025240c441c500903900c2c060021005c036421900c030303d02a00d518041c030701e41c402c0d141c1c5106070120700184800207003054440c130b980c5c3c0c0c00203072035001818040c403580084500d989000c408101040081c01e1850b000160074014000300c034004401203501f44242100900365100701203a40d10282d03802446154903a80d000040d096a8650815641c0c603a07000d0b071445030041c4c2c490510300d4048001e60400390030111031140c0000309201040085070401409901c00c0c2c000c03074480c0180c03102c03040030300c0755804c510764603071000b0091280440300050b190030303019040d0303800b0001c082814401c035280d4030700f1a003108032 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 624779037 1250 624777787 624777823
    0x1080a0b0a0605030f09010c050d0b0a09090b100603050709050d0f1205030901150b121909050c12010504050718110c0303071b0c210b0702060601110f0709020c 70
    0x340b50440a03260764003d840c080c0c0058800c82c000f980c404818400c070a138662055031f442d403802c1900d10404026040c24015244d016203001e4000811186038842c121f22103104024009140c50705840e80922a40e140e84000103040c00c0c2010400c000d9400b801d20029584100c03100a01500340342041e0540d5600c4240003010101d035003c40300c001603003103c05503103d488007000030310041c1312860340d03204010024030030210342410500c0070a034010703100720445520a803055140100c0105921085080d110030300c10946041c1c12039190b41001d401e100f451100c1d000d5080d8020b0000b0700702655201c0d6625044e11405030400b42854940381c4082c650303046507465800241680342c83e42403101d105510307a8815210345001c620109080c03d082c3d080c03100340191b040d810010491a45190032400f038a05280406100300d1092494450300006042d544580d00809a9900520641c40c0c0440054100e00d40c1004141c0e131076100d02e402c80f8002000142c0c040a0b500c8101000d038a820100680510705070b42c00342541e400c00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 624780287 1250 624779037 624779039
    0x1005010e07091a0f0d14070c0510020d0e0d0c031701031104200a03150608040309140607060207080706060b03010b0702130e01090b070807080114010c03170c07020306060a120201080a0b0a 82
    0x28282c1c0c0000202500341100d403d0f144e101d5810564200c907584400600e207800c422b483c45880c141d142d024003260740e0804800f09070b00004040041c1070034181e01c00c03e804500e10b80850018594044501c0d04040c4a9070800003481d41541c03a80104010290f031210b100c1c0c0d0b1241099070404411041445107104003032841d03901c5800150780600034018680c0c40c0002120b000c080020610b1107204024026034042c3c84600806040c07002d41d007110141c4101254101030104001000640680b000b48031081c0244140c0d515032a080c6405030559503650312070000d2a40500040c4912032a0000b01d0726141c3d81224940c0006169803a0180a45901102040c4039481c210754081031000d51030702030340300c0d1807036690302c0304241e9910308203407200318083c092a03406c50751035001124154014168455264000c0c100300d20550024540310800c00821589014001000b04013082107040400c0388175000304080341c2d4400c1144c200307a014080022203400290400070080e01080d0715034010f90044a22410160201c1121 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 624781537 1250 624780287 624780307
    0x100c0602030c0a030b0d030e120723030607091a13030501110304120302120106140d050a0f06050a0b0a0e0a08010504030c020a08010b10030f020d0e1005010e07091a0f 73
    0x350042c0380c10f030001ca0b0a00800d0310140ca01001c09402c843c0e4143c689100a514450500c44034035075940341c42242d8451040b0108859610507040b10310005009000c01d12510782c0c2c3c05150a154014003420184103c1640a000000154039000748510745201c0c110f840e80600440b017120391031158809032065192507120401c1401c4070340114810741c002d040c007609041c00340108404a114800c0340c4007000565000502410780305640c1c184110542e01101c0e41048200d81c1d4940c200c450540e910200c0b01d0b0b80c2d504031800c01400d4000c2c1002000110707441c2c2001d51400d0901d0b40c152062500400c2046074400e2180c5681e03035161100d40107840620000c01a40c9040d28000c0c2c00300c0c500e0102684103e1a03a9000213040405010324040c42c0f03009403445503c039902490540c0907200500303520b0311540d0248121000340480e0f104052903001401c00501020036600f0a0108540041c0c11084490b000f460030400758681040400c800c4544003c21a142c90301c50700c071a01c8007409655030403010035400207011591 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 624782787 1250 624781537 624781561
    0x170a060c0f0c1403210133080a090803070905090a0903021b030f0a05060103031d010c020f0609280e09061303020304090911100503130b1005060f070b06010c0f02100c060203 76
    0x10307175442032100601d00700090701c2c3c001b04051038001d20403004054800928001c2c85230300c40e00c0e0401d03030501002c1820000d1399545611a002152410000750000780100454a02819541c0c1c02a070420b0041048401c6030720001d443c0c0500c00c030b401c8080350361040a4080ca45082000708110801c09059031688c085600c0d10540702c1c9020320050700014007007035141c44021041010706840400503103541c1e5004640e5801d211102d0003140007241c3c454002e0041c10841c3c0c4402c803019201d030b0320040c1846c0c959072100400e07141d04070140d0003454a00d541c440411402e602c00155032038200242c1040130b0820012881c0032891481075401c5052283d0a03d8150420090003840070000703440101c4142c424152002400c88842c0400c4500e04035010240316610082001140c0098001c4a489524001c190b19100400c0e02c40c0e0065007604140000082c004040c40507184075030360840400d00e82048030000e542c9070344418030108000a1300c10351a41400c0c1026600070052420260b6110b40c05540b203140c0783ca04421 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 624784037 1250 624782787 624782789
    0xe091f0b06370f0e01180e061504080a020306130302061b04080706050a021b0307060c060228090611120315030a120905090408040b0f04170a060c0f0c14032101 70
    0x854114040c00d482503000710b01c009000300b103181d06c408000786007054002845001401b1650000c000191035040e00d103151000303102030326042004041e800100c0c81458a0321000604070000c9440c40072a2000217a80800c50542100d003418262006030041d48103d030482c491039010310064441c0000c00148540c020018080c685449e400342c0e00500005074450b0700ea00303c0c021509a043d04003000030f00155008400a03a01ca500980006041980360841c03800c0743c0100585404446003400310310081035038400a088081c0081e8500716071100c0b1007080c62503643c6540c0608520054002c0300040c05000f0344801881d501d800101200c4207801a410060036504801c130484d4000380c0100008a001c0c181404018001d0341d00840452900389010030f5894540c100076011454480200b100091940400880c5101c030083c00000c0c0904030206d240c050221400745950b0814400410b8864021a4001c2c260a03003544d000f00e1480d0b52083d40000c003034214401c035205030495903102c40d0049091164415524 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 624785287 1250 624784037 624784067
    0x1101110d030506132d0b091014060f16031205040b0a0e010e0c04020d061d010f06140a0e0a050310091502160f020303040e091f0b0637 59
    0x2111392150040d10100341c0d01d03541908140c0c420265001441c01101a150602c8000d41c14400036511040c900020b80c038120a454040d40f113407000030140045481089841c00300c1a0032281145880c80030310815105000741080000840001e48409060600a20922200c0040c0c56800c100600d00352900c201544000c0d5412400d0700d15000e09003200000511460300110031031001060300c20300302800c1101a62024007002d000da43c80380c1d000617201d0f44880d0301441008505100203015170600c1a0308864001c254899001c014006120200030719544041701c0d02d83e01189042041001d0040106002031000e41c002601841400c1e24207103400d11951003110072902c02d481c1e4144852200094405a000b0480200342001d03a540c1e8043c005015030005411282c8080d00344d0b81095031350420440220307000c841141040e00714018103042540c001c8036002030804402010804000c502000c12080c3c000c01c04c0c00e00304480e10480e141400785050b40c03400070440b08415104403007208201d000b400003403264540 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 624786537 1250 624785287 624785299
    0x3080f090105132a060f120606050406051602150a020c030703020102060705030703060e1003152702030c10030b0a1a250c03050f07060507050303041101110d030506 72
    0x1003240140d040c09558000c0c1e240c48a52400b480e0280c07984030300c0003210345183d11340d5410301c0150440403034040fa0b500024920307501d0701c0401140d07490000c3e21a20300d001317000d200240381c8542401071a0304501582c080d41c1040ca0041e46901640d20510707540c00d0a820041d600883c100029114225080002e20760350b0801da081c2c500340d1081006140d0b40308c0719070000070b0158103d0380002d80150320440140da8000c0a5140116049558000d1001502011303560103440c0003410406000b8046803844400b00014050410050f4054a03042862480b0040e801016200720700000c0409540d0100181c440100780180410701c000f030494400340c010b083c8401882c2c0620700e0301c2c0c00010070b00e1000d501c1c580c07911161020b41386803180d0840c24101d00d905c0e0740104040d040301400c0c4000420403600c0040041d504c50001825140e2102a4072442c08401e54032450401070b08114003800601c0100a0300c0e0003542c042103d03040803803c1ca00603100c41c1151020342d1704c0ca01c07070385551308040c961640216000b00e03030507101d07 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 624787787 1250 624786537 624786541
    0x13050612010b0612040218010f03030906050c06190209091005090c0a052203051006080601050d080706053c24010f120608060a06051c0807030e04020703080f 69
    0x15841c02d80340314016039a0f0094060040c80211404105101d03440380c4004e0012050041810b4000d041e01000c1e00596840113407444103104240c0c201e80024044c1000d13052060500c1244980240d075820020715200c0014000e080a42900c513858041c0c1e501c424000300103c1d503500d444090200c1c800020b1041920605020021510030301d032880481324000c20380d035100307803900c1d410101d8004d40c24080ba0000b60031f180004da001012070b2090128401c41440441c01140c0c140c82c1c000c0d030314501035041e0016841a100000440001f50101d021952026440840865269102e4103240302c00300c24001425a090302005821031940d805100c0103502100101c500401d0b51248000e001500d6200c0c074a079022502030400520b074070b40c050714060b40007070407501d4140c1c40090841004010303220300740d00860300d0b07600c50030503c0902e041a004400c084e1000b611101c00d00010030303075640304544039184c018044010003e284e1003071501c0756070040d03185000900250340c1c1b01c1491400401024040340e00000e25881540 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 624789037 1250 624787787 624787819
    0x1506080606040e091603050321090307150e0a0c0815060105040e1504021605060c2d04082b030e0705010e01050c01061203271202040209130506 63
    0x2800e0040d08080d0036542071504001d0555218a030103060541e031441001c48004165415902c0e8a014611a04c05191185101428003504c00e559121000e00307507164004000e50044000141e850160f00320160400c4500c008080c03400915180701503102c280100b210b140c0c1840301022014044400c20022a40100c554070403080d035006041d80c041e800183d080100f00500c1c80049101604000e408614240d0402d0601c0058200d80c0301c000c11383c0882c102c28180c0402c2c02004c0c41050b07482221b5a500a00d44142c01204c94104207aa03e10010743c49290b0070760074038607080d51098174040e03c9854201e50079880031390445021181c40c0b220107014221401c8908d0780030b070720034080d414070708500c003000304403482c01c100055800303a1800da911810001e041c044a00100d001340215030041002c04845200b088003170034000e242c01c041100d049122800310b103983c2c00b016040e0400d207007103445c2c1541c7c180c0c3d4194103200050291084500075a48240c0009405000008a0f4081401140100c0784207814068443c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 624790287 1250 624789037 624789047
    0x9060601080109021803070303090f0b040e0601110a12080a0b0f0a0612270b070507050a02010e0105040905041101080106031e0b1207240504050918010e030d1506 71
    0x984140c00107950301c00400c258005034020780114003544101c0d005036201c10021070300d0034103183e10a9000402600c0208044901e11001c0c1c0090000c24110030300e00f81c20b000112440c3c410103441c03a4104100c040c1c007001d1022041c41840819036005d12501902401d90000511000c002d0301d00503640d0b45050051405450424007102e0b5400c1c2c003030b044029552a214090b5080f40315954045910382d11221035128415500501d10000500c080c5859903516150410004941c1d0082694061150070040d0001140000880362215a0309180060b85d644049d030040b180d50099a000350111400c0100344020040c951b1510145940280e0307401c1d40f6681d031403404600382ea8501030780e183c0c008404c148091030360000c0c0e001110915006010403005410b406040703032407c80309612180f0390390201803a50601001d042202c000f1941070380303021401c041c00c0c00c2c000b490746840a041022845501c103010480000c003134115454400001c1c007a240c5500311b900c8000d0162985800511128132080d4010079014090 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 624791537 1250 624790287 624790291
    0x3150e060702030c060601031416020c060d0212100e01120c180c2a0b060f03070e01080d030908180112020d0c0206091b100201180303020d05060904110103180c03030e03060906 77
    0x88070541275541c50b401469000441034001160450055000d462682d441d41ca00500308812490001643ca4410500024030301d1000392800340d864080101c04c201221101d40b245056500300e20703c90100711143e01c1c1081c681c034940d5001c41c0c001d00c20300e01c00411382e07042903101041c000392503102c100b5004d601c1140f10320381c04900c8108034003001c01e001c2250007041c18450b20943c089006003001c0406114080020700d0300c540750380001d103410782010040c04004810b010200011221741424000e0309055901c0d40828000c428103503020801c010542203540c0e00c03c0403040d1823481c0207034085503140c440381c20000c06002e1220700342000d0b00c141e6000c9150100c0c0001d01e81320000e401d030401d00100240c40204045140c54550034011592100201c0a140c0b00d0910b00e402200d11940700142da5a034001c480d00183d680017001c0d9481401c4103010000071070400c0e841c4205070242446d000410541090500d0900c0035040c5010704060a48a07001c405c05030000844154014124101d543d90354403240510340d181781c1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 624792787 1250 624791537 624791561
    0x610051c0203251e08150603121821010c170f06120f07061209030e15160f031b03170402150c0c0a05061303150e060702030c06060103 59
    0x852210003420444001410720818080030305411940d03901c4007007180c01400130f400d010b200c00d10910300704030240301001080035031600100b888a042c40c6c01000030351036840d0750301c6100300c2d41c00018007103d50740441c8801d00f0041800900d02103180c9000101c0d00880302c119110016550b00e040500307000d00e401010201d0400d640c481400116644a05c841c0000300c01c00703017945801849030384070344881007418840c0b500752a56581c020400a441c02c00002e0429001000c00c402851800305840302080e4481d080c17080b4840e00381d0701d1186541c00102c000d48140b160700c0d590800c1e820f0120129081000c100780c000c1d40c1c2070099990006010a003e00c080c90400c2d00b0038010041005045407c0c0c429400710030707490340140000c1041400480d10090f01459500841c004541a0811041e034404c41c540300095002420061710420700f890038614001e00d044607540006050b10741c02e036601c070a04403410b030007241c2c04003109000d9403078506204001070340d65000100c40c01400d000b220002040b55100703108400704205c1c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 624794037 1250 624792787 624792793
    0x70e060c0a050f0712020411160605060f0a0501080f06130c020a0c050a0806040605090a0b040b160305070212030901090606060504090e03120c0d0f050c0702090901110a1b050610051c0203 82
    0x5d01ea40c200002031030040a04d0001c81d0081c80852400d0503c400d0421202e4000d401c081240e19001c4100211894501c84542c81000d030f1540c103101d00e9178401c0200b07a0003454801c00e00d8103901c84d207001400c4944e20541d0701050314109406084099808100061900d200c0c00c842c03c02d55899408016078039015001d18181c0340d20250024010074515040590058949003d031680c2c8074080d1515003140074101c50a0780e0f00c04165040c040e81140038002680c0050707135880c0401c02070600c3c5030000d4480d8401c43d001504c0d2030300840815655102984107030034195020000304801ca98500002e00710307800c1313882450788607454410407500704070020045a90800081e121602d290b038604280491720382191000b94a410768400840083d90450b200d414094100c68061507250754551040060111004240c5006c6904011001c240c0d4403010040c1e8400700c0b240c0c1031052003120000e220540d04c00401002500a00c60541402420040000d40c0f40945a0540e034003e810030400041002d501030506c0000d4140d4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 624795287 1250 624794037 624794069
    0x50702030a050a26090f0c030601270e07180603050a06020d021c02190207150c02010212041e080d0f0e0f18071715010305070e060c0a050f07 62
    0x1d44904002d1920071203500f00340c0384450501034585200101c81c4040e0440086200030b001c8040070400c041c05035008440001c1c00c082d00d03004080f03919980188203080e1034081d0300c02c50351895807002c0101c2c0f185024a034410050030380060441945d408140c442d8205400040d02c5625424105000304000d407a00040107240e50101d40d541d10009510819170369050503400c0c40064211640141c1410344c1602d0840050b8494030f86048600c05141c2210075007040d9408494100464a04019020f82d04070715401d01c291142660f00060b42406100741c00b40c81201400034000c11882040f80b0b118526201890b80c0c4021251103c14407075641d4040e40700200424054115002c640744224040303a00c4070405010449100864000300782081c0b20320741c103a5400d01d03040d000c02141c10f6208404190003030649560000d54204108640324005240511904143e00e80c00019040c41c02205117150500018005030b030303202c00380103010303446640c030741c004590f540658010205191390018505069440c0c10389284010 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 624796537 1250 624795287 624795307
    0x111201060e030d050a0f030e010207051501061805060a0302070203070905010612020406020303061201060f1d0f071b06020405090103030203070218070e0d050111040f0311010305040b040201030c0e19140405070203 93
    0x70b9a100d8111030400d900c6081140b0040230a002030104644690001e0101c030200f140340c4003030140140c00641c1000241c0002c580c240f207030001e583d0200c0d0415501256142e080030011800f030b2240e0f0402039014800c01ca80040c4008040e400f0038101c44481d82d40041000d09044c40000f41e00c80c51091400590090001c90761a1401411240c050304d1b0103800050101d5540d00341e000e1501d800d0748035242040358007207101c046008003d81641d00415000d83c1021520f0f1405028104103d0b400c0c082c10034819007a031a0042000075412a0040c15000b0301014641d030356403400940d25403048400301d00904500341c01000301c900c000f071080e000c1c3c18981c80741000360300c2c000d007800001040b103001607a03503648424601c0801020000104003901010400a00b03581c2542010307040c61407140301080c101850f110400010401100007550416030911300402e6902e24918121421500d900301198000c0c040d04803103103040c2c1d9001c10041124049564510142410030411084070811191203000d604104000a14 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 624797787 1250 624796537 624796547
    0x7091509061a070222051618060c08070f0b1503012405061c020c03090307080619020306030c09070f02010c030e03040b03041a01060e040b030d09051003111201060e030d050a 76
    0x4140d0360000e0404204041c40741742e0151001920240c1c1084010110310f12610f602c140400300911608039a201d02a1420380000c1c01c2e008000b4010f00701c00e00200c1d84108011261400001032500902c0e05600750030706d011183c00d102900d0f2200c520a40c84e00c014040b1100b2002c00c010b020581c00355900301140d1800c000c2c80010780c4950103001004030016110607203060103101130030009040030000c503100c481030750506240c01d1990300041240d81c00311003000700f40c10280c07501a0354140ca403103000da01ea0b1030320300110785059800c0c1d020b1903000b4042c07400c100c50980e0040362002c0c06651030b4000d11001400c14000d40498840348040c0c000c0b82c00400c010f100d203032b012030019500144034074004c01c1a0450b0260f030059005c001c0c0c00002c001000c5000f42492403415000302c40700804120702918000184000150148030607205d030354082c00e04a903001c556240690300840542d0700c0c03160496503c907004803200003000800d02554011680401000c00c0340d040c0054118104401070b21903c0c50704204480a5407 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 624799037 1250 624797787 624797809
    0x9060906041e09020a06110c0114070209090d0e1519051605030324030a120207080d20060720190f0308010602160e060307091509061a0702 61
    0x9042078039401074034a42c0e086440811201148000000f5000304a4810010080c0580d4051800c0140d146250546503801090761100c2c01001d08001d40c03121802c034101c0380540103034071010f94455003190404c0190400414001050005981d8020140c11070f8802c00c03140041600403034202e0078040c4088610701002040c442104d18403410f04905260b41010075100c40085140d00300c070560404401e00a420008401d00940c10030111119941d4601d9103022035980c0c41c00c001e01424000318a00480d500500034003541e40035128501c2074410340c410912000d41105109e5010141f2000600348613030841c517011850b103001d2421a90f60300e031b80440030311600165032103e6128016500480042d0310444100062142000c5c1c0b08101c004136920083c1130203400102e05070721040564001d0100b212290f0b040d0078411042c1c46060300e02d0b0701c0d16158003012901d00603250708503403c203d25200400c0303c1200b508082d50700b2150204d034184242a1104071106802c8001d4a405e4070030340c81448280010700d00914020 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 624800287 1250 624799037 624799039
    0x30b06040204080a121107050f0118031403130504060b0304021908060f0f2a07060e06041a090307081e0d1b0f090f0b16080415030c0305040209060906 66
    0x58181600c07010142d0600050307100842e44c07400030540083e45c40380c00441c00351100e520000540302481c42d020214840d850340b014054104500307040503400c20591280030f0806540c101070341c03820600c109070300169203501041c4100700c010a07100c4005400d140c18003444c400d5900400e620780c1162205d50074032074040c080f04020801078003803882c041042c600030041a40b196607540038001041c140356000700914080a44040900007603400034441c0800b200f60482d0746600c6800c90b29640d03401c1810858000c1510340f2024146000b03150601c000d010b030708524801c070036000c0740020300307141c603005002983ca11271200c0052104d002400600c0441c4050b8648120302080840c0440c500102469030000303c5002c1b0150402d42001480d296555030340c4090b068071590064205444041d0516108080040d52449002d01d85480041c2205858150700f54100529a0100400d41c40740e440710800142e020008038a480040d24040c00504581e100e402054011a000307407036104180c132030500340019190010101 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 624801537 1250 624800287 624800291
    0x50915070215100914041a1f033e0105090d080703080406050903040302300d03050a050c030705090d02010e15030414030906160c0302060301090203070f18030b0604 72
    0x1a00c400c07000700e00349030f2045070300c90101000241807421442c11202d500c0080e0168061510800001411411a03080940882602101c00b0380c0d41c400400d40640b0081140f2013104400500003042020034202d061001c00e40f01c01050b00e40e9003038841c1e2600c40c482d2108500344c810a2840c80705ca154002c00043c0302e40b400140c4580c0b0b40e8100782e255040c2c250701220b01140042d402d0000c0009101e102d01c903146d04069080050351030185103800081c10a0020faa0a5290940c81004009e030035861403103c0c0b4400e600300007611143c14020380064024002103030030002d0b00741400001610304804030200e070310940072512200d08250642c002d000c049100e00c50300303d051003c1e02041b031445949012083c2050310009010395aa450a4504902d001e0006003080703419a000b0b2015110b55541c0c80c00384d45803510481c0303540040049504240005d40c0b603561010f50408000400400e9078003060300118411007243d10b4030b0b030010036403840445001040324003130b1803006990035050000421959203150012802040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 624802787 1250 624801537 624801553
    0x62a2a1c0c2f040f050127090b01031a01090501050d080a09080616140906090d08070204050406090519020a1a04050402160512030907061101091401060f05040509150702 74
    0x280c0c2032540da4400c031502d42989500b011580d10306030051082003010004140301c1c03540340ca0442c0c0300c80217858903060158040d01c118040000c035140e0255032101e822013180d401d0b5507900d00308030f900120101248283c0b001c1036030011500c0481801214101c503809050000001d4943d04c070094540c000702d1400040144000e0b0004007810100001c81c05003603019110041300d1540f41014012420b85046544a003c050044442d02d568a00c181e8031030f01da06403100302c01d907003440ca01035086100d00341000f54007514281c03d200a01aa9504c81b00c0d1140c80341e8210b50500c54140d10b030412071010194020341c42848420f09000340b202410700c0d146c136001c10001003810a61a200082d06a8104100b440703480d00441d658001401003c01075400b12007040d214061450804207170580d216070b21341c040c2030103000b446c0f0325803ca0421f0135484101280d030880c05012902002040c1d40707000c0d00e80c17407140d10240c180d07131080414507141600c00e150050500c48000e2080307007044040d80c00140401080041503010702d0310 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 624804037 1250 624802787 624802823
    0xc07051207060b091501020d020c280807030c031a0f0a0b040b1c0624030b06060d09060b100e18041403030708060a09020903062a2a1c0c 60
    0x480c1c41c040c5041c90181d40241006170002032802e180c0c54125070455101e01c07483c4402d034403032038403080544201d8168400280403401451040039140d078407540c0b0a12440d0400000d000e215000c071010b0f02c2c41442a0a00040b491807003c12191064485c861201c41c0c0078003250b0410b501c1c3e40314460500c005440070231000d1110000803d4085083c0c3c04102c2c40140c2070f0010304000c1039105039000e00b601c40340708410b40d58003901c070000b43c8000c5000040c920540100840c0c1980d4880b01656070760949484180a1400e030340c508030025040c402441c502603103014036030f440c0460107070b0124480440302030410410314100c0751200d400c51502030015222100e08058a107102a82031006610400b05610340e1115414404141700041c0d80035400001d110b031040c44050190b503008114550410702004928240c010300308115040049080d02207500d00303500042a120020b039003581d40c9007588007910300a0004101186054582c03c6517440010310b08044030701c400b00180240000c490141c0540079503001641415 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 624805287 1250 624804037 624804049
    0x5090a1a0a180b0d0f030309050c040507030902010801090209060f0711041d06060d030c060b0102010b04020a02010f0f05040c060c080904020d0615020a03050f18031902090c07051207060b 82
    0x90050350b803140510a10b140c1c1c022a600070305007500020b90380000d044500d6110900044082e0302e00038105500c0f141ca02080c0001000005408074005004026500701120b02030010031808600702c1c080385110340001038044440c42074401c2c000d0081c107680e28061441a003105036170311402003100c0c203c00359101ca031225246d5100303100ca105032410b500854034020300d03882454800003d00561042400781800340000303a0046c009407003150320900200d140304441c0d0041c0d02400c2e01c549001d401500c0400d07001205541504030803400907840004101b5040480e0b41142a81c5044030060140d0b22146420000301c0d2045064400050040348124204480300c1c0004042ea0700c40d00d102071980d6290070040c00051007019000640c1926400181584030781e0f6a00038040d4040d00c0001d01e04040042040e0001080701c2450704e18518005054414224940444101c03040c0d5a00099005205d4400000e1039004030768102d44509030400000c0140740c0380400c1c4001e10382e00c6100101c4e130b825100d4848034030fa45c48203 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 624806537 1250 624805287 624805289
    0x4152a0507050a081b0705060d020a031407120f0902061206060409060b031501020a0c141512090f0721032c15120c0a0504081911010905090a1a0a 64
    0x140700c82c20345c2c0c0c96808406032800c00d00784d2038400f6282c000c51020030880c2d5030341c0202c0d0903402e4500d80c056210654000141d008102443d102041e014207002040320740b651100c083d070940d44042404000550b40365040100f01d401c0064002d400c95401c104040c00340700d4140b501580044014002c0d8541a22003241c81c0964134540e2150410700f1012040c020600c0038460151000b040a01c01402d20b650703ea03d4407400102c0790722486001c1d2001443c850001c0d242c08003104c240b100c080d40070598a0740d804914a5035140212403892031030003007006c8510100d4010a9100860700c2c004004401c01c01100c0e1202e0100c0c1781c0705400ca05100c9130b180c98000d126083c1c2c06290036205042055100e078120302041c043c40100e80e441205422400304119a03209800001c01a0001d00c0e2a00721901c0706e81b95081520284125080000c0612881c2c0002607038042c0140d210400620030b04001001603035000042d1010960340c0102540041e840f00010b44200103a440000200e152003440d02850f0b603944040754803d92a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 624807787 1250 624806537 624806543
    0x302210d05040608070c02090f04080d0905030705010501140108010303030b040f0603032f030f0c01090503071b0b0708030a09020a090204350d110a12050304152a0507050a 75
    0xb103400c000399600700c80c02c039901c01c119040140200e0f04035400214150b90003820000341130550004030381802100c41c10340700d03003002c042010041e02495083c000c0d925040007100311541d43c00e03c0700114000b082c000704001080e4041c3c5841080fa42141d900368040e0100149a581041e81c40c0c407201501d1039036000b001c00441c041e440d003583e0201d10301c80d1a00c8445140c412405041ca95904070780301d00b08000225405d100d00582c600340c55940388400a4050701501c40b004e0b00601c00440c4842c18800c1c0e940004010f40c030708040456006a40742003800241c003d030035020345900ca0034000981141d915800454075940f0033000b07001e146450b10700c90000c03a0810b0b0800c0c0c8480b100500d0080320171690980d001e02c0710b80c0c08607405d5443d1031200c9415580e18084211241000045240501008410030148007015801151007424040034580242140c2003218103035044030210461103450311851080c02c01864201814420301d05200d061a0585030204c0f01c841c080000c10450000851418072038142007505c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 624809037 1250 624807787 624807797
    0x210d14010603060303300c020a0c030605071704031d030c03060106080709051e04020f04080d08071710050609030f0709150f0b09090c16060c0801120c0302210d 70
    0x10071405d00804c10058840d0511801041003260312262180c1d203000c254a980080c00483e0002101c5022030134440e203051f00904c02ca51441000c01004803603000309115081c0360350341c0404c003292120040542d0f80d0039030f009000f0646004411092100141c135400e140303a03000e4110382843c124000400c0ca080030907880900040d061f241030150b04c90780040142c00a0404444003203039603680b103d418480d0f14142c000c213403180d94002015040102c0b0001503400811180059840044c60004050107415040f41d4203000248980c0006224903451200700d40140c50040c0e040800728104820311500340e220250603941803040ea8070b01da40c280b80400910f0b003e85510080801d840b040d8020141c0c0316000c0d0b4200034440348460030305008101c1c600007907820414049448040586408071400f01d14070401340b90619420401e440720040c07002941180c60203481d035558001d000ea98540b4542c400a0300441c000741407404c280d60803c054a400c402d15034201900b00113000030038000420051501c03203810b540001040c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 624810287 1250 624809037 624809039
    0x80c220b03070228051b041b0201050a0c051c0c02100c0207030507060302030108060f0402010c060e030304020f04021306031d010c1808030a1b141617210d1401060306 73
    0x4403003560f002c8072031400d52003035104030015a5070311b84a801c1c2c803481001c100983e0403800520764441d0010500b0150148903030610300017142c00240a0242211108184c40c00e00990300c100900c140220b44406510f03160b5103110000a40d203401c0a000c100c00b0185c01c40c415410403c140309100d205181088000b900205a118a18600541045901e500030002e140c0b060004001e45070000c50280d51100e0300c2d510382c1c07038030b0358940c0b006907030002003014046c003107614092500b068100004001d50180d402141d12000f1103001c1c50400041c0c0c403130f10301c007400407441c018010419503001e44c01130b442e40032170603907503000806041d2402d07401c481d06141d410f0b0004450401c003210040f501d00154001e80a81c401175442c0200681c1c000d00900169800095411400c80003003040c010307030721b02d030101301c04900007034800020400300f00d03910000207400f8060300140f03d410b9100204400184001d16100b854810540304d581c091030054050300801a00d85586440e0888841641d510f03200040c007078400341d10002986 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 624811537 1250 624810287 624810313
    0x20901080105030303090a0f0311010f0b0108370b0d050a12020c0a030b1807081621060203091005040812070c03080402060c0106090908040510080c220b030702 70
    0x89403040c0d01c454040d41041040c46248140070818444542d0042a03c0d03841c032000d0318003150450700310501100305520300b0b226108850040e42282071504001d0b640c0007d161502603842607a905134116a441c1100c0d84200b00c1c40400c05550340804016485000049103035807503022900c0e0303494500e4219041e0b00b0801080c0c1c104074420000d0b8410707120703c4c8001c01c10b0360741c6074002c21100411404041c102b03180c07000003e8040784a006d81e8002d0303c0e100e00705543c7c4040c0d8420050b903030717900341c4411551104941100410300b0070b060a002000389482e4003035200d18442c01d441d0701000307506c0644510f00314010341d000904008000d0240501451042c0344080d40c41d1903840c1a481009030143c048001c2045000140001c207501c199059005901201d10325503404099506a00500c819413003102010304022410080c0417029014004841081c1d609002203001e5482c110f600303090450302207041d0481400155901007922141d400c4141c1400c2d004c00342075441700200322a580040701c000c00141d001d01100616 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 624812787 1250 624811537 624811547
    0x1306090f0e07140d020705070602060a141506040b03070c0312051509070e1809010c0509060f071a01090b19060c0b06150708041a070305120a110409020901 68
    0x180380240351400030604045245400318409041401004802c0c400c104412060804a800ca801d46000841d907541d00342c80c00d103481c3c00040c4180400b40c0211000155044003134000e100d070000d40c008454440c0d0f55080054480c1e203505402c01074205006100100b069940c000c0258054034203a00d9000d80c8958a20340184195020002e0700c40080c01d003002d1000d0201900c070346404404040318170090ba41d0381c43d8030482e400b00030020311560003002002c0b2251200e015501c084e0007211080000d01102d01400e1042da40c1d4410081000c1d0041003c00130710151490840142c0702e03191081c0c0140002c074000d07490942c9003110030317045000e50b140d560054074010303e03041c81d0b41100307a0004800800c000385000c401030000000c502d400b804d08610704000510a50b5650741c02005450310007100d90700c4965a00b0415007640083c090030501e8100450000c03000c0071712105070740c1034603816030701c00c0c2c41c00a80b900c0c01d151825010700640703031103611040b03c0f44c80c503071109004d4405017021000043e250740c04e0000041c5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 624814037 1250 624812787 624812789
    0x9060c15090528020627030d0302070203010b04141612020a0f0e0411090111070801140f10050607060e010227040b1e0d030903150c0305010b0c0d110304030602130609 73
    0x524448098a420f0050312040305842c2c2a01c800b1165003450303118200858949002c0c41d89040d450300030b0b5628044550380640c080c00301c050080e0000c2140004000c188800c0358000d0300500d10004801001075810805400c031160031446d1450103100e05400c00000f101641c0060b2090004103504949036250103502c07684078544440d080350306001c14084583c080d9001d108004841e41004403e000e58910b0781da0820900c2c0003001900d0007000881c40d0301594020080c1d05444590400e0050000300748140150944481640c000410545c644a819502c11008220340c0211044554081c440c3c0e40d410792401c01c000c005145400c07418207080007500c0400c4100d41c09003800c588100b808007100340d4011000030b00502209020390300c0c3c50003d007082c101519041910340c0f000308000008549840168001e4001482000080d2801d020b5a40c0b1a40b51b4810b6000d0815503020320b90006d0040706030f0f24464071b18810201d00e080c054a180035200d071141406d0364803580368102c003010f0980c001c00c0b0b450740c0010014 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 624815287 1250 624814037 624814093
    0x30a050f0c031e0702120403051506150a0813120e03010e0d200102040e010f0509101512150902120a0608030f090415080a02030606090709060c150905 66
    0xa145190081810b1028038480307003001003e007000d0000840c801d0003002070b50210f280d1980c250741c40b107990349009a9031b441221544611003030200c011950340d040002404805030304581c81d1506201c01d0391402c50308000000c24100c0201c0e4600c0d5000c2c04122190a22030200d10345036a1400540d003d1410706003511064164140720750f100c90484860f25030303c1780750114500c01d40c003920040e00c90b0b1103204501a0040760819501c00041c48000240c4084412003403040322016248016aa922074a0481070705140303116040168007a11081507116100d682d4401e40d6402007640041d02403050b500018850b9020b800c04e9090710390018140460310b07090703103107150300c094a10010310146017800700044d141d00449900081c0d962010518554680e21074011408481498400c01c000c107685103002996144410380c180d0082c004e060105555003031000c5190721500b003030f13142c2c000f0071481c00808960f010003140058802580409030092542074501560450601460013001c21594840342c403402148425010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 624816537 1250 624815287 624815311
    0xe0d08070905010e06071a0417030103080901180308180f03010b031510150c0308090a11130b10030207020901080712110f040606180e0f01030f031202030a050f 70
    0x14590054828090312820701e00b43c16584480c0f004114a40940d04000b09508402c0141f11454010018018846c40c0a031503140340d040700c00400c1011034442804080e1000004101c46415940101c90901030030000d0440900700307642e2074860714019040002c06501e061200c440c1c0503410314101611600e900030440c020040055400002642e0320841040030700360b070040d42c0010744d1081d02c6502d0a001007025001a6500c030040050013407900da0740c1d1500310041860740004c65008500090324400141c0d021030b01c0d032105aa10390810107052408026400f040e521131850600588489602640c80503d545015843d0b8203d44108040000160406a05035126001c104042c0c42c3c03241c44414025000314076001c0458804000c07a09000300c1102158125040520003c0e01076444407101000c00e14001c090384241e5264820304c0c28055050b02c440440c602144010b00128025510f043c182e01e10a08011742d07140c581c0300118060341c0040342c6420400359180104070040c4a00510342d640b000912481c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 624817787 1250 624816537 624816541
    0x2a0b030f01091e0e031e12190f1109040e06040f020f0d14160510020c1504030b01170615030a0b04080c0109201008010324050a0e0d08 59
    0x340020181445905100d688549488026042c2c0d4000d800e41d022000c00c00748030214900350a030341e07681c0c01503460200e20200801e40d40340100000094892003418003a03550a141c03541002c040c1c0c2c2c110b450000c40600c07036440410008514541c03144140c003155000115403100e0860080004450800c1001070303194110004020010300302001c0782241c15811280304511400410108007400d00101e001403030410120005001030100240000620404d010790728905900c50051140d4a8040120500943e01840307107034605e8a4100130b110545512028038030304141d0390f07480710300600d5820303070114011142c0c001c00ea048000080c0189a0b00c0b50840c0c00640010f4200004290394440014000c1c003e2039444000c0360401c4201c4084826100105000784a50b014504103481d44610300307050b0080c807010543c08070149040a165542d01c4080ca0303266040e145c9c5c61500d035016107806003003908107041c0d00c2d0720510b21286200d2007030314080ea0510754001400c4080b003e03602d00d0022403060f01b00c180701030402 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 624819037 1250 624817787 624817801
    0x3020f010206040b13050c060a031406040c050904270c06021917090a0810061e15050c01060308120105011b0506060105160b01060807090f0605040608090a2a0b03 71
    0x100d4001000c0991760485202c6800c020303051030442c981c2503501000c00104641041c1e85508405101070280c0d481080c2a100c00040200b01c5099030512000f149091050301070034900355000ca9030b0742c455614220008510320f10b161124130340041c4101c4500c50060303002d2188135410082c82c1c01c22640e200c1d40c4020005a5100c180c042c2105440c00c5040744800542400c3e640c0750342040c0c07001086140304440850240d214494090300c1b483c002c05034001d07400041009651007880f403590171200024031620803095210812101035014451034901903403503010000001d4103100042c5a0f003808a401c11000754180800104805101c41042003641e03103c05001c0e0105e000490442e80150003420f00035a903101c0c00000c900c003141c000f0805412010710000001e0695002460203104045903038508200c40d441c0d00f02c0f0390380308505005210008906010a2107405d000d020301c590056501d80407651402c145a542e1010381007654440151050003112060b10300808444220180440c10482400e5280140c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 624820143 1106 624819037 624819053
    0x50a0501080f0312271911061905030a180818060c06010e06062b05091b151312111f0c0c1d0103020f01020604 49
    0x10b420321215001c0401225003400003050a0389803030b1074805030b00342c4108201141421107000c5140ca0201200104066481002d13414654402c40c070a51405000c180e40c0b4042e158043c10061203d18000da00900070001200c2c8a86806522513071500305541c090990715051007180301102085405011120000344690041c1e2410103c074891860103101092140f41030380401a004040140500c0b1a00841c0c140c01250060405080400c0d180a40d20107004a4111160000000003004040400d5008017035100301c0c68400f030308000301c3c54038922040d0401c4142c00c0d84900703003000d40c51840e004500140c400303041290030810b0002c0c2e124600c0c032900d00e0240c102622900d00d002070044440c90013080250405141ea420320500800c40341d8181c403032201108040f0b50300b481e14400420203042e2224045440344400349a2261545140184285104844084d0341150415020040411480 = true := by decide +kernel

theorem cover : BRFrame.Cov 624640287 624820143 := by
  have h0 := BRFrame.cov_init 624640287
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624640287 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 624640287 ≤ n) (h2 : n < 624820143) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
