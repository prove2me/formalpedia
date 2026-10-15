-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5493
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:02:22.165977+00:00
-- url     : https://prove2.me/submissions/e6b00745-9126-4d3f-a59f-dbe39b220abb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 987769784 ≤ n < 987949640 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 987771034 1250 987769784 987769807
    0x5010e13050f10020705010c110a03030c0e090f1605250c0306060b120912190908060910050903090906011218120210050115180807080f1203010605 65
    0x3400218850030807198140300d4002c8107030a0400315000034410a8002c100348013000b400703000c0c185140e2030515002c0102c0390300c0701e000340c1e661990881c0a814150f4910034294220310900454000300710150900806003840e1451a41c80e200488000014400000e54a081070703124a00710340814030754620952105001e8011000d844c1d900140403142049184c80010005400313000c1d1000404282c0c0b0300307a4a40701c03045000101e15000420034420b980100300c10b040c4601e00801540c5611240e0307140c150140311045c0b81903d1146468201984a10a174000c20801680c000b502040400e0090707400e008544424844c596280128840c203039000c1c00110001c2c406501c501c031210403030b01d12001c000c259010f07015402e00d140b1038030280c00e82e00c0c000c1411800c540c55404008a50f0b05883e040030400c0103603d8072850b001c11a4899001a0130410150340701c2c5442ca2880b002c20f4090500c400a40341000e60305d070b04550381c4800f004445405400b840c0807141d03000341400d060f24101c84207a01c07900c3c5068101c8a4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 987772284 1250 987771034 987771061
    0x130608071b0827040c020d11030306060412150f06060e090f16020316050705040606110c120f01021909050d110d03030207080a09210f060c1b030203041805010e 70
    0x60022885004101102e0f981e60b0f03d004440d45030086030040c10612200c10001131180c0f01d01020078403103902c10424052551190411a42103038040f0312002044006450900b200c0c040c840c0c2d100d02d819040400014a000807079101000311040740d29280c403c2070100c000d00640315401c031484003491905100140d588142000c01c80304000c2c407071040e6487c0c100c200e130403407900907840f00302603074550701c0b41506001c542807500c580c6006e0021402e10341d131040c42d40d0350782031f5139401413007800717405480c6445104c0a0031a00b04142c034020032560f0029500c0c1d81d9551000100502011f11860000300320580014450416000ba018a5508088008120000201400414000980202c0030190308002c65808240e0241c06032010f900f941d86c820707a004d0714169810303100009140c2c0d0980c1e0f05503081860320006001c1100b01382040d520040204d4007080700901610402c50101c030750102c10a0b5000c0300420903074080018429689941045000ea07100032801070210340b001d0280340d05209480010401c013580c80d04 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 987773534 1250 987772284 987772327
    0x1e0c0703020f0d0801030b0a05040f03030b240306040c26100e011409251209050f030c060f040c0e060328060b10020303041403130608071b08 62
    0x403108440b0442180901d480c10349840900058640001442000148081c803504018400303020310003401c0c0794582c02c01d24441504c00505042d5100010301207030321060403500102801208910100300d5007851074a8952007150124480c1d40b1b842c071400211401342c034030410721950f40900800310104145210103503640c00f03850280d8065801d640003995202d400d4005020781783d14080a2403e244c0b101c2404035039003001c0c00164188d00d00c06910706072007600781781d168680d035000d107807007048600c403601348000414084002510f01c2c040c02da03900d6450789001000b4020310041d941110700c030b80d03541d84114819071320691300106204070210040000907a88440d80c0d420443c001c06840011052a8260103866000300034040304d0116852104280324040c0308040d4148415a031504c01cac3d00350300000079181c1c44000d0009140440c030000200c0c6004042040e25030390305806071a41e40490b01e8000140003410704031100360001e44103031050882008414451103071590b0140409040c5407044400c0358842c0d0307066 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 987774784 1250 987773534 987773537
    0xc09170114090303101203050d020307170f3304020c0f07171515030703050615041103160c080a181707091e05040f14030c0703110105070b1e1e0c0703 66
    0x18030800029a27043e02c01180544101d89403120503d202980c0904000b8006240b030340c05008881c1006009c0102d180c40903480000d160010900c2000e000e03120000c03900c0d80a9042d0031500c0403881e4085c0303000c0080c40300981c681c420701b101d102c03541e114074503020502c06011096042e00690b541007800816413082c20781061180741c800c00c10350400b07001309180541551090310540d000b0001e010880da00407001c00c46020b010780301030004000e01c01c4100e1241c07101410222060114103105090144103407581198079600100041e614040c00700014070201011400381700c5c024a4500000e2481c680d4201e01071005560710107010014604401d1000138200140c1594074418207035a80150744400340318140c0301c0c51050500e00100c00c030364100449104050b04000318a07074420041c14407299030004251088a84c0940785040041c42440103c0b04e601403c0390041041c44a481030040302041440b010b9818080703104446442d90301d150b08004c01c50403407003441040181003004503110101060060412130f029 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 987776034 1250 987774784 987774787
    0x1b040b0d0f0b0d05011512050712050a0c08030c0d0306080a02091b04061d0402070b13030536060a2003130e0703050a050403050d0c0917011409030310120305 69
    0x850740450340070483d01400711141d07507403224011440d1080001503006089100700048141c84250b484a03070341c0402d4040c20b0840c0780b40312900000c02c6030030040301e003106510a00c1c90203121b50f54080030340e407504407004014040c0580740c601c51a00703200e0b105000071542d00c0310051041c1013094080c00858140036020712540012100412810115480100000d0126941300c010417019844601e00c0f000c6d031407460038404c0b4010054400401e2401c1513050304408296840300e142c000c1c619080d2a240318548500710040346c500e40f07070350745144905002005030a0034004251040900710070072100e0b100b450350318800304004c150011792a404901201c10040007200c22a440e010442d4a4520603815541c0301d0b071040c1d65244100184c407070341401025003040c4c14040601007800c1954024080d0700544113004491550f5001022546100b524010002c0c0040b11402c00c181e102c16080a0203408a00d407100410480c440200b40030a100008072441101c010404004890404c0040c0c908519155029001c0010 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 987777284 1250 987776034 987776051
    0xc0a0b0a201b0a0b0a1b1a070e0306011511030d06091d030a09050609210607020d1404140310020a0801150f0c1115121b040b0d0f 57
    0x1e00201062190090100070400c014680b007004115240c42c50241d40a124911410400700b22201c081c1c4089a40d0342c2440b003200110b2048214100088006c060113000b0791544c08490100c602d201280220301070f584154200004009040e6038503000c2c490261000c801100514a080c400c0038412040c918640c1985e141a0100c481d100030b90301d903a004506035540ea5810f80003002001441c44800c00c580c5030103941423008414000c1e0501c1400d210b854040c3d600010275460980d2154440f0914030009a81021013100040300595145403c450481c003620407020b203c003445009a04092132100707844c00182c82d0505000c410089880424202c1d6018496003005101c404024000341003030000c00e694801c031a45c0340c035990101c0000b829580d001030111880003107403111350026140600d250052881c4034126191004181c5d4240185215080a007012640425031284659814081c0102c050a2412aa1325041c1010700d4403a074810b00c003101100b00091107d82803160000c64030301010303a10000e44040c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 987778534 1250 987777284 987777317
    0x402102102030f0601020d02060106030f060e09100e0304032402040b0c160e07021b0f10110706030c02100e0102121f0e010b040515041d04050105090c0a0b0a 69
    0x284080340031429500441002410b29040784810303400340c401d10040074010f00f0068081d407035a5041c061181010b40b140c85a081c05a80c80e04810003d002c045070162503843c00054954458030000c1e001c5001604000d0140d42c100000420f9600390fa801400d800c60008282050035007914040010b442801d4003800001100201080030f4400980c180c0003404081290390110000510f00390414410814510103200e03a00360300040d00f0310580902d628001e00611440c0001c0c01c0303507485407002a03001d12800b11404003941d1010312461083d1007402101d02c0e00c0d407124402e4090342c4d00103d0144c01684102841e090200305600042007800c2008001444d0410049150614031012280900302001e8600f1014614601850713074030040000ca50fa01c0400d50400d44404010700c81d51103018801c20308420466480070030042150000c6c60a80b0140b41107040155071f109400318115401c0e0344552900e800600039500118010341c440c20010001100981040032014998114a060b40c00300a0314031171030b81911 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 987779784 1250 987778534 987778577
    0xb09030a051e070b0406080604050405010b061305012d1b0506010e07020d2d11010c030603150b03060703021b0a0b1b07021c1e0803010608010603090209040210 70
    0xc10b4000300a860b05402111900d046001d038425090110100070400186074040c59668104001b00c901084a454504200e4003401c00c0d130790400e0384584001600a02c0750343d4403a01804541d004c0e00c0380401a644860345050f01200100109a503072802c800d00d60301c0d148110395491641d401c50306c000940c008030ba2921403900d40c0c243c0204988448039000c0c0704032240c04205040703400360179240405400418030942c01c1442c43d00214080030030b0b81040c142103018021a000f0b10240031000003000f090403000001006001644410b85a1880301620030403508458000c01503104000b500600d40364861b480114025806101c000140428508402000700801c0c42115040743c06008500c445040903038198965003c060b0080c130602608214072801600e40401e61540c1025642d00b5081449181c00c0400ea90310443e036408071041d10045012003041b05400103581a204950307a0b040c040da80385c142c02c2e02250a2040c02a502c4000c0b40c0c001001850590400108031500703150680001e00307070407140c0c07402 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 987781034 1250 987779784 987779803
    0xd1d45090703170a0207060807030905011509180c03080310090f0e012d0507020c1003090b0c092d0d0605041b050604090e011b0c0201020607180b09030a05 68
    0x1508060020014480600303440c007032502010900d18600040d4080103550b40404d0300c82e40040c448c591001800d070500990180400d1500031009000712003030320079601c00480309805409202481d207012a0700d52180070b030494001030b9000910148880c25525075484540006102c3c0d2a503180004010500c01114020000603941e0f154011034807004450587c2d00b580c00200015400502008404056800e00019036818594013000040c1503220100200d0500c1342d160951604050780450741010503600d5480000700300d018800e0320800b503e9810010b00b1600c240b140035030707000d445030584146150044089001800620307920340c54103104000450741c80801503009680041c3c0c0c640c00c1205104444e072008800030200e11100300355505120000d9060302a502441c0905541c2d0f40d000180e80c0d000758030800f5200e101c80221000180c818000500003210444100c3c014051400405d4003d4001c1580c1101c0304001409548610b0905c052142150041c40c4141ea26205088801c2d0110310140060083c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 987782284 1250 987781034 987781051
    0xa021e0c041a1f0e01050c010905070807030311060114130b1e04110c030a080711030d06090b0f0105040605070f0f0c05090702060402090103020913050d1d45 69
    0x1520b451201c1000303524503a0040c1c03410550411a4501141a405003050103001c1c82406d00b103480d01550200607004160284004180388200c810109031550001000d10440348a0b0303440044141502619584400c828030540d0001c21040284004501e00350201e841840250340c000039030b08001ca00040c0300014600003490110304901141d0705c641c18240148000902d844504030701c1c100d42d0340043c0e0fa0f01c1c45020250810000b012000c516a03a03c02c0304d019010741700c0102100c0d103130001855520010719181c031403c0207040c03410300c170508941044a880400e24805840e064245454141c0c1907641d940100c10071100080e202c1e203840005090500e401072070600a2500740402e5080c10244091298041c050a054cd80100700f000010391300d40c5107440c156541580e108889840e00c00c04c00b20982104503006045004105000540c1079010002002c425100d0304142c081082c0c6c2c1e408d01c500141c4501041c1c42907146541000b8a11000e04a1050b4450320220070070548009084103500c00d10741640e40b0758 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 987783534 1250 987782284 987782321
    0x513060908070e160e03101a18040201141e031e09060408030412120f140606090d060216020d0807020112020309060f07030e0106030f0213020a021e0c04 67
    0x22a9100b040100050145001080c00d241094602120b8085120b80e49004211a481e642416510140100300c001d040e800c0c0140902d50303015510200c5400110105809407241c00f040e0585501d070880003501961301a111280042035808200e0f05a5004441440c0746003030915040f81e002c1116802540700342212040c80c1c3c4460680c0000400e50301010b0105400d0703521080610020030168412640c22a40c0440350340c110344d1021006403005e048502c5031f1021503182c4400020340240c25001031080540e080015583c0da82d03080704001c2c00d801040305094000181a13610700c0004d50641c010000703500141c01605140705190b0000744441000d9004541c21300000c510841156001800200c5075440460198250b15100021642c0c44070b000f0000768040e448075000c0307141c00b40254005a0019030060083c401d1035228104010040c48001041b80100002c549a00b01481d40c2d1003034501d00d01d0981e001d042204850030705001d0050310240407035064010303403240031500da80b6132103180054545050f003107 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 987784784 1250 987783534 987783539
    0x130f02011b0305031608010803041e0509010603090210021f0e1c050406030605060a0f0e012c0a050616020d11040504030807030f0606210212010311100c020d020f0105130609 76
    0x451105c0c0c1310b4a03590382441194030040c0500030002c815039081e103032980307002c80394202407c040c038004000340d0344019005030740341001080080e4075400c2032800328020381300c3e1010b841895030220b0356203115646d2862031080303c442400a4203555000f000e0104000012601c550000b0104600c04200340380102c008100f00107410000075405004030b01c01000200c2c0c1840c100b9600003405004c2881e1800314400b0050380c5010410982e0080700c0e000d400c2d10810700b40031884131030343d00200126407480204600c1080300300000500c41c50044115100000100c0c49500540959428001104416001207541f00c07800c01020900e500c0f5071003030500c17980c020742d42e1601c903050500c0c006e81211060030b2848803407070034600c040c404113802c121007c01074030801c0c20140c1000404080c20340240a03188518606010100c000014044e4124801c500c0010840d02c0440800362040c0549040047d0107000350807903451103608001d072400702d070010034900041c1090383c5000006010000d111103940c2281002c2604080306 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 987786034 1250 987784784 987784801
    0x5040501120312050610030509010e0604060b01090807051f020a0501110316020d020a0b070c0203030f120f040c12030c140f0c010201200f090a03030e04050c03130f02011b030503 78
    0x5400000070f03103640400550a001002c620000c200409040505849030003191203500254004040204a8400d031015400d103842c1c41c03409446440d21050014054040100d2100d401003900f4007207400052070506260003500446010143c01c0b410705040d80070750040300d03021030800e000c1c0d400d080308900c00340795407031501204d03000c81424003d01c180115403015920000d0650001640b24000c2e0700001c250903507548001c41110506a0f10340000d42602000c61001c07030800494002d840c8200e80d402c0d4a460ba0340d24211a0141c4110489000d17104800316041040108000039034007800c64000d2a0614051500d922039040c0f00c56004c0d0751040300d90160382c000303811040500105640f41030901c020301c00300f010035100d07109440ca4408001e840700d90010704406ca00003190111800b001c0f0160800102a0303607424007421058500010074052411300000801d0070200ca0100c078861904103011380c5c0701101c10746422400f0303241d001c0100d052100200301c2d4211001501e184c607081d03034840c0c1e07501a078071310f4070740c80 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 987787284 1250 987786034 987786047
    0x30507060c02011d0a080304090213080105040507170c060c03090f1c02150409051006030606090b03040308060a05061801030f09020a120c09050c0a1803021507060204050405011203 79
    0x208804001d0801d00c550010b0b030740600005003c528420132200e03043d441e4400542c510303800c0c1e4005600e038800040c0015943c055600941101510311505a504a90f1881c44500f65079040f2401805030b04007410502880c11074080e0404640204003c907503000302484081804c1e544454001c81d0113070320100d4012541c0c035080d141d0542c2c2d00410769006548c0a894000448600c50b50034000344a00300d450304002005445605450003407034104001e21035824000700d01d11201125008102c002400c159010480c14040d508110455541c1c04da01e900d150785684040702d0a0201034502544441d00201c005020750310040904541c10855048400790b0300c149001600322010700000da81d0440c10034441c640941c1d03480c030002c400c40744800e520700d4500010f0301d0700d8000c09040340c0041081d140f07014244001400b1000140000e901c0c55140c4007103d1941000301c0021021610009510084410741d458003800c814000d4074489111700005801c2c262204c0c006800c2d61700982082c0c80c0180c1048504003816403011 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 987788534 1250 987787284 987787289
    0x1110021612021203070807050f0c030a03110f0109050106060e09160e01110a03020a0b01050d12050d021b0606041103090318060712120c050c1e1c09030507 68
    0x18204a608040403080a20141c8078101190001800110640d11a5000580b0300022181a60355640107480c000a554004407815900c5229a4458841040c00020b007283e103188000c1c010031482600e03613021900c000c01312644044074010010844c200390401d000c0c0500304d51040002080d464100100284282c0765602100d10600300c19050210000101802c102903201d1494148007040c01440188c4d01c014095441c4200340c4640c1d48154140f5034081605d00340c4d9403182e1488441c60742d03140c1c200403800035281e10280c100c0f0188030640b0300b041c0c052001080746400588000d8100310103004900701d20103910369071480170703088602009a40c1c58144185110b500350300020504608065203440d560b40540c50300e51907060841c1c4000a8950380d01d82c252005207601500b1440c010b009244c00070b08850381c1503001e0880a0071300300f46041c520b000e0412b840e40382038100010f101250241c0110744007a1707050000c11078240113504c0c80d007100c01031402c00540ca200043d04e0f480c000b2451031a00500e065140d5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 987789784 1250 987788534 987788537
    0xb060a080307140111090a0e0c070b010b03160c080306120f03040306060f050402041802090d140102181c0b190e060702070801020f04050105030415021605071e18181110 74
    0x4019602c6c50b9034502c88400159001072850791500c0d6114400c92200348213511014004040802c00018280c003440000d6100e20040c22030f040d0030ba04064002e0781d141d00441e4004141c4441480015801e0624802c0b28080c08a007008a8010310980d800b000e00310751158209580181e1075410510459030b070311403a06c006107401e807001c41c81c25162454445c0400040c054001c425500007600980701e9075202900000b064011480740b00e841c0d240780741c5500039480456480c0308601c00710b1080485250002c0060a01d260a28004100706c25a1740c035540b510710010142e0352080307820a9101d00100c15441005058408440108210b0822110103454100903510404050f8010071070b40e8001c6900c8000d6604448003824903a480c0e807034501d082c4041c1c030358101d2200d03951880490704010f18485c81d0011004e040c011400d1307545480d110b41e118585c08090041e8045000300d00b400410000304038030131891041c903001100003040040c0f26203c804111003a5000e0301d03900d0000180020510700210141c0c204a00c5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 987791034 1250 987789784 987789787
    0x70203010b1c0305130b0a0e0405072d2106051305160e060706050a020d0f201b01060e070f0f08070e030f03040b071209080a0b060a080307140111 64
    0xc071000340344101c42c20000c040220101e2210a010345001c40388000c0d100d01e403051602d401185070004d10a1f4512900280304c4d0f0304140214500500503580d4124040111907298800d5080b401c420040f8209403c1001c2040703003181504400002003021040d18504240c00811100e15250821801c4a444074030008041c1c6000709002c01685290b10320041d40b51076041224640d501040015518014014080c03c114106070030407504140703c0d40104583c0a081a04002d828a00e942040440c0d0601254245090220402d5130044100e41c0140551016400d14080808403026450b07080d603d1540c404011801d0b600140f080450300b0021b041600c2101d407030b0107000030940d0140100b05403030152407a0148008260002c9164030240480d02019040d801242e0385d850f60313200c96135016800418195000c1040510404080c4d00c1940e901e01100c0c0040010408a02e554035404582a4060300d4568002003150000619603003d201510703030036005403000510502c1513181142503e02d85954074544000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 987792284 1250 987791034 987791059
    0x702190314030c0a06090c05100206060109060f09120606180b0114180d080c120d060b07020d11031014070305010f060c06050a020d18030e0a3215070203010b 69
    0x30026045001301d400080100d52402c1c1390806150743d407416004240c00010520310310b4800e1750000b51175801400c1c20380c2c0d030504c410707660002103170b482039a4815000083d000e0201040800342030300ca88800c3c94010300c00010b000341d8030103c0300c1084100804003100c503520742c0301905403903800c0381e5464288c40015450b075180c44142d501101d5000104040207104500d1004018203101440d8142c030340c161200801c5483e07825072002d0302402900a40c03201c801d4141024800300b044a11102076034151a0b000d0304800c2200216610000407461983e40c11380c240c8240741c0210040710090080440801701d20243c80301c14140703028018190ba83c1608616a0f464003c01c080000c1e0b5404000c0c1000140c0104000509480d01620343c03002e40300c0c10008216040c20218403a0750b8650015005401b01d1103901e4244090fa2420300344507003102d2a21034405c089007200203031004115224801c0042194030b0308001d0300d008080c0d002400f00c901000d10070506410120f000000c40c202449044041142150f11120598 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 987793534 1250 987792284 987792307
    0x6120501090207390807210c0605070f020301020a0e010e0901030215130f0e060909060c091509130501090e0c100f090e0f041a042006070219031403 65
    0xc0300d00446500a50b003010210300010408101c64200390140340542070030b80d42d0350f05c401d50f450740341d07004a10584240c030b5041090aa5540c40100b005075200c0c1001e440c96260140a0300c0c1034000380416608880c4c820700460042e41c080c802001940304d40c1e221410042c141c1b10005050100c10001903008000b14401840540d80e841440d04414281c440840da8803104c00c50b1000c41c00300c0030b61111005405110006c605070540d001001d114680549804c1842d80d100030744d450303403100250341d008203200003002041d415042c020f6540011582d0303400c41c9481c00d059100405c001c000c1130455040026035072001441111102e000d61441c41240d50014800800c2c448006214000680341d50418080c0e0074100c1d1707a03060702416521004082e0285e00d24064603140000341c2060508030f07411251002914043ca41c50780710701440307038000d64101600c10303601c2a64880b079081c2c804002c44265444503007441303100e00580e00c00036414079401c0b51603000004c1525500e4032600d8686207000074907803500180070605011 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 987794784 1250 987793534 987793553
    0x1205100621061a040906060608090d1403040c0b0d06031106040506040905060406080a030503040b010501080f041410020c160b070f081e220609051809100606120501090207 75
    0x4070b801040000740d01c0003000c00008140c448000c20354200d0b04001c2031400b48000c65210400700c401d0380c0ca43c40e41c5030352010051030b228820010902c01007031b070300c0120300c0000d440c5102460b07202e4030840c0000205520742da0310711150341200382d07000421a2580000c0c420008012598400c01005403035040c101828800011034078021030040301611551000010403690b1240c010b50000d021032401c2e2500391a4604008002d907208443c2510150400c0d4000a959407041c48420300c13400103001c416880740c68594543d00200c0034050030850500c2140b05404444865100802031450301c800100701c04105229002c0081c01070354000311588500307101c2e180104048031081002154403031480359680b01e101c1010464178001d0140c40c00d0424001c038011140310444038009a6000615186078000e983e58135040314611054003599030040c07440e10ba25007000c00720032111908a4002c03402d0300d450801412002c400c880c16503010000058141c0748071100c03074103030f071144a0261032100425440d103c150780781c06010 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 987796034 1250 987794784 987794849
    0xd0905010e0f0f070b0c0c090405070e06150403080901020a050d02160e0c19021f0209040b03060103030e01180506030705190e101d0901081e01150303030e0712051006 73
    0x203005d00001c803090418010300c030920f076403103009100d01d00b10304243c1420366481980780160003a108485011480c5c0f0300c0c040115902050b410074030240383c0340c11540d0b00307403441d004007201034158850700c00c402c0002041423025440344045c5500070b100c0c030486089800e50aa400790300c13250100a00e102030203014000e00b41100d01c0c000451058404030f0050300340c01c03441e24031402e0300c012200003c0f09903030314040b07900d40080810300800c441c1400141c0e055800c160301c1d040300703102c02804100301d032190f07000f10350042c0310004240d031403641440c1100b07681d0000710b81c017507000710f5074480065000200b0031103401404907608a410854602030013500340c102d000c2061000020b00c1c0c04140010300043c0c20034071007156214011508045c0c801555569a804215550409601e1844214011180d00a45100140b2407041c04411812030840e284d440c40c5c6041c0d0003000c072841c48000c2400b5041c40818240b0080020f00007603840b590040041c85107202481e011211150409100d002d55018500368959001c41c16221 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 987797284 1250 987796034 987796049
    0x140f01210605010e0a0b040c12110d09060509070608071b0804050d150c0302090d060e010209060304120305060f133b070b0306060714030d0905010e0f0f07 68
    0x142015450100012054030303240103203090b0521001003043c0300c000e03803114056243d56400b880110b01c05000c20080d2500610384200050b806403041106642d5600000600340c4c801140f10700c0c0030000041101035619160382a220284c0710f40500420380700400641d80200014901845c0c58103140707000628403900e10103051851110003d0000a12081d54103c4000b80001018402c951000e0b182000c0e03440304022500200c00e02d041d1140520074040e00803107201c840018850741d80b050131076503144c005150b40e6400038007541d400d20103047d088d00c458004501070341c0501d20440a148030000014240e4000500c024000c4040001c6113460792910041341da0701d9000710030040749125020034000110203808204107034500c01c024140200041403c199140c1c4a04130059a004036200c07184018542b01c141c81d015080b0b00c081080a020031003001c0444c00e454030800950317150007003102d1b01205440b0108003d841c665580e8400d012010003c20a039030714150404080c20350f07a012034a03425180c8406100c2d040 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 987798534 1250 987797284 987797309
    0x512010b01080103111306080a060c02010e03090d0f050a030503160905060304080c150a0c0e0d02010e12100f1406010c0809100e04050c03060a17060c0706200a03140f01 74
    0x107105541e801080722280c6c141560030401542d50310145aa00c2880030420307604107180007840702c400f510600038a096039001070700a6150601280c01d001d0010148081900c40000070320001c03001550900800b403145020b0782e1502c0d201c0c14003103449030348040400202414400918020055502c0314825203a0068021400e079854064040c4074509102c943d50390075410303910700740401c03070140550343c40b4581c10322040c0d840000102c0003a0038810440040032029000c207049014042c03491502261060400c2c02c01c07400e07a2040c5614408040540318403414080c4510744030380c2c1400e210b00655415070350150302444e29145083c17207504c0d0707030529124131560700e40201706039054074401c180603401d0b00d542044050700070407082c944001d1200c6142c005444980c0b007454507650000340d541d4501e400540344c1158101910007501c2d44a054034540c1e21600045031041c0d00c4044c01100116681c50b694220000501c00503601c104d41400241100c4880f806503030002d1128003030201d4040351030707040c9040d00c00400030b14 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 987799784 1250 987798534 987798563
    0xf1e03090f05010915060f050f211c260a0203060a05090a0c0206010b0304082d070c0608010504090f0627260a0f080c19090512010b01080103 62
    0x81c41d41d4003541402511540c2012212020054108140d240800b0740c0d081c10080f1580700c5081d111000701d24441d41d0b900c0580d50605140500d40400315001c6914405046920203816441d4513041040034025a00c1c40c00c4503403440142990804005e0ba040404180303030101c0c080c00a41c2c081071101c005030260010650220014405071980f00985010344001401c1035030501d44406d442010b45420140400117010b20000010442c04c0301c030641e8008e40d44841a00e040c80c248000304030b00c00c01d4404102000314a81c0300c000303211004c1c10380200b0010303010704801d017045410440050100041070344203d01030780c0340030003150100740b40100301d400c1c1d80c0e401040844d542c41000c04075890700c04202e2202000d481c80ca001001000f081030403030b910303900040307440100c100c01d60040c60305680964046138021409101d26038418070312580d4020303445010112803a007070441140003500c220038402c01c1440440e04600c3c05114a00e0306a0f0341e003c800300300e800217002c51160100000d10003181032000605003075401002 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 987801034 1250 987799784 987799793
    0x110307030e12070b180102070506040305031e04140c060f04030605060a03020a17011b09060c1b0609060908031e030a060e3c06060a02120a0207060f1e0309 68
    0x104081e000316031071625a25035040004604c8010b03141d40c00c8009522220185204060080d14102504413014040a50702c0e43c405641039440140402603007001200203021032001145114001c030b0052031405d850016002d40c0c1c61801050b00b4401303204030000e01c400700b203800102c4100c80030f583c0d0200707000c54151031b0180030030049506604029444050b14601107500703044000c40410039016880240100c4001e0a841090121005c14410001d12804420700c4518040c0c002c00e56038a110b0204c2840503840300c92104079540f4150416000142c03402c8003000601e92198841002d802d403030016610306510340c000c0030810102c4c0402006802c00c040000f8a18049aa00ca0002040308003503035451854040b61801e0103c0c030740c01c0b05c1203c3d02c20b45038024881140b441c414042200307041002405036142c070300c01c1140c107030442c1d82c00e0700441c412200400b0550040c080070b44043d5034942c005100c5070b82017200242140500c606402d00b00905514020703100d0b101030304108030a948900780051250a075090 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 987802284 1250 987801034 987801043
    0x9012301170312181506010c0609081905040807050a120b280f0f0b09071209150903081308031b04030506040309030201080105150711040605030f0619110307030e 71
    0x8000c0003d9549404000d03580c2c0e080d1403400112452002a1060803c1e000894400e007802540c11600080350002a00005402075001c0a45207004104e03060030840e244500c0d10001d00d12000140c0081d802040070001c42804003d250007611007206d040203444d0403c440c00d82c80000c0c504014010340011804559070300d040480380060f00021140d0310502681c401100c102821503074105403203da107400c18000800f026072160082070301d4028508140b030b0721481c60860351480d0414102e10b4842d60381c40e000c00000c0800201c0a000841000003040f0b0f210702e42005495114001c0c03011910084040d21000010b4020048035840303505149e42c0306100307136206a0382196000d00c0c1c00042152140906020900d500000c802d000c0340e20036078070004503030388a805101d4010300b02c800c2150003d03800d01c81000007074660815900c0e03040025100080f400c0d591000a0701d00064014003120540004081c4044208981d625800303c00c00c9190900145420103800c420381d120040016007050742d2111141d400020600 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 987803534 1250 987802284 987802297
    0x20f011404080f0705040b01120f06091d0f010209061e0d02031504060911070303091e0308040b1e0408031902030a0c02100905070501050d0e1203090123011703 70
    0x1403a03991203903200d0010550360021000e0940091041c0c400000c2c00c0e141074010300500e1807040e510201e00000804548002c0c01c02585190300d4142c4401d800308038500d0030b20a80e030711352140c611a40004001020340c5414210f030400340c5c440b164010000c4441c00d4503610122052001c03010031642826007203a00d9070075613005181a003441b10b8000400c0c80000d411f0507540b8030b544041150100200f0740e50b0241e8100b100c580c108210000c2c8428044403000c03900a50042c5500d03801440c030801c000c2502800079400f81c41d01035088010070001030902c4140815009c0c01039018204000f005665240f130203100c11032040042c4020140f00c0004006100c605103001c40710f440040188081d500c906140d02014090a100160040184103010003a5101d04540c040c80240603004000b900543e03041c45c00442d4a0341c070840d14146c00d503440d10006001224100288441564000007681d20790901240c545d0079600034009407404020181115080d0400101010781140c82000b40400b030149010941800d501070301 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 987804784 1250 987803534 987803567
    0x15150306030813080606091b0a090909060c18141219050d020f030301030812070c05030403060f0e3d0509070e1b031b0c010203250c02010c020f01 64
    0x101d01120903041103d081c000781c1c4c1d4a50300341c90a656504060001c01e40342100c0344210070981c10000d6502c0f102200042600e0314243c43c1c00003d013500c07800300700c0c10340701c0f01c072003c89682d0350341e51800c1c5500b039102c1d19401941d142030040b52840380c03801f10b00301c0c1ca0b002e140e29414444d4050180c0414080d81c1042183c4500300000d101c41c6000030305042250326800d014081c5000b5000f602c402191380d4401004480c1a80d5205217001e0820602080c00101040005c0641090181e28107810011540810107800114440d08011548003100e00002050701c840202481d1390b588210040381c005c002810b503070b4036003c1c0025880321101c092201040c100f0b81e0340d0101e00154034500014031259030b03804580c003001d560020907140101c0c0c0314040d18102101398118502410541030000c1081d524005512451003a002030701d076420410001c15190032a8000d458406852070742400a42160051640069249200382130803c181c89940d0006030821490b508001e20420b40a118040240e0123040c0c40007404580 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 987806034 1250 987804784 987804787
    0x50901031d0105010e15012a0b09010621020907030c0537020601060f081f060f02160807090b061b060f060a03020f01051c020a020102130801151503060308 68
    0x401d032520340240310030300509403d14010000190001140c0706031081c5024183c0d0341d1030f130340f0068100a4254070075a00b030300e0320b501c0e40c01c1411402244040012900813040000005542494031414034010824081c0342140155061381800240ea0741d035090a91282203418042580c0031503203000c41360762007891448455484031650800280740d031010f44804609901c60320b440760070108002640c4e5088244030340c500003040004180180ca01c91a01d42c2e4200d05900e071266510488103025040c01c45c503603004000084ca600c03c0100c03800f42d04000c072a250000c0503450200503418180c400f078890445001e1002c03216221003000c0d1440c1c440c0d0b011603000301d0100c16480459042d80c0025915100217aa0340350300c0070019000b19105140403906030080382d50040c40004041c03c1940103403019040720b0741440055821400d1815003c0d414001816072092544c00142d45500002c035690b90040103030000d0b15142c2c90280e043c8040c4403104008010756502e403100c0b4005240d1801d0850252045400042c0305950 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 987807284 1250 987806034 987806081
    0x5071401020c22111603180509180a060203160210270809030f011508011104030b06130606050a09080102120a090f0f230d12050702011401170c01050f04050105090103 73
    0x100c503102c505c00600c20760791424200a6420f40c1c07414489140220755216500c42c0100c1c240001c4000301e4120b020091050380c0c600c45858a0b20000c0381c104a4084010400c202000e02c550b6506000703810381e41c038230528100300020340b001c24040740d825a0030750044491801c0d540403040c04800b0082d42c0c1c01007001008c55482d842c26001141c060b02480e541c0070281941108040b0701380e0b00600500d0b03820450b80915038103052450725541e80300803024280b690429441c0c0d81d9003407170300701c60b000c0d1001a246940361a0303603406000e04000c2610751298002c400c0d507417050000c1c0710120030030342d0840d4103d044a0004160140c00341089604c128840c40700800440c400b0030f44c0d100b04042c80f842c1030712030002e82411119140741603100e40c0e180c0d0f000100c0f1000040562501c001d506402e68026030b00002c0500c00028900d0360403800c02c001080030b030002442d855030800d055003d400304200c074010081083c43c04906004050a140c0f1060003240603040c140803000ca4508982e034844e0340940f15410003443e80382e400c000e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 987808534 1250 987807284 987807307
    0xf0207090203150906370305030d091e0506010e0405010e03190201060905130b1021061b080406050c1201170c03030a120e0f0a05071401020c2211 64
    0x20240070f8124052250100000e03c2442d004000c0040c1806000440407183c404980c108250082c521940902d40d403400804008601d0810280c43e810315007510010390085a804c0c440f000800c0070540d5591941608440c000040f004a036150450b41502c40f140045e07201d0b4500386000d000c105925117030522000c6421040d080c0c41000b4142a401039400803c200d546600ea00c3e001e4a104849400441c0f10602450001030b5002d2440760f4420702d040d0103039004a881d1241c94608908045042d06070965a04071201072100622410b4002042c0d501400c240c204120300203000210002c7c40504000d0b515000280b50030460001c880c0b4a410390780d83c2a49035a121040c0d10400580e440b5400751a100c0d0b003549190b02d040000031110011705a4031071041b01c00e10090384e6000b80c5416a450203003070081d140f407422041c3c01048441103103445540a85103c0d42428400a070340c444000d1401d04642c440600130300d01d0f450381d49056001018031210101821100300c2c10002400e03016440781c0c5600400a006035513078 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 987809784 1250 987808534 987808561
    0x60a140f06180306070f0e0423040203010e01150e010b0a09030f06020909010b0408101e020d091505010510090b0a0f0e130c180b090118090906140901020711010f0207090203 76
    0x2031000d030b203515001c1407260f408d000880c1c80a401c402c003103503c01440703029250040d20380164400d00c020008507103a0742c0d40c0c101e00d007540c40e07101c3c0400d011075880c24203200c2c0c2074001e940c05000d0902141e9190620b4036000c0020080350322480702a15404100f021030060007078075012960089005048000c1a507506c03203541c400756205118183c158001d0396640d4041d1001c034000d4211103014403e250300b030840001d2181c2c2c0213600c2148a1411a81d131200014005420200303000b43c0190b0881000501e50700d0081032048504047c030725082004548203062140f4010002a030b15040e081d0300e000c0c7c1d03400844040c00e8a039070b1070084405a000300c4c07a041d116612840d03504801c280b00d10549e2403102c0051050911858a5098040e185084106101040c02948988070f81417030b005902600c20401c1da40c4a101e00c0868040792030a50380d407621510b40b080c40c00309242490b5040306000c2c0086142078031305d0b11401a0200001c0c40d942c108080b8402100c3c2140c030800401d030180c0320000c0c1c219960304101c510006134 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 987811034 1250 987809784 987809807
    0x50c04091d0d050a050408070801200c190f060f090302010c090f050d0809060d0606140f0313022202121f030624060206060a140f0618030607 62
    0x5030074450005000c403540326060020108080c010500c01c1c81d41c1c94151240d400c0b80c0409400c10109000006650720100000c0f0020301c1e6a07800043c0c03040ca0458bc00c01415000c0c9050000b8020400840c0c0030380320005a07007584100c1501e20038840d403105240c015400070140c039000d466641045504903101c2c030145c3c0036840c00d40c4603400801c5100782c070400980d6000000e00c0740b90181c5494000801140c01d15840e10b0704c00600c40c221982c6040345042c0060050707004400c002034165034814041c07110b96004400101c500d601070210500f041c04800b0081c0c2d41d48401403550718100c1512031988110b40301c01c0500c4203e1000682c4038200807040918010081d0840182203076900808400b045404244e21244804840000c240031003403070464030355002528401354500b034501600c20700701d07540f07100d20070074080a0701d400c0c0c0c0a4045802c0540800928a210350400d507086034504845003020f5440003100b04c41c06d501900c00b01c5e122260051043c00000a011013290103018200c1080307601c96002180c01c66 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 987812284 1250 987811034 987811049
    0xb0702030d0b030f0309090a0905061314150601032a11010513030e060a09080715110f03160303110f0a140a02071208070f030306080f01090503030109021606050c04 72
    0x41502c42c03508040d564004c20308581101c2e002003200822034104100c0c0f00b17900c1249a1004201c8030103540d86c8901c1e1007000c072039008100031040011410401103030086075100f8502401000107000345034a025050402424440c103065868100f40c20604c1d113005a11680581040e01851250040710058040140303c4101451075180000154100f00c080a2802d05c580e090364a801146000c10180f02e00c0358000300f411018812402c60000c0d40450821403003001d070803840020104c00040b010080c00407600420314695940141c8040a2418000001d03038082c5500d65110401e403030030608055004209401c0c0b4071202540004e41c01d4188040c64005155110040d913800155001c45010407560f40211074614005800c0310000b08007401160780c4030b544450003013070068900019560396124428640e14100c0c00b00352540c5040006000c284083d445900c0c8007c024400b80d2040d0f035644e0340364881402070020341c603804242c0ea80340b4203481d000d41e2011580000200311509100241c810a178110384511075 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 987813534 1250 987812284 987812291
    0xa0b01081f090c06110a08030c07020f0d17130905130b07022e0f05160305013302010905030c0a020a05011d09091c0e030c100f0c020a030b0702030d 65
    0x1405051041d890b440d07802040f42c01c01942801002c4440f409a085a840180300c0c59440d0f10103d40c2c00030085000e020025044e81e5965128414400f0b1401030304602881251000c003004040356100301c600d11165600c2440680d03e520104c40741aa205054010200c000c1c646010404803005000018000c00c5c0542050a0745a0700c90000300e07030343c80110700d10030a600c1802e0306030144c200344242e02d1010031185031004201070020481810850300e0488000602c0300003c0d000c01c403a1030305446207038094118805a1000543c6900b60305040c00401d0218540b0841c81480340e0001074400e600241315968848284c82d924428003000075030302da000c0d1506901c202d4004100050b50741c02445075800040c02d02c0c0d441d290700c92000b03040200c081030003000710805d401103100482c2c01d24010508015101400c0d210040c40708600014107180200200545000380288103840d03260940020811669041d41d00c0c0c8031111000a2011070321140c0a54402050782e2555024082655004409005c0d420203000e401c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 987814784 1250 987813534 987813583
    0x3010306111e07030915080a060e130809030705030718061212030b030a0209011e090902060306212406041a01050906041505071202010501150c050a0b0108 68
    0x7025030310800b1024400000942214121141c08401400700140130741015660280c3e501c0c60b55010000c9541050005841c031310410043c10b0080c032629001d006010396620080c500f0004200031000d03001c03405031074008082403c584903075042100301c0181c40060160b442c2950b0b55241c0c412001c8640c555480c8490030716030082040e01d07905d0103010710141c210f046540010403580301070380107042c09462541c060042c0e50801c80036895019810b40203203407007540241d000c0050740144a08030aa5000070882904140c00b240c090394910b804d40303420a8007242d54811080301042c0d15010b00000c0528607549000380d61202091010f40c807008803c1102c450140c621075619601048111101d5800c0928032048a84024209503c160040c3c0480c5a001d02414509074454045103071b0307030080420501c001800006c4090408c51008520b2841c5e00060009004a505041105181e950900501c074100004000c1748401d00c4010040000e4154100310700003070f256125040180c40c1e6041d0015950200d0344c02c00c04 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 987816034 1250 987814784 987814811
    0x1e0f05041a0907050402071e0809031002090a1e1205070314060714030a090c0306020301051005130303030b0d0614061009210c0f06020a060b0603070c110a0f0b03010306 74
    0x40520508500003c1c0c0015400e110401c002504504000c0d1a100780c288044016040040001442e007070040100c03585884800c000c0602d4454440c1041c1c07059401405202030a8681380c00c1c1a05440a04411103514101081c3d4000c0c032130403641c41101141c050011450a107c0f02181a50903a405502c83c020f00041400e8025a9040c003643d285000840d4600142603401080002e1600107100e088041015401c607211240d5909880e0420349446600200421080c81c01128a094410543c01e0007410318110380d0541c1d11401c003d02c006400c2c035403100c68401466070740d48282242c086c0d01101c10060f080441c1348050100c03000f140e8007800352541100d072800c00c034056018401212a03440c03200389108034143c1131800c0c0000d51403007203e1110b88070b04041640e4005264a20146c5040d030300800c0c002d05a424001c0a135500200fa20303008010170418030415940c465401b404403030304418140c00b801032038408902a8941d81d03004134840303a015800451811604030045040728020f60b014080034004480 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 987817284 1250 987816034 987816083
    0x40e060909030d0b03010e031c0c08060d030c0305040e0f070807110d0e0a090207080d27020405070c020418030e0306060d0318031a161e031e0f0504 65
    0x8020400e58030600001504000d41e401c00003070700c3c030007030000304080d01f814001d2855074028101c2c0012000386840501d0094006114045c0c00502c80e18040405040040100c0c19a07007a485018041080e013002c00414140503c2c1140c009008c4007058200d10700d4000313004014181d00b41c4180e00040c13500710209424a100380110b450880c42c05010f0040d211035201c041e50301001803802c598101c152400f0000c0d06400920162032001d0140c0a41da9851010305010300860f00f0092156108d0342d0110302c9983e10307004901c0035086035a41660001103544910074161010100f00000960003030509034508652085000c4280c181c621984442c0c0000407070300101038550b00111416a00b1000c460700d00008248244c00340190b90180e840d0320315610703449031950310011315520780c005165061031090295040b004c1c04d24100403101480c0c0340920300c506040d8261500b000c0c04c2941c01b01525070380b48403500c4011f00781c0d0b0ac002c100010b40c10007145940710b445502400c4112002e850b504e10084002150440f07440 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 987818534 1250 987817284 987817291
    0x100905060f1005040c0306080307050606030706093c08100609022118061f0501020102070c090b281e03110d060e0a0309030204062106020f091302040e0609 68
    0x2c121514003030614082c031008203031560a0384101500c90200041d075410600003000d11074022009442640b802c030341454505095035109604016010a08100712501114010400f69040940200c0d1340c01d02c140d1200d500d90b01c40702500003204810000526904000b6001d003500040d00e0041c800c1d150344003015800ca01645101c07003810500000940403500301c803c0384c01e9200001a4184900c1e4190010003442c1180840300b6055000502d4a44108660801365080040400748000d600d0b0128503030700d03140c451506200c0c11b84040c1e283c0003551f425503240b051046e001000d4401c040d072140b910100f07590581a9078843d00c1800082542101580e0701201d140c0703010f40350480b50800c5039140d64070074040c007140d840c2002d503491a5900c480185404c3e0074400011854060f5444000d03441c1580100000c03075106038030140084049036465008508191040c03501a5004080180c84800b0007503911000d00c2032850b200d031301408000d074828550f40c1990282c81910a0207100c25440e40d10f06091151052054 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 987819784 1250 987818534 987818551
    0x5010b041d0601170112060f090519051207030e0a050103091a0703090c17060907050d0b0408040b04060206010821030c090f0a090b180606040b0d0e100905060f 70
    0x6a1005448034003901c80c0c1c0ea0060070601d4000ca1880c032200041c19505401e0b0003100308811140740c61820702202d80603a101400a0b02c0741001003840719522142d48007135a5030051240d031a80781000040c80024803a40d039140b0000780310195a0045850001c1900c0c1c0701d29286403107621484000b09007544a8860403602c1a031100500000880449010240010040c4400109a1140710460002c0c4444040000030400e0040401004960641d040d06001d8002c1070740caa5036008541c00c112a0b0b98010045010343e0300651810800d440c1c5080180c02c030700c25034000300f21681c80020f0000700310780e0014855040350600410340700881d60001c8828400051403542c815040340c14004241c40c070400300002d040d180d90040001604088071000300c3d10050440c1d10041c0710b5a901c40d45900350f42000c90500702c080703401610b00c451914121000818078016030164aa28000108030908541e11603401204d0024190003140d180c0490b03480b41102515100c20225094010100810f52026a40c004240034a015 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 987821034 1250 987819784 987819809
    0x801210501060315150e0603280219052806050702040e06010806090f0d0905040b01050d0c09170303090a080f0c06130c060e22090c0b0417070b0d0f0912090905010b04 73
    0x20f02d0403527400c5080f841c0910034480d0f14490310900680c1c0b0700540c04040c41c220008901224604010051002200020400c0c1d419030080b40884110950300801e06a440a04000b5121f544500118004050380d03e035420300c034860340d000030802071030000b03400d03200c0c0010a0454100c60880d540240d11780c0c41e000c04940c04074818600500140c0b4003500b100703c2c2d072001071500c3c2d400d0410b4008142e0035101c001d051100403ca05070030030700055034849481007901008a0046242d41072160140b680c9000450000d041120042a0024103021140c111500c0803100001c40300b090810707007030100c030b420503456044070360040040c2c1c00035151740100d52072007010300010034502c0d600395414007105040e82c410342080401680d07034000a0004840c80d007020068001c590095490b1824085107100320001c100c2c110069901c01d0130104401d2054004455086c1c83d4104045190140e0000c1603002e0020403c3c000c0c4684000e041c00b940141d44160354004a0f800c0c01801d1101d643c0e43d1241d0000c5124600074010780d07a02 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 987822284 1250 987821034 987821053
    0xd060203180f0d080717310b06190f0306060513060e1803190207050307060306050303070f021c0605070807090b0a0c1109070203040905070801210501060315150e0603 73
    0x8031300c46a8829000d09141e899420141581244d0503c100c5004454155049683c0d8020401c5030300003140b103050001c19040303200300b40c4800f0390710f000c0209046d21580300040035924180c4e046d901c010003004103500702004d00761245007440c068142802140e0168070104540e40c3c4038013040c02004202d4165480c1915252908030341010350b40108828039246100801420b0041904000d02030550541c681c00340c043c0a050004050a0850590103c800c2609009080c040c6070350110458010540c003501c0803400c090284042101040e03000f0750103208a030380070810801d00950f60400c612407011540c9102280d6905202514481698050100d491a0520010b016980541c0112100038000c883c40708080c101400010050941259004010303000490100103080242c00b4040d007202a0f828510744540c104903804064101144540010250300300b0000140700f0203600080c059900b100e2400da580001c901d0803c00380c9402000700480e401b4404c40040d011a2015415014803001005801843da = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 987823534 1250 987822284 987822287
    0x611040e0411040e1b15040f06110703060f020301061101050403050409020c15040f20060316230408070909020306040b071106090601090f0c0e130b0d060203180f0d 72
    0x10b919410640e08180d40710400318100b01d041240162196003014480c0070082c0c103005000f80081c0290300004407480c1032209000312440c5d0050a42625001c0c0740c55000b20342900000b603e088202d50014040c1807820919031310042c0d1540096046c1d42090b180c0340c44a09040c1c41c41c0d8203d420440c0c000e40006d6013408103000720340c5a5001014070700001000c45d0f001c4400c01c54848020700e000c0e202256164082401c1788204a8601c85490b0305403504a81e1020740400c0c10301085142c803000746110311100241040c02000d50003a180b00d40245442030010354504c1d4254154441036110b80260783c060b00c80c10000055080c064014140701e940e0281c00313090075494a40c1c50030300d000c10141ca100e06005990b121030000300d00c1000791030310500300e150051005500d0010b04c00e044031050400c00e04000c0c01e01a418042941020b000d40200d00b0031b0b241504007980c1203a00200400140d144560701507110702030b034410303c074080d00914028442283c1c00400c80070850420b5984596a07510a0030581140c8041010385 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 987824784 1250 987823534 987823553
    0xa03020c13140907080c0a150509040603051e1e031204021807020a231c020c100509030d08060d0b060112180b010b04121502070f0f0611040e04 63
    0xa501d03040010880c0031050070165610039040f22100c12503031180004220038101002851140d0805441c403542d01ca00b04503a00c10405403400c25502449800280c8034140c2d1500e5001000550f000419120b01512031486080c1e031814240e40c820760f5118200c812100000801c0300b540300013070810011468545590402c810000b07000380166805901d8000e103001c00c600ea655028030580e43c0e0b501401c100364807803501c2d003226402c20200e16100f10781c440e10050080310000c0c4001002651903542034280c001c41030100c1c90504002e45c841d800c0400001c0805880d5001006800c03006030031002c0c0e40d051403001404481c2004200c48079a032088000c48200c0228070402c006641260061424404078105060810240d807030f80d040e150010b0042149910a01c4071011009001d4030100c1200d40c0713000c3c174103250f0700080c00200d40c0103031080c0b0500850300b0808002c0c2d4115081241c2c088441502c509580c1880c03920116000d4090311500d003481049a00109280c045905a801a84401d0055100ca8940303e948 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 987826034 1250 987824784 987824809
    0x70c17061b1206060415021e061b030a0e010e0c150a2c030102040f03020f0306041101110a02090c0310120f03052b0b0f03010b06162a15020a03020c 65
    0x84c008100109050701d491500c00b4204007541c0040660070103040d00d0082214508416900a030064414007201c0726101c41c00980c89a00f62013a65240c2e101d109609004103182c4152110715071a201d01e14080c800c001c2a8251038040c200c1d2445641c0140c80d160f01124800d511001001800f004821390590001041521a022101004051110b540000319089900940241302d0000c925803041045107051814800069400c3d005081702e0305103543ca18202219001100e4144150484074085412003089609080c036001410200d5504214030810785903071068540c840813013034174000400d404e01941483c50210b60300034907903607400901e0f84044800d03400000c900c404800b0504400008070400c02c40801d0744500003500010301941c070782c0401680005c0c40e1112070099040c4410f042440d940c0ca815035501d0342e000d5001141d000084d02e04a07801c51801d4040c500314145401103460304906601205003075400280034032015410705003059039105c0d040d100040c0164000008030040303041ca940740040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 987827284 1250 987826034 987826039
    0xb0429010813150614030c18181203150a0602060a090c05031c021015090b060712030c0944010e03030906100506040b0f070c17061b1206 60
    0x440c4403460742c031100b4003d40440e03034680141d100c1c9001d02055030b003d4a440401441103004150084203140810020b80c3e10f10a242c020040c80000500254000f89110f41d0050040003913907400d41c1c4101003003907a600283c1d620300c0710031544500d03420103051983d041d200340d8446800070f040380d0361441407000c05006440c0301101e03074080019000405480410200c0ac04481c03400d05191803904c0290000e01c0c0c24032420003600308608040340d08002c0050300d015041542d04d106004204c240c642c00c0400d0311880380c0c134002441c1e440810b0840410540c980d0120403440c00c00d55858040341d5542e1002c240405200c447d46d1002d129488c2c56042e01e06101048a0000307843c59840510b040c40c0d441d8442c02c491201e02607048a4200104000c0850000d024143c0c1c0090076115100d4010301b0500480c000f07000d9805090b0440744002803055003541a0307800d40c0d420076071103003144038426100d000604030f80d13042013100f0b482e510411000c14985561001c40c554000b248000b5035003041c8079020709566902d8043d03ea180c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 987828534 1250 987827284 987827311
    0x30c140f0901060c0b07020706090303030e030906030c04090c0e0907030b0102250f08161205070e0406062c07200601030803070f0203040501090b18040f0b04290108 72
    0x2440d40c641c144a18020103054454144000b624200701c5001c1000411800840d0810a030502c0a541c211030414103494240c0303000a10014881c210510314400c221040c1d80c4980044100b000390078035480200190744030a08203002c9601040c03c19140f130342610302c1c89607110614200040c6540e200784d0103640d00b8401481101c3c510908603051450201c0381005c8420f200e601d049080c80158440246100140341801c0108068210322034103002c2c0c1c07109801418850750310701c60240c051200030414000581803012844625003801e10700700d402031090744156a0614050f584000aa0368201041134890f10380d58802c00d41e5a4418030102d8101503110174503405207801c0c5400c0403140303408102680c041d600c10f00710b803580c2e8103112038043c00b9403442184050440d4800c000c24810b6076402030004081700c40d51542d50346c80c2d4403d006c0c4882103661b0002d4a503042442c04403007180b05900f5411400d1450001c2e50200202d010400c0d4503a000d00490200107071012031940c20904a5100708480c8d0f5010441200c084c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 987829784 1250 987828534 987828559
    0x5041a0913020c0c090408030a0c110601080114010608271e0102130803040b07110a050612060406050a0b090d051501080d1404030b07080a02041220030601030c14 71
    0xc1e2007a070812280d9499180d0105420b0180e90040002075002c5400f00d070024118034203643d4082c4980700092011070100e4541074801961400f030011150000d1110058030380c1d40d80c40d01c9085000300211034003848406040c0c00001151805400002e015850368000701a0001c003200c00c03d16070490808a0908034400c01d0f80600007e0702c101843c00803e04103500260303075680c2c442d083c0d009004041d045441c0c01c0e00204020001e1000c454116600b42e68800c1202c102c015030300001448000c4142c0c001600704d100003410100017100e0b610010300c50001101d0800000e9100c6091284005250007400034071070040188802c241381006404403501c0c4284102c031070340318040220100d040c00a921861495001e010000d420f0b41e002404030a920079042046428070f403071915200242100548040c0c244600500031420106040d01150064107200480050703015503441c0c02c9454403c415841d80f140f0034101035800f45840c0118039035040f031b6000b030003801078503040c083c1038903828140352041c503400030509804 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 987831034 1250 987829784 987829789
    0xf12030f140a0c2009150102010b0603070807090e0606250804030b04050124140a03021e12070e061c120e10020a12050c010f050a0501051201050705041a09 68
    0x605002d4210b0340c0b044070b0041c03107103054241c40038004400281003030b980d2a4034607a0340301c0f05101c40c0c0c0515810140040d403504880181c0c0100724100c0d0450300014000100402140c02c240a40c2c059001c035643e098406641d403404140c03001041c0c404e40c3d80010100403091018121450499000a4100c5014040c503082c0d40c1f01400d80d070243e0300c102da981c1071080402007441710030302c500b4420146080380075001040464074079205c21858020203190441c0170b0000c000340e0301c520504801940c1d024003544015044407030381d001e002c02c0b5198158400c8100c00b2003224402c0f0f0100309081115013407018900540c8407002001820542880030710404072000c01c0c050042415004803400e01001a1241031140c0d04003000e100640d051002d580f021b5501c81941c0c200060101101101000e80516049842d082e03804100750140071004c80e1605440e06200a00c0401c94060b4800c030b04980c01144c4502e00300902450480c2070701d600b01c8028002c25010b2000304a00240b41c8246080e80100750708103807501030101d00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 987832284 1250 987831034 987831037
    0x80402010806060d0b370341061501020c031005060d060c0e211f090507030c06082a0a050408030c15090109020a050d06060509150a0f12030f14 63
    0x40c034118090350441036a030416814080341401703000654000580d046444408400c444051403d1000d50304a0410342d080b060020786a036a0300328049005d00848c0034000342a60f034041524181c6040d00a030302d41144c4ca600005e03407800c01c3d41000d0050285101e10100d00001028014211a04000c2813102c0e000080ca41d0703c25403000c00000d0304c031510200d40706002c0c84603400d240341c901880c5040b44211000d0aa00005001c082c2e80013004c42500d00c0340300c80e6800d5001e050440340c010014480d40002000b0030a00039060310640d10b56a031365030f000d581d56080212456a1040101c400c1032070b800c140110060194000302a0005a41040e500e40f96a5802861856110754484c0c80d19800405040b0100108da04041d40c0080841009008000041d00051070862f014865203220b07000c0b20401c01d04100041d0001801400d0040007000249000703500c80c0303132003c0c1e28040c4d2485510081c20215007a5424040b800c203417001045038040144003680d068030058000001441032249019907010320360540c20 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 987833534 1250 987832284 987832309
    0x907180b070b01060f0e19050616110402070b01090e1c02010c03061a0f070f020d0305031501020d1e0c0512071b03031403150307031110080402010806060d0b 69
    0x100c1090740c60600b0b0a0049100c4010b070800070800a0015401400c3c1340d004c00704180750ba1045440c40d00300d0151011400007801c203030b0b000a80118000c90090a000460300d203c0032000e0003100d80e403201c04800403c001c00c0b44501c0350024421689000140701c0718000c1c0d401344881d43d000408aa100c1d0340480240404444222900f0005030745407140a001c480e414014240105080c0b5032005440034100702c8800c0b24003910031078100140006c689a401d025412103040000313600909800c0c0d00041038107006100e50310854001c05094542c690b0804903520009d030041403131005944018055504054020107034050810760410070441b05042d90111300244000f81d80144904a25a654102803501440407038500380c90101c07000f83c2c01300030004690450a0540d070518201e1402d0b035a590356000d03210396042408100368040c864201301104104240c3d03110760050404540302c512040c8006011503640c0c00c2200c00074002032241c00803c1035030415101500d40c242e1407007004a18108150b0100e0503480905 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 987834784 1250 987833534 987833549
    0xd06080a0f060b090c180630130506180f0f0c03120f030601050c03130603020702090a02210702030403290c0a0807180302040203070c0210050406020c090718 69
    0x110104801c0150902c00c021001a040d900c002042c40c05e0504a58030b800750b201c0c0702c0c401c010b90441050050f90b03040200e4010804c49401108a03c81400750202248044011051882c084a001c55003001c0644e01d11007410303500c00024062070342c403041441140c8811504118840c03045a9450100040c14000360f102291a0401010a40210342c2058a801402100c42c40542800c01030b45c1d0380180050201c80d8888020f0270301d036965114112040c1d2462080184940b814000a000881c0069041d00181071083c02102d200b10191540004401207100d00c0718000408100ae201c08448a85010916907000c849401030341c1c10580d803902e6003080540e02070110102880c3d1040b64082d4002c140404541000ac0d200c4a0707401d1a17000c404c09031082d00c025020300d051000c4090301c003d080801e0f10102018590290045d500c03400c01001c00f60620b14181c100300d01c150900300600e184035105005460455166600a02c130502015007441880712019000303504016000f4200b0075182c0d110640c400050592 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 987836034 1250 987834784 987834803
    0x7062004030c050d0f20130b030c0409170d0b0f060a020303070c02040213061e02070806040f060204171b0906030a11061201150906020c090708072a020301051e010b0d06080a 76
    0x46c2c800708520b1038500d1807030078001032030030006050b0342d20001441c030040c002c244c40016445455040410342c031841018284250800000c038813020080c1034005a12440301600c080c1252a035020802485010341c090541c01030307100748005954244078030b903500c583fa03001500040c9400500564000b110314290072580100d900031003203503003080c03804401800030203441c8060001e01d81002000340c0c54210203840034080600410603402403011680c11507005103600c07000d0403004000e640b141c4e81c0703820481103001c0c00d41c4205002c044a5040003c1100e2140303034000c0180004030395036603600500c01c18217414180c12010074880e000320b50741c031104540c5c060040d802c010b003603d0b2a028402003000c405a04044115004810f424842e0786401e010a5003040303943c14620b04543e1409012500706040c2d00f4a0f00300d001c920061000491980b2a40c0800d0314001d0b0020f1006a48410070428480081003846000800b000010090241c1c084081c0040c240440c5001c140c0340c0d40c4140841c030307041803942e083d12a07410 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 987837284 1250 987836034 987836093
    0x1104090c090b040f030b0702030f0409091103071802070507030614011a070803010302090402031014060312040807150215013512030a0b030307062004030c050d0f 71
    0x300304025400a10402c0d80a03850107040030305404081c0720303510000b40418007200100744402d00034400d84400e2201100140e80382c996912004025222159040d40c0030041d64968400034100420128140c81801c0c0121040280b0607a9600082d400640240c402d40283c8101200080701da002c2d5205561025541341c03003d50404400c018074140328050648088801c0203400000383c1d0340b000381c0f81101d404891013420769582e030010a0a28412420140b0080d1801ea04420320009030384009000e0001642144e215142101d40b00c0003d20580c000c0c0c1c0000da00020041041c11030300c842030004050f0270705c10345d848460340a50f0701080340c401fa0800e42041c0d0741c0301c01c440842d0050903800c224044500741d815240e42e4042040030307150710140c2c1490074122000400a1129000f80d0412440e018000d0100c99540b103090820a00504540d10485900310151408901d80c00c000020b503010340e81c002011810091510040010030900c404086880300c3c1581107800104040d14403403603854a20080130022901c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 987838534 1250 987837284 987837287
    0x10080703150513050604080d0b0315150102010b2101021b03030601170112020103050408090d060209090f0f070305090705060a0c2a1205030c0f0703060c02030403030807121104090c 79
    0x5a00400301a0785102e50f688001c00f103040021542d41080e08807002d590345140c030a6840c0003600c000d04804d078240c460100e20f00d04410304400c0640c072526480030340f0320a12000c17400490980b100d142005034402c0268a961454001900d441c0c40803803401c40c001881e104c456451191a0910a0101413140d0404420020203507049421070488801d0041400c05560400c4c0350345502001001b40681050307901c01c0080c0c10071421408403161584028250b4400c00c03007519000000e58002d000160040c40f08d41c01280016015030710711805840e4010b1201619a12604201c0040c480101440c440d4030854600080c03549071030004000e202400e0f42c98039030b4005281010201010f029412001e14a19a403152503203c00a9841005943c0340180400305d0036134608005107140a0710125407450b0094140c080308101c400500c500c100ca204030414044011125000d83c2c0301c1c0141d11001d0042140d46000443c000c1c070900c0240011750002500288001d240028214507130015000705280d01c2c1d94401400005 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 987839784 1250 987838534 987838541
    0x3022106180d03020f0a030c0c0c1518050f10030920092412030403020405100e0903120a05070c0b041506050402090604060e060f030a0902010f261008070315 69
    0xc280f03040c150300c1d1042d072441102192040010b9482050740d1000c200101c9071280b4444030001c2e40041c0c540c0b403529111640f180003100240b1607507010403801c01030039280021075030a41003254402000390400e0142c41040c0420014444028010540d032000300c00c000460303c078891111880041c046c1c4454210400610200843c045e00d1000c070380c00310354800d020750544211480c900c2038040d00d00d0541d0a1004040c14a50700890308025849820001001203c01c00c85860604580c0042d800000e1516080c01c0192a4030078071420a5124890300001034001240d17070016908841c651401d8181c5200c140ca0300007080500b0780c3c00b2254501040003450102059014450140c00100c804500e0541540001005403160748100000e22407255850002ca60364082980d001d02155041c0b00e030b403443c0400604006000014049020685820b29034041c00d100344020020b1050a44010441020f00c5142ca10010002866500e0301c040340310022805400610058009500c44c0c040c3c444c0c2150100500c60a4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 987841034 1250 987839784 987839803
    0xc0b2208060105010806181911030901090318060503010303081003140a0b0a0b012f100605090c0906220518010e01060806090f060109090204170d08060a0302210618 72
    0x60740140306045030700c0421b608682e000320040c10701c030350400310348c10782030001c2d0181903101d401a2201104011141e801074108074990b52003587d030810308080840c4420f61003000c0d4028040010710030710040c000a4051500d0f20340000c004003420b980c0c40c2d901d50313461820404418155100e904584511800c02c07036510f4000d80c021001b0a803d000e641c01d00e070b00003400c40201e0301032600c220507030a003000c1c2e1003403e81d113a000060141c8403e640e1144100700c0002d0290015106050042452600068120544c0c509640241030018642454004850328a4026200b80e1591950800c3e68002c001010f81e600c0c104481c05180c1058400425032520007400140a81603000700144500181000142d99404002c20b42c0324490748500011b44c0c807410700488040342103800000340c080c03000901169070301200110700d000d080100c0440c0c00c1e16000c540101e600c004146d460980000380e8a80c10700052801c800c14044021003101620380846103034010178908182541c1502c501a004010095000d009001c103050 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 987842284 1250 987841034 987841039
    0x21e010306240302070602070b070c17120c13050301150e0606030108030f0c1f1b110709090609150617150a0e0c030a0501050109180c0b2208060105010806 68
    0x7800a12440800701405040c1c0c2c00348100741d0700043c54403c2060503415900603c1c0c00c29030140807443c0404001d0018400383c4400e8580408038030166030b499003544116104079500041090158607061800070b582d0300006d08185002e181755030085000c1d1002d2042850b5441a05803410710b01c2e1a10101a2100a002c0c0ca854041c440400c0140b0288000008480c103111310301500e60b61361603d07004110b007010146140d00c0c81c240721003289020139540580102004244032442d90003402d101c0354050b80c0d2a039146110b610a60090901045139550f103a109500c500e000d03c4003c00c002d8015620400241031012032003203080e81c0d07607200307000c4100440e44001031050030304010480f46100c01140c0300c050303600405880b0300d543c42c4c940c1c82e60304510a002e41510b412014045a00010035454000d028000900403061920f1400c60110004c0760340d40c0c2030340e40054104001040260a112850320783e0b6100050f0b03003a9481e103403c4904601340d501039000000708180b5020305655414540018441e034070140000d031 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 987843534 1250 987842284 987842309
    0x10c063312020904020a171b090403170a0e1906060e13081308030d06030b1e041401060b0a05070c0e0f072f0a05060702160909020d021e010306 63
    0x1000a204000075114150112035191450351180f000501d4004141c20800e41c040200143c132411b031300e002401007105101c0303c035024001400101800910801198013800180320901100302c00e0864926041c0c004803a44000315545926004452030202000d82c920034203590180000d0510940b4890707140500807011146032103040074030b100c0703803001c3d4002c10280811000280c031213000307060020640000c06041c410303a52645841006c4000600c0c140c441619240c000b0300001b22113041c1b2940b092050000d98a441c0040d0321a62140d01840b11071401c0d4540c15940c07a140803c2c06000500070b40700c90411541c499564006601d000c9044100a501c90440e9034400414068220340c0c00483d2580850385241044640360521401c00707603000d014a80c5082c14500c0c80f40310003140d2004c510000798500030401c0350110780380c10808a80c0c0340e0400030030aa0404c01e0000c203004094a03508001c261500061000002d2041030300010011802071590f2000c00354084061806542c05028440041c010030700a00b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 987844784 1250 987843534 987843539
    0xa06080105070c080c0703020a0b0702040f0507210b06161b1202040507020111040b0c190b041212112809050d0c0b0703020f1902100c02010c0633 64
    0x9020f05aa206000b02030401c04903c0e01000d02c420011007005640043c0950b0005075502c03081e4406038020300c0b082c0d008600b00b240d011448003072800f442e40a01d1295441c9002c01800300250501c5526280c50384032005d464100c1c0d10710f0b03940d1b00b00c080c020080301c982c000c891401a074a89102d40802c8038a02d112035a43c008004c00c502e903281d0300c2c0d4880054059401142c0e0755500c80b03003240140306024101ea105440410041003282c8003902514bd076100702d10881c1c03080c41948015118091060310000c082c0c0220100082c0005d903000891100c0c030340b090030011b041050b5840c6030802c0e101c0440150308190320100d070740c482c80b60f000003041c2140bc40e048042c40b0800c10410005004c00350754090140220820f500c80c4003040171400c4844001e00040c4c500300d4070f684451074025100d0700c80300c0e080e180922410f02d014005502d08130658080070b5005040704590080504123644d04007000b00c00760305101504541c0c0700411414001c00450b40d0b0b11031402e851202201089107401300904d1881c050000004a06 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 987846034 1250 987844784 987844787
    0x100b060403080d0f0f0b0328060209150304150c0c02130b0d1a0105010806011830060501030b0108070e011a21150f010e1005130e0a0608010507 63
    0x1114107498024245680e42c1d0380541510025040300c9011030001881d22194084d0f132141d6622800081c1700880644000075056008000d840740b001104c0c2c0a8400c0850030100001c1c00c1c4d40c02424003600c00b4246021640c0072404044c15504210b60946010115940d2010007541034410380c0c01e80300d10340c1440c06601e0180e80210b840010107010800d140707071742e0b009502d000781e84040048860b07540c0010406900c2c1034488000c06002000c0c880c803408103d5aa011800c10340c091a2500b002c440340140e00381c902031030020001300d0318845078100c0b400320582c07041819000d44c0950500742e040e8062240401c5651551a009101101c16440040d4a402207203050003005d866016a90440301030b0406030030748181d44000440b1030310514132480c003400d80440b025010300394002c406510484555510741d100742c0700c0f2820b1081c00e940480380280010700310140712007503190424000400b01010302d080e5090141202d440c00014109820030511202403104000410507113001d94000b4020410081c4030a04040c4070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 987847284 1250 987846034 987846037
    0x5130207030c030806011e031d0307020d0602031905090a020f2209050f032101140f01030203041a0907030615030507030807170316030b0427020619020f100b06 70
    0x5000f4104079940010030866071040c042d80b800905100007401085c905698064020a2056030380e041d28050509071000d01c4501105842441d038000c0c0c01ca0032040000e03078403000258001001d20720280d1010b80c205405000c50321481b44240b0407240208003490b024010081141c011312552071090400c0030294046400400e0400c80e011501074011800b00c074189401400e11200c0c40440a10b03105c0480d038901d4031130580c1c0c1402d00e010642c07610781000c1d98031b8120219401618000c0280c11002c00c541070645035210358029544070340905411503076201482d180d9500100305031010010b80d880b0740c40500600070284242c1381540d001036405150790b403465403601d80b905551311029211107008a107800130f001003800d001c0402440100520b17920300d0422860202000d6099011001901d45020308244d818117106842780e241d485234404c8065845108008884080404101d821500921201103244107450b0558144c80c16038001e069000002151a4988200039070002400d50514090f80070340d031101070 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 987848534 1250 987847284 987847307
    0x105090402090609040f2703080c0f1605240f040303091b15110339060a0209010e15070201030506013c031118030c06040f0513020703 59
    0x32805a100d00b5071100140f038a024160b8a00d41050a040717042500400310380c0800070703054a401c629540340030509903000c0845070320540200810442408622a488403c0141c4502a0106101d83c58440c2d00c2c881001c841484900454680c0d02049216280d4040c1080000d00e541401d8bd494a003850b000300386494415001d040541859625070001040c00148041c03c0c2d0919884a014004a9540d0305010a119150782d0544001201441c0340340c1424000b00031100c2a2410f02c0c0070350ac041420031001d40001c032040280000e045945a10780380356604c1401031a208409a00d001600c4600b040d00240c603480ca890042440f55448158190100c0352074400d4407002f540a00e400503855861200603504007040c0341c0601d80300c0d045680ca180303200f410700c00d00c03540443c40d0380e02c11000190903003001c0e02950804110545c03244d074103200307084841c200200b00c810020070040c100c54803014840007080003580103421642d00b90885078002d103c81d00b05080402d494010f040313011403410301d16850007000e549818 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 987849784 1250 987848534 987848539
    0xc053307081c02040302120307060621060506030309030d02071a090607030c0c0513050901240501050705150f0702010606090501120e100e0f0c090114090912040f0e09010b010509 78
    0xb003011141040540e8184c40c003850b0702030090312502c0040858142da070f070048001250410f08100000ca900c01c131480d00c1c2c02034607a607041100300c0c6448940e90b8801a00000301080d405100500c521a080d5070201b0201b4010442c230b4024241107810008201c0381c0503e18950f0022228040010b0302054580800f01c0e1885901803904142648003450721050390140c44e8407940d80500c0b01c0c100300e000000a030b0300042c010700311103000b00020000b542c160101c1c0c0742075800812140c0202241081030354004d100905916104030152114007a06c3c540c1c0d503107002001c1d618604000d42220401c2050340e0244035100c040d09841c2130540a65107801d00003401e003803003040824403031915041403000100e0104015030007410314a005020116441c540e00d40d441e582c0256540c8544510980300c400e604141000a0503a141c0c114101c880214440a000302d82c00d0282c401e074000c0c80354003030052580d44104054000b60100f00c02110031a450703d1034018841c50084d14443e0704e81d14050090060b40e810404a5504280a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 987851034 1250 987849784 987849817
    0x15100f1221020c061201060314040203061303140304031e03020f03060402092103130e01030503030a180501060b030709080f0d140705010911090702030f160c05330708 73
    0x1d81c1c030128100030b04150840d13002500480d01c010700305101081141a030b600d960b020001203403221248200600c099074065016002000840c6c50140c0300d580d0011601e000e8100640c60500c10110180103900440c0c0c2680001c8003003420f105007a140f03019441168419240950a19000c040c0d0b9481c24400505850310599000030400742d552103c2144203c0550000b41c03c05a528440000320345aa2101a44a00008801102050414078010124180c0f40c005004600303654800c08118010988059103a81403803100c03140702c0009409000d40000341107089000354803401c1c496000740c41d075a85500070440c0c60300304801407100403c2c009500420110285030a448030780302520b40b180ca0740308070700000c0e00c40d5081c1409401481204003c00040c1032003034410b08000c0d950441c1c200c1c0c59024000c07003800d104000f0081000c2d5401d00800300e52081e8003031180d036242940d84c1d800151010320042c0d80101070710101d02144110000130100340600300d011280d810303c0d240c0b031561002003920030440b081030200710 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 987852284 1250 987851034 987851093
    0x30806010c0506010e1806090f070f0b090d02040b06070c1802160b06120f010e0c0109050a09050a020f0a27050f06030c0d0c020304180b01080f040515100f12 69
    0x50280c052046c800c040010f80d0500e080c81050107880e242c00e071400c08450310030007000007a21f0b22841c01e00300c1103600050240d400c1c0b03501c250030050f00d1490743e81700b13a0780240c6031a102600c580d103040040814920030803031084258900300c40c101c04e0004010188600c41d2060280a40e0030200c0404139140c03c0c0d214003844e14907954600004d12000c407a2b04522150711030080320341611101580039650001d0700c50200d80c0c080322400c00440e4600039501650350002d40d00b860030001c8022503080f4580007a040316001d4101381c001700354212950052522000000d5440d5220b8240043d5034a041341c050410b1780d00011464101004114040e941d20300c01c034081c000010000e01e0f4640b40800f528003d82000a0a20950182d540020366940090207103000d42e0984441d501c00d1a0024070078500c00482c10303107403034229640f0100c0c490300d81c07140184240c07128018040607442601d420f14081e442052402001400b00e4204580030402c04403070380203640c28413120b54914011901101c0241503030311a02c80e5080303240a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 987853534 1250 987852284 987852301
    0xa030f03020a0b0106200d02031b12030403030902210601210605091501090b090406090819080907080a050c10020a0c0f140301150911090d0f030806010c0506010e 71
    0x9507060010b8500a00c10300046140350740001000064811000394070b1000303608110442d107c0e00c0031007000700581e10400090941504180150f40004490002d58100300d002e41c080c01c80d550b204507000c03400030350303030310600c804600d0f10115604005100e40340d6800034881c01c03030690381d55a1041c056125507800307a04020480f0040c082d0b015000b130707034030800500c840d0811030a0282e4626000d52800710880c00f010020420b501c252003543c28a400041001e00103031900e8075144002d210408050311070040030401c04204cac8001d0450445511915a22081d261070101b4242e81450343c250480070013038100301d0f91079000c60800145d0010704071007201c0c004003070013049400307914100710864000c1440d60500400a00501c0d0f06c032a000c100c0d06c003144a90b40e811000d2041500325103003404100140c01c1242024065045030741e000490300700d4680b4035a40307031064000000364a096004401c4810401c0040314200b01644102420341203a428200510000300c0355954588800c4140203102003000d0050020b118907 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 987854784 1250 987853534 987853543
    0xb060a120c0311130e060103050c091b030421120609060501020c0609030f060a02090f04090b13060b040e100b18193e0a020a080c0a0204020c03071a0103020a030f0302 73
    0x20012201c00c101720300300419400e480f00e0003440166440d0084044401c414203120800501c64040c0700030b00c10300f9900f05551a1150b81001d0000d4901102c804800701503002c1300400a1401c044a40b10440ca00d110142c1342c0302925015040245121b040c244100202e0342c0001c0c5084051400303c800e1901c1d249034001080c03501d10500490786c0c0910030401402548903031980180001202660b5160943c800601444242d840000d8000c0204160b580092186501c0a0088003800e10072030001c6402046035000409440200c00c000200d070b00032841a01c681c02c01c600c00c2d4200800191404800c05090309224010312100428000900c0c1000600c800c007050b4039480740041c0304452070481e208034001c010419080c2c030100f0700c8a0b4002055204003516041013400d440828045500400088c00c5583d200a419086560502c80a1080881000040e55280080d02c000a244e000440e203400460800c83c5100d140000b03000d456907003810061015844d01c3e4100750641750840d400d500b139014945000c0345070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 987856034 1250 987854784 987854809
    0x108072102030c19060e0612040807050a1410051006080601050c10020f0c010b010201050c030c070c03020a06020616111b0d150e01110c060106030b060d090b060a120c0311 75
    0x40800c1c6607066019803070711008401178a80960b41d008040f9a02c0041c400c0500c5145001307040010200d0004001841d460028440d0b54820700c240c601483c07280c0d03250100055555120b4810348c200265000c0b14804603c9125070294503445100c00c0c0b40e1400b0341c094a80203014200f641001030000b038512040d0010001c00781c44052078641196211000207180301d260308454445003045d42000040802c1d588140140c90003090070400d21803840d1100c0036800d9035a8003503081211801e044d55400009a0b44a8440c103000300000d401410040c07800c803500500f401607400152041c010428141f140c00003002401600e16100d07a04800040040c1600046000100c010028010b404900c0c0704070411003240c200e03006070b0010200902140304c0101594460380502c908002d800d900090040020354442c0c2c11044509001038422460f0440c01081e0340c003941e403025001d5a003089242c00340003042c00d100000c80c0081546280000300d081540e40d40c0c401441032440b001c1c0640b680906407003241d03980c4140c241207 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 987857284 1250 987856034 987856039
    0x2303042604090b01050c0c0111010905060f1509040317150409030c030806041a090402120d05070c060f02031e2205130e0604080a0203070209040b09060108072102030c 73
    0x52031020300a2644554000d0003904445403c2c180c0c0514154000c5c0d09030342803540414090403200020750011500d801d11101c4081c9959210004480031039001e0041d03e001d0502d20102c2c0089252441015480f0904403055500074a0701c8010800840d912110041c0a0424003203484002c0c0c441041801e1b00766856100c180c0d00924250b024400c0507000303405011454440d071181040c1da96801c08200c104c2d4100c0d00540c1c403034801215a031120340342407000319074030034030003080f41903802080b0100c281361040030300e6042c020600c001540c00500100303c408000600a03450f00302c01c80c44a44500940324001c410000c09011000a50001c00400d00c0381980c41c1d51203899401030400201c240000c424201500c034181c0108a1149000f6001c00c140c0210000e042440d0700520301910b03030359141d8205500061411046000c14004040141e480c01c0c0f8941c001c0e03004a200c0c02c43e50901d030401c1803c01070180d00c00800c0c0d40c480001040002c485121030702480c07410500308414100c042c00800d04000c070303145a069 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 987858534 1250 987857284 987857333
    0x1080103062f030601111b0d0602040f1e0b041a0a02012d050a020703050702091302090114010e030c010e210303010b190212041a0910080a0b01230304 66
    0x2079980c2d040c0070141d480f034082641c1e43c00003081e401c41901e84a136481c030300441402034408440d80441c1000d103290380c1c0c0d07a8802c8000619040e84d0307806131203c0c1c0b5035540000504003003e1010138000b246204084014200518006e85854504408803c408295040f544d2050802103035042415000390310040103101d40c5081400c88840d19142406910070207043d5461042c42c050200e10316038828400d440d04d495158981e41d15000c0c5035020800115401042c0c00e00300c80040c00c0c20030041c0c86030070086000b0500d841c11100050318a100244c1014840c6580038002d600411282017680e9010f135500c4282e03a82170380d03090100b02c0e5030078080040d442168000401440000000a03100b240c8000601c0e09891100300341140c8250302c901240c540d03541c02071018190900340018441c02c120b4020149888560070b05a924003003042c030210b21001b40903152130012600000400004d20380c140510002e11100f440c02e0b030f80e2066600000303079001840f140b000c2030800c404000242001130659541e009800740480c9031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 987859784 1250 987858534 987858611
    0x5010c060e010908090117010f09090825020f180609060f060705030c07050910060f030e011a010f051c0504020d02030a0b061507050c042d060e150108010306 69
    0x14401d81d400f00b800580098044502e449036401c9a0b041c1c01c0c1a90900052791304464035110807a40601a01403080d0760b07107002084001c0c10300840d110030b4104285c01c000f62401c203400d240100020f10000c141c115000d0254400003001880801b402d035680600116149000b9440301c4001c204000703100d280f00c1e9040f01001071000701b8040000702501401e8068401c5442064845041c0007814000791003c0707022000800d001d100990013405448400e081520f03001410400c181239040c00c1d10500c04e207000140e000c01c90001c03140d5030320040b10116020300382421864010640280c25130405a00100103000390b82da0003050840d80c1300f01017145404d400404032080040113041c5031010341c0c801d607403080c03041c1c40c0514000c6100411105444902c0c0e00f0001a150054086091202070103009080f0095982c1c0d2920520b4420461600000d400f10039680000b1124140745401e0703078501010f04029080c007a000c0743c9006a84e0302203151419660302100104408120141c007900420301108060054007602c00c48 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 987861034 1250 987859784 987859793
    0xc260303071808010c0518040903050706020a0e060f032e0612110301081005012309091f060618030f03210501090911090f01060c21090609080c01050405010c060e0109 73
    0x1404800c0c150b007550f1010a40d47c4800c00080304c4041c440240440c50601c102c802192040d4050050824030341465680b50380482c0002c0c034541e122141071410401d0110030320144420307580b00c5110400c004c403018410800c55075910008220300c3d00c40d020400142c0301149400c80c0442d04920841d054850785c1c00e03102e5031600d10060b2210f03414600d02c25201d1a040002402801405481c2c0c1049000c62106a40b900c1900602ca80d00d200100460101d200300c20040070f8030f40500c5504034000010980000b603860810900500700c418103000da0100342e40c0e0341014804070341d0280380c503c0c0d800e90605082070400100e00e4a90b41e0341140081c3c05281c07070b162800010300401260070000c001c07032040300c4991070201c0c0a4200801c040064032140c0d80001000c0043c86101e003e880701030740c821b004582d1003138808540301e41c03943c000c17900c60b54510000302d10039000c114003504032182d1009014143c5c0074000460034540002c3c00e90207130f44911410490b41d003501000b4003015038030025258074000d009000118180c2403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 987862284 1250 987861034 987861037
    0x3203010f05010f050406170c190f0e010804021003201612030e1b03030c01020304050c030706090605031501030e03070b041e0f020d06060e040c260303071808010c05 72
    0x981e5003c41c06040f40e18040520a10840b010f44045031078070b83d6070070200307031007100c036224020991703068548204202d80403502d0035180d0030020100d81d5190a48180400001090010001d80441c140708180d0301f8080181daa18a40035148844d0b4500000c003031070700340b0307014025040505010459220004030007642f60042102410181e0142816003042c40322400103d0444841d0005a0345641201c40041828404502c0107407001c100102100d040c27014240035103003283e20a0b6400c03641c0c1d52041c85480c00a09040c0400401000a420181e40740c03450894007400d9840010110001c110b40780e1141c0c00643c3c00b0fa8065131244d4185000c580d103031500c81ca45a40300034016101030361440b10382c145105510101d1803000c591564040c2070f02400c2e0800b42d00340303c0c0e8100c041c001264101d0315a0b44c0411208003807040203103d14040c0904c100090300c2d0840f614007400300f2a02806c1c0700c51b49980381c15001e80000007100e0300041c880c03030000b00c3c1821680910203056040d4000072071315400e0080c04040698042c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 987863534 1250 987862284 987862289
    0x41412070308100501051c0c140d020c0c06250302070f03060b0102060606040807060804110409080a0e0427061e02070c08010c0804170706110705150103033203010f 72
    0x12503c842c40e203900054500740141c4a40d50158031004420140500a60f08031107005485805d00e50540382c4134520040042d000b141d1203108440d8081a03503684918100044802203506544d050f2900c030252a1083c030700c004140c1c400d00c0500601140d5401c2510030440c58008009a6940e1030000d13407a4a090b0f00646800c40000e8014420304011840501d04001110101d410850080c2072151034604141d50210004100742c8005401444040080d1141e0080d2403040d072107044c1c100c0e03880000150180010110b145400c0c0035615101401c1d0f40d84c40d4417445e0200c0300688403c4002100254034141c0047d1541c1154080c0c0011644407803603103000180c000d021403912582c20484a10303103415403070b400c0f900f4040042e00010a410080b9010843c1c6a101c04030b51074002582510f06543c64484005507410100403191a080020303904c014803005003c01407911340c8071030310f0038401d5245480c01058104d000500590840031004424403400e001d2100c543c0c42c80d150020161030f5a0341d0303000c9001c1a4041d2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 987864784 1250 987863534 987863551
    0x504150306140702030417210408190f0605090123060f010302180118030503120403080f090a060b0402040302151b0f0d0f03061809021314041412070308 67
    0x80c69155040b00c8005241d00c03d003107681c000c40c1064544a100b40000181c51000d1841307000341721000d00101080c018080c4c4125450400c50b42c0e592512141500e003001d01000b0a001c20050b4500100281c0f545114614498002c0008a210b40341c0a198031f00500300103880cbc54810054030700e0b00c40544080d56095100b101c04845480b9074014400c01581a44200140f1240340c0060300b100c500d02390b0140519606200c2088011040c5c41d0700c1e5555549191f201c40300c02918062100c08000c109503100d1843c82d48161b004003103c0c4181081d9009542e02c59401c0d8000b4000c035140c12003102580c031641d052307030015600142403100380038201d004000281c1c0b001f031b4080700400e04d04103404c51040000070703070030407010789000141000c0c014032000b1600721f190b0450402c00c01d52240d00000380c0c90381c4100240b17a0690340d6140005c0c450b400c0c0c0704000d520141807065543d21401d040040045400d11407442754456040a41c54002e030281d856040d003000040a50104407a10125811080c5540070551501c641d649 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 987866034 1250 987864784 987864791
    0x121e04060b1003021224100822050607080a02190309021008012103140d020306041a0a0302011103090a080609010614091f08030307030c0305150609190504150306 71
    0x8002c0120181d01c00c0701580341032412154045110303440a0703400c401c0400d000008140c41d40c014000001ca02d0b141e8510340d10300158034007017480b610078035844000003210980308049000401c01e41d44c90351181d80041204050000100028a8035581078044803184240b030064182c0410082c44090700400b22000264001c0700b941450b5034800740681110340c1038441d03111009d0343c9090f402150001d03541004070114100400c80c42d141000030b84034070280c1000d59120320056102e241100612003108c61054900d10902c0d204085181c86440f160081015a80c0a02e01140001c48642500b8a18800d110aa039040188228002144c0201207034080c02401c1d020004d1019030f42d10682da546400a22241a03882081ea4001c40d29032040c1041c0d840580b410101e14440780c558030441c080c110740007166010f020070344801d40c0c500e481e5414819240d20280303590501c0081100000032801c50302030380c041c240c05a1981c0d20100d6550004090100041100800070300ca59119059098194402407004403141802e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 987867284 1250 987866034 987866059
    0x903120a0f091410150503070e041703250305070909020c1c05040302090a020702010915030e061503010c0203030f010303030b0111010c090e0c03160503060a05271803121e04060b 78
    0x2d1141c051040b108014000c8c0440360418826124122010700200c0d45440414501075400039040040c61003910341d030030704d021800030740c1c4a01302d180403000280c1030405180c0700c20000c0c80350b0030081200a84a02c10300068483c984a41c40b03600e08030314502004071000c1266158000c03140d1050050081d40e100345c41c040b0003504c84001c2c000681c060a08003d010601e0f001d01800b81a00174582e808175070f08149800300d070380d406880f1980d0525005603800c05581240d200c42d600d00b8113003405000300508681c40103515625083d848401c002c00107000060415496600060304c603849a12400d07202c4c030701e10300200302601e280007026100c00300610840c0b4142e0503080011b4490002030081e0780c4500d419044920040000501c1151243e02c02070031240e114824881c085401d03220640c5500c8205504000401d403041115696241400010510714aa0700340b20545a82010040103881c121091950700b0f442c16200c81a0070f41c00c01c3d8104045000d0814000c0c100000c0c8172845e00101c1d580301c2e00762500c403500b41 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 987868534 1250 987867284 987867311
    0x30c0d0819020a110906010c060507080403140403030e0d03051e0408070b0a050a20010e0610081204120312230a0209310903090306050903120a0f091410 67
    0x14403804003a26065030a5413500301410300a17901035004005150043c000c040380d546040403108240c804000080748031007007008041e00440000c907504803100301a07003032070b2a42c0c2c2c00801c04c5141070b00b068090000b02c13505008040c0542d065513280d4501e540054032003035a40b4640a1560072920620080d0310401c0d00020701150b01502301c46000c122079680d14509440400d00384d80585020307040c0c4500201407046413a4014082c494048204068409040340c5c0c101080258882400f9420451507500000c2c20908881d20303a004a4084418004820840c4103041c10b0590302c1f0454940746c000b0080c106a182c1e040c06070410f00c91038035203170301e5042f07000b090b140c4074010b0049000c0e039070503a83c200b03868014020380e031918003940800d0781036141660080303e03003180d5107081074601a400031404903031800002d01c104052402002d9121040c000250f0030405980c01a886400010308421411642c132940e07480c01040c16046a5491608000d6201d82c1c495411402a5501d52000754000180d02c1c01a1aa103040e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 987869784 1250 987868534 987868543
    0x6221517040b0105010305061f170f010b0a0804081207120c020d0206060420040b07020306130f060509010b0a0b190c080d05190e010c08010b03040b0f06030c0d081902 73
    0x85401c00031902e503a07820000103500409028065a92040c016000384001e030f482c500060624041a07510744001241e1b40340e4400c03a150010f0851051113102c1070041c0040c00c1043d080d124443d60358030f04400300b52124104241c0c40c1c4280c002c1e50303e02c1c0304d03240f04203e4807a4202c07034000b00048800d003003004031200c0390703608030713150300984288600507080000491114a0150010351000b84041d01203007032801042d04400082d849940f24141c510004180c9034150300e001c0c0091a4410100400c41d038507060a035444030403070320350000c00404507030f600d402203240e502095000807201c0350043c2404050944504061005070061840c2800d14a01000302c0300201c2e10900031108015442659981846011840180541402044546010b040a200640c54115030007002d00c211000e0000250909000c24024a60b641c16000500714000410500000500d0540d901c5e80c80040443d400d40c4a4413600c0009080a440e035007d0f82d40a22040d01c48410300940c940141b4030300c502154008441d20303a680050b44c58 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 987871034 1250 987869784 987869791
    0x8060f040b0a030809011101020408010e0c10050307050f091c05010b0d0f0807080f07110108151804060204120b0a050603070617090c040c0305040213051506221517 72
    0x2c14981d400c000007980c1101038140e030001410800c40c0307009503281d82c90890b00250b01c02017090303440e4042c44141d80d005010b403091a0a003502d0114040c8400c1d040130f40984000303003004040080000d1120281c900350410780c3c1e81c2500003031940d60001c01031054502d503001c0652040e03619501e84030440764071f0700d0200c80440b03015a1040303000b01e00050319120516260405071058405900c1000250b0300e0b06040300081c107946200d00c4400e1000f4400000040036010010100c5c0c881407944031180a49603118041081c11842e101c400300e00369a5980b030305030064007580e8171a00e1505104000041000003075084988901c021000403c43e5990f4903040681d10f80e15032007003c002c1550860618401c00e50156110b91000300328084604a81e17441000c41c0803220b01302030780800243e807542030004514004034650845226000180303c02e0408a10380c00015034400b001c2c138817414000850000a005040303214050021752460040c2c0d60780d45800c00d040c0d910325855000c0005952505680f41010040d0440b0701 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 987872284 1250 987871034 987871039
    0xf18061503070f0c05010b0901030506101a0d0b22060503010e01061512090516030b0f07140d24030b09010e0a0f11040f0c03060602031c05060a030f0308060f040b 71
    0x40001c2401e4155400c0584c05400c0d83e05540301c50783c1100345d031a9010820b00840c4150000c10481c40d0600c0c0046079808035030090302c080700400000441105801007541e6201c0a400c90015405c0c43d5031002a8184800c24a0004480800740e03400e44806020391001c0b0850300250028000f030035640341003508036010380c0901050804600d203c111040d104034801111007214140c0007c0b14407160301c4407031a185c0f098402011858402c43c00784100140c030039640c4d410151440310b451060030003200c00780a00c40200080200058007090113482c5035440d4200d00003000500030f4000b2a5212805482e041c04d007140000d960b10301c01400890807100c3c051003050180c5640402074981c0c003a1607a290501d042a12606a0350207443c080c104482c1d40d51485403080c5610882c5000944149100002e01500c03550340c03000c030642d0010700c0544207450351943c08504140328070700c0014143c0d43d031030005801e1031500d4102030428441c42500508054011050a001d032000b1500009142100d0b820401a1400c3e40741298 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 987873534 1250 987872284 987872297
    0x6030c12110403140a08280c05060f0702070f14040e15060d020a09021603030c1103120601140a020307050606120c130f0e0606100302040614090f1806150307 69
    0x854860501014900a040140c0352504000e448804154001d107005c3e100d0501500c0141190420b01000130b1f1594100d4104034085545603100d803a11580000c000402c421100000a01d14504c00d007e46000b5080002c1100600c030b0b15a090601c6500740c0001c802e00a901e0303c00b40902010000801c0b4a25401412130042a80c0e980c40605c452003040c49400c90304a03008120118107089103001400d840d2082103410ba60301400c3c0e050050945586400200074081d02c2daa484030f00170008022500305000800c04c3d800651103200040b141c001c80b02c00340103115440072032020f51071507000c401002010301640848485807900000c0210344a0b034051102a030390b0040003420914140204800304084808100054000003082000309441303003d104209141c10100402c41545414000d0750004a210320f81141400d00701400544000e51560a0101c0c80c0400314400010b56585480c2455110000d8514000c03c00d407404816640181550b00e644a405c0002102500224100070340c0d00c00c0401d5614607 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 987874784 1250 987873534 987873539
    0x21060f021216021f0504061d0d2a05030706050109020301050a03060c0903140c2409011809060b0a120c0e01030b0f030102070804060f110d11031306030c121104 70
    0x5090891003070b0303100158015400c62140c0500e008a480e101d540b1070344400b1034640307442d18042c0111441d40c2c10030448410581581081c080c4002034481100d40305017440000c072010141801109030ba2240c0c6c0843d002d0800d20207104212000c0050041140f0981080c0102e980300d01585007640403d0141a40104030318000300041004c0341c01444084a003801d04c59501911b0361102004114000c0e5803901542c407621210216041c910071082c0d00d803290708a03141d20780c91014841c00c614860000d6643c10000c080c150408280040038000005191182c0f041019540d200d400428a07000807056038040eda401585401c05035950040301409191951170882d4018075000560003403007107080b0b05070040c004002c134000075242440100315142c0204101c2da11039141c031100918a41c3c441d54104208400e1346e030002c01c6a4400500c10807003c00034180303c24400c070700c81e410a155000319140002019012040000c00a400d9404000018880d0340d82c180e6015005070403800380c03003525004110b0b000c001c0004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 987876034 1250 987874784 987874801
    0x50d0c110423010b1308030f0f0318030a021507051c240f0801061208030127090b012c060d080918250206150a21060f0212 54
    0x2002d4039020340c0d02e880c00303100b211050b49011070b4260405038540c100040c40543c52070009850600614000001b1841c141a6065840b01405000391210070f006011004c03d01c3c07206826681801c030300705d220841e6105d040c2d442d0000e60b2a000d68104906501c4094007140c00d0a125400302d64000c00c9444400da00000329582c3d20000300400641440039049c0454000c41e07101914248100400010009a01c07413814003000608548450344000c0300b40f0407400c82c1c000010040c8082e28111607101c0c1681c3c8590346e507051104041900030a001243c180360076034200c100420590001d0682e400c1c01c55407943c0d4450704103001040d0303c3e003003509014101084001031483c9401d0000781d01380e5100d030300e1f014242081500802e5646204040380c00d807040c107030010888256402c074942c40501d0800394038440c12800c0d803400079484901c00381c5104410380c106a440003150715030703c0c60300c0000c1c0005101108480078003484100d00383d42c4206c0031206903040801da07500e04842e9000b0348a11070300310031850b1203c2c0c548208 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 987877284 1250 987876034 987876041
    0x607020306070804050f1005150402070c0b0903070f0e0406060608090a0f05030403020d120210090c1415030108030c0f0d0f180e1006020c010221070f02060a0507050d0c1104 76
    0x481700b07072142e040081e03030400301803000c00850400c201000c40c00c0c1c00c250740c1e10b41081d82100c0001d030255106024080115600313003031920480e02c4001c040c030395070204140480e04142150300a01c0e10003642900008202c00c020088a211308d00496080103c10340b80d5000321030403c0156000c6a40d03500144514020480c5141619003861059048900e441ea580c0c1c0410000c404408054402da40c0e1096036142254042c410a04500340d034900c200102500390382c4580d800c0c3c03d1409507c240c00703026200c06680b1345480403480110f054210806449680d16202603991b40c0c088007508100b03000792006404441d10000c1d40c5500c03103855403981c00190700812411299203201010b070802c42880154001003020168503c60701500e201801c0b5070f041414280040d00d4441440300032811580f03d2040f51640407015250104980d41c1c4503081740d0381b0441d5003440024600c40030b20180d8098000114501401e40000050400070304c10000c3e1540343d0740e06241941c2c80c0c07881c01c401a002e008840142802031806a0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 987878534 1250 987877284 987877291
    0x601140f0702090901051b030105060301060e010201020918100f050901091e0c021e0d0807050a030b06030906040c0e0c0a080c04030f0f23100c030b03030a090e0606070203060708 78
    0x2031141000119000100000c40990b49211142d545400b400611052100340215031000343c440b141c80d551500020070703001d04c014411102040302101309010303036a00c00e4040b540034000060a0403140f000034421250417007800d075605815459240c000092048021805908441005100070042d80c40c240d141c40152030010005100e0071940003016071180207074031070340c1c881401d242d0052001c118850741c0c0813015842c45207906465032111a180c00429449100594450ba079072804d0f64442420580c1030f0081c0180d191084d07817140021040251400000407840e11490207001c2003241550340c0c44002204400070b8940e850b44200400c031010f0014011040d44c0d0300300201310300e42c615090b84d07030321010b0f005d0f8680d0303d04943e02d030060341c54003090040240c6864010b03950041258410782002015554501c218248181c81a45814003008058029072004002e09400b60a9039501c2c000c403040141a5400d80c080d03182007030381080104016081120584080c15805402081c0c0768a40c058181c4565100a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 987879784 1250 987878534 987878557
    0x230106180501020307021306170a1505040807060e0f010c020c0405010b0c0a0f0c1802031902040f0e040825060615090608130c151706010509130209040510170105060114 74
    0xa0b100014440e80b2180e04252720300204000d09070010591034030209100c40e00c881d40728a0350810301800b0100380c00b00211800c0725841100011b540d8500c00e01c0d14149102e03911291529464909140f540c20f401240c3c0c1c104041c81254204296030300d0b0109003580340141c05000302554011f40340030b0001240c11107030303800660050310700045003613484003030304180d801c04c1c800202899000f0050280800c1d00e803010301640c0501c540e081d41014208004422001000e202d05000da01d640c1010600307115401080350010f0031000720400b960b0342c00c0c03414000000d51074003045841a00e4000f002840c091050304000c0c9005003680c034100103a1425400300c0e030008000c0c1000845400c010325250001d200f5600500040180318403451f4417130380c40c0754007070b04400c03600d8150902801c3c5401000741a070b90040031a4000c8004a50410300100c041c2004002030054290031604070f0716040c00d001c2d82004480380c7c0000c0700d06203031000b503090010002e12400e035401500c5142c0441c204e50b03c00070003082c0030b0010741481304030b6 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 987881034 1250 987879784 987879791
    0x9091807180b040c0c2916170a06060801091406060a0201150305100e01090804260a1110170103061112040803041707050a11042301061805010203070213 67
    0x610000504540503003030114003080300d03042c1c0380c0208103c4061b40501a85e10280d0381c460341d483c4030f06204414100400c1d44142c91821425458901e02032103488024025000391000d042c43e04c90362140080a080c086c1d0000b10300700e40c000243c07000143c05001e009040080641215455034018080b50344c00800450065540f22300c4010380c44025050300c030307006500900c01040380b01010303106a03084801d030042c2d8004d141d06115000c008124440304072000c8030340040c0054680001056a00405c1c502c012450308d26000f00c0540105010005042d42c8a003d0129540700c40e140611070180e41d25400c1101818210304d6040c01040400c995a1080300d0749504403107498580281c1036600000c0d401e085404480485001c1f0a00c400c0c4400200c1d0840c20b000305002c018a080200d07110303a5039403541e240005202c400004a1080036440b283c118848941d52014400b030f401514104201d2101c0c02402501c1c002203170200381703005150a40e6400c40c115841078016619100e0300d5002c6c80308403141c54511031000d545 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 987882284 1250 987881034 987881051
    0x13060b0a030b042307050303190504030b0a02030a18022808120705070e1009090c09060603020d0b0306060d030c1e030c030e010201051b03090f0d050909180718 70
    0x1214040e951203980300b0f400c86911100202030002c500b8802c1184c0c4c039166480b24006000641300082155900321464800d0781d205030000030121800c1c81039400c01400d03030352040207100000c2510b80142d03019040c600d0090041440c0c041d14015005101e41000e507000c00c0440000e5901522400e4269040810b40780c1e014081d911400310724036080c04a0711803092000c001070104117000d024405200a000441c50246090400400341092841280a40c0d03103800e5556145808114600240c08001c00403044144050781d90741c0c80180094005028510040342000c0c4803100d03a144c049100e5220700e40003403028034030441ca52001c680340032a508c0103d440c1c0300400044030f1111580200114282c0c86596080b01401503490020514942502c00718107589c10300b01840b1aa2100c80d444d45c0a001a40c281c0303035140c1e9103000e0450b03c3c1c5003140345c0c11815409180941302005602c08001c19400405980c10565502d03041c0c0d152001c0140c2c4c1400003d15044100180301002c1880100c1101d940c0c28580829000d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 987883534 1250 987882284 987882293
    0x1215061808010c080f072303150f0306180c03070e09070902090333070302220b0316110d08042022090c0e0a050f13060b0a03 55
    0x1465000100416860580000c4440c8520042000341039840c000348410048001c0c050710850340684414828104040080c00725407107144400320001014050340c0d00810b0500c00b04130b06500543d0201a610b00244888025061841072140d6180c4050001e10352a5034580307074075981d000084400d84180c058078210300c00035542006802c01030b0620044d222068100038000928040d940d50000f14045e00601c440907541c2d40100b01c100454186081032403c1e401d210409524034203043c0b050410380002941402106170341075002d082201070550343c3c009000402c0c1c000804e095821f208403c6441c4041000074248003608070300210103202420241c0d40702192030480350812800355180340007c1d10407010001440340014107650040d0440e901e043e0040003141c0428020f01140747d29030281607a4951416941c10b0941c4204503560b0004030254410391203440307401001d40140d40c901100c500f4480840c00e83c04100e442640144141e418203000d15040d42c0d00c0300090140c01d114a944151502070000204 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 987884784 1250 987883534 987883571
    0x9020102150c130e0601030c0f021203040212010c021015081b0301020705150702010f0b061909050301020703021b0105030705030411030a0f050c030d02070f23120d0201050a14010612 80
    0x810f00c041c41311019103400c1c000142190078480400c82007020084002c41419004901c825100101d5085aa540d40d40c500200300880c40100b00c00c0d03180d61a10101041d22a03020864554410a2101c01d00c0144410090012038031400d003e0156160031602c5012104061110340d03120030384014001509100f22a141c040c1440000540c028195106070b042055013582849503c0346901100e400f004900314003404030310310f402001c216101d00c0548260102c11180a0b028280040500400a654802d010b01d8000d494683c4008025652165800581d400d50700a03415207108036481c1e682e0301e0035a41c81e616074821100c9030300902c5405015408400002ca00d07c082426061800b400042800180d6501418a4807590000c5681150041c007814000c03041e500c6840001c40d50071a0101c2945105080c1c40000c0e11207080c1026404546d0010200b020500441c8000e18407001d500200300d550b48625800f0191000041c2184016541100501a45008074103107010109001c00001d9100e2030700c0241c0045 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 987886034 1250 987884784 987884789
    0x90c03010915050603030307080708040c0320010909110f070f0503031806061e0d02014503050316061509290d0b1807091e09020102150c13 61
    0x40b603109010104038241c18000c1a4110200340c000b1491458510303230081004c0d0000e00240200001680800c0034040300703241c4040a0b603008a02c041c8500744c3e04005000100c10607404030301081d4403110004200030382d442110030402b000d403802407911f2025107100b421507000c00c40449007441504130030700200f00300b00043c5104034001c0d41c018800700c2401e0000c0e4030b40000102490700c504112180d41c1e03088001140c00700c0c1500415210900c50940920040c0c44c000b1880c601d20318103050941000d000040c0080c0115080706040480100b0010b154488400712071003404098242d5204010a10311305d2411515940214002c1c08009004480b0600d5010344040c25803224610340d071181d150042d00380001c3c0c8806094040c000c404552048214041142e903a580c51016040100c81c00024060248801c040144a85048103490301e0315282d51908004002c2e44240c0c0c0e00c4800c2e030503100002d000181c490300380c5080d016002845000415484030b079142c10014061070b003206044c4104071400c11200141d202 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 987887284 1250 987886034 987886043
    0x405070e060a1716050409120315030807060c23040b130503010903033612091d070305070f022517060f0c2b090c12030f0f090608090c030109 62
    0x14041e0b1300c2c6100300d030920000d81284d07209a250088150001c0c4001c00040410000e5040116818250a200c1e60b410703030443c0d0014124800c0040c00b00c0400050ba80800c40100ea82e0326103154114500c4400c0105004c01d8010509230340d020402408080d43c400050491380d00f42d204040c404c2c7d0384641c0070030b0075281f1104045010a07141d0701740c443c14000c0105030304030050212405030101c0b02100c2403580305540c003020242480c0000420f004816100c1d09641d800740c800751440f201c0070200d202e1404002c0604450100c0000d10f0710300414505845013500c26103424041c0d009140c00c5a46580070300740110005060381c140c0b23003880781c00159002044944020074207890050110b5241c84481e46400c6500100880e46480040042c80740080c80d00c00c1c462101b55000400380140c034280c080030070051007291405450b1048204000850407504001c3e2141e00e4800d5a0f00494540051421f03210f0103404604980410066881480554458080c240d40030342400101c5401c10f56200100b400c480d50020f041c0ea = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 987888534 1250 987887284 987887293
    0x60f1a030408130e1603110a1b06090c170703030c062a0309140f1e012c0c040c120c090512071a0c10090f0b011511060405070e060a17 59
    0x1d402c1a403010101c102445d0703810244007150700c2441c1a1a240b003041801003c1c003c40c030b51450341c5182500700616005a01400c20403200280b0f091100700c1c0c101c40d00c00c0a0b0081c591105c140c001e20380106510341240d40c1521000b003900c44642d1004054490b4460f0000f00d4039046030280501003044046010b07001060310005800761280c107007103050008034a0651400c1d4040c0324821000100080e40602c0102400b854804105158003207174050720108025050000310304020b05880c8403401c40038164440b0101c00c4400800c002410701042d50404452800400c1300b40055200c5030b40c4540041d542c08515203840a1792036103c100188a110410760442c80a0303120202c2031100d80b808845880e004821852680d0405201018042d90783c0240303070b615107406803906640c10410103010303179485030726501035924100b83d070b1900111250000c0c03041d42040041c40b140383d03c10b008000492141e0055800c50050a40942015031103803020001030803460f04600b03001070000d10b0000c4060b20010303440d001405071 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 987889784 1250 987888534 987888541
    0x31e0209041b050f180c12010b0a0833010507020301020c0d0306170607030f0e0d1106010b04030b01050405040503190309051608060a0b220f060f1a030408130e 70
    0x600030b914003500124000c0c1030071648196107a44041a00d001002505080d04055440c038015040c0d5015600034400d400781d8142c00400d000f22048081e1008070300a41e51203600380d03602001b441d40c0c0303225140400314005a0304a00c400d0301c880d2010241d48c109040c146289054501d0f400b1a08980c080c01040c60140c2081200d44062a03060148100034803061211090003507014040580311840a0045020325035504540c0310602e009400407420104820150f81c0d101030320700d1016040040d15000c500c01e03805200c0c000301c2c1a0078441c09841c20317250000b00b40c060680c01d24003403000500340a0710030345492000344400345030b0740600c06250819002c5d42e5804140030400c4c1c50031070314100c80840c841d20b80000c218420301200d8000169642c0c800300c0c0701000305030070490502090f104c43c2c11003592600c07003040800b1900146040e80101c43c4411f150700041100c00d40e40c4460144080a0780a285210002d00d0841444040303580052b6030894000c010b138502e0a858504410548440c03580428008102a001c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 987891034 1250 987889784 987889823
    0x804060b0127140102030304080d0b180f04030305060a0b070639110118030f09030506010b0405090a0c05070206030a0e101b02150105010f1110150816031e020904 71
    0x10760103c2c0d0741c203000850450a20350f0fa00340c142c1c040c001e4a42c0f05c10395249032108180d9a0b840b8581070720805a602590681040350342c0500c0308908039000e801181c10321010a00e241841031a000440301da0085d180d051452a40e64030014001c600131008151400021030420621002c07903c01c1da420154075a1003880d084113101810f2008204900141079150000302c0641910007600341106603458903182540810007842030303498001e05c2d000078001348916000030a88585800041c01600c0702142d19084d1a0317181d41201054401075040100018402d0004500505168000d1a04042c10100200c1c0c1e0803400c0310283d00e4000c0c0700c8920700e0620f444a2081240e004047e40b24203a00c40c0c0752010b480c51000d4030044a40e0a00103125503410413900b50a011205485440f0b4480c0d0304102c00192801d070816011746e40c02600308181d4075a2070144080b00081c44483c000307110401400c15041c2c03429028a5034481c1e140007450895144200c110a03003080340169102450380b486684560007204c0d188441c03040c03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 987892284 1250 987891034 987891059
    0x9020c010e060a060e160203190306080f49050409060e240f0303070c030c1205070603020a052203060b0a0b030a050c07021809060f070804060b0127 65
    0x400c4140c03850004c0c20710108400c0c00e081940b2907004240d2040070480d5520880c6140f1400c192a2421000e400c003055440750316800c8003040303400c91801c40711aa44240005520344059203001c0600700d50400ca10b0280303140050141e0b68400d000e2054004100c0708402c2c6043c50000e65075440300203840028140410410b5100d840094194200e051480d46020301e80042c581400040259a00d0f8061a50010a980d455108200e001003d410b132501d83d80241340402481105000440d800c040140000c02d085801001010300306030401c00038000180b516600754002d601402c2c00c4802c1260400c540d52200503441503044e140c13641c0c1a0f550000614500781101140c6403c92403030302c03440d841c0b58200081c0141009480e00160980400a00360711481d00045081c0b03c2c4400007074004c8901420044d00303002000e88548111104030555810365101006030031340110440b501000b0403102000f107004a001c55102d1280403406041000711520a4040041480842c0c40b0204a8404140041c44802507211 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 987893534 1250 987892284 987892291
    0x80c0d05030103031d150c06011a0a02060106031a060a020303090d09080c09062e030f090b15031005011203020c030d21060e041a0f04082209020c010e06 67
    0xe450350840d41155001054940300490003802c98550100b00c800c1603545160780c403840f151850b0745030380c1c07481402040b50300d40320240326184000608403114280502403204840e0400c540da0301500b000d070b003444800e90013407030949900b80b800ca40d120b81d00e0407540c540000a16546900340c0066889190220140e843c0000c051610002c00140030b10412030040e00251003001c0c0c1b0001c07110005a41c0d0780038041013003000c8003d000061104011140d88884c851142d88900c52a5940d80c18000d01c00144207803010342d550050010140b0812000240c070382c4482030584030000304010244d40f86640320f160f41209441080c6c004003000c0e409603040300200b503010401c0e0301c0d424100b5000f40601c1c460740b0b10050254480350030401c0302c9a0716501c401090b00050350000001d03080f903451482e2282440e042940006c00d0104030b0b02c280324151008a1400400f03450b590340b18a600c182440d1520007002a81810f13044054036002c0c0f50411a040030801d101e45001401200c0301700c000020300d4820841540c0d18012000c4d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 987894784 1250 987893534 987893537
    0x60103170c07120c05120d0f0327030f0f0c080f03041e0b060a090908030612030c030304080403032c0111070504050c0c01151404020a0905040f0b0a09020a0203070213090807080c0d 79
    0x990b006802e41c0110908281043c141000620543d0710745130383c0c60301060f01c0345050380140b030144117204140d082141d00e500070501e40d031115082c070820f02083e540031010b03c0001e0a205420b016900b00f14424100860b401845011110504819100c10b050001c93e45181107445024078010080f050811840c0f28004081c003c40030300c8042c415480b40200c0c1d200141019002d42d08079010300d080300d0400c1044820205046086960301c2c83d05040c240c425403c180800c400040c60003040b103011405150a50882100c00c000079051300003500011744070311602e04a110030f00d0090000000d503560705c910030710f8894040340c0390082d40c0742c0036414001d0031151107172111050030305044801c4c05103c1038030f1502181c001c020344006a07104070310300701603a280007103070320103580030b8104404000d410400782c00c02102e004043d00c4060740213443d41c00900990180320300c02c2006034400d0080c100503150000000c270108190f000005400d07000b41e190b0016507840440c040c0c8414900186001d000d400400003864006003e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 987896034 1250 987894784 987894793
    0x110d0f0509030f09150f04090c0e0a0b0d1a03100b0319051c120c0c0c140310110f040602061503070302010c02040c1218050708060103170c07120c0512 66
    0x43d02400d9168001c1000c503500420f0160740040c80c0260744411544050400c503401a11643e607541c2c081d001d07095031010035000030b00e03030b1507840c0071418650580420784181500e0030303041c44149002d6600030322040a02944065506c010304c2c60070b440c14000803041034502100854150912418940740c503109402c0008031031101800d09012542c082480c4411840c50340c1c81c2c554000e46400d01719075194030840000740061401405800c840c0e000f042d1000907521a0742c0c00348841c1d80d101848910b40003510102c0c0d41541018031046c10381019a408501d0803125014542d00f450040d003204100703a08039811400c0560f010300300740081586803095030043d21000310002c0c100c0307506540c002040070060142c0240070315155400307030403a03502960b0700941e881e0f0030b22010411450340c41c1202000d400c0a81c0300340d0306405154000725032000e003c500c10341030b290040000d01c03a090503003107d0065a030101e0a98004da001c2c172078000c03c1c00c43c1d00b10100c0350031a020700128805d08c0d0405003042110202c003506038105a20 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 987897284 1250 987896034 987896047
    0x908180411070c1206110d09020f1806040902130c02071d01081f020904140615040e2205071e05011b03110703081b0d05040b1606110d0f050903 63
    0x5003100340207495080d40444108115890100d000d0901d01e806d13101c26078000308102150003045d03801505081d0007201e41480c07036140741c0c050103104120803040070390324100c00c40020f000341000d1300081a02480070b0900e4800030034805501007111203100d900e40c01030300440e1003080440c20174036204c41c80146102092443d545007140b8240e81e0640441c04400b030807800e007461046402964140c480f1104050000e00805507440d4902400b030500f100c14601c45d2480380c00d400f44a500180a480c10b80d0300c542c0000307031151101e030300505c11815444c219198100183c150680051400c0c040f44000700036111501315400d041c8007601c00071401c0b1307421090401605030041a09a01c00c2110920101d0309428a1044040c1d0300b0130131800c1096a07013014050a900160031180386454441c50131140078030f00166403698404160480d0b0501c02c6101d46204400b0030320803d12410340b56550082d0303030362180800145007c441300004c0e040f40c003c403c3c40c032402c1c1c1c0e4940c0c2d01c4000714068044d0a90081d0304102641c540b90 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 987898534 1250 987897284 987897293
    0x7080d0801030618081206030d02030a2003041a030103170702100c1e0503070203070f060807050a18031209060206070c0b150301180611070305030703050a090818041107 74
    0x400500c006440f642e110032400d07545031400c44008010036042145070756140c0b00e0143e40d1164010907101076020b481180120301c16248040143d4240d40285d42d54050360f100d0728030038400c03240401d4115034910b0004000001380a801150f440c030b01c0c040c1510308651650b1441c240304180d0715040509400741d00c4200f040c07000580e1040301034581c0c2c103030705c0c1011060207500e03040c10034001049198443e2101c0d240004141031200020107002e001d44200c1c1140c40154407220b00c120140858820a4046a10b8001141416002d0005883c0c0c4181526140c0e140103d006428454441e2a078815140d59000c000c01c018055400390000000d848607000130021810264001000b0194030300c00a8841030320b1001251403070501071104040000300500034030542440700308040b0005c8403000101d401501e4480d0400707400c0c288000762400c00c0e8054072100d0850b9200c02054000e003400602c40310b5110b60700e0240800107074508004c1c03c6106e070060300c01c0d90340548090038441101c1c1c02044d640345100050101c200000d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 987899784 1250 987898534 987898547
    0x30905010815010c0510020d060e011d0106050f1911010c1815020102090622080c1005030a0b1504180504150b01090b03190b0d050601030221010e0c0307080d 69
    0xc4028602801004881c1c05c026050030106500c04030201d0000448406200003030700540301350740040c141c070074541e4ac1c1d41108044000441e09200e500c6100030004001d403034018405006442c5003030410302d140940344ad0703500503142810400d80c40442d291001d5510030250901c0751034181a06810b28190003800810b841c61224414402c034850201e40d28400c041480c403c0d0151a03448030084c00d495121451064100945121250300102500015a00103241800015003030007941025142d44042a4410000c841c075a05c010241c804181c2c541c1c02e10007854a819210340007255a5003045070700c55050811001220030741c0b500c00c131165070030a03003404003044020594840102009000049100c83e900050310409110b0b07002c9440c821010007000b086c401c118990220014400d003040201c4500c450070000710701106440a8200d0740043c0041c00141002e41c0c2c031a034603181a211501503200110415801d485203082c0c0c40d00709410400204401e41410071200000e80400c50282429200a03003004129 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 987901034 1250 987899784 987899821
    0x61e050603062e0b030a0e06070e060304020d020d06051515120403030b15090a050a0b0d0c0509191d010602030703271d1b04051e030102160309050108 66
    0x341010500b10039010340c450514524031043c04480c03410101d40e69960030f851908219101901d0034289079641814940108046215010703d4840803600051a0184042c9801c0207108a07040402040751a025a9480e141c085c1000d2041c3d00210b04c0d2702e81644009901e41003204400e000c1c0c0d003204400314001d1000c00070b40314100f0100501600300d5483d828203d02034800c80920315008140c0b242c001c050880c0650040c00540b805540d000700b440d03982d03800c1c0041c0c85414030a0301481141809031420b0036071550004031212016103401b508101e80740c4001402080400700350300c0800000300003044000310701400d1140340100e00c03284104944c541100651280315400004040055000421860310b520400b150798034507200d41c4201c4000e4031000c4852886880002040303c108180b000117000010041c44824005030200303905080030b03d44003c0c0000340fa00c40e00c02d58030302c1074a8050703443d80e43c038244058012643c1014507a05000c440707050161804041c1d400c643e042008401c00c001303082c0003081c0b80004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 987902284 1250 987901034 987901051
    0x71e29090c040f1814010608070f1e090606050c062d09070f03030f02100b060d0b22021c09021e010203070b01080303070e24030c0403050703061e05060306 68
    0x2502600101e0f01d400404a140a01c4103802d40d505214080c44a07a0402d4a200289000208290303070b1260340056580312503110320070b00b0345c0c564001400308469211801303500885d694802d0448030746032192001520b0581c0c101900090000c10038400d41c1000700715041d0408903130200050500c061703203041c440e42d4004030044074040c009070340407a460345e404011000c000c00002c041040641e448ac034000304150100f21280c4018450140c41280345542e51180071021000208440d01d8244900c06c400c000d0800221030726404124080244a00c001884080e01c0c102d210400050350b07407007486000003600349450381c5022498607041d1040016154080b468040c41141804a00c0051440e00100d01d1442080e4008200b000c03c2d800000700380710000043c6000b0030f159100c6142d14400c1006000300f01c90502010302c66552000360503101d02210720011504040c82d0090b0501c2d041d12622503915114155008640c2681c1d690500f0038030314104400b0381e403520420081400030341000c47c002581d40d40c1c003410010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 987903534 1250 987902284 987902291
    0xf03070c020a171c021b09090f0a05070807120c09020f19031d190b0601091203120518030a0f030b041a0f010c0c0902071e29090c04 58
    0x3907541d24050b080c01021007143c0c282c882c0b03207031620080c0c80d1a260903541e80e8440030114120302080c00440d140307581d103c2e40e4415141e80d0b00c841041141c040000b5008038214000d80300014140b800c01c1c025172140a00a0005101d1146032410407443c2203001c0d0300001d440b403070100000700010100034031001181d00402c80540c030b46504200307100e06407180c00500106401550045555290590001c0502061540c080c90341d000c02280701c07d46071440c007140015420750b8003209100140c032445180303800060600d405400d0366140d000c3c12003004144174040c0c02050325968102d680c85401d0044580c44070140c2510480000069140c659a0080601800900016401a0940c5842907000c455545402401442184100700d02d0000300e44040300154003501c50395016040d2540620501c070680381d400040f00c0c0d592464195040b000303412400045644820302c0f0303003000326010300c0300d003169425000e01211245502d0954058100c071120458040c40071001c481002041c11000c034072280903520984010 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 987904784 1250 987903534 987903557
    0x506042a0306093308190510060303260c0f1e040b03100824151c02030111090d17071505220209010909031b2a15050d0e0f10110f0307 59
    0x1508180308d0010500b8181d00d0001c000040c035600000c04655403c1e4881c4044085c1e407698840c9000560072034070032600300d40030890081040350300c2e0001c102c0b11540080c041000103140074900300c1c0e9803083e844281204c4011050201040c00c05020b84001c0000400419182d045001c05a04081a80052004410b007540004200c1800c0d03075130203072011400800134201d0212030403845080c030030707141c106902962800d507501e02c86031001c104a034840c032401070080d0070034100766417404680307010512004a00c59040c002100018480c2c54a5613214040000104803441c090048000015002c114580303c100da0524036400f41e00e4080c034135415100c1c400e00104926046050641d4910440a2442c0089d290300600300b00b80119440d00d5845400c10340c41c510701c000e28080207200d01e00c405000e000c4151034032440790b4a000340078000400c08018014070110312840881c2c07071681001881a10961190004581000200018460506506114001942001e42d5062840024000108130109000800f03000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 987906034 1250 987904784 987904793
    0xf0402100918021b0109051b010c020a0510050c0f0706080606090a18060305120c1e06270a050106140a0317130b0d060302040506042a030609330819 65
    0xc4c1c00019000c4024400d8405501e401d40c0da54214000d8032110104c072180584e4258869036200ea043ea030000c062501c4141403030108620300602c16030003014880e003045030301541082031245459950010004e80b014a00d82013018001e81c070000c21407440389078100030040c030030368400039990287caa20122090014143c101082c00805403030300090824400e0030b80407101c0761400d000520700d03a00646e094a0101000d01c1c071200684424084800d041e0300100700241d15002118036002c00401401c100c1d00c0c3e41c15841b480c0b1070030a60340540170340380c5944a89090045070140304d01c0d01c1241e4800c3d10005c0c0b41340e203551a81e000d040c204212222800c2e2000944060041800c0180c4025023504601d043e96000200060402013503d440300b01e0155003002d000030150728180c0705208005255001d20400350500710350484807140f000031040141030b42d038480454201c04520407400c900840380e80c5070048402e1544601e401c001c403090604070b12403040310306100020b008940030341c84865000034010b0980070b0313260 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 987907284 1250 987906034 987906067
    0x5040305070f033c090812090103060f0e0703060b090112110f0310080c04090f06090615060507150507020a0f1716030f08040809010c0215030f040210091802 69
    0x400c91941d980442e03004d010078800224101000b2103507510508801e40020658034990f1521850081d43c00004828121005c588000c2c03405c100e0524000980c540c8800004650940d190094001200d03400e007040940394251041002034150703450301506105075040003c0030f00300001c0c601000d550b102d211a070b1614000314203079000307038004098560320380c6420040000f11107024440c03641c0c00d10929484545500b81403240314201e5811126160034120340b40c0360f40e40072301840b0604407001660344410341d10001c041c18071000904030300da03151a0303104154240b80704070300203429186640e1441d000600c0070640d0002040c52509500425281c1c40215500b000c8224420a140d07803d8102000a0110315040c58a55165503080c405c3d01c443c0740001c80a0340071200468112002804070a0801105805600418400b605d241c402040d03200340d040703580d60009680d00180c030038080c21039140c0c003440110f15000d8550b070740e41865850840c90f42481d003528142c1c0b4952014410100690000700f44000801420 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 987908534 1250 987907284 987907307
    0x3150306060a1a1617031015120e0a060c35060d051e0715180b0318031207030608160b091201090f0204060f050112020a1106010605070c060305040305070f03 69
    0x22140d4070035800c4135031007600c146c0c4201c81c4500000003034800800d48400740e00702071000e240b0725600c8401341080c01444000519180c0d80c1795400d80b08240400e0005038582c0207106101101c3c0d034aa1095000c0d201901104000c403035030100c3c1041c4d100e015100488050303540d150b4851401c40c0e000914101505003941086120740046454940c3c40c440802e045e0000209401244c221603002d00380a0b50100044031100c0c01e183c603034040405903550401a510003900a0741d044200d036106960359400320140e0901d03507440060040c0300d07021103004001c100c03078051142000500c22071014000f1501c40035903e40400d0890302400600c05e1012666030210b031107500460044111140080181111740c0c00c0c891801003000030301b24071803030900308041038403404022980300301d40060b141c000f802000019084046e400c80c000708000c01c840c1c420058100d000401c1014001e2010b1f80b40c40d80d0740c58450500400c1224a900810b050500700024400040e81c80300c11941c407203070400c2190b403e0f0010713868100e030150f040710b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 987909784 1250 987908534 987908543
    0x21902190e0a050421020d0c050c06041419060206010303080c091509040b040204060e0d0501200c01060f030b060103021803010615030b040e030a0c050c0603150306060a1a16 76
    0x80104129000140e203c1401940507030380c1e84c400207907268080038503a2038801d80f040040e00101510780701c25010b81880044a0301c580107407540320401c0c00105080ea049540104145417000c0c1020003503040c0701d07510700090501c05e105112000c0c1401006541d64106210050800203043e000500f001c0070740e025204110402415480b000118642c07101690300070740d8900d48154900032380405c42d403501e442201c040300c0c3e158560381310901340d101c10001080301440c000e8441d5501c502c1d00302d500d0041c0541180c001b49a90b6a020341f00d000315545182141c0c0d2071f07000304030b07104405401170001c10130340401c1030382c00882482d01581e1000c2c2c44005480f03110100d10b48030b8056003004804220412110303c0c0c400000030ba66000c009019070364003008181ca0682c814068960020000113140921030310601e10018010401c98a0300444c0f24086113556004a0340d0400084d9407041c051000e14091141d142c0115049802c03400c514106454070640c01c4c04008545000840011611801c0150544240d03006400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 987911034 1250 987909784 987909809
    0x2010f0c05040e13150c1107090c080903031b0a02030d0e030406230412020a170d1709062a041d33010905090a0c09050102190219 57
    0x914001070510741040c0100d91420700c80c24002282d84980780c1c02c0c0d0080c15004030f01c5c6008001c0c40c003001c1c0d006050008418041007203044054109840c20845100185a60800040d012880300b034014440c040240940c620764100b0030510114000807003214030180480200555581c81d00d040507440c500c104a110000c25081400e180d1102001101801c03c40310b0f16120190810807140c242c150f108100807114084940034041805409003444100a100c1d1005d04200b200c2512200b80d2443c0c550040064050360b84078084070003410b9404003840312000110316014000313003440c1c00c81c65140c3c8070007040000c1c56843ca603040068915807a09903041c6076020040c0f40d80e10b6889202e1100b8400d603040422801e40c0180003c600d8036001a02039014506890a0003000c1e07640748246085c0d4903011080c02030400c0740c1c0e4100440c00e55140d81005002e41003124001401d407201c2030010300413500b6603100f1415908403071008030069500b128407945a55040394003440505004140b0000308815030031a0484841 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 987912284 1250 987911034 987911051
    0xb070c030f0e21150a110d02031e0103050102070515070f0f140c01061410021906060306050705030a0c03060503030403080d1b0507060f15090f110a02010c11060405120a02010f 77
    0xe01213814200e041003000031032880c0c0d6442e0f81002c145c40001509a0308450300704100300c814034459001c1c54100c412804218520720701c0b40c2c1d030034400e00420b800030368290b540081d084007003140400800d0000c3c50110041c0f040c0b0700e4603503030140500110b07081800610000301e40c80c0c0d00700d41c8a030345201c50b03022003190b145450f100071440f00c0380200100c0c0181903085107c014800d215203008009240740e240c80e640100300550541309a18584020b4100032201309803110404000901e203806124403072482c81e07171510b44034900030360048107646042c040c83c07061614010007804251000700894040d00d03000559075503154880b441c02e90051010701d00500d40b2500451190450682c00b0300240704440c0901c90034003000c00c0012030841250040c0c035002c02410b201410400c8221a150401000907007292030001c0d14031b080c0c5958105031f60100d141d000040c0d550fa40145846c541040e814860f10803407d0040040385403503500d20f5510056079506082d002008505100000e200350844034500072081c905000210 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 987913534 1250 987912284 987912349
    0xe0301140711071d1b13230a21031b051e0f07060c030201020c120319091208061912030f02061618050901030507030b070c030f0e 57
    0x8048100305107941c003c04000040401c1d0001c038007500800403c0c0400019101d106070851a200842d122282c001c00c10b0000784e149100c0c00320361400030050f49162281d0710100707000b1092180d0707031040c5081c803641d0303102401d11200010829610b000c84001c0c2c01d034030881d01c50341002e49507038180c1070402c3c84c0d1180b07041c01342080110110346101d022481c000c20320041018500c00d02d0b02e44401115004160b800a0010011148249981c4540d140680001454011003940c1141816103403502234a28450000600044880c9143c0780b110410b0098010030142601d17a4070010100c0d00841c0c00410010036070003103017003940d4800c1c00700d4000c2c0d0401d81c54140107548a0000c1c511104e41a4203401041c090000301445500100320148200d01c0c41031000180c4083c0e036019504943c02e0b800c6020343e415696000311b082d803655540c0501843c0508024035920345140b07020811114000d1100040000ca085003000281d0043c1b1715a42d0002c03a4104001c0c207104807408141d28002c8884040d00705010400b2008030072 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 987914784 1250 987913534 987913547
    0xe071b1101020f0601061b03170907050f1203120417030901050402040507030b06090d03020c120f010f0b1c061413061505060a03050a0902030109051c09150e03011407 73
    0x650080c0c0030385000d6550b45502c213488070ba003441110046141c56042c43c001e443c61040c0e221816119080548004e5941003412203900030884402c41d465110f100144528602441e50008450341224500000407407a48015100c0c01411510303401440c0c8900400c04100213001900900c00c0c203d402d0039260700d00b070200180644003c0e07905a004602e4400841c220340d03c030b40a4081085c2000c0c2045182c04825828804616800303d8240d04600444e4050f03c001e03682c0c080189400c501032001030a60740b0f0305200003801c503046400310700788144c0f40c10420b44003a10ba44461207034200c2c0b500d41401d402045400c101000c0d001d6a2058821a0032580030400c5072161011a20703607950003000208007583d900c0309544080702e40c80c010a54840c000f03001c0e10071803038170a42009a10403420071011480c501e20f075000c2070949088010442e6107030130805019000c14550040b102c1c4140c0b903481c00c400030038a0201a0f00c0311821841c250010041c2c81e12501c0c450362000d4100c01c0c1c11001584106c040c070314003944000c04c0d5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 987916034 1250 987914784 987914813
    0xa0519022508071b0501140d0603140c031c020c06130b27010903050325050a08070b100f030204050c07020d081e0310052701030602030609090f070e071b 67
    0x151083c1e10024125040c04d07803082c600740d48041e1101e03420580000c4503528140c00000181203101d0b15405c0110004003400390a9500414410081140036403480c200b60070421400040782200002c0000010115400079540381c441100f52142c964410210000b140e840304190040a404030002584217000b4107050300c1180c4540c030401c48034140000b02e000458903402a0712010780161700520000e83d140440f180d0030318100b1024000c080112080f5618141444076000e02a07074150404900c060074071286d90401e0f5072000c00528600e0801e820140c40710541090390002901130743d0750304005400082c03030384120f0725000c0c1c004098010b500950b14141c4601e510030100c050705400100010b6484409075000d40f0302406030301480c100305900300130a00c48a1030802003060300308249015005440303440d4540383c030701030b600854001da5685070038814400d0309200034155440c5503003c800c9c070b00156000444c01809a440c0305210046a0720790342c5044851141080200c04002d42e4000740e1010012101c465081 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 987917284 1250 987916034 987916043
    0x24020a02071505090d060e01020403140a02010801080a0b010303030906060e0a0c09050102010b010c020f061b0d2a2a230411040e19090b0403080a051902250807 70
    0xb800e070038070304a9250041000c1903030005140d8040c41c00044a07070300700b81c1800c080c40c00018203141cad41340c6480884d080b882c00c286005403c920607030400d650344202c601d40034214080c004c0c071a400312903841100b10b002c1440301408160352900c90380304211103500010020001d00d0041007281c100884518000d0003181d0300030021480c0c51000003241e5006002d16460350f14161108105140c3d0740e000d1040c940c4003400010b501c05420032001c0030b100204038000a0400890b001050765448014014000c4d82104003040d4111000101d00341c05559050341e075180040d44848181c0c0c401101d64984642404905804c41190090381c80200703030080303480c5a20f40000380300d2311000d151080040c24841103c2a402c3d104903c040d08100611566180a003885d070406021070b4250428044090f14030704480705d480049070000821001d01c014160b10000302038222039014810081c1d801d10121136004c680443da40200c0c44da4001c91601c00b4075482d0900e10040034084200040b1401d0507180030300a039841540c0469 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 987918534 1250 987917284 987917309
    0x30909090c010e0409020f0409080d0c03020403021f0c330e0d0f09031a0a05060f0a1401020f12031915061b12091701140424020a0207 59
    0x3011504006401c07014200107845400a00200009010140019179800d036002800134540c01e1442d180c031310681203558040c101c203c0c0ca580d0403e00000550b411140e0380e004240c0148424400750351401072000b2429010f000021241d141020141e84103400194050a010101002040c3c16420b010036011512007083ca07090940800f02e0340f800485403070082c1c3c01c0c0140c1c0f2801e05030a20364085e04c8142d822003054103100c115183d1b81c0d0380714041035140203242e0001c50140424400019070030700a89030441030485c0e02926001a40300419040103951046800903202051852250f900900980302c0706401c01055600501d0095546440c0c0d52085c0c07002085802c2240500d4520002e03886016804004424150b103080d180003c00c0314a0003800c1c004a104c294644040340028400c04031800c00b0120a80340d00d40d68900e00109600d2404c085c143d00200b0f641052010745800d480c0c0c10742c255000d5401404a0102c4004000c4514502d41c446482c003400d030f10000d501d10441d500014080111240c180100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 987919784 1250 987918534 987918541
    0x603120216080a080705150907030201080708060f22090c030203070f0b0f0d020d02130e01050a120b0c070c030c050910241e03021b120a050703021e030909 68
    0x41d8032035524480d00c4401d4100c2e910000000390f051000b013500a01075821166442e00303010420308264401c0c2e6481c80700d544030190810840d43c00410090f480708090521080d68502440404c0001207031208042c030660b084040a0741c3c02072114828001c00c01030007001c01c01040700749020403c4c502c240c0010f138402c0c421180002407503584c01280320140c486c1030101c00e0801b4000c01401d81141c200d081c02c4540c02e80c00784000b4401c120144085c0111030028285115980c2c0b0b000c0e01915a030700107801c090b00500340840284212908913114080a69006000506641d20960145418060101d0041049030215000030a2000d4004c50302c09480e02212041e9040d110165075240014840c07007001c41e22000171004144005580c85e01014400540c1001c2100c0403803101000141311940030104040b95020800030007802d80d8501c120090284a40180030200c0803108407802400344460407000c0160019440341054400e212481100110703002d070340c202c5e660041313805459400141c01c040c010141d02000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 987921034 1250 987919784 987919813
    0x806160324080f0f0a08090a0b0a1205010f0b25240b090f160c05100e010b0d0203120f090a09051509010e061309081909080615060c0c0406031202 64
    0x1405244013240b0040003000d070f040d610700100d074115000c19544048018000a206600f01000340a8426281c0c0c441070312a108800080841e101078000200d400c3e000c200521448481c101250f0b11301c122075410340c050f6600b15540c06c408092054000b070402480311104080100c04115100502614520510040310710b41c4c00d2000004045800318042841000030602900c11031004003200c000920342606604000d8940518044030049100382c101e075140400c0c04252400e00c40c9584103d412269800303074076140c1c0c0000e0350350803c0c150303801003010002481c0110f5007441c40c21610101341c0039051003000c598620b14880140ba08446010b074031020003101001c82d1a120a0250603100395802004803601d4030303410f22080c0c0c010384682090b029901c86000d004200ca038801f030803c1241c45c00802c2c0041014000c005e258104592212840d54044e40502c0309200c00742242e5542e980c030a0b0342d103640b02c18121040c0761601c50301200158201c3d10300f2001205010300010141d41010380c4c0e800320707194403144194 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 987922284 1250 987921034 987921043
    0x80d02070e0c120f04030323070201110408060c03220f06230a0c031116021c1509110d060f0506030c01020c0d08130608040c0905010806160324080f 65
    0x2000fa00242031940099005105050345503001406444e0004d41c1d242e50b8500042005580c0d203e5800340300108007044a40e9509004040500c03440c040c8103800c0510306a000d503079400002c0d2401920000c08400900210f000094080807510391a040013680d101c14100b5101c40c6102041c140d880c2410850094020100035402508401442012418030354070035207080010304140251100305525251607000e00400300703001e400a04620900d41c60140c4103441007007603045548440b29081d980005a83d0b0200711801101040d045c120000400c3c0102c03a450700c901c81c3d4103c1403006620070400c011080034007030580d00c032503040410b01c01e0400140d08d07800c041540c0c2e04c1e001c2e0b04c054016804000d105400e401e20351802680e441c030842000b41040c41300c9038042e00c4120203070040000505000c00f00001d1024415600d002050f6a800030406c42d410500c601c2d4903044010545160110b0307001300001d403948294032a6003140801c1c4968249400c1040e03c403a0010264819244544a01700c04008142c10104 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 987923534 1250 987922284 987922297
    0x9053702010c110105040b1201083a0e1003050702010c030b030703301e0e09160c0501050108030903160b0403022106040807061a130f06080d02070e0c 66
    0x844000c2c141145545122240c2d41002c1d5140c10030a0500c80000c040b07403600007415500614188900440d814a003809141421a125070030f09640060300400f8407d001c41c14420340c92a0384454030449001ca80c20503110304088410b80790b000118603481440307469040c1d100c20702403803055000b070003a20b00703084046013641e40000d526585500020020000a054201007410641028901404e0300440401c414003d903071420340400072030003404007000d82200c000640340071004035003080c24814002d080484c80f0544010580132084850b400d1498415000d8483c1400c2ca540c010020301035503031a042071984940050304018000d10030807510300c203407050f00c13204901510b12500c00c43d0b041c43e1650b001c004030700c05a81003412410652104500a815003401054030a82c000c64810360b903400146000000c41e8181c03400300e03103008030685415880d5520490303a880f243e40e189001090321504a00400001c003403541c0944002e214011a614503150003048185c200d1314080101c429560f2004031000c014403580 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 987924784 1250 987923534 987923537
    0x2132304020907230a09050a061704020105090607200a05012c061204111e03071517040b0133050a1218061d0c130905370201 55
    0x5070010301411301c20a500b4514003e0100c14070010503082c0d41940e41d55011000540009440c18010300c9a410402c40c924020002032403c4c500400b100725010310022005040207041180005000545590716415601800e80162000b070346410b5014000e881b007078502c0c051b030340110b4038800002460b60261030b00229101c00d410b184221401e450f03e0010030172107402803196200300141300c4465150556203d0502c250702c52115a2034021030760342000139903400c501c00a602c0e030008141d900050303100030941c030f021901c8000701c0c0c0c03500d2a0003100c2078403a074070b02c0f0107041e05100c0740300200014000c104030a541213800901c0c9503070454240080c02c0e521441c90607048065400503482038041d0f80c0c414002030178070301114940346680c1110200814203075030300840b07844485240900c1c180b06112540c420085040c640b1416200c84540404030340e81c17144c000c40e400d10304c40c9840c1a82842800500c0c0c0228501035400f000382c480f1141488003120021403840510842d00502159281d400140c441418103400d405 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 987926034 1250 987924784 987924799
    0x50d0c032003040e15011d010509090421081b040303080c070219060f030f0b03071701140103050a140118080307030617010b01030b0405100b160213230402 68
    0x1c5207001c8401c0c0e00000c4449035507100400000078a10f01840070305015906000c22080c6805040000400c414143c03032666000301e400300f1b403028a981c0c1040c11130314080010740b44400700f40e40301c0c05d01009030200100c94000e842903e159015641e07500614140c4109280c142200b08541c00c040d0440280c000c6001c010081580b1802160302c40c81d02d80083d099151004146201620301281c0780380c2000066440003001c1003166945c03485141c1c2500405081200d08103041241c180e07402d0021380e507030015100340969104000108800d000c0c00f134004a1480c505071109503c1540c0d00e03c0d04aa6806415009461844525071005d900d8034060140041a46400807064030504281e1181800c5910107440c02003455920140040c00325080c0c00600003070700504000044102c1084000342c255021180d10ba48a10315100c100403d0009000d103500075070b001031b00190f0310b5842003194862500e4549002960080e9102290303840b01d00c141e0428001040c4c0b030b01d080740c5c204003070458031001000d058030000d40c00000c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 987927284 1250 987926034 987926057
    0x15050409050f0f061c1203050702190b1f05181e0708180a02090903091806100507080f1602040b040c0c02060d09080309031231030e060d09050d0c03 65
    0x4000c0c410001d00703c490211456a4030071a43c40350742c0403880004c01408a0340f03075030070005243d80511010140d030718000f0694101078001ea40d00303084403800030100315201555850340b3709504015141c4d280600006000300000c075103062a10600c503241122407080641502c041358004614800000d4018442500d400500c0c1c0c0380c0d1880c0940a481e00c1459807664443c0c804214056a100345610b8055254100559903e100306420f2140d4483d5500c62800041c0c41c0c036007405180e0f214107021141055062420310749801061402005c54403441c500610056008900d249806c0900300c403810800d1310840d402c10542d4617100601c1b0585280e18284c40100d40b52070900009410f0842c0100300c41c0600e150002039204560380c0341035090300290b0300041d06a04c0811002d50200070803001d19044088060f181e10200b001980500c0f03c064194100749100500e0f10b190800c05016101e0314040382e000500c0e89071950fa2041d0b0002c000d080d00141520984140c5004101c0d1a0003a10315040303032500355580e000c1c0d00c807 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 987928534 1250 987927284 987927289
    0x120c300105060d110d050a1d07051014030a06060e0f030d030e0c0a08010212010602070b041a090a080a0210140d180506130b01060503100e1015050409050f0f06 70
    0x100000681844140c4445020401310f9246005118a031078030503000502e4101403140004031510f1180141780782d040e0384040f99983c54001303079060443d6070449110342c52901404007140e0b040c850011866420002106000d0180c90301d40080080d10516642e20300d90b206018100000c40f00390300c0b015500750b00590f5100b040a8426000f034103542101804a40030114890045241c0740d005030f0040c41c1e165070120305800e035028000c03e1300c4d00400b0107100030080b0600b02071850900d03201f10720503200003003c004d14101401d10284280c0e581c07a100205540ca849a541e15800d4a441c064003049210b001001d40405200307004820605058440c00030280c02c010f5410342d1500200280c082c81290b804401c20500700080301000007074402c0318511410702900c01c2c1071502c0451208180c0001d41803000070710030020094401d42d03110048583c40e03075180751076844d2003030580346040541d0000300d0420429248680701e150002e00804c1120340003007040140d07a03100c482c006030880c0f0548401c1000301c066004920307180f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 987929784 1250 987928534 987928537
    0xc03080709032a152307050c01120906050c0a0f020609061305010e01090f020a080102160b13050604051b01020601140d08220303120c1211120c30010506 67
    0x10000200f03040c202a40301d2020a90020881c2e00000010703800310071540e850000c44241a640e6039103600e0003401c081d01983c4080d110400b0b001541d04100320111201c0002c4919001000660b0304584100f0450818a032044a998003440104001c07452001c64000751507c0003550600c603001c003102030000d0f6111020034036002d6800309000d0301d05648801400da8148001e20910b615580f02d807130702c0b01d480021881440140d140e43e03403251030f80d43d105010b0004040c44100c0d030506136941c45070040b4059a240040036000344600c02001c2c003030340300f804104002c20134000303008961800340c091560fa0072080c480c012660340509000c0d03544154403042691241e410041100c10600e84101c103214202990a01d00420307500044a4071480120160801c10515811204c51104200d840205002800503200701904c104000d4441d10344455607015650f0b4680c4d6a4010b0f00e1115240100145050a10403a05079980d0400c00400807424103031354482d111040b9080d0319000c55120003a6080450f841c000802c0442d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 987931034 1250 987929784 987929843
    0x90705130225020f0108010608070327030e0906100509040e0c19090c050304320d0c060e0a020102070b090a030c031b090204050a1a07120c0308070903 66
    0xc0e0381d028032403600c0c028002460b45038021041007035a201d40a0301c0c0100490300450036083d605100000c40180080c9a00c4080640e206c40907040104038100c04114a24203030350214107181480103111582d508250b4400302c0041c000008403611001900c0f108100301a1039413802051011540c10003042d002810301d504003940e901014000d031580b841b25034010405001004418103a007480c4000700b80901c4c01284540c800740500382c90304a0171172a003581c49250001480040541004024030603c084003034a551160151006c001a00d01854030b05030080d0a0502404040352000c0c05d0105441ea6500d00080800080c0d40581c001c00d401403030622441041e0f40000500c03074000d001454040045151201c103400203500c910300400303c0c0e2203140e42d5102c4010380d0390403c0c01c100f03004003c03c000607903c03002000c040d500d110391400d6032a20030181005040c0b04031040185241111034141040a410859680074640280c980140503600d401080b501507525001c0203204604e4004103000203c99415114034 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 987932284 1250 987931034 987931069
    0x303031618090509061e0f0402061b3007020607022b0c1509080c0103021305040510032310050403050c07030506010503011a0f04021312030306051008090705 69
    0x45064961602d00265142200c00103055441402030244040ca148480340050030403450201540c03d1610002c5685140640042d00c41da00204850821800e100d4403c60713010b030705004481d45516002e5603c161000c21501060400307a2100e621104071451000705d0307508030b50080c51285040b0702d43e4204261800c082c5855007480d1700315684103121042d07500c4100c80f150700400034541001c0c81c04140c00004103010041d002000012502084440d40024102c84200380074240542c0f5040000e034907042550765644413a512509080078000702d1010b0512140540703010301e005400400b51440e56035660b5a54440d290700036400100f026007550155030009030814882d283c5a86050004055189080915041034880b0f4100c1c5004002502d024481e007041c1940c40419452021041c500159440b21105003940c00380d60001118403040e640511008046d060b459845241c45842c1e0400800900fa54080e0901070a5441a91040c2c031b405060560722841004006202407030409041c0854442480c44181e03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 987933534 1250 987932284 987932327
    0xf0603190603030233071211071109100e01030b040609080703090620120307022409150606090d030e06040608060312070302030a0f0905060c0312010503030316 70
    0x80c4803028038000c0304010b41c00f0781d0041c20041c1c4800942545024000d2913920018000720100c400c0510350240f1030762002807400d0848603942141c110324050881e6014007801a4030008100381040864030b83c00c2d25142040c1d6486515640b000683c0d00310003040e004641c00304045100400002d01c00e03804456000d03125010118689503107a070b88044a41152078224080b950f0a00d0a1042d568400740b4840742141030100038442050050000c2d449403035030f601807030207880000000b5402c01d00030031508401c4101c07941c2030030b4400b0401d0000c500c45041510548650b002c0d00800704032000d061203400703001c0c42c00140f005d0f103000000810040e000035118000c9091048000b11100f580e40c4081c003400040403142c8030f121451400104141c24100100e83d11840103205018030004a903000090f11180080c070304100d0399100c0380040c1500c41c003002e03610441e4070510000d5138942c1c810000c006800251015000742c025070741c031681015144e002c121b810080130884000701941252181100c2c20b201d40c054002403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 987934784 1250 987933534 987933571
    0x90b0d2004020a0809010e0d05071103010e0a0c231c1704082b17070908070b0c0c0102010e0d140903100c080a02031003020609031501140f0a050f0603 66
    0x7406a0304441c8550300891100400c200500500b8000e12484000036000b4000c0d46400f40c0d4007400c503020b081d4014005400d0600d0903441d0f92000d42c480900400101d0459180d9109032401000344a12400b4041140c040c0d001441103260103400240f0b01200d0082030407503280031344c900e0b40c0054040e0700d9055504c0c1c0710300400802205030880c0140041c00047c00a44002c204940c0b0040484103036800d1040456039040c0104034441d4424041425022035034101c41543d26140c504440361146508801e52500440c800001c6685201c002031070944c0c50030741071300c180300c14100040e0b080f41c0d5007007684031480d04030b07003070100f20544680d014403000c0201514043c00c05c0c0700400460b01d002c2c1071459003140540d41c3c100140c1c2340c58201010b5980442c0050095155107000111070102420902c0020301908000c0b8140d901030340d051020300480c03859034184100540c0d459045403404503103008024080d42c0c000c1260062400c0a042c01800c0d141d0140c0150080d801d80d0086c01410761004009185625000105 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 987936034 1250 987934784 987934789
    0xb0412021b0411161202010c0905060f07080c030d020a09060219060b0102010e031303050c0a03050d080417030f1501020f0303180a080a1d0405062202131d01090b0d20 73
    0x1c820030300d4002c0044145d8100c0401c80a421100303401c20200500c16810070800c4035903988800c0741d00040148225984410355031070320340d0207801240c83c2c0009500011807482040c220940c09840042081e03030300d5640541d500c14044c2d84464100c1c1c1c815021141401420020804a070086140c401041c400080c0040745184184d0941d04842200c00c03101d00305010030014800100b00010f80c02c0021103811071100e245503a07503030396224105100c5081c41000e900003000d20517481c202c0705a0899009070b241e600c1c902210745100052089400e0a002d400703940e840c55055100007100c04038054010020b524685400d68040b24690711196086d045d8820340c0e41031030004100380090010048640c43d1119809904062001c409822880a030701492420f01000200d41c0c6180041802122030111003030b00200103c0f2040181c030828503030405a2000d080c2c006018102c0e0304e88400c1e0524583d440c060147d0b240c1207004241c542c002c14060703102900846440100b01d040c0c0514240400044621407001c007400003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 987937284 1250 987936034 987936067
    0x901230f0d0b0f0903210705071703190e0307060506031c122708030406240e0901020304031e030e0d030b03190302030f0f0405030a0b0412021b0411 65
    0x1140c501c5000c0e070901024000040b21580c12500304030146040c8600b030460017040e44040c522651b001c030222400f26580e180074004840c01d0381e801c40340c81c4107110014092014282d00a03034002d49040001c0284014a1030b043c80340749a28800e040c05186411055200c0b00c020340320280045905000d198a00016000004500c01d0f46515607191b0030300c00450a03c40d0700c2104c4ca51800902d16034140c010004000356012017036141181d000c0c10070b54503522141024002001c80c611072050314001e68800a1000b9038181e02c18048850018400301300b903030b0754004030b0300741d000984004001c40c10000c80d000e0920f00c2c05841003c1508940307030000f000300e07429480341c0c40c1140d401031141c00f11b07594140014580c1400d01007a8030942121030504107007025682c00a55074440c0104400901d280402c1082e80304030041d040782d000300402002c5803080805810400840701058404079803014080c4e0100440c0c0d030020403000d0324540365108594a1464485c14130015003c0081e411b65005820030440080342d100f0039 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 987938534 1250 987937284 987937309
    0x1e0e0906010e1308031b0c0106030c091a0f21070914061f03020903100e16051c0618052b03110d02090604270b0901230f 53
    0x5000349034035494082000700001015001c2140940d002412030007040051049a403c412001281103c4450b03504081170113000d4441c43c043d042d404c2c1711001040c051410100b40554281c0e110070031208540c4e2862281100c0d0300e92525800c1a010084140c6a01e4000803000311680305101355441c079022480c0203428819107400a05856a950114050781502ca01010741c0c0090180e5002203135082c1103012003919000048111b040540020b00d040d61501c1c140040c002c6402d220b4401c0c00340c1240c0c140e60f9621052801d00f0101c01d01115400041d0134a00980315903aa9010740180d1400406240ca824019000200000118a00e80344003680041d10410400085c0c01c140d60b0301c4400450768000c030b4080003402d00440741c101410722000b0f600c05d105600490f91900f4041074010390760400a8003007440c5000b980e0048900d13071840140040300030301c4800c851111a00542c01080038030f03059010440606008c1c0200c43c181025a210546550002c2e928400000d00040401613a140ca000c00a000b140010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 987939784 1250 987938534 987938551
    0x9020a1502010b01050901200c0d11090a0902090705090a030f080306130510182d060f150e1203030a02070201170108060f0c041e080f01060f1e0e 64
    0x1044a0a1041d828412034a03e40340900e4210f00e820039010000b8075060a01500e0486101065144018010100070800342014081e0065034055098141030481030417594405001e402e5110004489900d58858481401c0d4014004513094031400021191500704014254101c60394007804400b08020240658045202c2ca012940d40d240110038041070320600341005180d00e0901003403140703041e407800500003070798402e2000362201460070002c540a400804200c00c0c1554a403070b80340740c1110f2010307180c0040f265030900a200c081d41c1c5200642c50740540348a0710790051998060115001c0c0700300e210360f00f238540003080c2c6000d283c90341d6a80c0342180c0c0183da031001c07401e5001402c2821541c0280700300c0d2000c0440c01e2507691035032500c02001e4464a00403c00304840100d4000240701008400c1503074094a41c81e42c021268000f9000815002c4c581806650528840e0800700084407005014007010344071541060340080d0700e0720300751075480400712080c1c90740040060004103204080c03000703040c0b040c20072 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 987941034 1250 987939784 987939809
    0x1b0a0905220c03050402030309220c030b0108070c0512031f0b0a120e1c180b0301030204051501090303050c0c0618040c020a030206060f0a030203100e0705100e1309020a 74
    0x80c98600402c46205202c0d003070a00d803d12003000096039000c426600000713030980301200c1002e40c8592248031401c0b020085040d191a21101190841c4d040c3d01030609d400c0c2c02c0c0c8481c002d0ba140d0365001d85014400800c01051580009030034050440410003543e00f0454400c01007502d060500103211070400300c1c0e08840c003d0708000c11848207070b07640001c84218442c100c1404002d500c9902803440c2d00d48140b460f00c00c00303004018400d981014401c42c3c21800412201c505454565218103201d01c49034002c0c40240e11441c1440b0116181c000004200082814161590380c00350386181e80070b0b40c0710f400000051080d0f00890301c040342c20340c4915004101c01c964014050044580045c20002220f1038148401d0456004c020345d400040d400088940c1c11034130843e0f00d07000803c40785000445c1185940c200a4150046030704403010903145401c00740381e03a201b01054403c010b0701c030000d110903028041d12500000310062106a102e00b401404030200c1103000d0000f007050300064001c03402c2108182e202540c907202 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 987942284 1250 987941034 987941089
    0xc07060c05040e0a0e12040819020f0603010e01060f050c0d080709150c0c141e03030405060d0e0705102f0604050f01060806060a09050a09060f020a090e1b0a0905 71
    0x80c144003400007940c86141071410507040602300ba980c1c415050001795090b00000314481590f80700122103000c1c0f8030017004aa60396848001a008080e420320484001c510007010b0384a4041c001c0c0291503105a501000304010f082080d02180d02e92400b0f0126024020482400f08542c1c4502c440801c100b8665101c418810f0031510702001d10b540d140e4814a0f20fa00341d12031410b0301c0c1c1d80d00c000032380840b1619090f44002c6d420150010341940f045078070066002c0d00005041403195030f140c01c050b10301c1c4d4a00742034440b41075a840900444035094140714000840e0741c181d80300d00389007a81d000244030700210300001528030081409440c01e01c084c1c4003552182e0011032402c0702103000f406908050020000a0022800c01c0004140d44801600400364480d072148001800d003640c40e44030b50601c039044902070007103500c0406104020340c000c03010701e400200c0c04d0a02146186c28402c005024407030101080a04052040c0d000c010754000e0000d15040005a400004480e96a00071091a4210380c221900f001c00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 987943534 1250 987942284 987942311
    0x14160f21020f060f15150d020a120f0504030e0d030201090512220806040809030102131e060e0d062408030d051602070501110c060706021803060c07060c05040e0a 71
    0x901c0c103816429132000f00703e8000b03409402105900010740c2d021861442145003141540155083c09076010301c08222041096030046030301d40c030414549000c0000300307080403006080c1c50048070040c02207100e40d00384503100c0c1407c0070099807030b5000c0d200002e0740344116a903180c1071125580c54050b50600100305411803072038915407540341d945140c220384662850700040c951110401000541101f0010988c0a89920203404a0f424941c1c90a06281c40c2612844500c1c0c2010842000a2448410b1000450240d009151243c2461002441402c540c0e006039a100e01824214110701c00204d400103080c615006111204c0e005401c5210103103441d0088000c408040b41d0340207101c00140c820056449089070340204021094804c20329290149004a0080515203200b50280503000780340010b440003401601c0c0d01800c4c0301065460f1040a8000d01410169100d100f81c50600c07024204014034400968558809107404c01c05003010b034202a9030351072940707154404030381700c03100c40b600c8850303107540c00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 987944784 1250 987943534 987943543
    0x2041802040c08090a08070804151e020a0c03140705150d0b010e2215061e02160905100902070f06050c0a0507140a0203071514160f21020f 61
    0x30703400c41c03928030f4032890103c203480d0f900c4d003090501400356040060480d06020010045902510803000500e103180d4182200038902d100c5441100034181c00794010002151020544269041c3c0145248140604503114111810b41c0080400d0a520841c00006030f070381c85030714443c1c3c1c2c0c04819084442d1030b40048240d0005076106030402d50304003d0240c5818540e0307590301d0b401c1281c1d80340e140e001100000d4101001c2008003035500320419001f00c0d03020700052040c0d00c06418194030f01031600090000146820507030f584d4118882700000044068801d20124040b980425845a80c02d007003155007640d00c0094004030792084505440408482c0080c605000b040d01503e40c00c400ca500c103c41ca0020801d0700204140908d0100400008002c00705184010003080088075064000f400d90324095038400d80c101080401e030a00102241504040c40b5940c90304c401a501e0003c4021020f290500250345c1d00e00210742100700c01c8031000c107401c0c0c00618840180e0082200c0c4070058000300608171444210b180760 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 987946034 1250 987944784 987944801
    0x90a0606090605060d1821090812071e1505040b0f070e0f150d06030b090d02031918030c051203070507091d0d030b040f021305010e04090204180204 65
    0x5440c00c0102c204955280c2204464403040070300700015003440d800c51280351030390380c04030080c0c0792054a400174000b0404040184507100c80c1341e1242400c840d0749080d02511581021a0840c1c001c205111040100d0010041c00030b003180e0310880414101510368070540c0422002c6d0b141d541c05c56448041208004400307800e03a0b088204903030709004602e0320b02002803d01e44a09417550040182c56100c1040340c8600540c240d003242074107a03598440b01c1c40e090b0074004000902c016901c07408040003040c001d02002ca450707449480560301442c607040080d51045c3c0300c03140d00c0003000100803600e460700304000711180c0a031000d5803140c0d940b070080618040c00c1010011140c11504600e400820900001500000301da800306d03818250007060300000503060b40350094200ba802d05841c0a01c80c00c9094665042d4020441980c049800f00030450030f0600000c228000d103022500425040002408950300407541c240e40040018000308a5105c1030340820290780a01040244040c07644510304110300d418000c4415 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 987947284 1250 987946034 987946049
    0xe0303060111010203040f241406270a020a09050306100312090b041e120f0201021507020d18090e07090b0d08030a0c0c060507180605040617090f0105090a0606 70
    0x840c00d02e600c1f407550024810130001d09110210051a81c0b184d5042c40603501c51004201c02c1211194640c6c2c8400400b0b01100c0151280086901265022040741c40380321103403852000703003103107503030b9510400700250304c90450350042c0030f02c404001403541d0b0200000342c4134902590a009085156290003407054076810403000501425040a201007c0c090003510103e03942486802510402a4100c214034840c0b500144120303155180140248410b000031000c2080c801c0e402c030f0304504800062007c5d140c40c141c0d000001608030440030307000e10f8807401411145069074145180d01d1039849846208031f685000c1003071402d80085c642040403560724441c3c998610025242840c88105a1780c40c00c1080c4402000c95040703a9907034000040191259201c07007e00b641c050010441e0f802c00e180c0107091201242c100b022044a59080468540e102c1c1c001d90341110b05684401340c03e900804c3c036444c0585401407507501940300d407003048604828240602801404130303030007805400c5410b090810588085410400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 987948534 1250 987947284 987947287
    0x3020a0b0901021e070f080a0503010e09030403030f050307090521010516021203090c0901030602040819020f01140c01092a0602030306090a0b040e030c010b090f0114010c060e03030601110102 84
    0x10020294820044924a191303200550310342161400b5010340b44094000381030901d012440c144029005802035041c0c90405d0641c0851b81d8848042c242d8900c80c90100030009445003040c0412180505d002e540c10407944d0402d00b06042c0c503640820341000020150034611109020641e100d685d080c13003825042a8179503000065410f864102a45c4d44010918644010100000003458800240242a049580101021010750b5a0709150001e07420500882280740a500d10318030203000103000240701d40342c0c0682589010f4089100644000c07480b10340c0180c2e8941c041000d543d0411080c4103c500e5603102ea0b031005444bc10701c15509000d216a418001200108903d052154540010a5943c4a1001c4940c4440b50b5124820381011b00b10205025822038107001d25030325081c1b400301c0580342c81001080200108208001007084e4454195400039420b120840148104400041740703203c890010b0411142c0786030103a903210121106403900701e84903000407003400031a69009035103c0c880c0c0007060003503 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 987949640 1106 987948534 987948547
    0x1030b16093203150f060a0e18010506030d020a121b15050703090c030b0903160b01050109050a1d18150f09070602060c0306061603020a0b090102 64
    0x8907010811603224030b01c0350400091a4004044c1401000742035202c100c00d1850b84074014202580000010f44086035058086c0043c03401012a03250301080b4a8846240908540001d41513038803d4018a078085c0100c1d900080c03030096141c100b07010b80c00c2181100c506981c824203c1130302c001c410368000c105000380020034240d51405250494140b0441d90341580440884545a0300200001d40d2104180702150b181c2c400f86910180b145e084038548901c000315082c201c600f10300d01f15008080701e4018481560b1202c6914000c017000c0d00d4000450703041c1108406070180310b040e01c0050401c0100080c183c1da04803103403070f4102d980080544003040000381c4443d88158084130f5144003c514500881c1c001100016000e0484995501401c801c2d16508206c1c0c25551018000baa0312141c00e02858042d2003003102c50312060b51082e0010880b043d041d107804070107080c0082100c5034503481032051 = true := by decide +kernel

theorem cover : BRFrame.Cov 987769784 987949640 := by
  have h0 := BRFrame.cov_init 987769784
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987769784 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 987769784 ≤ n) (h2 : n < 987949640) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
