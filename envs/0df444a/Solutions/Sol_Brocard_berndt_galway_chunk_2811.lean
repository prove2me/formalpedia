-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2811
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:48:46.118881+00:00
-- url     : https://prove2.me/submissions/f372b7ea-cfb9-4742-a384-dc89d068db5d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 505395683 ≤ n < 505575539 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 505396933 1250 505395683 505395701
    0xd02031b180a0902070b07030b0406120809040e010e030417032a011410050d080c01050c03040506010504050c190e0604060903140303070203071709060403060c0807111b0f030a0303 79
    0x9081c0b95039503110356001c0101d200302e42c13015014554442c009000f4504ca0b8004400d40c490240c00890322680e2002200c03c827503140181100c005601091045071400c2c03134032842103041c412000a020043c1000c807807517240e00ca14043c4405c10640f82d03c5010702003a08004544103410461310b8204010018080001e041800f469254219420700e000f203015107540382d00c454000e18038010b2440285142804024105d603000f40b0455910200b0300148100080c28400c09228110103c040f55032481c19142050030b180058000728440c034503100038001d2440c4668155600e40d1001c065131140362080e89002c3d076040154640040c0e0096000801144441d88250542d0031a841021726a02559030145000d0700c90104480480c010703801805000041466800004130350701103a001c40b40f410080380301190a99004d82c0041d10b4030742d12000d030581100e81c4281982d502c14ad0034507000c04d010b01030503501501c136001101d840c80710384035550354070f26030b03030b4405802281701d10700102124404032071480c0142c06403c0e988 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 505398183 1250 505396933 505396939
    0xf030f0702100603020108071116140109060804050c091305010908090a090504171b0d090509160c1506050402031f0b280504080f060907090209060d02031b18 69
    0x2449541c0b103040d008210980ea41610790030300950b1800c10840c0d0b50400d05440b481c0320701c100b0b02d80c642205403d090300d00c05003803415240052814641c0001d49484042d07846202008a6441040042040442d44e0241c0360400c0320590241d803034449413100030400b20381c00a030065203031030ba81c131040008000041c070f68540d0698000b101c050340d03019042d0440c0c00c01c65000d4802c40042114201078280b020040100708800045c282c1c00b80b07031400303140c0d103400414800e42c00828181c040c1404030345000d06106030312800404104038141c13410580100390030702422005005c88641d114008800718507401c140050403000e081107403030345031a615420340e56550b01d81d85408010100313000f00b05200003800310f41d581d10170003e80800c5038241c004a0a0400c050f2480141001701c140400300e0007400600080740000c141c84014031640c1045591340b4101301c150352142070b400380304000015854480c0030544103043d01541005861356503c05608034201a641180d58003071200003034000041d1540ca280b0031a034a400c3e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 505399433 1250 505398183 505398193
    0x90b2107091808031306090f11011e050d0f06080a030e10050307020a112b06050f060a0302040908090402070f0b010501021b102304050301050c120402010c080f030f0702 74
    0x1030301400c003044072964000390401008000240400c1244c40e224100541b08090000c2d0680d02516a03c1c0003807026241142c400c501c40907500140d40c1c1c4412034110102c441010b05640d45100d4002401501c10791014000c1c19032105492401401a84d1200c0028071501041e207a5103141860010040204034a410344030312180001801124400c0c4252031143c01260000c3c005440c141e21401c03030507054500b5095106420181c90a521007804026081240081201c81400703802841c042e0250391000f000c210340c2103200c41c1007114541e40c4440c4501100d40545002804096a0900101e0f41c0710f49262143c02a0001907010108001000c0d490350b20b502039039403c3c0785a43c94400490301d80c4840c0707074501c100ac803804425400307524000038900e82c408100c2c2081d40304c1c2c01404010204da0341200c0c00020304044081820059800d0a0080e81d80c494144100c2e140340c40b824020101c250007014002030304209400c0d1401041103910402c654007000c0381c9402d59101e240114809641c50f404403180f0b0014000c5c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 505400683 1250 505399433 505399451
    0x10602030a0219020306010e0c0702041a0f0f1003020703020c09040c030b0c031003110102100f0e0f0303010b03180f0f010209040c1707050f0d020315010f0216090b210709 75
    0x1c560050f8169009001d003a41d0b9107803109010903920003070408480500c0c100010720050380c1d140300d0324102c500c03c0d450900c00b18466400b040300c1c00340400340060082e088400075003490780e40c500644506840c20706006880c0e400c181400c9207003901c04003035039030040301c0001404288040e0f80c054400712845804068240ea8540580112034001901c2d07602d8005681c0c402400001ca41d10502e110040040c8120b42c1301c0e00d14103a03c88103440a1a00124000c0d40c4c802038040206410301050b050240d500004510b135501d484505035a5100c010030b07194549a02140007861031105008404288460008448a0300e2503140c2c0700c3d000f5445161150b110300e141405006a150240c8283c0c5030b11080c80040045035554124103440c03e500c400c1e601140c07a00100251600402d4070710140d03010f04490341104003004081d0002600c129a541f03403403c01d40d803002405008403800b0441c0301d400c0c1c1b604c0360400301304002c0d1031b4003007240501800103031010114141e080d050030400018181046030103140f030034444a10 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 505401933 1250 505400683 505400713
    0x709090b090f160302011d0603100e0a092409050303012301080411010305040201031d03070c050f03060a0c210f0f020c0d08180607022401060e09070c0803010602030a02 74
    0x402070329115510740c1d0a070b004c02c00b540c040c903480d4001c05030442c1c42c15a1850340c040041c800b5030007101c414074291203000f001d00c2040c0301c11004e1070344030032811000c00c0118850b03142c01b41c00440b040824812002c0c0814040020100e039040702d0901d035400401c80e0b40f20358450342c103140d0040e90041d4041900f85a02c4404080d07611920741c19000d290401c04210003c1c006600440c0940402407050303051585450346020203201d000070314212a0311040c042c40d2115541e18081b6504072103648220b00c101c035510354440496802098940d0400b801000c0021a002101001d0351000407007140d101480361072441f81c402d0b0343c001d900712441080d02140108440b500000b07116080f07008d2002c1400e01070340041c1c0307031b007061ba0f00900d0469004016413142c007050412402105140c48000c03540c800050300244105ca40c4007048034a102400da00380c1403861402e40c14501d00600045951010030700c01e00d05800482d540500502c02c0c5031440e600007440355500e684960001e90b487d4411070703c40e8014030034200030841d118 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 505403183 1250 505401933 505401943
    0x408090d12080912040303030e010b0a120b0a020703210b1905010206060d08181504031a070504031104090f0b070e0a091b0509060c0d09061b050d110709090b090f 71
    0x1080380c0241302e0406045403004c07402004100d000e10010741d80c0300d0920503150341d540d8580c80108140c03912f034041e8001d03034a850316606801a2107100c41500511010700000c0d004002c50841104103454601e1040740340f04ac08000d01034503000079030071a2001e1680d18a1481d0900303110f00b035074001e8084071030584410040c402c50040a14018104030b400340300d0100c0c8882041160802810010001c0210001c90042200d60398800e91044500007850480f101d6021924141c0701d5100c200c6091030b9080c00e146803a868951665100704920484d511010038080001c081c800288258100c0300040480ca04040027406806010321100d12444014000180c00300780c501070000a140140848005001d0541080d26030b50406081d983d40038800380700c0f40305050320800000058080545c1c96801962410b01e0140180112034654844c10000026017004101c0019680c50012032901c0c0c1040d44414100e052810202e0176003012407014249241842482612140eaa0081440c401624044650003041035511 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 505404433 1250 505403183 505403203
    0x50f0714090d0c09020a02010b0a0f4101080105030a03200c3c01080402010c0204061d0a0c0c02090f06030106030b09010905010e07080309090408090d120809 69
    0x244a10000e28100300c0c81805450420380103000e00c90300030410b503650010100030f500301c0301c21140c0c041032410801e6424000c08854850030744a4204e0b070303428074040001040350b6014881c3d480c2c1d001c1520307040e40c8030351449400d54a00c0803049506e1020314000400d1000000c400c00c280002c0c002400407070203140115503620a10f41c1510348044207588110b8020400300c1c3c91086505501800b1014101500c1e6100e510540d84440440b00070504410300045a2245803680c11140340303019144e846925981080501c2e411540900301280741c0c041510006002e8a643d8000501b0a481c0700d0605e043d20150740710190007050f2000003800007108080741210030070405070002e54405060703004608990500d4420b00d0f082000030f00086201912034079034220b0000180c605104030380d0758031b44000170300500384030714500702d82008003401c0b80514200c0519900d000380d403d5944900d0b0090301050401c8601c0003202c6000c600030304a012503140b941400a81c1114030702c0080c01090034100001d98100c8045814440 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 505405683 1250 505404433 505404437
    0x2f0102071b06120e100903080103030212030f010e1005040e0708010b0d0f02092e1404050106020304060f091d0f01090e03030406090f0b041b0b090603060607030927050f07 75
    0x1000e401e04940c0f002070444d03000005001d004030110419203401e640141c0d140140651640b440d19450b43c03030000c1c980040d01c84000d10031002401400000d0000720012070440312881c070a150291a0307a2800e6204042540c0700960044c58404038001408010542108035403609008100c1610604103000e11207200c014002c040c002c00302e403050014038003100c4860708554171182043c28145080345840a40c40140e81c0d00d0723005400b01e0710801c0481e500029504007c9010b80302800366514003500690b4070301031401000c00b0300c041018041f809a01c1402008001c1090f00300c003401c16407408003201864942910118201c0300c41c0c5001241180e1940140c034407082d40c0c01300a6280d641c503500c0b034a00030011400229810810016030101051160f480240541c0c000c910b0f142c5140c80b8400d203a40000d4003940141900c400134000d51403195203900580783d00103415910a981c504161030200d5400e00241c1044109120703017950300e45400300041c040c400300096071100300001d484900c0500143c120803900040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 505406933 1250 505405683 505405697
    0x150f010f051f1b060e01021b0c0a031e1505071e0e0105070c03051b040e0a20060c100204030c050108040b060f030c0604030b1e0709062f0102071b06 65
    0x318962250300904100f89142103c159404550340e100c10907a400d084036411a603401050101c06800391000750070390000c0c4040100b0483c0e03915800708104921622028103541148006c1c40d1103072110070b01000d20a60300111250340b02400c2c5416400414080ea0010b00080c00c4003140d03030217070a003030b4500350200c0f00940b1400040d15076000111996800f082c0211202ca102010020014900b004440300f18102c644d03000300440080380c103004c11180b141a09125640c070401c004030104004039803c48244030359070b1070000101021004100e0300c0c40741288004081c840c61420340b0a07010a03a0160094034403801101200541c2c44004541c050820f0300d002e090007641602141c1580340044007814a164041c091303500d031110700c00002d000b07904141d1050750844c0300e4004104c0c1e0b03012801904000c05601403800081410403a900604c1c00e04c41b03005241c14840401c240045806000700c1d035010b1242801800f00400b10801c1109010f0b4101c3c1a04580c40040c1260003045040c0d4820038009440555071903030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 505408183 1250 505406933 505406989
    0x60e07020a0c15020a080d0507080f0121060216030f09290d0b3001110a0f0c020a030c05040c11061f0305070608090609010204230102150f010f05 64
    0x18080843c1c5031030701c1c00e5200b20031049000402c600d002c1c10b03411500b440c0008203880c01080140c601000101350171041903c00d001404118001c1c3c0000c6150031900d01d41d0003007042c1504d40840240b0685211800c1e800da1022341d0750070154070080c2119950541d075246140d4a51312400540c000d044c4809854518902c0444a107a902c61400a03080d5801071500115041640c507001c92654495550b682200407400442104506050906542407148000080089018000d828000f502401080d41e0401000c000300418540c81141d19905560300144110009a034a18004042c3c01c144e100d00c3d4016410a503041548501a0700700c20307880d000c00d07006030a180e61050300258100304000741d401c440c008100f20210118000b00b0614001d003a6030b84980c642410029a1245000030040005880c0d071b0041005120b50544054419080340c1410160006820361800507810b0840003019111030034522010403590040004059040301d41c6e1450300b810309503c1c3c106000546204c40b00510108203464048 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 505409433 1250 505408183 505408199
    0xb120318010c0807020a030311011d06040b0c0d11030403120209211513021c0807030302030c0c0d0f0e010c0308010b130807080321010612270303060e07020a0c 70
    0x5581c0380d8071480790075144c040c80340e0000c0c1402000750000d80001e03030313000783c1c400403400c00740709400d00c6000343c5080500b01545500e1180d51403200500013820109a000420b80c80984001074130000410482d0a100f030002503140e403509500115000c1e80001e0089104c511001e4a078400c44404180c05009581150442440102400c2c001c2031500e846100721303261070100f00b00a900c96070007400d00e500d04802c45455801000b808080d8040303010034800d600c01d4000300044110088400e03066042c18050b84030307034070368150440318041c0c03480c00d43e010301802840082c2e05500203407e0001c03010680b03a00c951050158011240341c400204014042118540144044203104000d0032a148040d50355070506a01c60341c83e40e0900c10141c0c08241e880c0c2c0042156401d19814518268142a04020301c071b00641c90500020045103c0c543c0902e5002e54541d640304144405841c030341014502111440c428600d180341c010002c045c9440780401d40c540c014082400648045070b130481d40354008010360302280c00c2640f0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 505410683 1250 505409433 505409447
    0x5040203010506090d02060d14100f0b0307080c0f030a02070204050a0e030a03050a150608012c070e03070b0a0c11030a080910090503150109050603060907060e03030d06090b12031801 80
    0x707031f0b4407410074000801c1580003401810041c140c4415100600d0520f00c042001084081d000303405092041d0805002c414288000d4075480b80141c509000c1540b45d0b101082c1c074900c2003504d0802080c00020030400784410301c0c0c0083c840c583c07081e50204a0340c2d40c1c012008044590000100100b90010031042142d01d109400c0160014101240040e5041c0c0042040041250643c06000030450a00c0100841007095aa44909541300c0b80c040c0c0c4101c01061031900383c503c0003882d440501407500000141030301c080003250081c1100120866070341000301005484003a002404132102c8170091a041c18500b00407031400242503001d4119420003030410100b00884034607110310001c2001c03000f80005c069074208094035039152140c0381d41d811035041c0302603032080d640300400490107540800244010300c0400520441116080e1400003a1101000006800c611981c1c041305015400c00d8008648a5000e40c4001641501103480103c10f040500885842e40139602481e11108010021400f840d4040c003c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 505411933 1250 505410683 505410709
    0x1c02120a050c060f18010504020312030a1d011b090b030c030624131e0b0a020705090c09030105061c110a081606091d01140f030d02030c06010504020301050609 70
    0x4040342840351040d9403034940007040b91500070088080e82170180548102491000d5501c0e8400280168949600400c1c1d5910312251540d58110000000510b02001c03a8454022807616661100741c0c403500302142c501814113528108000a0050001002540100c0400089038540c00c40c050075650f0740740101041303410040009030001c0511165040440702503407181c0b8800700e00900a0748800704020b4030400c21805030044050300c503980c40103164180211840d031044a40240300940e035852010412801c02c02e1541c4107507009020002480b0b020354045000c0c000b108001d5008020f43e41d030314010001c1c072007c00341440100002000d00e21010902403213201080f10350103424041b4444d5500c8146240225002c01349070f18084e0713500c0c01e000269001540c0401410505003428041e10401581d8040b0101845a00707441417200042600c10740ba0441080710505009094580382054007001a482c3d904c0b44007040300c14058070b800421240b07442d20a680c16914082e003014200101d0000f40301c1d002440d48 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 505413183 1250 505411933 505411937
    0xc070201021504050a1b12020904150e06090d05031006112d060a0606142a0607030b0109060c0311150c0903190b0f100b030c03091c02120a 61
    0x640d001c01a0a40040b655004503c9000180000e00890905407080a02c1c600440740000542e2000c01562525030480c400b01030301181c10742e03034607125481c1c071f103250f585800c0000a5460400720b09031481900442e02e1482583c00b60b05607902e0700c00c050003c072420b10080741d845000f12000041802820b104100254601c40c41e4170889076031140d00d00740326030b14196140d80540c11703080b64091070619840c103100d22600240140028400c250410102030458a50b6080305806040041000c0450628075003100c08030010360f5582c1c079800079a620340c95840c0c010455455011900708030088800394842e4842030210b55042c7e03a00300d4000c2155a04840c0c4007a80c0d80300a00620404005d031030a101082d00030741c081c02010b420b140d9158112402e00d42400214400c00c5440740c0e6502d1114086407424104030350203400060078016030b9494a0b0701414000030394009075091440402000341e01c03000780f4000c42c0980c222400b111140c000c241503124503174082046100c01600030a0b480700c54141800c002d4141d010140c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 505414433 1250 505413183 505413193
    0x30e030307092d0909051005012321010207120c0b04020103020309030909090d0e0303030c160f12090f05060306130c0c08070605040624050f01030f0e060709120b0c07020102 76
    0x746003c262110040d0030526890f50385032034480070448200512038804403c0070052110358035049024109542040082e40c2a8040c0696001741d5980d0404c10396036484000c00c95100d00140c0c1250a0003900100382c2125603d1141403140350050045505900c1c559124103889207641e1660b004401035007000d00088001e00c414420782c1c4c2a66612481c19124490003030041001715240c9100604102c61f0340c0301c0d907001760400c006005590070007004545051002d560710020b035018a20340070b101d982045a0240c0031500501004060942c000d002500f00c800c0070306010141034440c000c00902d84402d50b582e070380c400c00110144070700e10b00d680c114010f10f421500f810050100103480b10300035684503103000c40d842c0f99980104410010103100380107100100111105d000c0002c0540b18501940500800c0d1040d00380224010241e84207400c840903100030860203211801d450748d24295110001e540410100d40b800c5404916424884000900da03030b003004e03902029840e80c846243d150b61012070168114014 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 505415683 1250 505414433 505414499
    0xc08130827040c0c061112010b1e07060f050106030b0603061003181505070e011b02040b0d050d1202090f0103090804031b0609060201021206271303030e03030709 71
    0x914420510f207040c01da1074080d601502440e01404644107041c0c91b0881d803a003407140820a1001494560544030710511059464100c41c000740502800c2c0c04894102240000d8000100485900940138010061070240240d90b2038184c1502541e4a10f0000394004109200050251a02c0a081c100350340e40c6080c00546028000c1c100302c0b14502641e070958402001425586120354184903031a072010752858280c0d8501000000201540920822240c1c1d0701e0b002c1030035000303541c1c41c6d9001d07002c0144000c004004401403840c040c1e482c2c42d050686040802c00081c40c1017000401402115a402e000810140380001440015001005850019103010710248804000207251411441c802882d149807040002d1902c10010b21100341d6800030005c40e4018404007030700065581080d82c120f00b0803203240500c0c0a05031144024025051109032414400c00c0900c145030541c002e820b100607010340d82c10300c8048c0c1090183d5589102c140d03540c0001901c10b040c200304d81116002400c2c010800d504c190303460035003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 505416933 1250 505415683 505415689
    0x101d0405070302070c050f0306160210061202120a0b01050d0303020c030d0b1c0b27011103060f0108040203070e190905011d0f07171f0c08130827 64
    0x40c0444900010035800212003052042030035420008100883c0d2074850b2032124030200ea143c042c050104030002e000d03031040890003402880b4880812400007002c10000340d131003003a8507690041201c00c1e0b0003500c0c11013040c03000d6640824040012900030700301a54503441c1c00d040c0414810f0310ba01c1542010350902142484800520041080e00c500d4079021404240c81800c1111240718032210403509466500074034005a11300105543c0484690401d034140c81d40700c41155a02011180a21410b518000071a150f003010000038502a14058442288002c0c0c41c81c01540e03010800c0e0740107035040d41b0104040142c01c04002042c0d40c48000c0081401602600a0713101050b5007020308102c602d41d44581c1100340281a03100c26144560500f00148201e4020424540d19030131140206401c2011742c14a240b0200c80806c06102c89000c1201403040c1030000360300d0480104411410440060380840c00b00307002004410380c2d4450b498014500b42c0c60035810a40c030326482141403002001d074041007014449156 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 505418183 1250 505416933 505416941
    0xf061f0302120f013201050703031b090609150207140a1d04051023060f0303130905100e0a15050a03050f0d050310050607080705070b1306080105101d04 67
    0x403081d00007001e115410b00c441d1980d030b407101d4881ca8900040e207400303030512400c0705c84182d00c0c4504207003800c82d5a081039007000c8001d44440d8282c41843c8400103094607105510214142c11181300b5070310120700513100c82940040e15200109040140e0082c0c005114541a2111390380c14040004c140107042542d612040102425000312100d15403440401c000900c4400d0140c8030741030ba1550000c002c40f42c07180d1030038030610003c540d60f1180001c0300b000280710b0351140308440944090040880b07494103410119460b010701203024040f44e2500700000706030040b03031903d0200d05a6204c1140e8202660b20306403260010310a14400d207070b00302d8910200013130700d840d1041114040d40c000d901919440e00d601e4400c40c50312040361440d0701001001c00c204240340c0fa2800011041e100700715a031542d00c1e144c82c2000000c50088040140c01806485800103580c00c00100501c0741e1044400880d00c1c8a42d10001540e00050910905420952a4a42542d8a03100324503030520740c014070200014900603000420111 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 505419433 1250 505418183 505418191
    0x114010b07030e0f01080f040c0305060c072001050a110307060204060504230f120f0106170f010618090602070c090f0608030f0901082d06090f061f030212 68
    0x14000040d9107060607031010865085450584452041e2051400001e01b0600000e01080c4042440c1001c2802c001440d8600300045422104440c85428914003003141c030360040104070381810350010700184540180307111082010050f12800d0501d184190155462080184194102e000410103140026498400f400103004550784150722142408000080445011040c04104004188803a00d943d503a855021441100351029a103050050560303030314060740174203600640d5003404030111b9400c180f00700903512030201e6000c5070001c036803248501d0f089030924050703503d4400d004182d003184200355402c0704004a219220041ca405803039152914140081e42040d0360480d03e400710081002100d000708805448544050f501c2c11006c2c0b101d00342a84203a080f21414440e1640001b1408510703441c54146034900704a80c3c14815980b007054004035002203a2042c0704003404000b00e0108485062543e03c00c400c090110911060f80500900c09a0103004584080540030080003401d480c3c6414070f1409 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 505420683 1250 505419433 505419449
    0xf0a0305120d2405120c0604030506060319030207090c0c080d0f060906120b0403141204021c050c010c02060c010e0606030c0d050304091515080901051f0306020c011401 74
    0x40303041007000b02e41518100c0c00d41000081402c42c034400002d40b494511021102c044684103070608018503a00d0804c10301031059644018003040000501074007080c05407042000b01c0940ba007000940302d48022040703042e00c0140c01a80120014040340155503c002d0b41d50040381000111084107a03910a601d03402800741701080c640744d414210800c06103004103406450000420706c03130181003203a5160010f000b00c401412404a140200e01418091212490502810342c261507407128501d4801d40640d80c1607500b03d0040c8030040c1c084918034402610510305540c0100601047e009040c0111040d501c1e081c03081e0791240d070402c0007204020003442903043e01b1015402070046860100c0816041c02e01a4202c14000c2c2c200300c030501c0015902104803400e0740c511000016191034440103620303400400344c0090742c03c01d050400102205030817444403845003480c0c80091100340c1c1d5100f61000f002d042c0380480c8211f0b442d410428000100c0d50b8000c0c01d04d80541400001e020860380d548148a0802a400050 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 505421933 1250 505420683 505420687
    0x70c050405040f0204060501081308220305060103120302070c061d10020a150501030b0112080c010f3305011b02091003170306060f07031106041b06030504110f0a030512 74
    0x11070911b80190402403000342002061ba240c40c0c3c0c110138814403080c02c000d001d07a0703002680b001c20f81e0000500c0d4083d118400d4141e1022520b07854420390300c000a000a680000312000b071100000c2c4a40201c40d038036507102500d00402c504e412010303580c0f42140f0040040c0e01c0c00212018089444a45040304500d866034001e00031600c0a06280902c000300c120940203a90a1000610108030303680b9400341107941948454610103451304001089001d410f20401c20307942440d40241d030002c0c4139000300f8032002c0951501004101070b810781d0b13400c0d0035200e05a50b02a45617403004000b00e60061381c440c0340301c4152414030840104d0a500042d0039002c00c442c0d035a202c20034440240144810f82c2c284c05061034601100c28914100348000070020700501d0805401ca147c002415010144242c40070f2441803405400c5075524203081c640307140003408002c1386510700f200200001407064402c1c0200d0b4001d9401545008801001a040c0018542c8003090f00d03800021071900040040c10421906c0c4103101600b40c038035 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 505423183 1250 505421933 505421963
    0x14030c041410050102120417031621030b0f06130e01080708010c170103020f01030f1e151d09120a02010c02010b0a180507030e030a0e10020d080a02070c05040504 71
    0x302d102d01542040341107510040c030000031425100103c0d42900c80301d15100031301c21280300c4494030b1880354815a1107000401c10300d44040200000001c0c0280c05000401040d0900100c0120120303244c00711183e03031103050851300003020700741303803004000410305101070700801a129100d03c10003100a034440110369010800c00c00c5a50003e110b41c05000035075103002c4102010708610402c18400600010388101c00c810884070103603000358010900344040c2d100500c04034400c410502084004201516041810900300c0004030945c420000241e074541103080c5820300409000d03065492009141c80707040d10400303030300740c2c4500301810241c582224594004503051400302e03002070175180c0c81c40410380904e02121042c0320400d106a211001d80000500c0000c03035561b43d040072005480c01c160003132614040003444034442ea0380007014810074103007500d001c4890a1400000ca940d801178500382000170b451400801e41c000802e0300284105802900f819080d0740d2590001400c44905680403207038144644024 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 505424433 1250 505423183 505423201
    0x40e0906010905160f1715031510090207110904050318030a0b06060c010b12030703140a09032604060909140411100207120807050f01021314030c0414 66
    0x7409004564018829801c02d15290740000b02c0f10f000260600c00034001c0c00711003038031940c2407010201c030000c0c0914040c200701040c08070500b03c0c0c0102a029014003404040d2005002982034060b072541c80b2200001441e10281c2002500408400c45049403180981c0300703140e9548203920f000340d010700042c0d5551401c00514840b040c1c2c100d12180c1c040c0d0410201c40340866070f8070320401e40c01401510100e46e940400c4040900424480683c3c1f0b41c000c4141c1c00c1e442807042c000000d008028805d1f11103001e070103401d4041c41954041c4c0c00c00d40d4000741c203038001840010506000c444546a081e400801d1003030034822000c41680254001c031001500350201004000001d00460280d2240e81c080c2240d00c0c00c0c103496075401c0000310b031a41c42c000c40b0b00544020499108000c40c05c000c180072001c00314400d440e40780400c0c8590040105a50714400c1303091000e106001803084460282c01c0088600f0358510704001c3c03e4130359600c1c207141a4107002d0075001c0491ba031542c3c018464491480d0340000c000e1b1404503c2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 505425683 1250 505424433 505424443
    0x30f0301080d1404050103021605010c09081612030f0207090212311b080102160c0e280b090403020a0201080a0b060708030a0204150906090501210f0b06040e09 70
    0x1805003040200e0600fa41250390764000c440c140c41c000e00c0c016079030710850383c6a0b2151140156000f00250318150100071260362203421101035030541c40c03c1d07460702c00c01c058101c4210701050080383c003464040204a00000d004903544605034000b401900d01c0560b649018400700e0300309040303a194850400b01000402d1700e0301500d10a404c1c1000c200d03403440e405901569464a006110000d1507903001c071084255529061701d44900074074400e0000d555550040074150182d25000404446421403000301180c11f00d585a003c0c0c0c46210710140c1480406c1d0485e0542101202c60080002202e40d80e8070050400d40b16098024445c0f8025001014400610b00c001400004010110810280f4102641d01c081d91250110303806150008191034903030b01d42000c82c800a124581c414141003c1c0c0700c0716481070703582100c184801c0340c005480f61400940e40d500151043e0955683c4d0310914101e054890306c80c410160f00800313990100650000b9800c000d030f0045030207a807040e00603800401800c02040325403401040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 505426933 1250 505425683 505425703
    0x60106030b1c08090f04020409060f030605090c091603151d0714070303020c010b09070909060f1a0a020a122c0303070803090c0901090218010c0302030412020a08030f030108 76
    0x5010003109020703210f402590180d4401c080c440c48242c0c5680485640381e030140c802500d1503a104018182c3e0b5090783c03a04103000303444102c072031604100005104510100d41d0304030b00311001d40024281d58540ca0f45040c100d0800b45698203061703881c440801000a20f1112130040d06454010448004940d0180e034580c89004010701c0400080c040d002a4400c4d10009036084240e043c00c000d17072a1440c1c502c166016101000741e0035044105171082204860b4000c8840040f1484140c080110640310302445840d0a02e50180c60ba6a01141d110304407501d241c0c000904044200b0b10584109a825580c0c40040448601d608000104441020303007104048071207a850840e14940c10b409000605404203889014100002d0090100400011100030050012241c8030700002d281c500d5940c2c503440200001c0d0004100801c00440c8038042c08035550040020070b9540d0b400d900218105803512a50141801c0e061100300d0b0018181140010035540800142c060503503480d0b105c5450398180001c007032500010039 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 505428183 1250 505426933 505426969
    0xf02010e0a05100c02150d05041e0803040f02060d06140f010e0307120305040b030a0204030b0106230d021b01020903120418020306010302041809020406050105120a05040f05060106030b 81
    0xe404209681d5a44882c4048003c54180f007031800c1c05030300000c0c1c071000300d50301e00b07265009002480003601e5845902c500e116074401d610300c0c0d02c4038240501c04280c04240960081000071f0400218001c240d000e800c0242d01d42c0300410180c5840d011150000a4034081d6010750145000c10409245501c3c1c20b2052229429080c80c06240880b000e100003550354a0500c40d4055222100500d034040c544a8422203001e4800880400c0d0360f400c3c5903181100030360161005490b940c1c0418000304600f84101d084481d8a103042c3c18101c4513400101107500f42d9480010070802c03213030b42008194200b0700288501110f000c1c00d40001602c0d008840b040c0350600411300050500400100001d11080d41076400295001110b003100507200d0ba24140142d00910640d04800e205070705004514000e09196000010860703c2520300348034a079981c00c0152403034041c94100c030344545000b10005891160710784c400c07076101d8003907410301082d00800e8035102d0804600b0707000f08000a885000c000c9886c14071a400e5850700303e0300 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 505429433 1250 505428183 505428199
    0x18080307111c0503040e07090f0e090111030106201006170f06090307030e040b12060a06060513090b060d020313050f06060108010e15060a02030a1206030f081b0a0f02010e 75
    0x83d0795416241e210b0390181100c81ea0030040890a014402c2c01e820b0040c0c0407820648442e262212616641744034121a41c0005600301031503000c42c080ca500940e8124ac4043d20303201d0400b40311440c03903100051006001c800901c901a61255429414050303103005019984500740000d95480758a030a00004d409070004690100c0d0034808180340000460f5019509850110311032903ca40008014104030000141e10000308618006c4901c40450307810b0042040350f00821140d5598dc5c01a56240190b1150448c116807144c01040003140c1c5400c2501b2206008049900c1c12108512520407a00103440000c544042816000c0400404111142d041d01d5813400400c81850b10740b00003003070b4403070500901100040090200740b0b402c8614003420b114480c02000c841d01c40a031180c00a641341c01080c00d260006d49101e07604014240d442c4100015a0340140c0101614040c50311008500d512203200d5580050b04620790400c4a0814080d10801900c10602540d40111500004102c0034240061705d20030301d20 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 505430683 1250 505429433 505429489
    0x1006170706080f0903091806011205040b0105060f091512010f0311060c100509010506010905010e280314030915031003020f010c051005090f120405011808030711 71
    0x308060a500101004003411560344e646140c6065014100100b03400c510403032054110b503008031307001501c170729005c0e07840307087c01600503a0003c02d0340c1055401400605407040103001c0c500b0320000415032003c0950215103803014001c04102d66402c0000c0c00320b815a4082100100c0342d80700c02d0b00600614042111100c1541542c580c60b2030561210203483c41a0030002d44180c000b0018449401d0a20001208211700d00d00030b800c00303002c0c00007100c0c884e001603403c100214280d0300801c085080c0603c064104000b000c4103051044000b008103040c2e00c2c0080300404004001a0010b00f44000c1e4000300c0c01960301d80c10034405000380031051030f04100601d0030910401c84844451102c2208607901141e071030613100c8201006892014001c10050118010f8042e034602d06101c41e0001400344807505c088175562540c0c41d00f0706844503c0c03035110381c0e40d08bd82003100b044258032500c46e000c0980c0c80320341c04611144e03844840c0340c519030189408803014142090003500074a0969800951042800756414802c0c00d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 505431933 1250 505430683 505430687
    0x60906060415050405041103010b01051e070f0503041212030c021504020f04020708030609060607021003050403050d060801050f1005010f121103090307052a01050c0f1006170706 78
    0x120040050380103940e5400c1400c2c0c0701d14030441c0d000c01010050010052801d05061200117503020a140502030342c20001030281952149003103440002001048180c910244524502c4650042c4402d03503200c50104201000300d01c090000700f00801e024000c503000320090f4a81a0903280c1361440074414146054070030354556402042c204c00300703040d001035000150380b41d00c0000c80486800903426000791011070b0f60020030407800d0085014003001c0b114451f4643d0340008014403845072101c025001600d80741003840e214020380120380c000e803103814140c3c00c00a8402c00c400450728203070700c000c249070344400610040c45483d0302c0b0036401440041d00310004a04150018100341c1510411100704a00c200e9808114030040e40504e0b04010b02402c003d50b6030074004852640d94004510943e001c0c096209840107078100c441070507001c0030242c01c2d005051100b41006459031741100c50f081159002d540030b0405000c40078480542e40072444040015001d003008010824405d41680b42240c40d440704030140035081d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 505433183 1250 505431933 505431943
    0x60602070b03060909100f020a0e060412080304060f14070f090e0c0f071a07020d030605030c060a0c02130c111501090b01110610030605150a0e09210c010e0609 70
    0x9040d106100580c48515016240130303e036a0024146c40d00e40314201c03020b00c1054000784030340d07003140c3d9540d260004c0c282c040281c5807246118076900303400c15124000004e0348910185900501940000640d112002030440a403000c030b84260300c0e0106888100903c990304683c030000c3c024014a02811a5401c140a0780c000c01c401802e2000ca00740f01083c000b00201502c4221030040f5440340c29401082c0403d181081f000170150303110005409044100d0f42010f01c288103080443d41c0080091204800301e2041c000142c2c010106902044180e5170440090307202c0b25540c41d1100d41d40c1000159601000100a0001c000031048218a80000a12062004904019a043d946162400101800080300580d407404e4045500c04140c0a1001008640b2009490740400c03203006060507c01e40e41d4008245144510051406038041640007051245034140f010345948240b4480854440b24001e030760341d80d0350045c108103ca840c281e001402c00d6045000b80540181508494014405401c0c4074000700d07258 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 505434433 1250 505433183 505433191
    0x3050405041406131a06070b07090b0708040902030c070b090606030d030e0303150613090b010801121212020d2d0c1d0a03140a050c1002030d02030a0905010c12060602070b03 76
    0x15525078151051019001d00b90701c17400c0030001d000c15650412841c0070002020b0072280e01e00410704202c1d00140d0a5403070f9085a0005d58088a51840c103800d1041c440000d4001610107000c900e000e10464000804200d0903901508407a0002d00c1c90b0714011082615020340e04120340708250500c000301d81c85540000589800101000007800307540300fa84007058443c080d000c055801c2071004180010288140d034440841d80e10b084c1c0e1811026a02d98503d50300c030703c0e80d400d8020091801e42c1d03124081d10b84199a0514a141002c4000d441c08150750588416074081203c5d642c00c000781c0e0781d441220203c2006e40c1c0d0000308005101400304880c0d01c01c001d810b510307400d003420a402c5015880d8025980e40c51042402440d0301c1401528501080c1b010165180c44c0c8410407503c0c2e20809003a00d505241910400400c161658000c500e048c01803000a40030390009002003c00d162104199000244203010340e080c0e0a940f551040e07052001010000152042a40100259044918140316440010084940c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 505435683 1250 505434433 505434469
    0x110105072a06020f0318010c2d030e010f0204050102061509072703060b010210091e0501020d0906200c07050f060903010504030e180603060a0903051603050405041406 73
    0xc0303441c0904011000c0d02c00c0d00050050000000200f051004410140c140c2c40d00b1408004c01c20321444100564003410541d00c1055025202d20204841d0990f02128441c041c0d00b51030003090518650000f242500c0741401c000c500703550049024006c03943d04200319940001e414034240c50f400c1c1a040400e02a44000e0881da00700a03884100a00c0c045240014001d40720302c048008404603903d0420000405480c841d1500601035620701410088807801015045504060300060b4401d03584009a402400300c0c0c0700320380c0e6540074044014180d000303114007821540190004141c0c1031001c06001100840000c203500c0f905000c1c0300717500d80c0800000780c0ca4140c66003528069408111030002a20300d010b01000a940343d800c081c208400c040c1c1c072048507120484262040e00e403000040768020302240045071f915402d58040c8000522440440d0082c50046000c1c2c1045490914080c031402c1c402c9040d0a01a00800d00016040001d0f040911403190380301030810300b0101d241400000244008814103141c0c427 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 505436933 1250 505435683 505435757
    0x10503060d080f0a03050a02030403020d0e13050906060f0d1e0204020c0307050c0112020a0816050408190203101404060902060d0e06040b0604051003030f14040611010507 75
    0x45592a400000c0da5203075044601c69484803c5600000625400140c3c1a80082d05107000b00e017031001c160080d01e00859141c1c01400d8501c940c410111046107440081c0c80c1e01c40016401d00702210030b50710805000b40304001c06000203140000c180300400703014001c0b043c0114076101081001c40c0e0080541e800c00303010b0100141d911032840c00050003034000d41c0c030680300318000010b001003003240000e18028801d0342a03e0310031064088202c40c00480c040d40a0900c08140b114002442da0800c12102411040c4035080040c2090f40b1407280c3e51070401044040e21000300c40702001c00951074208102102448010028490000c0038501e5509a10000e440104840e4888403d0000c640c1c800040d0354040082910412588030302032403035551403905403070a503100c10125010946034106806490300c1a12881c10581034140b031603604450050605074207000b0040761071620362148403180014401040141d5640010380c100309107490869501a0900042c804054004008503d84c01c007040d000e04003a00d0442 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 505438183 1250 505436933 505436941
    0x31703010e0c090d021e01030b0a0b0a030902150c06010315150b0702030a060c02030403020913111306030237060206180304030503071a010608091b21030309011514010503 75
    0x49a124407030000a521150b86d002028817101c80c0e00145941000990303003402034840420034490781d1211030003098035a020800000042c40e0182c2c001060b141e2028140c0030b03000e40380d0003014544d07070000780780b02c44c01d500007500400a00c02400e801c9010403406500411010405c8050300a0500007480b41b48840d02000c5030142c15542d06008190800c3c1d003154007400701400c0d00c00004e403a60f00c03900003280300d84140342c0460b0f202200140500107451784103d84e2500e0000143c00c2220b088030414403c50016254640440182c80300708000011594410000c0e201c904900b006c00889810b10580c201d142880010070031850b0360024115400c50580002d070f10074511070a01050840c49a41c00c040c0c40f40c440000c0d4801003140c0c150900c001440c2181d0719082c01c1c1d0f2910303821110182e0585404c0002d600003401d03035143d00f480701158800000001c0c80c07140c032a5588800c2d00304441c000a0b208600d50070200130000d0b0800c00780111050241d004002125450034980c102d00b10705c4040fa40241007010100000b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 505439433 1250 505438183 505438189
    0xc0a0e01171510140d1d0f010608160b0d0b060d090303091208040f1b09060803180603070503011827060f090201050415300b01030c17040618060501031703010e0c09 72
    0x9900d0046d0000155243c1c0c155180600e8060020780c03007118401d100d41d100705154100060000801e4580400c0098905140061040f0240c4441d41c0000c0d4021020001030b0f80764009442045d003028406e80740032a0105031410008905031081c920b0b1010301c08030300c08000016600749481da0840750301000712003000031425040d80c4041c1c0b883e0000131100c1c1c13401d1004100100000040c00140701601c070145001d07110481400000d0105441e1140460070910040c86410640d00c51010752100001d07001428040e6002d10282d24000503111700c10210b440d018000900401303020303e0040c1d8140702d1043c4034a00ba03540c0003e00c0e9206922414040044480300258400e104000e0312550128000c00003801c0660040341c01c1040881c1201542c820380741c0302c00841d0a5010b8003030300f0120401078445030652401c0000003003900c0c8004004443c1240e9410100041e50303201000e2001850240d040021558110702c0c242810b0f0a0400303600c0c4429a003070004012080c24240c00740e510240f038484954550a030301d004 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 505440683 1250 505439433 505439471
    0x100e1002040305160605120c160f0b0a0609020a0905010e03010e0a0308090f0c01052b0f020714060402060f2508030702060f0c0a0e01171510140d 64
    0x4404850000a000080c03040001d541303500c601e0790312110441540c1d41c440643d030b503220700120035207034104036800600d130311078100d0181000c200701415078003001d119507440002c400240321048844c407200e1000c0c040c54080c54403d61002c1c00d01c0280852800c580304001401f4003e00744501410002e17000495140383c2c4080d00107002000340f0000b181c01900c2c6500e00604089011a00e1101921945c806880704007400100e89214042c182c41e51440c010868498040f01801c1c2ca6a48a12203600c06100c0e0343e0280d588200395a5a0407030a006031608003070301d012000d40c004506085010b40c01a81800056903902040354010258600a543d031003035652000500e075032044401e00300398081001d219042c1300303840005501c40c1c181c6078207480703003951440e00341240034a080c2e812402050080c010f1420301070141c040140c2c420710505104c04020319150044030861401c4515000d0301482948114180c100b01c2d070210b04003400d908014118540c0c503001c103c154012844500303070040d261541800c6944104c20 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 505441933 1250 505440683 505440703
    0x1501240212091f0c02090903180112020c15100911040b1605010204060c060f05150915040905010912020a030e06070c1205060402100203210601031805070509060f03100e 74
    0x80f906241454415019050b07402c2100c4c26401008030400058000d01e0200071500b99144902c8080038003020740d401107074a04000304900010350f50030803261110000c06c20000101500180e40c3c82c03124503228001120881aa5000c0c11400382449561852005c20200340ca064841c1e0702901612044010010368042c1c0884101030815440080d001c2040b40d0711910686da0399010300020300c64192142c1416088a100b1601200403c441d04050041460b114030100c0e00501c1091a05440c0d1002e0000181210312001c0c08444031383d590955841040742d040d26080e80e004560024240c0d1303036000d450150003078a502c4003107032041400041400c2007041c0b01c405040541881d05a50104007854900940c1d50740c1c1c182c03402da02c14040a040d151100b4400403c603004601c1d01c0c0400c0385450b850940f61038001d1809000307070b411705488807e1400c5079200a0480c001240c05440106100c9180c00c051120300e0300060091402003802ca0940512070b100081c41c6103015500c5080041c40d50a400101824281041 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 505443183 1250 505441933 505441969
    0x60603070314010905041e02010c0f0302031e0c0d020102030705070f06020706050a0e070506040b0d2310090c0302090a060f0306170d0e040506090621150124021209 72
    0x1800204e014031159110358401c510605441090148840000900b48041c100c024001414200710034001607a140020f28030030b2290041741e0408a94402c50f0b10460480071266640075004101800349031020064104041074038002181745003404803004015110b2020060178803040104188104007260f41100c3c68035410680400aa0030055440d50160065120041c4148110500840c0ca460080120707001c82d54503600d1589800714452040c40039043d44245000301004071440781054050303542059100300c80c0161290503003130401d25050b007154504c80801c010180305102400c50760726280c0c03003c800d4840d24103001181e40701101003107000c2c0c0b00c46e170801c1648150907000b405070410006184071a0402c0368943c6143c04001006010490b001115042da000b08898045002c03420000102680800007040c0c1004c450090000030b464000100f000100d003145410041000d080d480d440003c070910400d04203c030941c3d5116000b9a900c40f071440780c160710701c4001480b074150348e01c02d40c003d402c1003014 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 505444433 1250 505443183 505443221
    0x30403080d020406110f0601060309050304030204060e0421053702010605011409090105060c100507020c0a05030c0d0b0c130b0904060614030106080a0b0402161101090303080606030703 81
    0x6a01c9141c0a90032922400010138480d1030414841c3c400442e604a08003441300007826207a2030042c0443c0a8540e40c002a13400f80403c100210158685016040140080d11440107882c10240b03058640140c440c021940811030040d0001a1158014101c92404150391005088030590000b0203500080015214480302d0312181503000c51901900305038100d8500340c179029011607042107240500e12512a0003503010502030010b01440c0381900290100060b03040444400c50507081c0100c040b507006440200140e030050480030390524280070040013400081c0c015124400c4e848000c40c020108040340108900505c0c4002481e2102c1e02040c0c82c281a128078004641681d00c4e20341c4011980719034901405681844004145180200c402468064075078481915580c41c0801c1140d031614003801c000c64042c0c5589034420540d0741c078006005100510764848602c682d0a14108401e1002d1125a506012400c1c0d07081000c01d402404450703000d1815a040c9540e55110041100100354518400c10701c003402d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 505445683 1250 505444433 505444447
    0x30705093115080705060a020102090a120204050c0705060f07020c030703030302030f010f0506040e070c14010c02010606021c0804150c0f0e0a272c0606040e07150203040308 76
    0xe00712100c01c01c8a81540d0802142081412800664040d8080c00070320780d02c000c100700218100a001042c51580f14400141410340400c00130700f0111480d400322190340999949982545454841c290f04004806403092038151300b40c0d03605844004c01030500c14104103c0000410450003807042c0100c0d81e1004095031212a107901c0c01500a40055a1080c00e07803078050000f242d0922280885829584006d01c100e0920f0f14201104449070340c0100340500300714002c0c0b1400005034a16154140c1c20040c580007051149001000030b00b10b801c075078810011980071154007180394004202c0c10064824601e010030303003030f607480c1810468100c038410205200303890b10302241c01059211002c107441884550324400f21151410800c035040710385008a049070003001d06030044280321024556001c00c0b05010100300c10945201d04113110000c1c0c0409042845144200460204203000b600d5101c40211000c1180510000c0410380c1c4840b03e000b28150f90f04003100c0307002064020000d640056911188803665040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 505446933 1250 505445683 505445749
    0x224100b04060f080f010621020903030418180b060f03150c0a090803040303080f130f03020f0c01050309030703230d09022e031802120106031e0803070509 68
    0x3c158035114001000784000c961241030b0444d1040c121002c6a4540d070005544880c02c450340701c1e0040e00c0c2c41809500f0002c0c0389071500e081c0f002e440108a03a841032501110382c51152000d6174500e03940f1410002d00502110006828913110580010b015030f207041240003050086490601200002c0410314920b0042009000c0c1581c01008010711075958941c5803903590401c665a40100c0c00f004004c00c92000c0007410700004282e0440c0d00c50b1001c49144220242d5442d0180382031520300c015801030300076104800c0d44401c100503110350040c080c03802d03030303c0c0d413510070140c68a1740141400101089000340c14800d01007000c0c0c00816081c60001072041c2e5030340105d000c140c0203040900c0704a0040c00b242c44140c090202c41c0a103d1091111096045510031480100302d000304030f405002c4140c000307202d43d8140540c03542d114000803214401c00002c0ca9500354101064009550281c01d0b207410311801c800c20009681e4019603801460a0030150384801e11400051b51200c166161110010b0240d43c1500c2010 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 505448183 1250 505446933 505446947
    0x706030b0307031a040c0f0605120601090b0a0c030818070909171204020907030911010f110d030204081b1012180501020a030f061a0f040807240224100b0406 69
    0x86c400d0b80404d2415540b104010031002c054824080800d0b1b0a100c6482c1c1011254801580524145402d0031070315190b0307540c8206500156a50b20002e0200f4407038a003010340168020b90009000d001c18070006107103000d800d544e810280036507103403a034680b40380034100030b0700d00c94850700f501c0d680300c803e40c407404030b601d07958900d0200300c038181d12500f414404180f1700c0d80a482910030140c1c106604280000b4404019a0b40b00c00b10f88589007044580000c90103400420301070440c00c492540d0700075903070318609000f4510b0310101c0c07040c82100c0d190081240c00940e80e42c00844c4010705180c140000595030b00b0301c05000800011101302c045013904c260300820070106500500c0c07210240c0e2001c0240540a020507401c68483d4001c2d8a0b01103c5000000300b0340b8645805810b1b54003060880615040c0c94801c0e05091040560000f59580c1c2070352490744480e1a84110120b60410920003440521090036104a401c940c040b20188025156408540c2d15503500d100c03000a0004e039200c00d41d440d039880c01c0c028441 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 505449433 1250 505448183 505448191
    0x40e0d110114010611010b10050301150c15060e060a08030a11010e1e2407030b0418030206060102120a08060f030f150601030f061a09011806051c020a020706030b0307031a 75
    0x5503c7c0c16995103c030b1410030301240c103201c1256036980c01c41c0e003800c10401c07000c0400c090440a003c105411200040c1c07481c4c000c0c1445c0d500304140810414900380c0c0e080340d59400502003d1044070b041400f407080040001c280da85141c810300d4020400c03826100f9142c018100300c40101f04a0107440008516403081141109001890004135904003200883c99040b43e03504443c4a07085000c2400400c0c0307000d21903044441c40d03201c02880083d41d002400d0780e00b0340103034a000080300035130000c500300001580c0600840428050f03c00304503140015a40009102030002405644a00c0d01d42c805183d0301c1c2c9081016074144402101100c0c600400d00d00401601c41049680c180000e0a00b030540300820302c580030300030031903a80c408407143c0165020060005500420410350400a0b5225152044c404058801c1c00801c16600c4403641e03501c000c0709002480942c4811245014010000c000b2400d600080340c804480c0103141c006070005443d00003d003030003207940c400352101507000515000b000700b240704640a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 505450683 1250 505449433 505449467
    0x220303181509050907140c150c03040b06010309080702060d0b040501060c170d020f0318010f0e0a1104020d0c03020309070509041208040206040b03041401050105040e0d1101140106 79
    0x10311561402001e0401541c508200300080c5000020059401c1c0382807225000541410a2172401d501c454281c4103d401145440301039521076091000d4282a440b10700b500f081e035504a541c170790b00d8507841e50020120090300c02410181d80380940c40a00c0380b0b0000340c4003d2603004100c20b41c2c0d209101d004002030310500e003050344518900000041c40901546801d070059031300c42000c0700002420004c601a03a0068001041c41e039400300208900340c1c030510015446445422403201a00612903409070071107851110403003006140c141c8001c10248001215a5860303400800b5001038101e0b5400b0174064042c0c4210380c4445070600710030600c210780640256100b00400302c100d07074955988608000c02040c0948014001d458030500d040d082c01c0c45000c1c280c0e0311034001703000c591416503542802600380d44121000c1c0e0b007804003a117100d560a0320a0003010300400d0100d0302400046100f0300f0741511a8407042c11481880548100019540002c0d001020712000c10310880da243c0d81e42d100044c05601d40a601049 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 505451933 1250 505450683 505450727
    0x405120d08060a05010c14032803060b12010b1e0313021c030906051806070803060f0d030203030a021605061f0602073501060303030e0c040b060d02220303 68
    0x11040c00d0041916044500c165614000d2400039216015540a141f01c840b103a4001008801c0320f0003030020255020000124002e203481d81d03013a2009084a1058200c1c1c4406481008503c40304030421200e28107451040c44110358401929100f003602650710344103c480c091000c41040010080b102c1c10800c4c650013507400d4000c424081621409800401d40002c001c59076460007401000d1052014041c00c24403035001074080507501000130708982118030100c407110701c0001080040e0500900b1103083d20700585c0c90900c0c001150390080d40380c4c000101010b1300541d0205650b010080001800c42d50160080b043e5031241c2094885001045441944400900e800000001d031b014030010310581181c4004891102c0e44424030700c140e04403410600c66404600c24403004c08030140307080c032412000394401d403400500024880f200a00381000709820342d00c110315000c41041d00c4d032035480450b2210302c0c018000603900e056004102115028003510400d0b103007080103000c010560040d041c1e013040f862042e0046 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 505453183 1250 505451933 505451941
    0xd0b0d080a0917060411011701090f0b1206010b03070e0405040c080105060a03050a0201050f0c06180c0a050a050d05030712080a1503240216080712020a0b01030b0c0405120d08 77
    0x1254082c2d03c482c0c0c1c1030380c03203e0006400b05845a0416074140380514020482500c4c011405a400354281c20000d0301507961115040e0541451140c038943e001d06442154001c8200130050ba15070505100e40c4810071000000200081c0c4161341c08440e07050002e008201034207003030826000c2d14216009014880d840c003400308040c0c0c0b504030200d408a030b03030180043c0303210099a03004540136040880c2900080381c00348150740030034005100851090903c4524031031025034041b58a840c1408a14400d401141c0c680024030003034568840b000c042d102e040e982c008031100d1030701d012450351045c041c018011a032070780c7c210704085900a41d0140035901c007181c140718510000004004803800751100802842c120004420250a0010103a240400c48480181480000010422140c0b0103c40c1140c0d5603100084210800140395442c2c56907681c035100810350140d040ea075004000206002c040d1188103c200000c80b09003900d01103d01600000d060165640034440100b56500b03130a004c54004030b030300c81c8001 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 505454433 1250 505453183 505453199
    0x2404150504020306190b1f090b030108070902031b0c06150f0607020f04291207081f0e100912020a02101112031017010608070b0d0b0d080a09 62
    0x15030140b50000c004c0c000986654210084002600001c0544140c407510306483e142c1d00e8030b5007550f1068001c140d003079070103125200c0200180f0240e0421942130000780700504c4021000129007040d0790341c55200603525261400d0100152106c1603d199607000005498814090f012a02c94018540f808001d114080040d041150000c180c04000c4d821030030600008002d882c010b075608051741c0c03010f80300080d601820307620011445650100201c0f22041d1110400032030620b03c3e00c0c1c04081c8080304c058070f0820305142c0c1450f00d86102a103804c2c0000044840c049ca8450b25034007448402100404842e240f48801e44400c01924901c103081d169190123a66000030f00d8004224030241ea5030081040c081400080b5050700d04040540c4106030a04c121200c0c6110822101c00071070107950501d44403500300c3c1c0360075140600040311000207040b59040c01401c00c02c1040c001090000d843c2d00d05a040c0d11440c81d0445240100320104056038420240902c281c01e009951006040344940769407050030054640103c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 505455683 1250 505454433 505454441
    0x2030a0f0c0302060c070201050d0e07170102040e010b0f040f0e1503010209130f0f050108010b0906031605011d03100b0906010314040b1e09250e041202240415 70
    0x3001e0b0240c3c01020008080c04c00a030010811540305040c16401c0c201d03030300600e104480b406841c81d0690381c801e120502451441a080d02e071106960030003540341505110b440114a0810b01c03d691404401050f040e058286403010b03140a0305810581a80103599407000009a030005c0c1c900c440301c0418015010b45908060080719600312000d0031150140342415218001402d20340c600500107035490401402c286410700a00b4002c01c000c0700042a4110454100405050048c00b0f45100f507204c0742407180d0802c00051542c0890301e007400c080341c0399050001002c100d201c1d4490600c0d07043c0606000e0050300e0b4010f07840407800d05016140d5031703c95520000194126078070f812498401c1022030002a0000d24402100c80d4400c0000d440b01000181080c12804081c0059900c61400d0b01300c250034440041d02e184075114100a04203500402c10701d0202012428040a8809003070300f52040e840b800e941d0f001f000a180015085205c60215003c090540181c80b0400e03141101e03181890806840d0403103213406 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 505456933 1250 505455683 505455707
    0xb15060711010f0914010c031418040b1906030b042316050307090b090a0503010204060819051605030402012703050c06070c060507170d06030303050f0f070f020309030d02030a0f 78
    0x814208692060001510800d4047d0012020011044010300300400607070054064075030034450340c0d0b5000043e00200400d0340c0c10a6a1103011304074002c1e503111000009010542141c0d4107040001e5090110b0700410702030540540b000404041d0f2031002030341800100307040741c410b00400012810500104404489034801901c00000041c528601032146580a0008000414005215101095a13540880d09a8100ba4442c0000c00c0c8103604208006880b0385800c281e02c0e029100401292030300b01890001001c0134401c6a0411802000081c21039000d601400070828056030300e030460501032410030700c0707a15542c001105c0c64003400c0011281c44c01d02c0019104050340c0302014031141d504004044400c0e4200d42d00c00e503242592101c000110b44000c2e8020903100d08800008078105046040240035500301a2035141d22141003420070042d0340c00104401d40000861070402c4c200b08807102e08900d54040c1226555140c083e52001c40302007034000000304904100c9440740c81c929122aa01076031201d56183c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 505458183 1250 505456933 505456949
    0xe07080f06010f0c05011418010b01080a0504060902040f0209120a11060c1203040c0f14010e040507050c1005041403070302031903061d04031404120b15060711010f09 73
    0x5010403071542c0500700200c201c00184c81c1003041c100503a1034803420f6071540405000c9042000d01170003c01300201100301c04200400c4024411004400c00017080b0120081100244541d11000b04e002c01005400503007405800070400d10401c1200e00245d00258496a0306134410803885004042044011480c54240381e0071000c0725104036130708014405141d02051000b40700740078080000c1802202c00c0e0165021b40c1c0141c0d0a03100450500042c81c100741c0f0b0a422488103040000c0c402005680d100c0004190300d4800d0b6000708903501c1c1c040c2c0940e2140078001c0030030b500d40144103049480307061951110748601e00403d00064032554004240e0307201d2040c00c00150060300f0030005002c4524040c07101c0090244240350000d00690f8810070300000344040c0c0002d0002c00540c4041c04145580541882d07404030203001018a0701c1d150040e6020b4004050b07100404841407840020072001c400780d190340098401800385540c034181d0b8586041d401c410038180034086062542400000741c4a04c5140007a0750001c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 505459433 1250 505458183 505458211
    0xf0608120f0310050d080316051c0c090f03111f050f070f0c0e090f0c0d140a060e0a031e0807030509100e01060e011203170c130303090e0708 62
    0x1100008076680001c0c40b42004016507240004d040c1c031040030700c2c0c80140c060343c1e5060f103d040540301b48007802c2800601c1010040140001e404c45c06c6041485081400d207550001a035100a141c03d5a06d503038503a21070404000b602c0400401d10079015805100094115000b030740c02030044034803403008580f5524030000980140001342078075008400a0010f40e004034800145590b05075250028180c40d9040300318402074450500400500c00c000c0b64442c1007610010305040e80351107002c90081c0e015184043c00c06a511410010280320510103054155003040c024000424410051661012000d60450001e0000780d0680c0303400a81c0c1035801000f0181765952042c1e0303160301d10103c2c0a0040a49503001d02e010303408c4900a0007029100d40200381e0000d900202d0410b1500994560120059014080105201032050006a801880f19002002c521001201e98a8400b4050000d00401016815107109540c01000b4550014542400c0300c0c41c804000489640c0c85404803036009040d07504c40c0d40040c0f4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 505460683 1250 505459433 505459447
    0x1303030f1a1201181203140910270819020102040f0e1e0f010807060507050307080a022802090a200a050f0d0506010e01050711010804081c0f060812 65
    0x510908140312810742d0010a4500b0074030110b40b1220b1099108503116004422505030301c58050140ca1000006215004030350f00e040c91006860785120406c00d28040d550b440070000e02603c1c9091594580903d4800c03048034030035071812031195400f21064225440404480117541e500c14000c03201650100c1c8213158481c1c0c501021110011000f4003039095403402d601400354640081440c0910880307803d441440030794508600581000c40c0bd81040003000340800214010800000482e0400c5a11801041e07480003164002c03807c1c08010340d5501843d4002c00143c648103000c81d904080da4034001c8943c0300302a150400c140045131200c0100460000c800a00300c070280c200e00011703000b02071660524600d85944420380680c55400542901c01c01c96642041c06260b5902800031000fa160a0800600d010703a00c0d1030710080601102100c40c10050703e5000079041107140415070340c00740d180e222245810703090200d4410203800c40940d5103244618241d80040d641c1000a449080b071080d1281e50362134420 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 505461933 1250 505460683 505460689
    0xe01060c081c020a12110c03030f0403180806040501062304050615120115020a08190c08030103030203220501121a0603042405060901140109030b1303030f1a 69
    0x1206100410b240040c0400b181c01c1015400281180402982c501c448080703842c04407021603251407000090140203201220791440e0000449030012012007a030032455445240c100c03012030007008001a000c1a6000028142a000600e54000d80c480d400070710031aa140c150304c500801c2003d0a45006901d03c07807080010381060750080b9046003005c1c00c0d42d200c4130310750703548101aa44070154282100550000400072a29102490102d031066840074000d44e05507601c41d20001d02450440e60910710b85200304140c0030307004140d4208842e9110344403e40307942e981d0501035220b40081030105d2102d508901010308214040c820340060b58030503168070039800d40400f000740042c412901d14002d10020b102809103150344e00000343d8444d51141030510100744050a00d51581c54011411000c81e81c140b60601100366603148005040d00c082c9118141d542c8150300048074480c0090b4000340c00b01341103070306111040c0c0202121000d03281c001c1e01c09104c01205031542ca02101c40700115205071100261203014145 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 505463183 1250 505461933 505461937
    0x7062f0703110f0d0206090604030504032310051509040c060e0609030f010204180e031606140901061401021c0302310302210604060b0a09240e01060c08 67
    0x1034001c0c540010b90710b9090802529041040f0700010841e0b0003000e0f00f0391a11340c100704a0342d1010010000e44440d081c03039900601140aa07000c0101005600700140c4400118626212801c080e6035003119824000e425046000380015a1a00c00d014400f441070220b44c100403032824041e07507011648418062034080100e4912113004074099001d1010004a202540d0400208020200340400182d80310318118a03075075207049a07450302c801c4509062500101200100955001d440c10209001e141862440c281000700185001c45146a81070010300c184180c0540c4040140c40301402c8000000d0310320001660343c4d002004501c0c10700910003403691803152280d0041c00300d40380210550160b84060300010303c1140e442d180241104078a032081001985407111a00c10400c080e4040d03800f00200c140d00264580a00600260020b5100d501c0c00f81c241d1a0340880380c00820b44a0810044000c40c0d0b002c06040940c0582000c03881607117100d01259015904404a0403a40705072551601401669a4401d10b9 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 505464433 1250 505463183 505463197
    0x160b13051e0703020604090e0f19060507050423010201050a0b030613030509030604030e0301200703030903090b12150108060d030e0a0b0a030905010e0d0e0d02042007062f 75
    0x20b03004075100080103032146000381c000382003030701c0300810903076203403038007589000303280c420700c8200394820f60200356000d41811082c04000d8000101044d1513072032402c1560a03108580c004040d0041c01000741c9000a0507204a44c00c50300264000d210a4640902807020365520008041e4503803c0603000c034440f80f0000c4038540d12184241005801c05031440006400e0180c1200d0640104151584882451030288500440a050050781d118041c14400070031100d405614001401d0598440380801454042c2c54513400800d0014030840d66070200d00d0030202029010340780401c0c001d80c50a10326403a0340c092040c40b03100303510160001d1074020311501c0403038404241d0f000c4250000e080c8400800d01001c0d0800504182c1d00c603450108840b096803400a0071644160017031121a006a121540420350103212441c018034203c2d4011220262400040c00803e18109244040700007103542000c60400d640140010900958041061b00105420400c1c441ca000c602c150349403032409110b00989980d20054034507 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 505465683 1250 505464433 505464493
    0x110406030e0c1e1c060c2a0c03060b0a0f0602070612020405030a0206030411040c03050906090a03020718020d061e1a03070f0e04050f0a0614150a021002160b1305 71
    0xc0d5a66121401214100000c00000601044070b409081108201d2041d03491070543c1f4040c042c80710794070340d402d00c06228080205003940350a0204142c0c2d55544091000d03088100c1c050301001d0b43d8110180d179410031485200c010a07860072107030746030503014426101100c0e8003601a0010001581c00c02c15143e1004000f15000d000d1a5154081600c95124038031000907035881c0000c880c100840d520303141c548001c2c0003114650200b515040020380c0440e007076003181c140aa1701980000f00c03182d101c029000b500768017001c40d807412a002811a11034419001c290404480b4643c1c40c1d503c91707008000c00da0503050b004149a9007000402c800c0c51240e11030400e0780b4040d183c54071903603403100b000808ad5502030350342500380300300c5130240060001c452003210010690000207068108075000810120390940c03245031051240801c00424003802886039140b4042d00160465841c03a0000d10b22500080381c0c3c2c4181e0380003a107600084c015001c40301d282e50320590000014140c80181c0550711401101006c82180 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 505466933 1250 505465683 505465729
    0x80f03062706091f03060e0c03010e070e0c071a04021507060506040e030a090528060306080d050711091b0a050304120c150c03110406030e0c1e 63
    0xc20708403500c400c88008100030101c07115400c00b0810401d44407400340a003da0704a0241d807030214103400b20024001c4039800100440e4288891080780e017000760140d180c5406508100c1008802400840e484080d03c03480c420040d00ca86600d0100c0540f40142e10f0014280000c1d548196441c1240f1010160302c940b0040280f031003000080410300303194008490884051740c0311028080246001d0084070110301d000720095043c0020b904006101d02000c2c400d02d0b000b122410621181d01540d0342012000880c5402041c2010f6501c04c8010000e00b0705100310140b81c000c94883c038503424070035001ca402c46508000c40c41800920703002041600e500203807400e0303124007180080714800c0c2d0810001d44526403823074a40680720329241c2003000000300244225020802c107061403000144035446500b880c072140b00000507a5196181081d40107111030741105c2410003003c20005440366058012000002000302512188505401030100500401c01081850150030180c00400d04203c419402c40c0c107100c801c514 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 505468183 1250 505466933 505466959
    0xc090e0a050d0e190b0306090f06100e0303070b010f1a04140415150210180203070b0d060915031407061d0103140112140d0509010c050f070e150d080f0306 68
    0x1e041c082245e8403d400700f00e00441000b54a240400f01e5940c000e00f139031207038001441e0180000300f001622520003000d001c10000340c021240c41c2002a500881e500410324940c07075844071003549040707242d486010040d40b10400314001c201e100c00c0a54040750660013020b000516204100400b50121410946503901504000134010310949606001c81c0003540192031081c403128000c0081c0c940300703140401e5001d904030355280141c41c0051210304841d100180c0380c0d25000c0d803240c440c0140c500740e406016614144031041c0d040c0501d6600b5241140e101c2c0303010343e24200040d160325444c0d05180c03080e800460f8200349101185215003000040c20032052400003a05241c140d94001d0590007030f04003661711415403c03602e08000100001060001c070300c00040a9155500b0b400400c1071040c581060304128180000a0800108001e18405440c2d00d0b000da500c1c594642090302003480048844070401d40b606a641c1c00715061070200000c0380b41d0450f00061810422003190000c03940042c1040303800c111400c1c400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 505469433 1250 505468183 505468219
    0x506152713091101122901180303031a120c060901051b07060f110615040608030309060a06090605010206040219080a0804030507090b06030a0507030e0a0c090e0a050d0e 74
    0x80d942d00c03608401950040c0f181c0010990380310000054181031419200c0a03400420700c00c3d1941d0340c61002030400e280c5913800c0040315080707120070131543e51304e410303903008410550103801c844094050466007429a10490301005411a10314413528140d40101e0007924103814a0b034020900e07140103041c264980000d900540309004001d02c983d100c2500258810301c481c1d82e0000402440001e2031426611180c42c003039049444180203841e80206501c44039145045403120340102d8024050740302138944038600150f00710740342c0e00d040380c854102a1a019012880801c5446054242c480c1a4010181c6568990038000d04158025000c440c1c01071200b0b001446000400400c0d40d1031380709424042d103540c65841c10901d4a006034108122950401d07482d241d43d601c5503025a5400840740c040410140c4030b12100754020085202c12065034050401b42006001e00c803c52101110b0070b00004008070f400300c18100b03032600007071507006008c0c0e00403603030b039040d8036100301d82d040e1a002c80100704c100510414004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 505470683 1250 505469433 505469441
    0x1080402030c0a0314060106050406092304060303050901090506031003020405130b090706081b0304030e121002070c0801060311010c030927050708010b0a0c0809040f0506152713 78
    0xc00c40758a60900020b105d55001408802e004001600f0810b0403d800c0c9130010f01000090301421200c3d4082000060f1051240c0d40c0e151907403403001d8004c01000e034503070800910070760005400c24080303042d103000050f00d81000c0048901c0f821340003070035070f840c0f40c02e650800024002c003030104400c104001c400440428100f0300d1050203047c1140c01001000e103404005007240100a092310038078002102220503000d40502140e074002e90501e044c04590000308000340d02401c82c1d0060915a1282c500c0080c1c01401070350042c21410301500050982d281d5a100060036500140030050855541c0d05a030082c9500a01c803020101d03100382032040c09251956100070480c00800740795250a00d1f01c14403280d1001e00c0e44607081d040541071801500d250b051040d400700c3c5208441c00641085100032500c014801204240c48603130400a1046c0601108800524082c1600f0354501d48a4410071240040c160308280480308000a9225421480c000d007007200800d6884543c005034001d424000b00044801803882 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 505471933 1250 505470683 505470689
    0x50d050129030402010e010e04200d0608010e0a0201030207330f150612020903120403030201111e0a050702042903070608013f030e09040206070201080402030c0a 71
    0x2503007200c0400e0040d403803115490051038100900303010002d20000d41d0340502e095464583c01c2c01c205580750b220001003002032044080360060040d25000c0743c8010a2030070014003c82041310000d005079502d4640440c00c0b50f03501412001140c0c007204540d80194066005044201e02903040004240d80998400594164102a1a022044008603401002020702c2810007410b88400104440000041c1d01b14840c011070196600b440310704000540360342880e40448014210140544200721803c921881c6260800c1c0001ca01650030151540801d00030ba009403105800650074100710804510703602c40300d035480142440d0030042e0812030100035860343c0c02a20035601c00304010460340358040d10304464681500d08414420303001000c04100c0302d58005019819118100c0e0001d00410305814104007050700e00108a400d14001901800400d48010600001d01c2c0203071160044020900104011420b04441c003d500c0361045c460640954811901c907075015101030112001d46240c4030000d01881c034154 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 505473183 1250 505471933 505471949
    0x30c080304061e080f060303130b07020a080c0901060e010311030c0c0d030606020a1103010e12040f0b041a070c0302040f0213141c080904050705300115050d0501 71
    0x20100181c680c020000c00150b80011070311100140400001846100c0182030505c070b440210b00480c1c2907680a10450720182010103001141c00d644090b9840c0310b41001b00c05a1181c1a01d000000709003402260848880c04010181c9a25a08181083e5442404045944d041564842c518210032035848000d5010701c030100007241d191100501c07001e02c0c060001d01840101414134a04010320307900024580c01c50355002c040e0f80300c005180c1010a0040c6040f00305100a4072840700400c2c0054070450090040e540c40301005840e40f5210001c00046100d40e120300c1d400e0300781c0c50461425202c0b03082c000c5c00340306d480382c00101045a52130300060140c655821001c000742d81c1c00600b00b801001e141405074018210403000081c240083c4000460380c00305200d1003000500b000b004c0508202d080ca088894a000c010401c008905200308010f210b508241c0700b440701c00002008080001c4c011f5044d05d00c030f4002c40c030151074090382405101e129102da6060100306000c41408502402a4103020304d5003e05521 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 505474433 1250 505473183 505473187
    0x2b1b1b05040e010b010509151201170d020a0c030f150e16050108060f0d0512030906070e0612011e030c0306020705010b0603090307030806120a140d0203040810050907030c0803 77
    0x3504010848400702e1140000c1d80c504408070041e0303600f200c190380182508440e0020280c14130440c000d8103118900844141000c26400810b00c2c4008030100886801840111109500790800c00d070b99a518082c0c010b00b140604100130400105003072580100c681c4900d4014488070f140d4000c0c2d5050720440d00c044402a000300c0d200f4664075201070304000080c4401d2030700b51480d00300b610102e145110242d01c0e03d40204000a1400103105040003015240e1074005002c41d03589ca0a03032106a220842a2070702d1000841a1264161500d03080d800d6410a2500d14083ea0b1719911b0138011840a07400c00004480f00940d80d00c00002041c5100c10b050b008600034800943d03507188501e05142118501d0608074403070241032040c4020040000107a0b14150341c035052146c925100c000002c0c0e0b141c000540741d005503101d0a400b41d03042002207201d42c3e8001110700b084802d128440c0c075091307032a409603000384140d03907110326854400c1c6125500072580200c4a1415140e4943c1c40c0e44440c240702c80303d40c00c0400241c0c00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 505475683 1250 505474433 505474439
    0xb01050f1c032c062203080310151e0305060301150306060e0601050703091205030d2309010b0f0915030f160b041202190f0909052b1b1b 60
    0x45603d00201e850314100ca0340e0305912003c0002410b44c014030454000d4144456034803000c010b40b0300c803954091500241d02ca612403074460740418110405018511000529070040340000f40551005034004d003407101d06100c0c60342d441c03104500070320f030042c051603040d901d40c00401001520500284065802818086002c0e4249081100110310280c40103041020412480000c0b0350b108644905035104250305226070815070238150320f58002d41f00300d48846440d1140c81c2d81e10500c407003410700b034544200c641e052060740c803a0075060807101c07001486a000380200c04a4003052030030801e43d5a102c543c03140e14103c402140740129141910051101e0015400b02c41c100011496881842d170046c1403520007940b405003041140410407018440080c064031501103c068800030340401d100c0644150051b1040c010740c0c0c1d0814102910400344191594003e045005e10305404410321300742e2007481d0045166a005241d401121904d51000c481d41009a44207000e02c0003800305441018411252008501100e003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 505476933 1250 505475683 505475717
    0x90e010b0f0909190c050402030709181a130624081305070b0c0f011a0f01030b031c1206030b10060c03021b0d050307050303150a030b01050f1c03 64
    0x402030741e95208048101c1040000b11000411250007100050b050302c0c030162900d044800f000d0f1507000740e940f050012040108060b840180c503c200e44002c12420940d96103000c0500440d003c00f04000404919000c2c009010309100089048031811040001f0b8030a5031681417060540264410210191110445002559011904d1500602d0248010170004440d40d1100d980c1ea040b4440d805600c1400b14000d040c07840c2c140841500802c8840080c071510340f59580c4000c1c2015101560340c8104800108420710354400d110701c0560300390240080c400c0c424101145945d80507001030190030410a0100c6030080c2c021070042c08010b51007651200b40354207101d003805128030501e80000d410424514103a9011907070000384241058500d0301c05030303152040c101c040b0380a04c0764141c000d000d91000203840400c20030000000d51003010741882440214518004116200103d8440540303011075040c0140254034009070f40f2980f800e0010b00050085401e0301407511b0300c002b503080540c04540c0c0d401c2c4044c1044 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 505478183 1250 505476933 505476949
    0x902070c080316060b0d0813090c0e030a060b0f060d09020f04020708070f020102030910050d0b1c03030b01170901050a1b0c1401020c0708030a02070b030705030403030e07090e010b 79
    0x21501001550808912807903d0100e54107000d00600110380300c100c2e18030142c441010403403070160040c1c01650741da003030011400207e1000384200752405180440e007a01240c4038800c84c0c0107944009016241c0c029240c4c8038180603003070400c5000e500030b40e40312204800d80d460000500001c0e541c04004641d01f840d60040100d04038801d41c401e40150b00402003800055424000c80707003602e0380001c03014004406800100e2a50088052040e004130703030f000380700760b03003640203400340010b02003180e010301c62901c081042c0042c0c11140c074051012042c459000800080c000c0c1c010f0400c1c0c59045c90050b02c042903501140d502c6031820f86a5545595481d02803000c0800c541c0100400c2010008100d0780b8600706400061100684090140c48400b00000720b4000d50020f4044a81c034103616021160040c2e256500d180d00c0b68004a401805407080b10b10004600005000b81e9124400d941c50329821680d560314150007034010014450002c0c000c6020118002d04144034000d0b0b642c1c01c5000004410513030505004840f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 505479433 1250 505478183 505478189
    0x601080a0303050903070c2c0c0c070b0703080f0c09031902040f1a01050729010609090626011b051e030103020f040b120d0206100b1612020a0c0902070c 67
    0xc1c4d0001c01004020a101c480803104030f030131200f400340c40c001001c11108044103519500c0340440908009105942c2e00060203454000911019980500d03034cc0d070184102849185401801304103107c00003101010f00051003a80840c98008544c506103810000070700301a1440f6603060420903030502c01d0190300301071060304040283e40508000c0741084100c0788140400c40e04800741007000c006141000c002611241250b0000d14142091400e1a02d0307800b408408424040c040003c0c2401100041503001401001c08450244015600f50640d0b00e800c29614071410030010701940d01e07039071040100b0b141c0108507a281c2145588103600c40ca60306a036101c42c1400031740203000444040c0014009603403000b440a80b0010119800910341142c000410105200c1940b000c0940c011340c010201d40503000f103001841101d0280040e03001235106c1c01000d0250040000035007219030b03a0102000000c4c3d44845000c40138505004a54080c1c0135552401000d10799900901c030030980200391700040180074000c0c4805 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 505480683 1250 505479433 505479451
    0xd0503010e160e090705070b0c0409050609040f170702060a09050108060f090109020d0e070e070f0f17090f0f28050d140d09050d020706300e0601080a030305 69
    0x707444100b9000406034191180d40510036090a404500118014400c54010769808407240c200c514241000e0348858025210350300500e802d040004150345491030340d080c4a00c0e848500f1050142c003035180e4014420070b00c1c107440d440141c101300e480301681d92140507100d000810340d5003000075800c040004082d5180070f0000b90140c2c0ca04110380806540e180c04040c1920171140c40140c888103200e04001c0508030041c2280c1031402120004990944007042c11482140c580d2510310703104403440c1013181c540728420911000200d200c0c0034044c00e855028041900901c0c28411a080354209624050821001070841c040590282000c085003400b012800488004100010408844913803070312a214005150300302c04100d12140c9180d1098440c40c141c807040450070700100f2144007580f60250392000b80c502044098400c0c40c2000940c1803086100724200304180010100d00c070340500c2c8000070040001d040c80d015903245d15a90000c004100300c154000c012446c0240a06001e9041c05000c44401400000c2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 505481933 1250 505480683 505480711
    0xc0705010b120d030203090703291b040b09030109050613110909071a0d15060e0301090c050d0203010204080a03050a08010806250e220e010615050c0a050d0503010e 72
    0x10103440e000c104100d0300c19403410051b03980da40c2e0111450800c86d06800c000e107070000b078034415040c81c070404043c01d8030303200100fa5500c5192544100e09915032045a460032480310104000e000046a62000e445c80341e0000c0e0000c640d210b5280d071154140f2400b00d958524010407039040800340f02c031300e0f01001d1500324151004101c900345011215100d080b0f41c000c00140c080021351600780c000300e03c011643c0807642e000081041c41030b0002d008a440100b0705c50700c0002a43c0300c460040d02d00d010304c1411280b035072140e03000e05034511348414000d84c241d8003c01660b043d5401d21001940750340034046060503a03c00d54401c0c1d03071920b0200000d4100d41c01a001207a01d60b10131010401480a0401402c0c540b0313404c107801114000440b1412519440200b24080e0400f004840940c2c01c8040b0304002c013580060183c0070b01c844407000f1582403c903983c501c954000144400c0e86044554050402482980d0000003556082945910f410f031501c0c80c010400d500042d40003004000c10341d80081503a0304100042041c807 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 505483183 1250 505481933 505481959
    0x308164b0c12210806010f0219060f060803031305160609120c0b0a020a05010b060c030306040923030304020109050f090613060f080a110d0b0109150b030c0705010b 72
    0x9840300c500800d030010100d845200c2c01d0101c042842d04401d410002400c1060720315110060007018143c03100c0c4d0124040d03242d1189094004141051a141c6c82c103180105003a07540c9900c806050500c011b201d03025500da01c081050441030000f58482c0c0d09001541000c07480d01d2403c1442c042c031000c0d0703c01e10300c11101c000703110407a40400390104031251a00d207401d98006504010005580035801001c0c0d500000501b4840640c002c12405100c40c01680208034075020081406134904c01d00d034460380950400c200082d036915040d4080e030344650182aa80c3c0d0103040200c1040310709030007007001203601c0e41701000f08011580c1c4440710001902c0c00307440442d071000860001c03e1003801c0142445201da6140f0340103040200c89030b44407000510b0400c000b820503594172440c82d91038003036485050b1940e062040500d003160130700080001d03503160b11108450040c0c4c83c005001000304010518512521001c0000080c500d07003060195004090340d40351141d941406142a80c219000005018054180b00c8415 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 505484433 1250 505483183 505483193
    0x51501030b0c0a140c0115080105010f0b03040503070204140f06040908030705031509070e030717030316050c0703030512061012020d0e0f061e010308164b 68
    0x2294201c020001c0701c0e0f44903000e1503400c2d0303002c0c884010f04503840807011400b03040144054020b07400e00366a0300c461441041d124400142610003d01030002e031051190810804101120000d56009000d032050364101a065400501174a90b04440d01c007004140f001803013081c281b0042c1080e00040116400c0000a41540d600315180c040141140184540480081d5024240501c09540c5640c0200040c400746045440a01000010381065029100711000400c04142050761140038026507030045045a41b14004081e605000012003002c00c502032100c0740c448002040070390013840c03181e140c15482c1c2c00c042040301c00e21000100f0b094810f580d04107018094a07040624030181c01000d400140c0d440d680326110002403c0c100d031541620f0301c40e4604600e064500410700e5402140600c1a07280c064000c1140c03c240034a00b8040900082410000b01c001307a605d1003a07650072240301304000319045410031148401d9221483c059040d202c050280384607080018001005c0c1201e841e84840350003407240d00c074 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 505485683 1250 505484433 505484453
    0x60611030403051f0e0f07081e07050907050408010e070315020313060b0f03060a2a021f0e010c0306091b0903020402070c0503030c1b0105040e0a0b011e080405150103 73
    0x80c2c402d09201c800340f0740c000304d060713084060750600460440d0300307a819003158281d072100e5074030071980d09009505e0703107281d802070401c240e2401c0c002e071000030a0118203103003c11001c504060301c80020b202c4e040100040c082400e003c3d84c1c1c800040350003d01b41e42441e504001600a000d58429442240f040041109107440b0843e20404660400790000b0b09030300c2c2801040380c0860414002e5894881c0e0320410480810301d41059146d04c08500e1040366001100d581680200000700281c00960000015424000c1c0081c0480403e404003c00c04922210740d900400d003120855241e08c1c0000ea15804c0174040301c0194014030380581d0240e030b621268850010402007c5c4200382c00020710841d00020001c0c140204502e108002e000e008051300c0c3d49000c881e651580c2c40c180102d003002e20071308100310310301150300a8080c4c2c1d0403203200d00c2480c06c141c4d4441a60070020400454050f05110304005444c00d4079101e41480801d01d032481d160b0404a0801d401c005140c0004d40c0da02d110700c9503080d0f005000150031080 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 505486933 1250 505485683 505485703
    0x120209010b042106020f0d06170606031b030c0d12080906280b09100f0605090117040c0f08030a03060902090d08070303141608071d0118051306061103040305 69
    0x40e1070b000f03280e1403070520042e100708401d10b000c0b60030105294075084640e0b48250201e80c0c0d48864051102c41d100403440d11200102d40c0c05070305801200030004c81480c1d0f40f03d40304030740c4d0005003610000300d941c0000030382442e15150192603062041801a00c07450304803400c00d4010840c28003d0204d0318010b01e0342d03200e504040d01d00c0040c0c0c42c2117441039620540715403c004070a080007070101c0300a01c0e2561922140c000c0314420100800d03400c0c8030001c0c0540c010300c203d0303001003c1a91250302000b105203100b411500050400c4403d94003a40000074405841e0b1001e001801440d006141e98020344900203050724000d40001c03124910402100406d039441a00c0b40e07074031681c809106511910581410303002041902c50102d00d95040c10200711003040000c805806103001c1e62203038841900c90007021a0b4003044c211901c8010302131404104101d600422010740c03801103038281072010580b81d102003404a0075001c5082c0707040d911501d0030f1200700d0b0484512150301c0040340040d4241851512456960640300b1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 505488183 1250 505486933 505486979
    0x215070516270506010512040809030d11250302040905030c06010602010204060f03051b2b05040b160c061d011406030601091109090a1401120209010b04 67
    0x24115040040900030519000d0448121541c07a50381c0d5040541d0902c0380e24241c01d155003903100542102040762144034040c50041e922a810f000c40b01859a070541700140042d2a0034805100c1066980c0d4204414004907400d9960550300d9042e200340c003403030002c1c14041f001c0c80c56600c007955000031229442034001c81343c0445005c2440d0301c0354100a0304611400035110140d000781400400d070a0340540003402120800e41d6140d400c030000d1a003c4080314002c0c0c804208880d01912040803900e007000c0684041e03500c4840703c000c2c0c4c0181c0742039500a81b400060b600a0280c484081206108500e440d0301d9101408940441c003150b00488020b00b81c1983c000000c0078641d5030341d0031400b030258003040c9000c4206490000c011007005d00300c901c00c001400b250420300c40e01c00e4000104a85180740aaa03000d545000402400c00303a1040c10000d0b0710b40c0080221955682e03688401d503060780000c1d0090b00074824501886035034580c0b401409100035050300668814441000300300840109034000c612884201 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 505489433 1250 505488183 505488187
    0x1b0f050c120f031e0c0d02061b19030c090504140a0b03060f0408070c0e0403020f0706030e0a08090411070b090d14040306150e0117010b040b0a300308160207030215 72
    0x25030300b1a0517004600c60015144540c0c1910341d07580da000600140905141d1a080300309150701d0040140328852008401e41e82e6a111800b8000c00740203402c0760b00200c0040c05c1a060b083e0310b54003c03c088032078091080c01c60103803860030701507104000d1007420890501903000e0001ca14019010b81000e46001c1c200400328540050614203004c3e9031100700018040305c16417170303030141480d08000f0358403c0380c1a98040140191403000841a001744a9006c400d0f0007007024048448054540610b6030700100720380d6070040d40f140320b8001100301c41030040841074843d800e080e40a0070900c01c00e03803404e01002d50010a02c100700e40c100d02601203c00584007100e038004800320700c00701210400420000140c4c400c20109490368008101010010901c0c3c9c41d00021500811100790309104000c2601d64080d07c00c0d4020784103550601c0b000c1010f03442090001d0111380d03150210310078540c0c0c0c0040040050400c3d400181d004092261051200345102c4e034a1001d81b00820a1a041d03400282170f080c071250101c0c03015000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 505490683 1250 505489433 505489477
    0x105070f0507030501050a140f0105010905011409040204031b0614070206030406090203100f1406130506061905090f04090510020c24180601030809011b0f050c120f03 73
    0x30402c1a000e19070180081c00345040c05044640503100c0003000c14401b808441c005882c000145102c1c1b0704841c0142d50b041c108034544401136481552487d00d400315040304008030f03141925a400100004c52003031041c20441c90078131420407c3c08000750400410080502000c844101d40341d03094404407501200d1403580c80d02c482c9401c1e0020b25603054000c0d0135000d14480102d2401042c0c0c00483c101103441e801340310420104c095800301490450341035130701000082101c1c00a1003151300c8207a00c00c50140c262031400300c44280420b107000c1c070600b0000c001480000e1220302c81c200000300040c01141540d06011b00449541c90545a00e0420000c020345680841d42a80f80d160402c0841c00e41c0a21384c03200d90010203082d08103680750008455520140081c04250400500f00082c014102e0f60824562170901c1111801103500000c5c00006840ca0500e00e44240702181e20f8480c07420117580f04138014080d503800c031001e00170700103a090200310a07034100700070452071080b02104480c01e0b50542d203c1d40c904000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 505491933 1250 505490683 505490693
    0x60f0801110310060f052505070f030b0c090420040305122d04050a030602040e0705070803041218150809011a01050304021809030a02010b0301090c03080c0f0d26060105070f 76
    0x2071500100c1e4403403c54129500c0c11000c050101d01f03044e010300c0c2951662510b40d20048210403440c40001c00501e40c141c0018815103400c005018000001080840c00000000c03804090101c1600c0b007460030007001404004111040158418182d51020302c1802c0802251034002c60022002084444201340040d1110b0000420121006060024120020540c413800e0520081d0001e004848080100d000802c2d8402d00903406c0d1060164401d0b580c500d140d1b280e40c0c41c00c0001c072401841005200d20581c03040f180015001c81a03024002240d60091040b80c1140010b0222602403c5028540d15164041e0038074403144100c3c0b56540020f080c8542e81c1d8403035102040e00c80e4414454400d8911145050000a8170b001c4000c20440005500a1080518610401d805c0300c10700c000040201112407400c100003202040a0000c0902c0d10050310000706061541e282850903191000c0000b82940a0007042c883c2e541044502c4000c8842c404401031400c1d80c00a03046200d204400703000f100281842c841041 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 505493183 1250 505491933 505491937
    0xb0a140d060608070b04090b03030301030803010b0f07051e010b09010b030a18050a0501050106021e030a030b0301090b07020d090b0309061305030415080a110c06010e0604060504060f0801110310060f05 88
    0x8400f03400c0f07901d2259104500c1403103030014016a41d140d800c3c0740d180c200a00d000010369050b01e421100c040e146034a03000c001d1010354400300100400410601c111000310f4410312558440c0703195440005d1501d1000d07101d0b40e084a400d081c01c144203020082c0180300c5500142c0c1aa40e00224101380001d00034074400c1420144404e102004201d40300315140c0c1420401e06400c020b04892040d000c030340090381f18290080c401061030342406800e40c0706002541c400c42c0b00742c10400c000c0078050000603000c10306494891006008450000260b0b00c8003242014007944003107014010036995084c9820340c1452004291500d40180a201460351910700340c031b040c8a424001c4800610f241e10080003145582040504008011143ca8001e20724003403032503003502c0802044650503040c3c43c0c050706a6a0a11079513003034038003002d4840c541069030740e40301043c0d6480d1071180d040600074111a10140500d0a44c035242552482003000841440510074004481d60011003902610b41d02d00302991083c1507141d00316018 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 505494433 1250 505493183 505493189
    0x1d040b01110624010903080a0315050d0b0103020906120304120201210b03060a480c05060a020a0804080f120a0b1e03071806090606120b0a140d0606 65
    0x180211401c0c0840c2107150407694070710a001450f510b04021690005548802e20b0b480003030200141000750a846502c40d43c045240a0103041d59418000c1e19080444c0c1d1240c0004800c031000c43c200c4006205500d4071401c4180d0224003240c495001c6990f256050307899004922a842441804041c10401c5a02a501151030320b07011450090075082000e84080291200d03140f094000d0259502040b0912031034095507100036510401c111000c0002442483e440e03140b0400c01c41508904e445103980f1ba400007401820302d400c00d54883e1220f030b016040160600c840078200c4011a403040207d6099544c104107015030051700004072507160402102d0104152140385800c1c1280c015101c10410307000c406c1d6000680394078065414142c14a6000d48196080303002c018515410351000790108441202c0040143c8070900140700800c9051b81e030318910b03090321501c0d000305001c0341d05030042030701c84801740c4100001c04104940703a0f41a14541040700c00704103250070049000741c3e0f24040210a001d401d030080303801 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 505495683 1250 505494433 505494467
    0x9040204080d0903260708030a1d15010e0f040308070c020d20031b060a050c19031b0308060f0105281808030301050103150e0a090605071d040b01 64
    0x1046442c8001440b000d058001100c44401d401007240355030f01100941c0304d0b00c0640000c000c0c03400c1c000361601c0f20282c10007401401242e440e00c03106c41802c0201d403203018040c0822801840154140c4454003007164050700b02c00c40c182140c004210b4030b45ca003190703000e4000c0d400d401e00031a1502d54000450b50b1006110000c0d42011228401d041003000c52040e040241000070440f1391008100c204042c0c466542d08807602c11210f40220100c050320302240100681351450a015140500120505007414001031141c028075050b103462a041c150048858080300600c134803141d40009036641c000d00742c801c014202c03a00a000603c65458142d01407011180701000c038648030b012455001450004600203e00d01e5070014801c4849801500c2e041154101654240c2002d50f0941c0e082200440081080b0000a0a04400c2d088000385c000508113031580110090034021a0070001401d000054032405010602000f850641405142107104020781080300c088801040b013405000040724944244081804 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 505496933 1250 505495683 505495693
    0x50910090204031b0608060907200a08180a0e0c0a03061d01090e030c072112030501050312043503041d0702010605011b0309180b0a1a0d020904020408 66
    0x10500c492803044681c0b120304c000d48401000e84a440444181c0303c00c0d60002d40044010f8007013940795005a01041090b60342184914200010a440e9450020402426119402c0020b100c00240c102d030300380b690341208142e4580b0344c00d82c58884c2030130b200d40e4002e01d045c40080b070210708104214402d810080044c2640704a02c0d80f14505aa5030324110003082c82504905454410310b000c0d4000c2c04819130707544291440240401e83e24001c0c000c0c1d00140c090780d5440341001480040c600007100305041c1d689101c41c656000a41e0b604200601d40303410b49002c4100c04001080c4070030410040c080d0703030010280340601d8039817130240c0c0d045072a4030002c040503c42c041a80404a0003044003c0c0031011001e1100b4004c011105a4880f0303401a401c07500140a0700c0d0002d0b0000c08010103020784010300400175840b03071400404032580c60404801010200303070030211498031003020405038500036843c0d83c06030030000650300848a80201c2c502051198011a0903116004a44612566034070390580700108983c0098070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 505498183 1250 505496933 505496939
    0x30907051807080714090f0d05010507172809030c0818040b04020403030207030209070203040312210528060305100b100c1718030706021014060a050910090204 70
    0x164090760440d100c800042200d8002045075101d0301004141e088001c02d0710707191002c0071080c001214030720b20740c0e50340180340380305600c00040d800d21820303100b0602c40c0d60340d41031030350410040c0d403e400c0090300c1c0c0d1088101e1003015084a0061010103030382403d0145000034130b401a40703802c1d200c3d03c0c00010060014507020410074540183c1c1039002420701c6045808204540c2540704010032801180005001684105004e10050400d00c40007134000c003c0c2e00450b414556079a503661041d00e5000310303403c0010440d52808907400710320140e40c0002501c080e000c1c007103440d0070140c1c810081101200e04880044540c0064800c07102903200c28081c0d50090140c0d2000480c1c1161301014000000c0100d001d4148000850b40031031080303a10044169000719061544490070360050001d4020b10440400d06010743d10f44a0b455a08214a00051070681c001d02503030007581d0791b400202c41140500c41c540b442d15100300031079030350707602103180513604200d40348a03203522070200303100e45a00d40d42c000082413480004c0c04 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 505499433 1250 505498183 505498219
    0xd0203060103110a0611030a08040804030803010f1404020922021c0504020307050a1d0a020909070f090815040609080c0708010b03010c09241101151e0b0f03090705 72
    0x83c4074441c4060f5010405159100002c9030b441100901c04e10240c2c0050000031945d512850006030001e00400e1282d013407944a03181c10045034001c0c0d1088900d2500d419040160031a030490721071034514100e404606184118000c941503400403040da04a000241307407138000a041c01d905403840003102c100300c40b0410019a0f1104000c160030384081c0d110340310700c0c04001480e142810f0710324261000300d50f0205042d500081d100e0b41842000d00580744490702801081d800f619510300951146c082c50360740c640000c5034600050800344c3e243e00000c2c12504140c0b110442c40301c201c190540c0140c4c4c4620001110259410700a10502400c1e0008a16004401d40040c41c150705402c806910f02e01100200008021490141c40701aa24441c980e0740030b40170501c1041030354403643c03041c001c03441d1400d1400200c942ca031607003821101c440324031144040c0e0025041c8a03050b020007030301c0c2c0b0000c81003000d042c0641c2000d43c0d505a50140390680c800c51080000020720744141441004000c00c0c0c0074002592008017000c003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 505500683 1250 505499433 505499453
    0x30309020315010b04170109140606010809010c020a1103010b030708070e0f071413050301060b0d0e150f07020703050627011118150c07051008100e060d0203060103 72
    0x580c468481c0901c1241000d5107401c09904a0301907104c00341c5003e182c0866441c000154201903d0356550f185040310101d4410400540c0c1d243e40d203070161886280507800500842c90207000b500b030b141c0c54410783d4602c190300069240b40544e0860385540740c41c2209000680905115507a3300d4140c06031110020b034180d000200c8405442130618401300039910f030b0110303040c0003004a500400196280c40034240840e1310400510000043d180c840202e192035101082c2502d40c0d0740d00c041c500b180c002508070144512840380b08000341e0890301411103402812511a80400080c0c000018602c2d207030f012034000c5000f0040c0c10000e5030b09c1410340701c0518141410407182d441101980a6400403600d19070841071040c810343d401040d1504500c0d0400c032910080300d0040d4091580d494000030303005a801a40640304014141c004841d000406105007408244a0402815811181440500d00512070341e9040011003109a88044410000a0381c4d1040015070f50b00c1c1c2118080e405005640021060200740c540c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 505501933 1250 505500683 505500701
    0x190f0c0e040b0f0f19150f08100905120903070f0b09090105040b100503070905061c14040308010e0a060b0a080f0c0c1f110a020c13020909060d06180303 67
    0x50318010540c1d0b0300100f405648030407500c85840c1d0340f0386070000e07445130307040b103202c50240e0f40c01c0303100280c045002d03002128500b049402c10303d401d40301034104104415042010980c002c48212013070011056569070740f0354038008020b424004280100e103035001072328100b11000040070b40540c41c481c1c0980d210000b0425500100c840d50181c000300c000030406080c107018036403400074040c20540300c005400f4422112500094000c00400c02145000100c580c0c400c0c02410754208000c00400381e880d0084100c104843c90000103200c868040000c000c04a600000750a045078030903507001d5155034a00c078040008242e2034214051500c408900c0381505a809a8141d1013044005481c11250f1559203040d50b6901895030b1401103680440700005038100046604003090300c408034041004400c0164210082d000b04074601c00582c08500c0c03488003441d04180303d41f074507d241641189000d45050104014120081ca10340c00b59010120340000c00580f07501200217003045004940410340549001030250000d01 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 505503183 1250 505501933 505501943
    0x3070b09040b040608060a0c030b121e06070f03020c01110d090b0919030e0f0904290103030e1c0b0a060303030b1e12031614010c020a05190f0c0e04 65
    0x74007042c42410684601c80944038080c008001c155501010b08003e021030321041d004054076400c2d2a8019101c400d000366040e080314000d0300d100801c0024400c852024441071004a034031140501500a411a0150502e42c08924026a81e81c202d0640607004d0880e0fa4024540e82a0008007445505d4096101e0b111441c851580d40b1200d440c1d070314000340d84010400340303144c1040c0402164000a80510f000d0101c140024010038400140329001405032001282c0c1503c0082407003608541b540c4083e41c001c01c1251072007809880550450b01c00500100003841c82038001c1100c070103c0c1140c5002d141d501c0a1855100c1200e03000d919001c02c0381c1000d40304a00c1b048002c20b08140750305641e864404c880084c0c00d000d144046000071400e070200004041000b960b030080340802c016040804040e0305c290034955002e01c0b0644150cc45001540c0e003100d0110000381c0440d00201200e100041c408200c0e0155035007141603100501555042503190002001c0004001c0d0310345041c0010b0b01c400400380c80744201c1c021 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 505504433 1250 505503183 505503191
    0x70606330306050303090d020a0f030308090d18150509030d0e0111060c0f0304020604030b0906010f0803090a06180b0c010603050606150a030f020903151009061d04020f03070b0904 79
    0x1420940030b5401600a0541c103400c01d1020290701c0c20f01001d20000e45000814201c042c40c1c3e51554501443c02e66007069001500722000c204142104001001d00303064035240401854042141c2c030400d07003070240a90307900350300d2444000c10240e200d80d05840c42204003c069071494550700307001910703485071426040e000c114a6aa5001812808250b0910030004080c20341d01c0e142d603440c1860140c0c1e200400c2260f10000500011011400c9011400e100d52640740042240e54104010101c405005500c5002d0703a50081094070665101c50f4008030480d816800c041c007204050020400c8481c503240c2190003c0c035000710344800160415081941240c0c018001d039481925104140b088030203010890781c8060f00100300b0414064030a5000c40090000c1100040c2006100000070b424001030a034480712421400c0c0030b100150000d070a8510003070015140420146140012015501c4503900744400c100050300001015510f907400401102e40c070080650b00780390346440c0811015040071140c2c3e4000e900d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 505505683 1250 505504433 505504529
    0x180106050d3c2016020a15050d0b040501050d0620120f06030c0a0b030c0706110c15100603050c1201060207152a02011110060911120606070606 63
    0x2030680103e0164083c0040900e003800a990b090214100d0b80701c200d03082181d061000803041c8821a801c04900c82a544080d66050402c4a10050300d0340106601e11035841c100041016039242d00c03140e44c0c6540c0c80342021545904a50300088648000381240e40804400900c000c010141050054451342c1c0000c090b616a85130442859030740c2104515a42c1c1040c040c990600c500b40111000c3c59000b04a0031030750386040380c82c0d42e4003400e071118070345040380c0c278840031811180e41b1038140002c4c0b14111011280c1c80451500110314260324885102e480241a55038010034600d0201600301d554188800315040300950751444004e50f20580ba201d20030480e500d09808003819803081081081c0c8010f50518961502c2007006082c81d4107032846d504a052144421481d01a03a8050111160f55100a100007456038070705005032054411003c5100b0440034200500b0313030030540200701a0380003082601c2c2035459043c10301c0d048005051a41007101c560b0111755401144000440140020100120140405004c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 505506933 1250 505505683 505505711
    0x50109120528020a0f14061c090309030b1f140609120a0308090c012001020d0606031a010503041e14191101231e0c0c180106050d3c 58
    0x10b007600541c0b1b20204019080c2c861450440003500d58201c1007400700002c82d99035114401151003d41c001c83c04114000020001e01620145080c1d01101d030303001c4d01c20308145c811030150b420406406200d4824100d0410104a6120380c41034400c907001c09003000408619075400e20f40e0b10002a2400c4001803295000144045008a8070508240040c1c44440c008480c1119a504800c0c4800c2e0640d0259428416490055003500030b2030000c0402d5180084c1c00c4e0451542c0388540788403142100c8c1444020800d010000707851213550000500d075010035040402c0f0301e00e0b03c04104c00d95030030744c28000c1c40ba443e604070903072201d070a8420400b8070845400030440c1409006446000e45403a1022203400c1c14554405074042d15001040298aa410354109000307085900c0115604281c4900505c1da010442092003810300030302c82e0212082c10f140c00385903507261460040451258000c44d040035600d078038105100704040d03aa840d4040382080c0341015100300401d0300c200d4502d0780c0340d031350929107042c2061601c01344 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 505508183 1250 505506933 505506959
    0x904050c040e04020f0d0f120e100212031b0304050f0c0904050316080c01020f030a051e07030902010504170a02010f2c0d0501140103060606030204050109120528020a 73
    0x24580c01c44166143d5515002c10864480c00000307070f40c000025140c42d000107000003445929540c0301d0050302640940d1441c0040c60030004141c0107003d070014009451540d40c002680018a103640c104d0140e40741d84540428509020041540c441000c01009103c108640410000c04002e203200403949500d03a11020049040000e4801604a42040004041c0e010406a15458990188029503c0c0404142091703003281c0c8141040c8483c90710100501080103101d000300d41d00401400c0c030100b101400640100e59503000039010000303040d074403c000400c590040064030000c14901402000c0c9800038000c00743c650143c444124005101e580740302d00c2d044d020b042d1200d0100d84942c9001c5030300881d080c444074032965081c9003c1d40a80d0b201d0684000900c00d010308991511900d0850b03005500d14942070058070f0a035080030050500601051080366030140c030080c102d5103440100741804104c3c0c1846401c0c00b814a0b501d44198030f028558001900311241d00c0e41c104c900c03d5039040c0f01640c0c2c0b030101c4a601c0e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 505509433 1250 505508183 505508189
    0x408100204030312050a0605060a0c1a04120503130f06020a020d08010f06110a06020c070503160e06040b01030e0a0503030105190e04060b060c07271812030e120904050c04 75
    0x200d4034804c9500300c0c605460b40728551003100d00c100003512585920011341e80f40c04c0403d0400009404c1004901004040b0500700040503901c000d0040741c0c10b01e5074a640d180014901d01ba02040740100002e48002e01c046203040080b6041076a000c243c4009050000c003a6100d04240d801510070074050a070315a1140c91814126869401c400461506161048601170a010050000d0f48118544c3d04045201d80c8010446100303101c00400c0e0581c601002c0c18108031003040d11040020b03100104105000d44801c800d42e20107000c0381c00099000c816030041e0000c000022110b00281b080b84145420424004000d50507681c08813800c121481c480c0d64080307400a2213001e04d02416684030081000038502d0303044400012001000c85003004cc088185030329105c61a80112041d01289107610365808092541d144000700200080c096844804000b040c42011442c000f0040100140c412503e14400c2e80604002c80541c000d031205140701401c1c40540307400041c1083d116500d081c01041071007505904440032 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 505510683 1250 505509433 505509437
    0xb010509100611010f050c0c011d151803130905091603061a030a030e1806100f03021e0301180c0c0b041a010e040b0609010f0b07110d050304081002040303 68
    0x74242005401c039a10900c80704042c107290749a14600e41074041c10f000755446416076000701e603191001d03080550700b500e001c50748239010b0b8003c00c00d16080c0f418011468240c0607500f024080070580314104424298250044070310620b00000c40d1503006814505250812102020028061500c61100054071a503404003004404141101c0800c005011030304400c002040f19406c14020300c0084002c6428580051400c50005c1c1000d10f08180a250500061400303160303001a00c01030380b0708680410070848905521005200442d1a41210244682c0450714200c5010742d06800781c0c580420a01d40d190028024001444251848a12800f41d01d104118041825a80b440410800350300e521103800d5010f0002d40308031015041048000c89401001c900804460f0b01282d8245401c0c00c18000d5a00c01502d0039200b64150300041203152040d41004040d240718009850395044e292a001258142d82c010302500443c24800c41010301c107000c030280048800a800b602c40307103d09100894101d100e207000c0240 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 505511933 1250 505510683 505510711
    0xf030417070509060a0b0306061c0f1b23040b07050f01050a150b0c0c100201090311010905030f0d060816031e050c040f090c1716060203030a0218030a1506060813061808030a02070b010509 82
    0x140c00e0201cdc045c1c9400840c1d40342c1c90138a0305450351b1500c01c0320391206500b42c600d136009805115418009105042d40070075600b40070407071146008008020401a4030485c89000c80c04500d2440041041c40346024500008003000d05203000703c403010b0b0191030b10410a90100300c05561206403188103000740549654840c016501c0c1000c80f1a5048250b00b0000300755801c59920940403502035410480340f038416040b9988000315502d503240460800100700702245003803031030b000d00303000185000400240c45078048801050405048254000034020724401800001640720001030050026440315400401d0006031210881c0800784519040154421000140c0c400c200080b0104140d5010f4802541c14084081c60743da241400a0b2030f110a28109950004d0000c858010138640d03889800003d115604121100f49000d40d202d80c0c00101c0603801420a83c1c90741011005542300c0402555066880001c041d103c1c101015000c009410114003200c48021013070001c0f030a4a000203106120300240344c0958 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 505513183 1250 505511933 505511957
    0x6061e18071809050109060b09090403050d02090a0312030e1b060a0903060c0305090d09030503030f040203150106050c0c300f030417070509060a0b0306061c0f1b 71
    0x4001203600a001d08100812050301020303410060700500c00600f02080003007481d505200d024411103000340c2c40b07081c40450400c400c0c3d0041e15400900759106802d03061003902d8031003040c45040603100da6014103900c41c814800220411003000703800302d412001307030380d040018000e044009a074800d0100c644180024000050050170300e80140180750032210740c038048020701e07507070781c1c03140190b426200a50022079140c104111758103100308050b240803a024640000140c1c5141c503503688031701c0042c0031004600300c0d5800041c2517450800c02c0e030b895119840b0030340c9507940e900c03035000380150498031003214240250b050850352403800c8c50821400a203000700349030381650b044c50a04081341114001e0100d6002d1100c04e40e1061109001410081c855203100c032513154040e490107800c11440d508010700c111404024041320352070300c09105003511622030b16281d803500ca24001600e05c0c000c80a08510001900444030350400c0307681c02c03980054801100a000100741524056208080d048884001514902c900 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 505514433 1250 505513183 505513219
    0x211a060f1801111c202b050d1512030215060a0b030105100306080d0203070204201b030f1c201602010c0203030a0c050d0201090201140306040b09010806061e 69
    0x50002842c9081c00017840743c101c184120416501d5610810581003a4880c01ca00320b007582402d0b040001805d1040d40842060501404078041c030014916041e0f80e0352910106107a0030f40d0381d10050800208521a0400300d407074000d40c0c0b03912240d4445c1040700500e0100d00036043c40603c00040c0c803483e400c02d80c11a801e102c28050003800b038150110030142c41c0d0b80005040c40c2c06200d050f141f14459805075560f001c2c680140f1081d5844c01c41e01c10146e0403c4940d91007d240108103403200590036a49200758440350390102e40c41c50103550040020030340d000401c0c02c003a150140b481d00c4056000c0c2c40502103a020803850780c00118107046854001e50040180f050020307101d540841080d441414a00d00d50309503900400d265400ad500010042100541c0080c203001042190301d009a410348000e1000d1200790380000c00042c01020f01da034124502201095240ea101c0e0031420700b41401410750b80540d0b0750380c80707044c0e500d07102501d50303501404600007030386002007131041708a402601c0900241354401c186100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 505515683 1250 505514433 505514473
    0xd05090c130902130c030f0504050c15070203191a0709061e020604022407060e010e0d052a010504030f4d0607050c060106211a060f180111 61
    0x5117401c1580d2a0130f00e0810660600c1140d0090780a200105650ba68040501c8288040042d66802c8072201b4004400141c1d400208503103e0810407420041003540742c40c10014540101001100c1910504200703c0c405510000b401d0840d8413035561013056056207264010210301c00780a246c0141c01031400900942407000c0c41d8828507280f10708007e903030b23142410700000c60703002a481202c24a4581c1680da50a075400d0085507030301100c0102030280303070b41d81400140c810700c1000001c0c88100240003448004045508940c0f00d0052988000c2c000341c40e05140040040d00c00c0502d01001c2210243c01d00410b841642c4650320000c0411941400400300d07024442124900342c48100342030b50b540310b0700000b0500c207101107800b0340415110907846000d441c40003800c00c1c01c140c00c007400304034501441e03400200f5031160051401d03510b040006000b000301c9a0f020304003010f040340c883e04850002056030120b420f200c01015590301f40d4888a4408031a08011200c410242c061500294090a0021424151010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 505516933 1250 505515683 505515701
    0x50a021c020c0a0603020304200d12120c0e01090e010f050d080705030f04031103031e03100329150f1201090b010b072102060106140d05090c13090213 66
    0x44030b8660200c6000940845166005000025004001d0100304400351034440501c0500d00c3c543e0404410a1000c91141041c0c1c680180007508182c420b0020b1902550746d41d00100c05d0324005001d55866090b010b0000103460400c203001880505001840c1100140320f40e05039516070b84840305561500040040e44c10403e00e0a0343c290750208079040c0000c20400c0284001c0e4502203143e41c68070b03d142030001104810380d030411b0094000300440180c03624a20441000003403024241078807902d43c00e401c088091303e03a0304001d0820481025031540ca840d03001440620320a03540007200c460755042e00000c1c00540300e4150700d030465002c215050140c03401c41459000209201d00003d0003550b9a250425050000e910102603c140010207205101c0d28000308102684075a49051a40241900080d91110305208800030001c8100ba6859810300310001c58900c0b007482c070030612480c00c203401c40c941c4801e84103a2140c422903001568204440f0300d8041c024425070010413020203106c0c0c07510707068047c0034200 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 505518183 1250 505516933 505516937
    0x1030b1c052404020114031902070f151b0e13110f0f09180f010b0a0302070f0812060a0b04090203060d0203150703180203061303030b1f020c01050a021c 67
    0x34200b5490480000440100d85900101c030039564107080c000500700403a41a40c24000303c0c000c000300840031100ca4401d40c2c0d41c0401820043c1d403640a410f00c0c80c043c08040600501d00627085194056000440c5c2100308a45090750310aa100e2081c002c042d180c09014001854020031021480c13501c5031425444900c0b100600c801003460540440051a020b910602003000014808910b070505400c1c101914050030032045036081031401d01c0d807143e0504200c148101e480e03602d00043c1c0d002a80b8400d40642c4c03c0d0705d0788900d80784103a5441e0701d0290400c0c0c209002c0018289101d000113181860100010811100c1d00004c0501c1c090408840700701943c0003e0081350440e040d0001c020040c0c0741080411402241118910400e0611071002410b40700c808001c00075002c400088140581d0700455141e40240306802600b48142d06441d081d00540340cd4184564030642801030f4407215076140d01001c068014507800e65102c000b0000056449014041008005a108180c03a1000040d030030000d4402410b14 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 505519433 1250 505518183 505518193
    0x7110102070302151e010303020a0b0703060608060f0a09021605010b0a1809031803030206091002041a07060b0406080607111513020a030803070f020c030f06131a040c06080601030b1c05 81
    0x20080c41c5601c082031f401100181e111400c0d11082c44825114107070040450b01d4280710151038080e0051900d44040c000302c3c450b468106030a0f030300344d6900014900410b1841010b545420a54841c00111481500c007070300d05500300000040390b4503041800d1410340306024900400000d02c50807403030003404280c00403070034003a0901a09900180545002c0b009521a5000780007070301e004a00941004040500504114014007090160b0102510708900c00011250040c1d207440d040e0502c6005001502086904140f80400108526001207010b41c03145506445a010b458a05840541d5501007140f45c1200d00a44001151003a04000410b20b2600c4c001040c07082543d4481c3c41d00022039100395070700e00c04903001d0305e80c5044c440c0e014080301c00a041d0403005054031507415100141c80c0d65004152105555030002c11030200103480004242c102d2000c6000e42d0545000e01e0302e20b0801c002400f40c60085903164001400701d62081c05500c20040300a0615000c0c107048100715074602000304401c80b814012 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 505520683 1250 505519433 505519471
    0xf0a08072402071e051c030f1803090602031305090c0c10020301170610061b060603030306030b0c07151107150617061b070213050405060711010207030215 68
    0x202880300d003008000034a005a41d2680f41c07401031102003c07400e4080b10080c80382d5501000c41c04c0800d0b4000850411403079041030700040501200104a040d600c1000a4689041c0d9940300c4841c0c0e4044211504c6511001015030f107070482a65a030044580d0100840b100f40310900c00b44c01c040e01e034640c02004500c401c6040c0084e8075600d600304800350303070b0380003015038040010046005005844010703404940090112400c2400401e038050281c1c1c041d64052050368030362800d100b814241041030841e00417030308000381900c07071030002c002c0d01369840150340249806021a0040002008540120f41d20040c407101e54014880208060b0030b140c80c0c5800344003000e00408001c15240003420920745048107001070709c1814040c8030f410346051080103180c01d41c081030400880888401007400e5072400038440a0f100c0c03c103403001443c0c10807a421380070906820842800100040060f40c00d01400440d100ca900d00700b0104002d47c202d011351500900107030310008504404601d1010700b19005079403d40b4403040410 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 505521933 1250 505520683 505520723
    0x181407271d0102160516030209060d0c0b03130b071b02150d0e0319050a02150c040302040905010e01050a0b100e0a090903020f0105060f011409010c050d0207090b030f0a0807 76
    0x180c0e460303031040c1c119152500400005005100380480480048803a079402d6401040b07019000034003050107540395034840380a000c420410cc0005002142d019645c0f443c0014480101505480c412240743c0c0094001c02c146600812071035112044580301200c82c001182c003000b4aa000541401d0030321841009a002d85a241e4002c1e184480280002035583e88841d01c50100b2801e100e003030b0b510801c54107000040803603a011515414800055841c41c4d619258494400c0991296620003940306140404040030010306400c16551420982c0080026035500400d0302d080d1410784402a60200d104070078424141c3c0254103907000400003801002e40551120850401c071030450205801691100e46040270b110001d014170b0340d00403001e45500802ca452000041c210403982c58000b03040442c003142003030503a44100e40d4420560381083c00c550a0f05070340705000c1d44a030402d024515035941803249241050800103020412844014000c241d21500ca840b00c411603004028200d0348c4a15011030944080 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 505523183 1250 505521933 505521937
    0x2151305130204170c01050415050408060703050402030f1c0302161205070b070314011202030a0c0609080708030f030f0603150a231302040f181407271d0102 69
    0x81e14032000181e455060496000c880700403c008455154440c11925034240d900030140c504907002c541385c404d0410107103001510799000341d811140c114840c040801051a90540142c0d000328000d6042d1502142c0381300d60750342c40703004c01c50021500742e00c8490f80c0003041e880799009090642c0140743d040c003509010394820382030030040e00c042000510301080e00d100303200c4400c00d1070781c11111906041041c6a501d00340e54412480c14402d134501c00c60140d00317440564600703104200d41298003140300d500b190f44940020b442c80003940640380288c4105040422081d60010444442c443c000b5152420341da501808803600400090640340c150207a42c5241c00f041221812880c00740c03546803404541040b03c0c80c4280b40c402140042c440c4d85100c15000d000000000009551b90190190f8000c203144400c0345c07800000c1c03e1000c80c04c2105942c50072080051090b10191002400c80c68000da680d000e070b0f03034089025440e6042e0381a040c040385551841c48840c0301640100a0040900444010042d030711460908903 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 505524433 1250 505523183 505523209
    0x806030616110a1a060303070c09021e130905070516060e070513060501033e0c0d03050a0e0a12050703090b0a0c020f1215040c0302030a0f1e02151305 66
    0xc250210015900804d0300d01060303100b0005e4004500742080f540701c1c041000341a00c2491480c96000070481205420381c00b01204041041c4d41d600d584030800e04610143c50b4040c41a42c0c3d40c5447c02010458042c490811150041000c010b0345d030a00c409519488d0007030010310b072000d049100b4a04001000d0f20f98025000880d50201c4000900c80d01d801c4c000360548074140051020030150f0380c1c000d001a4680c0d241820341d10b44a104844041c032107087c1ca1003052182c0f401110040c4101e401c115611981504a1882a611001c06100408007030481598511260780c0c0100341d20301d0340d04e00144146c4188040c0140701e0180c039251000030b9444000388090f0f44400749920010341d1000d11001903041030300f0b45101e00b90040d110300c0c4091211880d003940f20900c103000c1c0f0301426103000c0410180001881640095130300203007071391480b4031540340080c1c84007644042110707144e1075030311810740801e201c103003c003981500605041c0c000b1141405220196203c100c0c2039580030703400c1c80c000c50729071030b00c610341055 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 505525683 1250 505524433 505524443
    0x20913170301080c0102070b03010b0a020a08130f0b0403080909070c0f06050f132a0e0702060f100503070302010309020d050f03030615090a090e0703120e040c0806030616110a 77
    0x141e54100070301c1c107041010302402c2d00c0c155403029030200f1070000d4500440c0d0448a90803c1d5980b20480c00b10220300f09142c0e240c000c0c041e8030300070582370b5480d4034102c0e90350300312911800c110b10f00c03550b900a500e02d5802544405401310b8018001450f0900b03240080300c0d4030a0103403415003450042540c4045c040c0da1400b20a540315940c079000c102a128002000031381103044083c400080b04a0795603400020040041c07041c16081c9004906152503524901d0100a0480c07091011220b2809400c001c1d51140c003102c200128400c00408944000c170700319500800d640001c0d02601d25981147c0040d4041c01108004980045440b160280880c005010f03920505610401075035070f03402c000d0f00304190f40d00c1584040e03603c00c1040010401c00da58070740b207a4085500c04840420b4a9081030a00e6092141d55440500600840c40d107400d02a03034440d070011281c074400c40c3c04000f04485007138100c5d0a240300b16546505540068041100c00d03060041401f0410200d2826040081a140c030b51418124408000c90b0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 505526933 1250 505525683 505525687
    0x3211309290103091112100f0e12040303020304030201030b12060703061701180209060d1203020418020a0813060608070308120108151911041502060a0606050702091317 74
    0x161108922071100c8191000d1905000001080d200d031640300c0d2a500703c90340705140804204c28070b01d030188035403403010101c150100581c0000b199564090401421100708074064005100420b12401090310103032501039000f9801c25086d40e006400401c00688455489001c1819640143c8230030025144524101da50106241c2d1034006085c205151344100004142d040001a1907030003502007a41c4142d40d0101e43e8103c0649680001c10884201400c015180388070098a000c4615015001041212180c85007038601d200d1080c0d05e40101d0140e040302c200080c0742c52010a5078641c8100c1410145801000002101c070340e1420110701c2c1406503807084610460219100e98166800000180103003100790142100c14098240c031a8040c030020b000710001000303c01020054012903004090703200c1e211051603079a649498626070b00c682100346002c018842c034000244c81d00c00e68010582111a2612040e0030000542c0c204004e5100c000c2c00301203000c0f40d04001002041803400d2412480001109040e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 505528183 1250 505526933 505526981
    0x30c0304060209040b2805091614070506130b060411040605130f090603020112090203030406120b090c0403061b14070213110408060a050105010e0d1b03080d0b03211309 74
    0x6d80b010954040c41c070800c6000100030804542941440d201c9626290014110150324400384180c0030340d96000d4550b00c03440c010059101030070055051441d01440c0000150b5a503103080101340c030302c0030300f00303503c6064240000c026507401500034100e044801114031903400d4032014825600202079001c141c182d0b445d08810019543c2210f040000d6658400c02481070aa880e0042540d9210394441d20301044006100d0740310000c440e6003c055110700041c082c402c2c84c10090100c100542050105071500c615003810150705070024550034203000740b20344a0341032002c11403a800800390440b94060b038018600c2d148519600c00f4920410940000c409400d03601c1c3ca045c03080c2c091a200c03000300488000740c903100c01880075a8010f0284811520300300d03440000c51000b4504444521407602010704503690a14021082004a001624480c80e080004104148213401050780e80c0208400340c41c0c50200e0440d6280b44005101e00419041c402403404091840c5e07204207202c2120201c60314105c094940790124 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 505529433 1250 505528183 505528249
    0xa05010f051906050f0f01090801050405060103110603161206080304260604051009021503390418060b0d020c1504030e1318030903060b0105030c0304060209040b 71
    0x100c0030182c2000d0104862810040440c82414509018038403841c0300c801085051381c450005403028101e04030083c041401c00d4604960ba03084280000c0784c402010255250807414840156480364040201c52a07848a84520580b0904110344990712419100c0d0b40202d0001400c100401c000d204001050044416103910030b044511030380300d003101c140c014070705100201d480050f00c920200c042520000b280480303440040c40e2006400004488140040300300020756550751580c40455950f040640341800681020704242444441d4040c5549010710003401500c03034410f1078110700b515034500042c903107444028500b07503a08000484240e03507400080b004803010b002e100e0814444c441315010b088a0419507000340c5544044a49103000341c11541e80c2604064603508141220000c0c809114903228050070000c080000c10b0000303650300ca00304050b1440551203041140c2c07203083c0c1c40744480d0460b1072720742c0d5100c007a5010800665000da12040120342380d41c0c4007080380145000c08d64140203091030702e40709 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 505530683 1250 505529433 505529461
    0x20a060908060f090304030606060c0b090102090612060d0f050303042108040201030f0908030705040509090a020315070c12120c0e13020901052701111603140a05010f05 74
    0x106104001100808010344100081d140c0e800011400d10801a5550f40c000640381d03000c3c2d03500103400c860919000141c40c942018011030054000c05042e2034a0b912003031202e0a03446959004d40e08000100074004041041d541c00ca17400ca00003d0000e00c0b83c940d240c4035100540c120744800d480d990800000e000400c1845000b4110200710031f040d49582c028103000c090001000100064141a25001d495084e03c3d040d50065409607400401251241048800284140c00c18000c0c28051756428010411034100000c1664003664000c000740140f03100c0d03101e81c42c2c0344a0017600c80800d024070f6544400018582030016490060180d68950b102c0c0f62480140701035034180f0a1000c1440b95420800d4001d40b01d80b0000581040703003640140e940c10313071040101d64070b105850900501d000b00f030419072850718004180b416100c5099030f400f21501001081180c03544440c541ca0300254004110801c0000c021007424003044505c48242c80c48103550b600c9884c2502c10340070703200c0e101c590f42e2000c112480e280208 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 505531933 1250 505530683 505530689
    0x3030a1d0606030d0c03110f0705120105010b0f090303040b03011230140405040203010308191407020405180114010302040606111002030a0207150c030f1b12020d18020a 74
    0x40282002d00341200420f40701c00c0340640c0401082000a880310515000f0703841e0f800d1481107c001c0b180300403110700906480c2c042a00400e4814034940c0310040c2c20f40014040c05041e0b0344c921540600c0d203d20315510004550180e02c840350980024000000c070404400003071802011141003a100d00c40580c82c015a0510303642440c18100b85014060592a50f40e04040a80002c001d040801e5071140c3c001c080c01c1070b801998083d6520a0000002200304000034002d040720a0200204004140c244107055844030051058000400024805000949825000f2940102034040049041c4902d007200d2401c0d9409070074012000c41301c6400410440c03d192142200500903031070a000d58150112116441e1482401122602c6401001041c0c10b0150350303040b83d100d660301541d1800795a02d00005080600000d0400d4000320746010180c1c41030598031b000e01100d00841c10520318458054510540d040c41789003030481e4100f5403c2c0071428100020b0320903030300705400403140043c0c4c2550501c100041442c0340c1e0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 505533183 1250 505531933 505531991
    0x9021f080c16020904060b0a0b130e010e040809040b04020a23040b091212030907061b020607020904060f05090a02150a05030112031115010905090f0601151103030a 72
    0x304282c1181030340c07203001669045a44c00101d8480d41081005018040390141e481001560005001e408520041c0050703c42c400d102c004155850b0a8030707008040900c240c148022a0600042c000351000c3c00400c0354000041c00090001c1d200c0c80858200c0e00000449004980c2c00d2a000c9980070700380370807900700b800d19030081e4030b02410b007450008a030041150184c01500f24800c05000760740280a04201c840420b110643c8918011850715603500c141d10811001c900465480708468243c80000404581c0141c58036191025690911110310760090054036040d6035a01204000c1c0040e000b42c50180142c1d02c000c112400c80c07801040142441303e004800074680c10094684442e80203029281112040c90b481c181000d00c0342400d2782e800c403c00b20f130a0014001c1d0079030600001402e0b41510305030b500c921401c03c1507948101400c2c1d50352401c0e60400805e84c1c0300c00c004001c41c070007041c5041040e00d614170b082e081070b89500c1c04092441d002503034031003c85610b4441041c2d5800b0b0200c04011610485 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 505534433 1250 505533183 505533187
    0x903110a03020f1c050307061e0e03030f0c1b07170a021e0310020d050a05130302100c02030f040f1d01031709040e030a02150a090c05040c0309021f080c 67
    0x10340c000b80743c1c11150b61100303014103529901070300000d6a281d040c0810b6900076054035601d69941c82d0400003025000c0303034000c1542c1c02814004001d0f00300c1c4200100701000340011442e40e21140c81318070312000000e2001540f0315003040701e015002c030001c3c48040c510700c00e1744c020400182803c122054040c0180300250417a400b000c1c1d4540942e4030300900d00000c9941c000c2e40c03c1c841c4030107030102e814040180c40b81c8130440e00005005840c007040d03074020f9114452051003000551600441c2c0e842c10103500380040c00591000509003d110440d034441c000000990045900e04080100100c8458220341c0c0150708a0800c000d0410401140c500e8060b40005068940b480560640c0d4422860542c01324544403000004901d41c003079510341d030703000a86540042d01101d45603446000020740da000c0f0000d004c820048400c010a00c1103a450240b400060361107086000210300702130510008203040b1541c0002c060b203440381040507890ba01204894a131401c84900f08280080c10054078900c00a8082c024280007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 505535683 1250 505534433 505534439
    0x4031b02220f0b030703110f0607030e0901050409050c040f0b0a030f050709020901050d0e15090d02100b0a060c0f170309010614100f0e03100e1507080103031413060903110a 76
    0x171031110b090b60360004c04012000800404207a01d524148001500f003000066954145030308000240003040044520255507030b00c41c4180420703524400c500a08076031107144004254136041e080358128036045400010085445c0001960310310081c0d00580f8403c01403210442409024003070300001d001700c03101c15844c00440600081440c8203101981e10004e5035021000c1004005020080040c2680001120b40e41011500795071503113048a004400b51040690f00c0d0302c0c5400c1802600c00100f0018400b0303c40919241041d03410f02c1c1100005c40d25034010441080009078028401c0088a1b2852025505c0345019248142140d040c0d4001c2542a8000c4984250795900e404035803002c0d4500d031034080060605940d00b556060101100142c0c14040c4440c103980610f180c2c0d0028440c01481401ca910100c05842103000000d026030700d6074000f803002c20050012038020441c24660250f542502443c3c0200c8000d0303000c01c000190032840015520641c2001401095103100c0b041410848500454030320f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 505536933 1250 505535683 505535689
    0x306011815060c03050304110409080a030f05060a0b28030e060106050f0304230a081306080c040e2205060106110d170a06050a0b0703090f030b04031b02220f0b 70
    0x43e585800804000e0004002401c000b40359040b00310b0100060000d004a041d1803400c000c00340c0113a29038400203442d004141d04d55006900465000d410054510982c083c2400078038901944994a450742550003081c07080c2c180011014000d141a840d40c0e40001c0900b10384151a041180690101c4200b0409102800780d4004100489070440d07448040c0c140102c1091444d80442c1d852015600190300452101c0700c10301902c00700a10004403030040c00b6400545642d01030752140c1041e28040407800c4148010f000740d441100e08190001500d0141c000d0110a03d01a08104d0050003000c41d801d4002900400c07a041c1c0100b02c0401580950010748040480c0c40802021800a11010035184090300c0204811192a0f4003a0010b088043c01c4c03100c10356191a101e44040e44004000c5000421038040040e1954035040310134140c030742c086c0c3c1d25800c540b144e407030071544200010b442c5030740000261074102c010390702c030055000400088002001c01c0e00003203042c0d1003150b1090b604400c0e921306003071f00d02c8001e036 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 505538183 1250 505536933 505536947
    0x230408090f180c0304030e030d080114041e0506030c1207050301062301081017060f0603161211060307080412052d0409060e090c01090e04080711030601181506 70
    0x11540c031100c9071282c1e9281001c450b1112540f40c40c03600360003004031610700c9d19805407409050303401c0c00e424040c84002032001d02c0101c40b00c856102d80c801e222510341402e40a074030713046260401d20080884a0000703505000401041424104148941c440c04080043c1e043c06c2c0100c4004201103041c4040c00f640250348100e256121908803030412411200055503104400a0a40a842111752800407042e001101559a0300182c1d05550384032415030001d085880d0003e8000b5920700900e1000040c0c9103003600030050300060240c00c455002a1800c8500d85803240c0001e1841040c2d5641c69103050b007003508109a480d121500b114080240400c03040e0141100f5544003540350808820200c480c9011082d82c160b40d00594101041c51400e040b0f00013064400f410500340101039203010f035443c800d0000c0055a60a01c6403140081c544c0202d0005004205080007a0081c10b01841c0200c0e180009040080d0411a09820007a601c00c851007032142406140d103d506511800004051030309420681e02070401 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 505539433 1250 505538183 505538191
    0x907080103061e051e010b0304021818010f0902101e050d0e0709150e0f0a09060e0a030f11030c1510030b01140103050721230408090f18 60
    0xd20303220703204800205440942d0f07615880030014100118208940ca030203029144c0e603c10340b42e030400100041241704160044a0040d03900801c2d051501c0c000b410344803000d03c401005940540345010a6a045110a0140e900d082080007400640b40e8024410082d40300145c1c9203000c10049100b00210b14480260341240c01010315052454071810310155201c013030702e288106541940600c000001d114120368009100050a241c2d50120031030b1035148811815038101c900e98220f01108010401810403980308000c03044c010500031801a911052951a00c2d5a00008400166804102e400c4081c1d00100000060740d400c00610302c2c4c00013000c44c86c0d0351082d00800e481e001c10f0b0802c0101d408204c402015800a41d40b192010180b903030750f43c3e12494030b0b51500c200640480d00705000950611700c51000a0719090450902c0d420a494010701000108100549500d407800b03000503d030f44882d8102c41e181d208a110f4100070396500c15400c1402119800307052428007070501501c4100d2151101c80c001548 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 505540683 1250 505539433 505539443
    0x51c0f02061509060307090218090f071209031715030d0f020a1e0c09020903122506061d0117010501060504171006060c030207050a06120905030d1e0b0907080103 71
    0xc3d5240d0100090500d01c041d03100c150071601c0000c24041c0254000000e81000604031140c050564444013292000e00b022a20940000d07070414039a0841c508030b9001925581c081d150000000d0341e07070f5052002c1880c2c00d4603240d00da00001807540c64949000c1001102c0e030f4800d4505002c031102044400b0b0340c0e0b420003410003019038403040c2980f00300340002c13196000c007580c0080d000d00d9000da480e95507000130751002801c14060300a25003800400c0d8568002c440500b01c3c0825481c0c0901e0423a10680700c00b0b4403c900446100e038940100041420030a80b2900c05d49140c20303107601c11035141102d8102c1e60301c851980c2503003990402e00100200d0f500942501e048440084c2c045100a0600280c1800c00882040c0640580d02d40200440c016500180c494a031501ca5000c1700d030750649540420414003a2886000c00140d441a0080e0684210740c2115050910500440e81040d910011640139202d84196103100140842d54200400b92140a00340003e5810f0340c03440c0090134a1400140410310500010304 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 505541933 1250 505540683 505540699
    0x50402033306030111040b07030807080402220f051008060f010303090b0c010605060f04170a080405060c0f0105040f02090a0203010602070605220308040f0b0c0309100903051c0f020615 81
    0x2482d80c0b420340100c3c1d060414080c0607a81d0369211700000300181c0150300280d001804910004924a0062900d04c1c01660000e10070041355590400d84162402c00009860b501c2c1d48030f0001e814000c0c0d01e07014030b034028150080c038104601d05216019103401c0004000440080c084ca00420100f034101c0c4444054812000c1175954038be0440d0061805400d03690b104c02e4115100041014840362804003030b0081d1152030080c010720740081140c1d10b642d255000b102500eaa1800c120400081c540103005044011455050750790b101c842007400c3d801c4070802c48041d6070400c03215a0000071440c000246c190301c00d2040000b14110350404134001c0d6611130038081c020911100003090b1030000f5113580c030106440345800c00d040301e4a803613250401c0071380c025101d9100c0071455084080791041100040d6405081c001d4000c60400d48850100110340b0000704001c000e0104061010021031810b0140824017030100916027030b10848040020114185d032010441190410f0081c000003815040c1425000c0b0802c440e050 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 505543183 1250 505541933 505541941
    0x1e0114060f01090b0d02030a0e01020703080a0b01030e19060e0715080714031003120c0503030f060d050d05090f15030403030c020f03040602150601053f0a0504020333 73
    0x107101401d00340c010004134140480d024207100e4150300254866280b0b108144071486a4101b82802d030300031004024049802800020300303908181d0301090000b0014500441e1010100c1040c1c0d09200041c020030a60401108041c010300925000c0c079050100380c2c000500340342d40f508104900001d00042446c080080e14004240806e02c40c0038500d5542409011030355580c144805401180d039142d110031603c29482c00610310006006201e88001c240d0468081c51071903680300e1900c1c001003c020540c5501c00303040800c0f400450000c101c1007110020540b50541d0b2228154104070a580051612034454806410241391062605040d2600540e01d0304001c10001800801642810300180e10311509120210b40018030540c009032402015224404000294407407e0044507144209a13541c150100350060210141030751f010400e2701e0114401e80041e10640603204406100f905403809454035881d50700740805d500e002d00903010614010030710f0303291a0010518000c410000c2081c0e011001c18200001 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 505544433 1250 505543183 505543187
    0xc0e0a020d0203090a0b06030127060e07031b0b0415050c010e0d0f14190c050c1003050604050612190309050d12020f0604020f090403030b040e1e0114060f01 69
    0x40e580107284003009544a1800c01e00c1c05594449807142540d00781411000f08106040605c1500781d1200031428240c0303080c041c95044041c060741e601c01103548039034450f00008428803c0c004440910300c24018a14802c0b44020b4410304624142c108141c80d10702040200807001400c5c85081250300309040450f15111608020303801003218090309140c0d03024000f0001003a5a020700c01da032805015450314a103141110101003294000e0720036081501640410140c0711901890101c10242e101d14215a2074910402c042000780810543c1c1c42c001c6919107007842542c3c50580641584140d0640e1103840b594410700740c040d503e031300c0700c2500c0b6802c00c60f10250f0010306200b0b41d503d00103400090310389000080145026802090030440e00700c018062890b01440703e00001c640365004a130018400c0d00920f01c2001042008000070b40101c050641d102040e09450700c40e4042d203004280c021010742850342d018014019592200e46c80030845900d07000002800c00c81c0040003c1c0c11507010381c0c40300d00041d041c1c001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 505545683 1250 505544433 505544437
    0x30a0b061603120c0c1109090709060e06100c02031b0303090409050a02030c0a0608360d02060c040605030408160212030c1e25051003020705190c0e0a02 67
    0x10129180071841000341904201c0080e480c0c0040342040205900107103007180d8005410b07000500307110320503c0c00180391401c855000e4020744a84c054034031803603071400d1040841d81e90358820303214401520b080003800e10b00341ca500860503119040c407010000840d40066142c000081c00c10700b0b0450010243c0b03001d620108103030740304918050000c10004109040060b910354042030201d06c240303e204445207003414828081d008866854960850a0301d4601d01050680c6051118440e60084036080c8106508003641d660381180e03840002c2c2407195200c3c48001d0030200c00401c000304400301000100304160313100c03086a034469007110341c0640b50000c007010381190200820b0f0181d40411510148842d0140200040c5280c080d010304968180c518400d161800c0040062b10f82c03400d411407000b000c3c5690403101081103d800d00584600200d4441001400508142100b1000a5804600d080400c40300300401c0000c07030610a00d03a254444940d0700d21541c1802c5002e007000054914010500c84850b41d01 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 505546933 1250 505545683 505545697
    0x80c120d2d0203250b0a020307050d092907020c061308031b070f030809010f03110c010204030308060d021f030b0d061e14071d1f1112030a0b06 63
    0x7003140c0c8905000d00000c0d40d942001e02c50401410755070814842c0081c1404100110b1503000d641d2441c284e4030506840e00a410040c910700911508000c105a1440540304c0c1c001c07018490000c182010f4902e44403495983d1003c4049120f0f5103801c0217101100d50005000800260200c1d1056903647c802848500313902c400360b100d40030502c40452144100e02c42c0304148040c2e6481d0390101d90074250340b0307003000204030090301c400340036081c0030090000154454000410082100d04020400d105051001900f5911503100030034580d501140c2401050381c0320101d1a00890200c412070311248940d00001c042c0d502000b118507003045030760383c000c1c2d0360b50094000074004540101000c480d4603203401e14002a188a1650030515025101040e041408510607007020790f4a80c1225200e558690070b00f034400815420f283e60421445c20b187c0900ca55808a8450b8000c1c0b6101400006804801000d8038484030800f40b48600e81001e4650000c0c0d6480c1d60540340d2201c02200d020800e8801400030031401c1c42003003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 505548183 1250 505546933 505546997
    0x60e07020d2307020d201f09210f060c0e0a080d03052502011e02070308150406080a06152405090d0203010c08040b15030a06090303020f0310080c120d 66
    0x1034840c086c00b00070301100e1040084195040c110001c440780a14a50103c811a0940032514540045c081e50705203001c1c2a8126003400034807c494150380e1690408203036034030401c4070f1854940c4aa0f22900c0d0344241e91030540502501c0d031002240c2480e024984508403031081030101035552001607840001070b48080e014511903000c9010014202034001d021f80b22a014113110300d503000101d003540380c0842c0300b1180c0c8143c0540d1648101c0c0c44042c210b90074108904000c031f038055158103003c60b010405000c1f02d25000e00c03030100060300e40075510898610480d6a0b0061048800e5952a1104020041c404090081040c0707070040e45c5410302400581002d210010103034066282c000039041c0160410b4000e03029502503841111260350700e0320001a0105560803207a016040a891040002e10581010301403610a04000d41001240c07070b4046440d030030803140110081803c1004005045007440f08401c48102a1350403100724003031780c0d982640c1e0042411918100618460f0148002d4280c034100844901c2e80 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 505549433 1250 505548183 505548203
    0x405010612110a0b1603030c050c0d0c050d020a0302030a030e1504060f110405011202070203030f07080d11090603040b10090c02010c0e1c0206070312060e07020d2307020d 75
    0x250810361054802c00740e82e0b500038184600040340c0392046100340ca4548061140100201c13250b6070302100900341144a203c2404001c1c0110f01c40c40c80184002201819590344074000e1100d1424100e160092940500041d5000050f1340c10201e0350200c02c50300000c0003420081442010300b0746180c0345c000f0815015a01039458414441004400d400511856403080000d110306009901031102070b00c250301c2030f42d02041e0784801003c44010309402501141d400202601d0401482d006050029401118201e821600006441501481c644540d240342c003134205405007020004c00c0811628800500302a050126000010f46008843d041520140042c50001d02407442c41d0031000e030280160000600109001ea0004003c034188140c801e12061400e244606458403541c0030700c01a03038010607041c0c3c2000410780501d4a120464000c41e00100245590380e800b07494545802428681d440e502a0100101c89404030750381014076008154076247c0d007840540c0d0300d0341c510004010405040e40103080100ca = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 505550683 1250 505549433 505549469
    0xb09061c0b0a0507022e09110a031a010b09180402040e1209040605150301031b081c0e0d0209040204050a1409010903080906161206030b0a06050a090e0703080304050106 74
    0x30743e048140522000d13001c490b07200c0e4000742d02c0060300b90751041c5a040802405122054212107421014003e03004100c2c0000001103e40445c076501ca50750010354501080e5902d00800c1c0c4441503281d030050070000c68544c20050f104000803018584000c05010008020000c9400d40d56180c2c008048008108111b9540b10342c0f409040300c0329002640740c1c0380308514040000406040005100581700703031800504c2e2550303080d40d6990301403440624a0118070001510042034034002040b804414200b180420040c80c2042103000700808a03982c10703580169011001c140058407100a41c03600203604540100700d950700d02810030000d003017142e07250342e902600e501801408032041d4460316889000e5682d08007640e5800715a83e940d950140c403003001d5001100c0951404c0c6205800c440c07407260324000d000ca0a1035613a103401c03901c144141e4200784902e550f14000c014a1911038650401002010414480c0e809814401070301c841942c800541402400000203003001001c1d0302050107030031900501c940341d500d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 505551933 1250 505550683 505550701
    0x50c0a060501031e08070b04050c0a17060604020a0c02121002040321020c010504060c081e090a15090b070606080303010b0a02010f0207120e0d060501120302010b040b09061c0b 77
    0xa03c402d0340d0f10440b03440c0e42110010b190803101c0100381c0040b1114900b4417181d0f0f4000c0e40c0d00004000f40c43e9802050910320342c0756a000c584e800217000c201d0368182403040f001081418440040e00702d91040348100101e0f94040c0c1c00004820f01c2c01d804980c0c1c09810b00791521035600f0917820040d1500c0c0b41c0d20000b008020849043c007201c000c21107481c103c46c0346442d000380c1039980d409001c00381404210180001c210329841082c840c08102d04c100c000c5030030000d50000c845203041c1c142201880803a0003240c4018107082c01c0e41d036480240b40c882c0007100035044c5088003800280c2640645140c00c040000d040044c4507140e0080c1000700400c0c8120381c0d4940c3e41d514040300c2500000d16800065007454580103080109009403140d86070080d25950400404c036900b0382e051403142e2003154000b00140e0003000403481500c40c2c03a0003003040c00c0d041041010103180084c01c683d0b058080a1103545001038000268654450300c642c0a54151a02c3c01c0707401546490001b84000040018000341c0c0388020090303005 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 505553183 1250 505551933 505551941
    0x5031905070c0512040501090308070f020607030f030c0c0b18160605090a1a090d02041b0f090b0c070e0c250209090109110603070306030512130e09100c050c0a06 71
    0x2c0d0062094036015200e8903c1c0d402240310301c0c4101c1e800107080e450300f0300201c5c08560003022414811005901d0341c1c040c0d80d000c240709801401060b004101a03448505640c1d8040c041c0d0b00002e0624900300d090082c8560340c8000074100a0321100c2c1c1e07161809000c0c0701d01d02082150308044d072a0308501000b91a96130900038910703800215500c0c050411280300013801e441201e903600d180f0071807c8600c5e060908200500c10008040c0800760703402034031018039084400700640008401da05503907802c9800c12030780c640034048040c16400300001900400580c001554041641d60940d010f04000303940d00d817110002c00d066800345042910004c11900f54503280180c601420344a01031091341c240350281d41d40c0400500721000700c20060300040d0314400d81501e510b003560042d03900090904001417030545a8941a141100003c05400540070004494421a0a241805008108054610312540b8084074096203404030039092460840d1660035002c41140204159010100020100c0700040362500b010b402030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 505554433 1250 505553183 505553207
    0x6030c0c0c030d0207030b06130905010902120a0510090503040305070605090f010905060319020c07080a110409022110020316090506030c041205010209090f0f0106020106030c060503190507 83
    0x203110741c001d1075805003004030740110302802a07006406080d185884407001e50301c00515040c1d21581ca107d00c80c40b160f4043c862159001c0c01480001003c450314414007108400e040030120140c1d0104400000080001a0503c4c15842c00100499080c2c11850080d2031070045401c01441030060700310201d5142d5004001d42402001112000550f00c4400d00640340c80380304d40203072500074004000003030000c40100a035291105a186d001845e04400007402c80c1030442d5900058020381080100c0e40500c120304075010b409901c200c50400c00381c3c80550020b03205c1c2d0002d051103650b008041d4005c0c0ba4020f0140022400203100701d9055589203480510000d409400741d94010119040e10390203d102e08001c820f4900c80d800070844c02d40751509114294401912010045440f990200f2400d4025207415039910302401101500c9005400c08485001c1d820344160041c90842e85000820408500c02003400e2044406c1d90501c02d60b26107c0340b00d0f0034001d100201102c5095401c060034020005da21034008800e07 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 505555683 1250 505554433 505554457
    0x181002030c3a120608030d0b060c0a0b1b1b06090f1209030102040b0d0c11011514010210060b090a1a07060b120601030b06091e0712090206030c 63
    0x1c0e40035002c415161040009209402c03403102070742c0154030322808810b000b201d4400e6003042810060400c00510540b18a508810890340002c5010340280456002da0940000c08440c2141041420011640d895104003000b416034801a008200790003141c42140d0721041000c2d040d159908085003ea90040c41090b110f0541c0c1c0c0704650008201a01c042040343c11124540007a10100316000324441c11904110029981950300700300010712206c810000f001d0f00041c3c90404905c0400844c0003030b0069280d40e030440d28503414192002c6d40145190100c2c02626400140c840006429500407890407070301181900203145403510100c1d103000c0c0c100c0500402078040701ca8081550715440c900b200000356281000344004288a5580029440c0d0441c05240c5030140c90511501440e292031840c040e030a038425a40d42803003a042c8801750402d41c4079079038007040305c0e10402c0103660542c40c1070001600007044102040350031006480a11f04e985c00510f50a500100219141e0600301b40a2a003a4000f0710b0f4262 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 505556933 1250 505555683 505555693
    0x4050c0708300f0403030b0a0e10080f070f060f03090f06060302030616170a020c060f0a0f020a02030d09020a08120310050a0602060a0f0f05040f020307080c15181002030c 75
    0x140030031038181c95103d608180c402e1032268860340d4068028240543d035030340c1c0c05103041c80c01180c0c65102c6d90741e8070711504050010301002441c1c01039071410301c000000079000c5034000460900c200750308200241c08944292070100c0d15080100000c0b0300420440c807004001c0250118846c06002998201c8004c2c0c9000b01c081d2402ca031180303000e08116124462880c8045400d00007071110041800c6151540901890340c00b502d4002e16002c03050401c4411103a001b00c2c850180d05002825106200f00f030007000e41c2c1c1c1801c43c94081a039a01030740d28024003030914034840d100c0f6600411034458489000090084000b00d82c0f5003041c1d1091910241c00880d03803056410f103295000146071502001030811a031468010b40182d1300c81d112018040d0410303030300c0111800d8490804024070022031060901c21401040c8180c0648554410941071040b981d011a0140c3d0104180700c06554030084102a60002c60312030960300d2002e0300036400c0030044070408076400345216001c0c4c400d142d0040000c1602c5200074043e51 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 505558183 1250 505556933 505557007
    0xd0b06040c090f0302091f0e0709050103090c09050a111318060303080705070609020a06080603160614070c08190b1003110f1207090c02010c081504050c0708 69
    0x200c8038000b0b8070415070008032014081000d410004c5185401022007140401490380c0700030484800d542c5944040c0e4840c400708108280e01798080441805041c013403030180002d4180da1200d20001c0304c0b9005442000b0b039550089105075100c2c4c0d00040ca8060300c0c4a015460b0582c40486461120791486480791490a441643d444021940306020640350301d5141e12909031501c41044803170b900500d604032a803d0750368000704050f80c1e0351028000100226034519410380b4042d0b0915003450f014103e05445851300d0002880300c036070480441000403558101058030b4074005d050607030034008640d001c0910350284900b000c6110440300c0b10444e0b83c50003490900815145c81110364903044092002901e400032074048502c0600e407850040d88003800c0107040003079034004c001e025070070980103a0000203800d40d02c4400c00e8680b034082c014180c1d4503045042141c0f080c64a0000c80d10b10b50903902045114603034a00001c0e04d204680000d482c4400d401010b850f84400780080081915100100e982c90b640050705624 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 505559433 1250 505558183 505558187
    0x90506071d1008060109080304030506013201080702210d0c05070b0708060a170a02010f0201110702150c0307050307260d05091c0201150e16110c0d0b06040c 69
    0x480001c0d0703000d05801482d03000c2840032904400041c00075410000c1c10000021400d204102520107075001f000500025403411880c8143c810001c140d03100c2900210155458840441d6842000d606080c20305000c55556840128144458045a000b03060605000515980c01510142c1400c0301c0200d420044101c1401041c4d80da030281c2c1d00000d01c01101040014070301c81c40340c0300040d0480c40c05001090044c0d12404111200720310300c080d00c646a03100c0c0d4200800c0d0341e4456606520520240020069a046801c2401845c4a20000a0701071607054050314440c250b500b0444003804502c405690304c503546490440e40303c3d48210390948035003100204a15440306010300c0c210246140d45d1180380b8090b806801c86d07000c1c0c00c00500e4030110f400f59407482c1941c07550f0842c0b0215074420b0fa900006a0202800e9a036040120780e41181403601e05c03950421034035140c50814062040c815040c04840020382c1e0300ba03289840c2c2034405058101480300c1c112010401c0c02040c030ba01480046409203c1054803a2007 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 505560683 1250 505559433 505559477
    0x412120201050f07030e010f021c15150c020307150504080d0206101401030902100e04060b0306090c070f0213020409050601080601140c1e030304140313030201030b0f0409050607 78
    0x140580038050383d00440c40e40da000c3e92010490303920410000c20b201c0416265a0200c1e08405c0b0500c0220001c4141943d40421500c18030f80d11208880b8052003803030400441c40c00750360013040d030b2000f0300244e195110255681003150500410446800c0b021708510301034020107a8000d0304c96261544204c02038141181d001044507441807032800d0280311168038000500e12421240690907052654403c5a9000342c2c0b00c03c0c95001141d1800d40702d802004504400b070208440301e40d130080300d413244144248580c941d039a02809401280d0705550076102e0b000d034140b00d000d128103020001d6102c100a000030018030120b40240040700d5100104000d29a600300c01940c10a02c1140c032540021000201d150090340090003500300c0e0315001c0111403c1c01040b02d0000b602c000151401c0740c00e50702c044100001c02c40341001648a401e01207010b1401d00352a074200d600c0c402c0881c0002414140c0794a1aa000c54032030b904071100034100100706014200c528100151544d106a410500007601c410a00c981c04003170782d007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 505561933 1250 505560683 505560691
    0x2090a080a1b030f030c0819030e0d110a140709090501090308090a0302070509070e0a0b13050604031a2211010e030a03050706020f09130c0306050108010b1b0111041212020105 77
    0x20000c510b10a690350440d00402600401c1f1550030090110b040d4014680a000c074070b100e8aa2000582103528040191400f422840c10800308a1700c0340da440b20002d00450165046603200070300c0420380203007000240c10138890381c010700340c40c61a1841100a01c40c0c1500422001030080c0c903105110744603203843d903480e140c20711000b07000761703101c00c1d0100418181044000c1d800200ca26000040340808400941c041241d5030000c08a42c401003a406840861902c42d400100005c071010f6107414519a01e50b440c51007a000d40b0f0100302d680038000352003103c6442c0c0340310115a10141030b07500800d60346800c0140e41c00f0582a940042e074040140295404c001803643c00032500350700c1b401d04003e041e9680e4800380d8041d8091081d421020f2004184030746500d002d110700780001e0f00003c20a00302c03003a4001d08a03051680000d0400c1a035100400007008900203d035906940c0d0701007901c4122669003e203014040340c0c81c3c4445060302c001800203410301081420500548185001c8000552994080f4217880d0151 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 505563183 1250 505561933 505561943
    0x906080c0306011709101a09010f0f060f1e08040b07091202061305190602060c031303030506041e020d050c0703052b0504061d010c0909020d02090a080a1b03 69
    0x340d030840c8141020702c800e0741c5c81070180c401c5608842520016a0036110210251140380c04110041484d51400351041780c054524032020144091034465104a003c0360380c401c010a100600e50300d00ca05901c41d03d40016010f600103c1c510008241c960001e0280c030302250b043d5211240c0c070f00840c1016200719180d0b021a100c4800080301c800c91a02040038039403240d803180d40e040d400c946000401b40c440d0110100701107500c20a40c02c2d420325000c80a81001c900401414100c44104100001c1000258401c054160149400652a030344e140110740209205100000035103943e0422040100f45038005000801d086c40d41030000e82c662104048160041e00c00060119200f031181d03112258164084150405400010303019103110b00c88100d04441003a201500d8982d04c40075403030085d0320154a800f8000c845280204511841120001c088013800e002d009869500005e0028026040d5019200301110003403001240e290346000c10399a502105104a03003501c040103c1c01d8424002400c00c0044035006 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 505564433 1250 505563183 505563197
    0x10908031510080103030f031e1b02150108060a0c020c0d050f0c03010501180207051f06050a0803090904110a08030412030e060f03070c17120f1b16210906080c030601 73
    0x41c0d04103501514100c40b440d40c245c0791427402d803c040b610034000e0500d19095445141103a105526009040002c214020f07400800d125004005108001601c0c3d40e02908502d40011003d407104012801e1032119842d095000791400d0701141130003404100202c682d401c0004441310120500709042c213840c4248500d00c04955454546c2f02d17498841e4004146052041007a1040120100c0740408405c16070034a08612035920b540c18032080c1001c032103800161003031000031401e003846440000c1704440c006000030b0021141e20401c070a15121580b000024000440a4980355510303150b0140016020392000e800143c080c4642460b14108642100d4203000003080c0c9901e9556165010340d43c10701c40303240840d0040b00281c1440038400100000cac025a200c802d104d210941040c0c0c0240b074146101810b103404907084200420f031070521280c01c43d003034806071810240c5842a1400e00b8282e01032503c43d070514242d00e03070440c07c20b00b80c1d000d01c00d10103582c4c042e140c80b038061710b407036a5513015800308880483c0400e0034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 505565683 1250 505564433 505564457
    0x181c02030706020d02160b01030605060a230307080a0b0a1431081c0b01030b010e2202120709060e010e010305130203070605070212060601020a0f030201090803151008010303 76
    0x8a8000704000344d1980805885d2803003401d404402c0303804031030003074074101800d00041c01000124004d440e040b0008070307240c80d10141442810f00381d2b00313042148030f02d4035800ca0a000c011600c040c0400b100800d18642541c5d0744200c41d0408400b001411140081d02c0c900e007410b00b41c040d030700c00042180100550030010603440d1612000b0303c00034412076004460081c443c0c05150004143c40000d00e012003038400041203002504054005450380006400d0616080071000041350741d0204103021090011154000d080703245c81ca401d02590061400c070240140005504102603100300c982601a01c0c80340d0320b18000555809080f241e43c07138000d0032280000d010760b540e031070117610940000790001952101000c0c424110350000b498000540c1c04100442c5000c1030aa0562400c09075031555046a0405000d20345002c1000035100e1904d03200084c41c1d0500111810305041c404d6012105840e4070940955407410800321107400c1c4d0381600255840b5407802d40341520218410760310241281d078907448400400742d03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 505566933 1250 505565683 505565693
    0x2070512190303020c010f1a030d080a020a110604050307170304021003020c0c0301091410050903030103141501080616020a03120203150a0f1e080706080a020c0105181c020307 77
    0x1d420001601056001e00419400d11000e10401581503221000081c6054411500c44618100b001c02d5501c6034104450440b040ba400182240c0c0c0b15080b81c01c016030b10310424000352400d0004003040151480b64030104420400000001e0a40d5401960320004000b02c29184840f13034802124001d4215541e041c40340881d900940150001000480c250391880204d0000302c1e00311803c8003415030300310a420714103510011050105030080c2c0b440d45d009010700d01d0408444c55407840188002032003d007400200442e551028044c547c2054114008002e031969510b42032a03440c0740a072412812040070004152980707000064003210140e042d25038440c0c090b8030030041402508000c001e1085014032141c207071310030b84c0d8100c0c041000e002070b5151061842d05100700c00542c010010880c02c450702c20403005000340c500001c0c1903000c071038407842c0c0712602ccd564040102000e40201083d81170b040d0b0030b11013448200144154124454801c00046864060084565600d001d2580070880d0150b0001c00880c40070032 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 505568183 1250 505566933 505566973
    0xa060b0126150307030f110103140f100b09101808030c03030a0b03030909190609092105090a0626090d03060621180503160302070512 59
    0x4005040440c65110801d1180d14008002001805200410303020070100350882d40ca02c292414050f0020b142080c196030f0b40c4900e1000700360001d4500080f40211001c1740c2c0c840c0e0080714035805100c03550f07800c1d82499400c0301001407007175407103000c4805999004a00715049030240c0300010001058048a0314201800b907402e030484410800a00d4011840800c4000c002c00040c4805075501004680e03c0c6005801b5100311182014a0303446900708110369016640c034209229080100c5001c40001c55030741c0d113040c40040800340e211039061030400452800340140d0701c09140c00240d290318072010300b260701042166584590010540e00030350b6500d0900020b88620103141080c681d500c0b003201140e18142e14411340c084119849a05540f20800b0034898582c54050f000c0207203407034200030301c581c1c084100503e40030600c55a0b400c030441c2d0729254060710708507640600c10181d4120055a42e54842c1d402c0041690380301140c103502500c2150740004560900803510f02101c58540050800064003a01021400c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 505569433 1250 505568183 505568201
    0x270b090d0804021c0803090a02030f0609030a050c2d0c040b100c081606051605030c04060c1a07030b1e0303030103060203191a010f030e1c020109170306120601080a06 73
    0xb1302c00c004088000481c890300950045411130010004400a4410580340403107104958000d900a5824800b24510000584a04008500b001900c0d0301034a02c01ca4503142887d03120741c107880907070301102d0110003552503c03441031a218001d40c2c009180a20520007500c941800c0150000c0000c201032060600c100c1944907030912a010031407034410f080c2117191401c0880c60b070079950a96103c003403282a030895294980c1400860405a0461410096041850040d44250350900413090066410400c074a031031800c4040d040d40390307800c0724100080d009001b030800d20480c0740210708140313940c14100c29202d00071640d45e000030021841c5a0079542c1e18006500702401010f0b540103010300380a0041524040c0501c40050381050343c0a00d107103000014032502c600301260043c14506882042e01160105404801080f07604014644440540c0d00b02d004100c03840c03000d03180c0400954120016000c480081d4006e81003200c031006200500e408040c0c0b280020310401410750b001c0350034000003641580141c941 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 505570683 1250 505569433 505569469
    0x6031a0913021f020c010206070f0e18191104030b060f04020c03070b041106190c03020f0304090501031106030c04120c03170712020606060d050a270b090d080402 71
    0x50070388140d0106800480f80c0814402184941d41039040b110390420140c19840c0091005120038103103d0700290110345800c6020080003070026155a81e9118080c10a40c807004080c1c0c1e511852038103030b03552003d40d0721100d4584440c4d03080c0320602601a0b041c030103a0741501c1c0c0103a103200032500c60004000d005204010f0741070300700d0707024441c80d0032150341407018241290044d0000c0c1a2460680f4040141c138488a03516480b8200030b000362005140c0c0900389001d40c40b4542060348014505041c203074075100c403500030b0f021140f00015000c501e0340c510341c00c803d0407244512680515200620100021400100ca20b01007010b003d200401074400143c030883c4181c0d00030030400141c65100d8036045000740e01c110110003502c2d03000402004002c900c01c0740d06c1070401c1d14802342c05c003400c01c0310005000b84509110711400e03a031242c020400e0764140d41d005440a03444685120710880064228401d244140c1c1800d03104000c4820020300c0a05000c1901410b4075495900c01403942d50f1582040445643c145101031 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 505571933 1250 505570683 505570711
    0x618210d1101230106090e1306091104050109060501080618130c0b03010f0608060d03020318010e100801170102130510020a170405031023090a0506010e070906031a09 73
    0x3d01d9155528051000c0c0140070400610b44c10101c0141c00e681c0b007640400626150b1104106101d0751400c000f810095010302d010580103200d04050312002c00101c1082d500c6460400001202d01c60742e031018049800a0701c03818a66961541004030141d4280b548001c0c55803284000b400d0400041c0c40d0790030040c40389100e164a60746a40c403011171070f0401d81201c80903918246c4203102c0c843c1c02c00c12059118504803007802400d010b80d90001d4a0340200c0d51100c51004080000045681c06000d84c240c1030240a086280e02d96071402004190036001c1c820108140c19007914412500c0b810b008607180c0310150154032050078a4501403004010b82c001130f0108501496201b8400240c0001d0b2181040802300207094031942001e0415007002200b0b090881141c1c81c1603411000c9110b402c6a82d1500109461120007507600c0402d0f5500304400c0c5800203250740039000002c241c406078808528003071250b070755403180525294481a8200c03a0405203500c140844540c004442e8904058500e900c000a1070a400b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 505573183 1250 505571933 505571951
    0xf030c0118030813140d030903080f070615030b1e0c1e0d1b09081b0d02060304150621021908030703120c030902060d02090607020618210d1101 63
    0x403c3c6034004004407424000507500411040141c5100360085402c116044401000941e90141a460305444010030fa1400420820982008031080e0356503150841c40c240f18400c43d020f001c52042400340011258a100c0b0004108a1111030340d00440c10310080c00b03903c0740c54807801280d0a9580009403580d4050b406000310145051030017015149580300b030f075408640c00a458203c4520301950752000360030000f01c0d4004120082000910843c2d120b925501d03030702c0300702550b004920f02404001e000b07504910004184401c2010200c207544d40041980e0080006545a01040e201c040c10001041c081d4092a1038140252070a000340a504d1071001c0b020f40059595a441d5030b0842e041404d056001c03c150200034503179030815000c1c0400d08070042c9000c0060708103a500140306801401d0080e51070590110f1007083c203403141ca08880c0c0560f00280841c2e20384841c03c0c1c460503140e14044410340101c03a403c07801c41115900c3c2c0155055803440d000980030303102c0d04000072501280b8102c0c685001d59221600c070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 505574433 1250 505573183 505573193
    0x408100b0d11060f1611091e130501050106081905070903021201140c0702041a031c020c030102040b0304060e0111030c0c010912020a030906091401050c2505040b0f030c011803 77
    0x10001415004070a030a01c021758101070f2003a0180800080c002c00d40a000c2180b0704044103075852600031500040d1405490781100031140a4844000030107a40c45d24002103100c9401c8011366210b0309949071803403461210240d072138040c0c4070207407001c1003c40c07041001840180f07050401f6882c02c004a0000051030200c040f011200a10143c1d9402030841d0002070040946c00d250040c4811001c0700c0e16403400c11580c0c0000b090340c6403011b000742c101d10f50245901c80e0019100340624041c62100a0081d500c031a100c4080000541c810385044880e240b404407081c3c41d40c035060140d8451003200d402c003582907503994005040627500c8080c2d0400c00703550762045100000d6001c520015001c0666006202c5200750340b4020300040300540042d0140006410100101d0040d007080d0500d010081c603040e80c460318810400f920b03042005100c0755242011540c14100207803130340e01d0282192802c40701480440720000038000028131203a4841e8041d00134001454203540074141d013400c0d40d91542003113a0416581d44607 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 505575539 1106 505574433 505574437
    0x62d0e0d11030d11090a060309032a0f0501020910082a12180c0d08032403063306120c0409060b0408100b0d11060f 51
    0x440c11120800b802541c00003400c4034414455004140d40c1c500580e0007428000340600b41522002808522900920b110944c040e100c008200b0328007940521080b0300304070708518803642c403071a4400003500e01400403c0d6900074000182c80e203021508000515204000040030091080140000284c010b480b1644002601040c2ca40021075802003100314019030a009400382c0104081104061f1850288040b000020040d030b10550010820060300030000e080280107800300381f001800d003a4910076040590b2036038a0440000c03c00400020b8903000c0100e540c0290a0300700001d15050813601d0100110030b8035007011482012666001060a034000c04903044004242c3c5404070310300032100c50449001e0700c01414140076654641d400000b0b90f45c00b07480f070801540328054469004504600ca091004100145071031442e0905459070301c04d201010604561184003089048040c0c850000 = true := by decide +kernel

theorem cover : BRFrame.Cov 505395683 505575539 := by
  have h0 := BRFrame.cov_init 505395683
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505395683 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 505395683 ≤ n) (h2 : n < 505575539) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
