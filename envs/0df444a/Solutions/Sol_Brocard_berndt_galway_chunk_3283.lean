-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3283
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:12:31.396826+00:00
-- url     : https://prove2.me/submissions/ee65c2d9-fa6a-43ce-844f-e24166f49a24

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 590287769 ≤ n < 590467625 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 590289019 1250 590287769 590287799
    0x2030f04031a061509010503090703081309180f033c0930051203010b07021305090c061b0a0f05100b0f09040303150b09030f190f05070807 61
    0x100c041d81c6041c0e030340b04010b012141c604c0150034500d42106100110041d0310400003140d000712140f0549410070364a035a61031458001000d03d1810100c8120107015121403446108a8000d400070800304414590b1690301d0401c1005c00301401704061039059403143c0c500c880d04100d1228a1006219101d01146180b8546000c490006400140c1e290380008948250400d2105c81180c07490141301d000100f44000c45500c0d10034801129140904075003984007a840e07e003e14000c0c0a90756010345c0d9050380f8810802c880d402018240c40076441d00062040c04400050b0009520b002514503d503611951200540307400758800455069108415160081102c030284800d03101d4400c5c002c907210310040201400940b24800300140d040b00c8540586019841c20035659908a0f000c2d04000032840350389002030310b601405400008a41e100042c0c800d6181c01c0c20002090100d11450280200d0158a00031141c50044090090005440d00d4128414410180410402807005c4e000b01c410300f9a5a092603549005 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 590290269 1250 590289019 590289053
    0x70303140c19080405070b09032b0e01051305010806060705030c0102090103060510051603030b0d03030b01020d020109170304111809010b120d080901020904090b040c1d150102030f0403 81
    0x2e101012021441c000e1000d40c4c022075002000d00000360400321080d00c1d039003001c030071680c2c1072048202440300881030219407040000141c0300303407035690020000600346c520081200c604000f410030507242900042c10071001a0b41013460200d0454071000d00169083c0690f0f8070240c40c03800002070141d41003034154000c11521b0006e0320b040c80956501d0080100134203406c2c0c411408140304002d00b000f40c03d0701d05003008202d0301c03078100011107400e4900403460b03c1145200c00c502080d44ca4040355510340e010009604044081e20080c40f90545580c1d0f00c0c914104a01140180c40a000c07000c14208500100b8a916050004e010010004001a105d2a400754291014100c1c6c0d445c3c01c100307103041d0400c5140030a003a01d5400051000d2000440c0864071414010800c500d9035500784070760440c1759220300500d800c0b64010350005199041509002543c100150300401810b41c255205001020300c880365135502a10640c0302000606880c0c0060b420f40c418541c00450012000601008200301c080c20f0ba0b040707013 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 590291519 1250 590290269 590290297
    0x6060507061802010804030309020310111b1c11030c01150e010605120f040204090b0a0204030506010b090d080a0e130f1d071406090d050d1b0c0605070303140c 70
    0x30321003100c840d80a0100b0074010380090408000580400d0081e007200454900c05411904000c04203540b08046071740680300b03401b01c00000078010604c82101001c500d0305200680c060712400c40c5604a02e04c0b0340b08042c1140b01445800485a00711210034400c0d940410700c0da00080c0100345401c00c15844403840303401100c01440b520300020030102c0c8150242e4900101c81140c801441e211000140b0385240001e008070790090320340c40e1310300000e240b00700341070301805101c24003603142c40c00c624000c1d0900c1d0058202c0308048805000880300c560f12424051065074200c01050765689101008540d0320300250790b07158100d0a81c0d05404082a85a4043c52000704001400c101488582c0a0060541101c601041c0c0680c00143d09102031004a600703081e0746500207084500c4d001003040458000c12503c0c0080e902a00b04035400410560041a09441400e011031807039608247c590314401c02d0401400740d0010004046070030001c0500a61204220000340744000d409441e021816500e680c2c071600d0b1240801c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 590292769 1250 590291519 590291531
    0x17061522150303140a080c090415090c090608041a070915020321060a0905060f120d03050106090605030712090f0b040c1205070506070f1208060a170616050c010606050706 75
    0x40102e80041d075450f4411030351084402d41fa0603032100c41580003e0201e0b54002d99030102260010158507081000341700d2087d01252810300c0d403602928030714956106009011883e03082200007081510640340038101c0d44414481602c40d0704040311b10700d400b50040c03030751145010302c80420b164000000e0a10b6401c0e08240b442c0070b40100c241e00c8010f940c29101da17a0800b859040502000240350065940114064582100814074000080c1d080c0c46e154910281908045400d070b510f250b041c06100d02515060074400f0507545085001001884000c1000e02041944003414000c4ca9858010342c034507a40290b8510304080c203078101001d5404082d903044490054031200003600843c0320b050038244641002c040c010300c81c0792109101e485c1c1e106040c122007036a00c03141183c00052000001a07075003000c40e070300d04250b480c0140070300203400300d0380d000311090004002e03001004100029a00d6400b0b0706421246042c3c5010f40d406850074018421904015400c01c040030801390350140c040d02400d4007034034040c409 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 590294019 1250 590292769 590292797
    0x6030209030a060903030e0109030306030b01060206060d0f1b03150606020f0a0b0a020f030117060609040807030c0f06021908010f0f270501030305030117061522150303 74
    0x480c41104030554040d0050042e0b140801c1183e400911000c0c0213044c080b9600389641d14140c2161403080084001c40d5603540240b050064601a5078050f05035030000305010b082443c00a2a00e07110040018011080c0746540703005c2000140c08080450341540170079000c6620780c0740c1141080c4000f10410551490b1030400901c06100083d203502107041c3d080504948271040d00c07040d4144400070907001c403031034003085413889080f4680c0080d07000b001e8a154441484103010007450920307002409407842200c880c3c0600010841840498030b516031706061584280c101842c145e203100c1d00300e19000c0d103100e00c0411980c8070300c0512401e44105084d82d60f03075209160380b40d0200a24400a501070185039241004040c0420140c1d90a50480e4003104e4001d050030058403a00d0070207403502608120b001a6011004028880b81e030b91031141d00744008006002c180ca400f006015010320400000b5101786440e09040d200401001005003070003400100c00d200004070711404e0340d4909101e01c800c0f40050391304900002 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 590295269 1250 590294019 590294021
    0x60204150e0a0605041509050607050312090105070e040207060e1605041416030e03040906080732010e270f010617130218040f0201080114032d071e0603 67
    0xb05640d4541c5905080c82e06104a0070074140305003221a06200703040c0c50102d59a5280c102610f4040e02c54001103641d0072044466075006840600450390b1031303040c9028400039030b801c07000b030308040c0c8000d8070016203404140c246a40035058448007075415016441d03d80200758658030071001515801e82c3d05202c0e411401070b208500380011070703040c00b201c4040003001203128441e030012202003207014122410b060701d4000c3d8004448080d805200240d0081408014003c0840041e2a20544004c0881e061040c004540f0b454980784d20f0300d050400065048419990f07840400094075050074041d51078001207041d2540000250a9420002e060855800017401c1e0b803103012101210b105060545256464128080f000710502001c00c90380042001041c1c0c1d6a00351807034455200d035001d42410318440d4414000036211000c1030300601c03050244540141c43c44d0b180064040003240e503170104500c640e070800c4600c92050214036110880d9004d4210000740c40d040c007158108100140514400f0501d9803000300354 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 590296519 1250 590295269 590295289
    0xb030a0308040206090a0b0d1a011b061e0e01091a0402031005040c0e24120703020f0f0d081e030105010c080309101d070f0506040b16060204150e 64
    0x40001d010040040d0060401c10301500075488080d20101c10384d612008110415004940e08011301550341d52040710080791060344901580f021709244e800703440c0044000c070303244420b1301028100c0d40c1c07240f130781f5035050016807403044a45100000c00c000c6101e2049225020305a054000d5615000345404011826500d814540c0901d80c000e00030700280c0f400c44041000b8040040082c3c9810080800014500320341441c0c1900c210f0b103441141c8086041690604440780c40c0541e100c1c002c0040307502c42c5516102c00104103050782e4044595048030701d152000140240c500c6040c05410030045440001080f0062025240100300491400140c42c120300c444101c074003003403042c00c0c00522240142c20204041c04001c540016103601034403803c814101f10300081d19810702c1d4072001303007481d240c00076100301d0103108220180c03c0c1c28100c2c0c06460f2030040050154012030040c02d240800c00240c1c2d5006241c40c410908030964032600a545544d03460302042510031055040001064072000321810354a001c2d9541c0c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 590297769 1250 590296519 590296523
    0x3061104050603010e0a090807030f081515090301060306020f0c0d0c020d0303023001060f050711061c050403021e03130b0307120e0f160807060c0305160606090b030a 73
    0x110f42160f1a250f8604040e00d009007070100310381d94824601d80450317003070340083c06800c1c0282c5590007141d150400041c100000100540c0901c5688807102c44250303942400f045440400c00311503522020f1420001c1c4c01084076034402071595100180300c119680300c460283c18500800000d94015082070342003902c0f81852040300a510003443e60115000a01980c064011001100070400c0800c2e1304c1d9109458103d038604a40c0442d00014004100c3d840d4800c3c0c5c01c0408010500c0c11703134280340340350791921030503002c460003079214001c0818540f8a44000e03040c0402541055441030013541024140a500d507020032041c0c81400702c50303409100414000104a50008242103060340045240c14080c1a454002411010810060601c96180c80d5000c0c010b15403004001d00150a04000745154985040700000100c0c00b400c0c62448108584200428010f08a0b10b49003010450580c1c03502e000c54146c4036807981c0c1008c450b0550002403d0009950220041c1e6090180c2004402d130b0000c101030352000c0003800 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 590299019 1250 590297769 590297779
    0x51b0f0f010501050603070519090b0c34090905120301170c0607020906130e0f031c050105090412020a08030f1501020606030c010e030a0f08130f24270306110405 71
    0x1027500314801414012120803c51420010281c0c0f1070303049041aa00c1107604407030940c481d2150400c0b052000c5541c0301c1481000d00b84d48040b1711020020b00f5008402d2003103400c2c1c90f039680c00c0002449014840005810210401c4968940e16403961600181416aa02980d4415488400b1660408c00c0c00c41d40041d8008040c40030035170745c41d000c0040c207032483c0b0050050240c49007400c21a206041090454801c0c62201642d1900c45804840c01000008602100f0141c2000010441030700e070341d05419081030300103295842e4540340000507440c2c00308130400249031103000030810242109921209002c1c890b029103d078407500360030b401240d03140f42c1962020740c182c0007540003002540c00344018840c1c104002d02640d000c0e521649818602804045065801c4880000c1d204082460b01510710050031000304010807990410700b007100600c02000760011030311400c40a0003003541c0140d414000c142400294880c800100340c140c80c06264151000300e035158241100d04000c0c0c40900213960503a0f0010300 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 590300269 1250 590299019 590299027
    0xc0319020303010b190905031903081f03140111030f06120703150c030905010204031a0a0606020c04020309030702091503010606030e10180602070323030412051b0f0f0105010506030705 81
    0x28921203005c0d2460342c01d01c180104160002860346051200840694944c00d181c000d1410314100644014801080c043c8051400c000c8110101c02e48200320b426079401280400302c0030450b1400324014525100c0c00d1103004000b0040050036130410807040e105500c165104203a1301d040e000c005035110b0301400010005191040207085900a1342d2052180b00b106180229804420703844031422030340513400c2524050101030501400c20000c0c50499044100c2c41800c10540b45801e40094450800c0714840e40314980000c0800c55400c000c00680ea28150003d018059500f8030501e005c45130a80f03070442502950078400d00083c01d0740288590551096410003800c0e0700e103c2e041c0c1c2d0100802d90140700a048048029400c404120144040d03c26117110f91034460400341c4100c00300100e0007010010000c4030a08008100008201c10080e2088909a00300300344c072000d400ca409140c1e07101d07481a4442c00c0c4903001d06d40385525000100c8041c003407500e400030009079803a01d040c04107600c403c60b004408203074104 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 590301519 1250 590300269 590300287
    0x7050607030506180c120105151c02040302180402092409040f0b0c0705100504022d031b100f0c0308040809040509151614090303040b0c0319020303010b 67
    0x14201a034001030007802003802e40114070700322030f01c820262035400003418045403548141c161b1005540c05410211030b4007400d0742d20340800d8009442040d80000c42030060112142c81d08240e50181c4000d0340d0f00520495510340304104041d00e03840f088600364425172494012400510301d80001c41c8082c680ba1012002140d590800c1c0410964050400c0310a01c0c290078408c0045020695803a018148142e200c6a85a0b07013410820314040e0351440d000d00103450710082c0801070b90b079507a003001d010f0412a0050380884c00f1005554091100a20654050103080d040e010307003e42584035800303086411510b209407251301003002c59420205500c0c0c0f001062141e400a030101e4041c201c41588144a251010719004a50006c601964000d5a510300d141d405040817046910100002e0b540c0801030040c3c180e115584540001c02e1103501c4915151108000518903450b502c0520495003c2c000400c0d41c1c564940102004a9a99120101c40305c001c207013445802c0d02c041d1002c400c581c1240d034003405041c10030100c2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 590302769 1250 590301519 590301521
    0xa0e0a1115040816080706120b010c021201200306010509090a0e01060e090f010e030306060904060519030c090507020c0f03011508060709050906030a06090f17040501030c050705060703 81
    0x146601540c411240c403800306a00101030010000340410601410b1249101c0d944d10389010381c3c0d034221000c1c82c4c100317170400d00100d0b82c4100901c00d030403500c080114041c00c940300103880d08180c00c80065005151884211801041500b0800080c902c3d640054114025450010b0440c002a00c140380020010050351b207a0745024860079411016040c0001041c042e82c038003090845180e54800041c401c2101d040056a4005110a00c540c011510080c4032020307045000507100c0c0310007020b040c4100c001003a051440d03166a84207102816011b881d541300b04003116500d080480161008a54042c2207620224900f1400d0248a0180c00c0c0760300144045100704040003c0180c1641d84c464140d940c8400100742000d41280100080903183c000e04070703038102644002c0448020303400c8180119440c509110198400041c02a0701c41e0b08a400042c00005074944088152240304002d44280c1c1c1d082e641013486c40020008000301c1d14240c90401030100790607000c1e1000e004110b8054460b402c07550014200c2806 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 590304019 1250 590302769 590302793
    0x20f07050f0f04360b16080f101701020318030a0207030b060d020907030506120c0a0e090313060306080709060b071104020d09060204030b330604180506090a0e0a 71
    0x145140d2072400102c4024481c404c030f204190346102070320b1044104c40c00d100940340050382294508203280b03808002d400740a005490054807009840d202c00e400a403003005c0c07884611018244610714028881c3c1480f908501030b410580c0c02d410b02903c0d114201100c0d85000080b10003420342034010704074062441c0c81d0303800f0b01ca800a044642001d215800000169182161648aa00540c0303000415082010600c5005000f003c08082250f100800f040e2195030740c15210001c803813180d200c1d10f007141e5aa0303425a046000b8038030b030b491145100c60b0010661903007641011094505130310450f01c2c400e66526800043d178290340304010910307900300402c00109128607a0314410050140c400351410b0481e405100480d1254a0181c4950b54045414000c0061a001d03079a0404c000d5019940a01180101090204e0380d4958440c6c07400c107820b560541c42c2e01e8600c1610000d040c800101954041d0745e100701c1c03000d0003044540b548610b02c3c89000848407483c502c00c1c001016050401880340d200982d81d5000c02400c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 590305269 1250 590304019 590304041
    0xf010303200718140a1823060408120a05160509010309120921050c0d17030a02030405010b010f0f0e150c16081507210903020f07050f0f04 61
    0x2c542e804100c21006012100914280305000a010b41202c05149120710002c0d00e0803c0b0241401d95040104031a021110107039900708151054248920707809840c0310045240c4a811401020704000c2402194405080b13410f5000c4101038043c0c0c1d6808140301160003c0fa4080c8100304640000d000f198441c0b00600360070351041c100003862003060b4848070050b031845d4581d0000140501014001e050320090030031320540e41e0703110580088610799070f180d03115002410454018001948120180003510b8054424030800703414403540ca040124801c4042e610454041d16698200400c1d1b00746940704101c01300741192643d4603800301c107080350800c0350f0001051907500c0c3e01a00100c2c50007c9001410003c200440e0208010b00038000c41030840c0d020804258807107001c076000300c50048900d401200400394402c8080c0741203207a1040d0041107084d600b018007911102c403860b16980004060300064040c003036921000840b4079481d5a0010085880403840205403c15149170032940c460606421085100d2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 590306519 1250 590305269 590305273
    0x7031704030201021519060b0306010306091a011b0609060b0a120f02130e101d060c04090c03020705010e060a050c0406140c01021c061a09100c0219080a0b0f01030320 73
    0x800c0506d04081654805d03000180c49500000c1400019a01351050000070150400148400b601001d03284810078040740d4058140140c0130101a44000c403080304d0008203034800000c20400496041401c020070400c1143d90040190200104440b11400d1608045d1a0300010144042140ba8284203420f205401030000050f100c040d90310b22000305016101210040d4180000c8900203070306803892000391415800d009070000414003903a1001c0750221400d4405244000c600284d5200c03040700240318a80025100d540380400340f03002d40c0c2c1c0100d002d0f801007031150020300c03268440e104203030228880c0d44a00b50214401d01403442d010141c0c00c0191071149d10070000182400c502c0e6118885904001043c950300654030b80d014007016920f4110a940581d540c40241e00340748039140440c5030344800d4044c0310b0034880744482c1c9808650b6041e1484000800f00f09410105a65501c0c1540e51849182c03030403500030005000044403020a50070072812250195140703440c2c0606c5800402c0300388010081e1210b58 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 590307769 1250 590306519 590306551
    0x50a060e0309031f050c19050f0f040b03040606050103020c100e1612140309011b0c0f0807050307170606010f05070605150321030601030209011b05070317040302010215 74
    0x43e64040c4600310001c030415082c0715103858940c801c5422180000c028409000c01880028000814070b00313803111108075410201c0c0d803004c1ca0b544e03100c0316000f40c2010b0019580002000304061820b9006075024900c03c1006104442e00d40e401941039008212400242e41e01c00303503540d501d2030045d400014213244040d05869080090131f030109507103d156049510446081c201200030084983c0301c801003c606071001e075060115100008088d00031444281d414280c098034000188450303207031023000030300900000f40d6143c0d6480c0340a0342c480c000d62248512902032480c000540c00c85006605041c03451000c0604000d984020066403880b00c0003c280080000c24000342d030004119110b511300458104028191010000d010149800c903e003002c0c1403090704900c0005c84030a00c0d101546e410002c24200035881d030f00c20a00480f5204c2c4908138400700b012641ca401c02c14841c01061210540340508108042c2c80400c4410760092320880c80000c0c01a8080d10001d8801403550104a4000610038012254 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 590309019 1250 590307769 590307787
    0xb0a050d0204030c09020c060a0506030d0f020c130c17011a0c0307080f04230109030311010902130b040b0108090601090b15270409080415030e06090d0813050a060e03 73
    0x3d490350313582100080942c0060b101407403103820082c03541d01903820a4103120928002d804a074032020f4140c0c81400f8800c12142c458080c900920040182482c00f0b0221508200c079a098000070340807541030000880e07156901450852455041c1c28141e850070502c3c185156000c2d503038009264080e108800081c0410f22210300041c080c407000b015680070724640141c072541414040d1544110300c5140650003104540401c4159800c6104c000c11030b81c2505100002051194804d030150000c1e040003907014000b940f20742c2c2007210a500c20a00c0c0441590300700302c0740781c6050040d102d004040e1b6242001e03900c628010042c0c580244c1003c0400000680b00d03207c42017409120010f039401900704da6a66000301221a100c204101282c1040d0541c1240e0520541ca126150700405100e1401019450038500c40740c1c42107240030360406500e17468200101c1c3d0051624882c01620740d21030007072440008005801240e03085042901074400180c0101c00b81806410079070313070440101030451101207580400c0c004810 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 590310269 1250 590309019 590309033
    0x40308090d14160f0f0210030522051204030515070804030504030b0402360a0c0c0b100807080313050303070206030f130516090509010c0c1b1e03020f0103060b0a050d020403 76
    0x1316078400c0c600081e43c15045c0c8104140c0b40d4241115204051400301006400e03060808240132252119840307015600560501a08021074010b0300540200002400010820b00003407100140c04003507140c1c41d1949803c1c004480240058a000d00064030070310052000c00c40d01e081140d0028070003482c00f03c2c0b06041000d1840007040d60000d410103841000f0740c0c09909030303001d00040d074000030303041c405c2001004407180503041c0204402d01414894281d40010b014142c481d076458060101a01110060f0303589080d201c1e5258405000e1043c940142840083c031400c000090b154000c0e40104000c1c10365507100c3d030000d00d030780005218001d020052544400460010302c400d001c124201450708806504041d801c105580020700320101c981c1c94000c81901d5294408100040300c1d90020044468007088601222030380c9450704071b104294a9007000800c0d03044ca0803020000c4a20070b451405103020178034010b604a0f285445040e2158034100601034000d0311920044c02500c82450703006050503244c1c0c48000c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 590311519 1250 590310269 590310293
    0x903060411010206060f1509120a0501061a04050901060e010e04060609060e221e0507031e050f010515070f0602071112030a0305061f08040308090d1416 67
    0x903a80c5110400745002959062009650044080c1c43e141c95418202000c80d00c100907141d0302880c110b6020034544a03564a451650342082c0045080307550380180303820411b00038180b41c415041c7c94140c540c4280716030007a0350183c800b143c80c01400c1d0313001a072a118050b100c075070034030b041c0300d04010b283c1449520b41e942d148500c0c0c019140923030b52122201d080c400080c0594000a2031b1503c120401b00281d949a00350000030110782810081c045034078400c1c01680882903445462400e45541480308128110f58140c0c4184c82058001000c0300300394250343c400d8400c030b42d0250380b018001c034481c20042c806420142d600f4034103100380c00240c2c0e00c6c0103281c1c0c40b0040d80e0502500100c8440d5000642c14007404a01000ba6400082c1240e1400000d80c3e400359041d070700e1150b006040185520740b000a5000c2e940e180010b2500c86080c5990a0f4035103004100070511070701120100c02003039984002c00d40c11800060701004590158032494080316240030316510b5a040ba4000004184030405510000b4600c44241 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 590312769 1250 590311519 590311523
    0x6160e0906210109030809031305060a02032104050d0507030e12030d0905060a0c02010612110409080d09061103060d0f0c2105010c050a0e1e04020f220602150a0209030604 75
    0x504c3c000c040c82c0c0101100740c0900f50000c0d80d8000d0149210310f00c40e072020041140c030101c2d10250b132810404416030542c01100d103565181840040190341d50150846944d200b14410815540c1c4403000000c195414014080041d000404003044011642840d9000611503410502140c5c148a1220300c444280c402e81e00c4100c0b59600804140040c01400303000d124004044e6000911041c0d080c84040b49034812034010140180400040107800f0341c46603442804610b41210705260303038480275018203002d05040b080c11901c2c50b00d02100d00500c82d030401c0907203002c0d010040505c0d038030460640310b9500741d481240017980c015010030340000790790303003041d9480c0c11083c59103944400800c101d050850841d103001c600c44003440010090305c5522079105001400072901124180d2010403101100070341102411a0903422034800189040e008038004058075a4403101c40c20007102c0312090000513040e6210b80b0402000da441003ca14007803400c90464030b64800f10b000c10050030008110000380c44e0220903582 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 590314019 1250 590312769 590312771
    0xc030b0610210e01110901020f0a0f03120f0c050711010c02030705040e010e03031f06020a11120a05060108061911070f03050d0c050703030f1a150409050f01050306160e09062101 78
    0x7140019601800701c0784509e00c001019054080c00c0340c460b000d003500821001400c10002e000440ba0a900d50340c0701006010202100300b0829034000c00144c442e6010303050a85030517028a511412540c03060309045002607010707000d440e40510b0401404058440581803d00395500e034015102001d5003040514440d15180b40100f054000000454090040741d0300301c1030454203c2d10849000c0794186040001c50401503826070600200e40c81904e0604010f072030001c0c0180555000000c1c100750008042c0e01594404880002100c2125104801c40780c42c10b5405942003010710808000c50655025948940d0090070101e181ca00005581400c69901408290101d0700110f0b841c41030581c984500b40c4082a101e400b08240511004560f0300c0c4520007211078424407802a80f0b02803416040240d400400000f042402103081261600f00e07141d4007402098005c2c440c00d4000b07200780035102825402e030489034464407071034003001041c803071000d034024400c541021f95203075010130540e0160350140c142101400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 590315269 1250 590314019 590314027
    0x90d1214030c0d050108030a0e0d0c090e2b0e211002040e0a1a131d03030a0b150f03041a0109021b0d050f13050402070c030b0610210e0111 61
    0x183c004202d41e41078001c5a03050340140290010103801c00e0b00140841d604461b0310080d8602803500c580c41c800e20b45c115000041c20488640340340100015005904541c40341c0d102e070381d4884003040000c0b0ae0240703a6410005000070341d42c06c00e142440301a4072002c0c1e51841c13030800545203187c04d107032070621000e140d03190584c0d00103030420190201800305030b00000642c40030310003400000b80b400d0340c101c00100c042c1d11650881e40c2820196440f0361080600078420040c03030480c0d11000d48007680700d400480e204254203040c410079051514110303d800701c0c0c40240000b21030610000729010006608002c0003228044030810624410001c880030a5009040d06000981da90110000000c00c1721820038200c40c1c41d82c00243e040c65020f070050160303005a685040c0710703521a21126990074440c02143d01480e0020310000d403040920142403c9602982d01a244d03031140c503101c00b020f20001e0402040c50f42c0004048946200d0f4003900c9501e1001c1010944201143c8601d40352155800c41d40d00d441c0480c94150001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 590316519 1250 590315269 590315287
    0x2a0a030306050901050f0108060f1f0e0402031006121e0203041a010e070c02061204051507020c030604060e030c0d052a0604080702030708060f0703060803090d1214030c 74
    0x8014400a0320043e00d140209525100208800c00300c210b07507040c1402001000103803151100d410300408402c0041c401260b1b130710350300d1082c4058004d1150b003000068a2190f040994100790080301d0084900c040d85540383c0d86068000c46240520398001c080d42619440103414028029003040881d9044640c0180e6038101840c000c01c481c4035107010101e5207540c0200402050751804006603108420f420481034109503440081c1c000c1c803a841c1001e00009082060100f44500000c1c07024045003011940d50032622907490590340d41e1590740ea030541c182c0c0a80c0000b000035500c0d03006556407038000da044034100006142d8407800d00d10380c4040e500000b0000b042c08542c0410344c3d680806402100d2001c202c0c41c0c8500c42d001c0d034032603900404c0605040e90028265045403070402c03643c40180f0365a0f0030f40d001c17410800d003480c0c0050b00036103a003400a810110f000c82c04060110498404140c01414a83d001e8820360ba000c0c4038050810b0100c0510002c0000610017920800085100c1e28586d03100c01d5031107001d0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 590317769 1250 590316519 590316521
    0x9030f0f040906060c03020606090a15090605010807020714131d011b0f05030a0504020a030206040b0a080a0e0a0311010b06220e10030b0c190c02030c01180b2a0a0303 73
    0x16510135000c020040e2035081c04260040341890b0850400d0310701d0070f101da48030700081000e414603009080781c80025080000c0c860b00d0303980c0005c042d12000d0341c0e885c1c1e050f29106800c903a180c030a8003915a501041c0e9001ca0020b19002200100044110f88040340742c20038414101d03115034001148801c0c6035101c85c600781320b51400041c2c44c1005400c90424008201444000030f00b41d001c024281000203580b280402d0035035030340d285000002c6074020151079640b0740700c02402405410440c80c000200717903c01c02148a40f0254026040d184404a000305585602a2001c803126100e240070b842455503194084111030303c40d4030050040c0f1070100c5004440c0c0100090350114603a1651022030403e81c3e000c01d00076989079000e40501142d4000310225040e40342c3d00c0040345c00340300700152410000c00708001c1c08501500180c505180c180214180c1d0032841080e001980d511100ca81444010701002d01e0074040b103101c1c20040d18043c0b0130710020b001d150201c0040b880011114a01380c01d110380c400140756040680c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 590319019 1250 590317769 590317781
    0x31a090405062e051c170a09080106151206050901080a02120705010207060c030201180b18012a0306050a030303020c06010f080304090216061505040b01020f0601090509030f0f0409 79
    0x78140b008010b00c2e82281ca910541545000741d610503031403e01203142c8400c3c01c590180c5e43da46c209500904a2890358040d20107640540007030404a441100d000440d04010700c101c1044482030402d0651a00d22040c00301d42c1d000905e03110303200c803e54408012403da202c244039140030740903420040050310700d2401040009a4003840c001c40300d900036803060015036800315502d011181c1d2401c1001c1c22000307924040c1d024041940503560b86500c2c1c05e54840a01a02083c2c442c0100900015580c6c05c2c103401024609840080048480104070120f80e514500409112103d9500241c42d0001c0c496449000050601d851984240d000a40100340b00e40113940c02c1c00940e00400c58401150801460902c0d500d84900892181201255021503205443c1034080283d01c07071aa400b140421102d2002c1c900c02d5950391907805450b004038644003071800c0550000031040c1c4820034480080c0626881c0418170400740000a0176590280410301800c030f08000e050010342040022441480d4540307040901d54012500 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 590320269 1250 590319019 590319061
    0xc0304080714011e0509070522020a080103290f10080f06101e03020411090301020c150a020a0e191a0301030b0f01030f0311030c0a05010204090f0203010b0a031a09040506 75
    0x8034000078046d0101c0005010812540240e550160960384110760400100c0c048038112041d500000d80c1d0000340e5800308055058a11a200c0d035498607281c0400c1200d0020440d6500d91015074070801300b60420011101c0c0c1c4d42c081c17401030b081188182c88040b402d0415082034502d003a154045803d10446440080484000d840101201e1100005403940082c40b80c0d120310011340950343d0b0b140080c5141d048a0100c0702d10f06000b9000f907540726459110349680b080c920541c022007d190350301284011107030303008640c408409540e4a8090580c144100b1151406140c644c0340820607214001892650140300500ca201100322516103e40c50740c148000c0c040d1000307103d1085000d0900041c40018044140c07103041913014030300101440f40c400031207450340c072442640340706038800c071204141040015001041541c524220030712100c40203c620000b0390101780282c80e92184280940c8030307058441d91290180c40c48000c461403142c400c1c40045240b125081c1c40645058210302c0c10892046c0d005d500d10001d1341 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 590321519 1250 590320269 590320271
    0x1110715031a0d020d06150e0903030901051503030a12020d14012103140309011e0608160b09011b0b040b010905070c030504051e040518070b120c0304080714011e 71
    0x800d5900003103c00500c3c08004100c1356440f140304104050b17140c843c1c1c01500d1188214008d0f41842e0303d110703507250811540b400d900d6003014001340c205682e1068500c03600601030011400c100d11a0801e54402090701018840c0d15401d0204009500090107070407040500e088140f82c0341d5061aa200c0034107039180c0520018050058040d40010f80c0c88494480718082d910001d588a0b00c03117101c81e44c00741c4503406406103514001c003906003601c4c40a0f80f2003021565440300704c48444442050f8545406120700c1000d003a80e078103000c2144254040c84003091100c0c4145d215003a90340d49640d46110340002030303905448103000080140940101845034030b0304644181801c4a42080380e5400401610441c026a030103610381000c0101481868100e1790100140100140040e00e019210019104440a80e202e01d910500800048804e001c82c200e8001c03444041c1800b640c0c0d690030b070207061140e0002c2c004449000003009090b0100b0f105489803108841900c00100b0009040c2800d428107801c14500800e5403 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 590322769 1250 590321519 590321539
    0xc3615120606180402180a150614041a16061523061c020304060203041e050d030b060720010909020f04150201090213060302011b05030901110715031a 66
    0x5a95600c258204a040e1000450f09940c9510100340419000c4000c5800030321014244400055103810120307036102000d684850a5950300c2c000c4904480000080c2c6141c00d00300810300a60702246240014a51103c00c81d6203014001003100c096250424001d07900c3d65903a11401001800c521040b50040140303000e04a220100c2800103400e00c40c41900d11071044000060492325910084580380c10301590017011501c130b00d041d00b01200a58012141290f40441d02c81002c1106000d5101444c461900725000704042041000c064000b0b2002c0890542c1c850300610203600020b5102c00074070b00c9814010010a410201100003404c00ca1054002040490040c01325004556080c41a0b60480d6030041000340508101a002da004001c40341c40690803403000c5088000384845d94205c1360031607200781d03101301c244000c1881d03103004044a008000e20342d4104214144441d8030603015105c09100010031f4a824568545940741c0010000125030080390b09c8400d81c207219011030001c01592602034500500b2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 590324019 1250 590322769 590322781
    0x60a02180d030306080712020f03071a07051e10060b16030c020f0913170304030f0c141606030b0319030c060e0102030703020d05090c36151206 63
    0x2181000c8030a040c0520300401d6080280752190304800300405144055411542d100c0f10040c2a48450850581c020030820b1194062424005002070031102e103184102800c800300202c0140c182e0080d4805e5030345214a802d12001d0210442e00c03d80315210400007801180348442400341500e041c2e170f10003264820140302c0508062003400440c040c141c0e1500d44041490124400600803c001c0761400b50810307500c1c03080080f840c1040c109103042d1402120101e01c01250549140800d120480e801070000e40940211a01a03001d01404c0f02d045100b01e00c091454061013802c07511b85440c0138070549005200c010f042094a41511854483e00c0055003d0000d040b0500c5d60303803034044400800101040340c84140602400007550007000b0901940009543d42e0034096001006904000f6030000368900e44400728149960004903060b0b554000340007149910303c02c20070031303101601c80000d4010116841d40172694946001020900c21040d0707081036140a4083d000b809203564a41050510315444201440f81e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 590325269 1250 590324019 590324047
    0x8040503033111011205010b070f020d020d051c05040b0a081009150510030b0a06120b0319110d0c120f0f030e01030e0313031101030b090c0309060a02 66
    0xc0d202d10411406094007203070071803101842400121007000e034010b666000040004260000c240d500090ba1025045024001640c0481c0d00a20644130700300e404100b07060000340301e083c0a60086000811050014055801142d1625580d2401300c40503046178400c00311603c0d00f0b41a0911103540c038034040c0d0a00303040c40300790101841380f40700e00401e00035090001241c0104120020015011040003031108040b818941c1c041d50b846801080d1044444613540742d2101d12174400d1241440c8000d2000013950319007601500c03100044e000040707a80d501e03040c01c100180c400700a003040459052100c02500e0810b4200f5079403122261548606c03800710f1902c1c0001041090084009440c1e01c07651b5150703803e02e0b80c03500007010a1045001088a4951043c03039050541142802e020207000307072400e000140c180c02030744e0703164880d6025242c034003403d8250034004203a001040e05c210807010304000800e0f091041c0002d001501c103c0b007104802d08000200003980b40244402030b000000a20706500302522400480 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 590326519 1250 590325269 590325271
    0xc081905030d05091e01020d0b04020a120c03022221030909051003020a14100e061e09040e0a030311040609151707050703021203010e0f0417041409070804050303 71
    0x30507140c0d00ca902040702d1104c203009500510098201520714804800c1019010b504400000703010b00c0e107882c04078102e03400c0600071100c121201c1d90700c46034501c081042c0007000304884124041059030903c0f680520124080d100c031841d100210158145902d00a009808241000c1803a032044554031742d01c000213a0003c06c0c2e50291780031100d002c00c407a40c03120744200c030424075580040d500c4442c9400006105400c45c111074070011041d50450740d11520808107480c51481722003c1c9821844c1000303031100541200c0301005000b1100c2800c64581192a0009420b4070b1250940540c25007152104604250301423007036035114004600e11505003490158007a01049161068661038411018824400740c420956014010030000321412981080c01000b0221b421954003100540b1805104500c1e510382142500c3c100c0d510408004030743e07a2000b10401d26002c0c0500111641e4418281c8014280342c80c00250024200f41250400340380090020031044040107020360080c00208400e020100d04c01004507 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 590327769 1250 590326519 590326537
    0x606050f16150209190501321207020d03060b0d091407151808120f04080106030503070605060d03090506130f080d110f0c190b070c08190503 62
    0x481d280c0c404054070318041000640c004010424192441d01d5481055001d07008400c01521300512030080c1c20400c1d8070010803402501c1c0441c008d81004215407152003540020f10101c100c0e406d4501102d0b40a10349550842410011100380c1c80007003101c030315410041a088202d552a050006a02e88060300c00d0030301c110f481c1d00724043c1d2103100410502c4a040c600030045109901121007095503110b80f8072300c009007150803000003070b00940c0c1e85542003940d0651409550504d000703404d800241031043d006580c0010452030100c1028007000070746482c203203d01b600544c002e40245a036040e051600e6402c4800c02811706110340003012010f030100f54044c0380d0302c0580d13005032825550740038046d014800c4520b1030f81c4455170344489010f02140f841c80101d041c520404668580c04010700c040e2940c00c0e00e40b2400503080260381c0c0310401c680700c98504128550381103504c5d002c090f034141e515011416502d6104031420b5408c10402003081111401c1003100041c1030f500d4140d000c1c0959000c5d0707501c036100d118044e18 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 590329019 1250 590327769 590327797
    0x30412141b0601150c111215180c010507080a1206091508120910180306050703021305100f0302030405010b0d050604120e09070f11061513060605 64
    0xc0c000140440108450400102003071086240401c5100c1c180c1e610401d025090611400f0200802c5960040041c40d9807164881c0a0307034810145107082c4500c0e030b00c400c0804405445454840b80428249510807805002c82c254101e03101011490381c1445c0c040001f2141c1c0c1003220401030040410480000e40e00038404500c3d01c0f0925a0440700450f024050030b400c0a0b440e28500b01610100701600792180d012511507606840c15600c2c2d40055000500601c400305030030040d08207031810400e00c20f0b900701036404130040d00f0503201a240c0e141c81045610480c1d40388003103030303001a44c140d282c1801d01c00d8500030181202ca158a6200071407000309000c1d0602c00708400c1c10340101c0030404005081d0414030250340080c2074084900c07a18140306a5400c002d44081d600c1284c90100308565610500c83c851410f000a000074600d500d030440b0490f00148282d08174002c210800c01906604601031010a00501880c95585254004d03001008228101d182030403045034a4403008000164004e8262030043c103400c11 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 590330269 1250 590329019 590329037
    0x80307030b0409060e011e06260f031b15010b04122120030705030f0a051303111e030a0f03050c030a0914180c03091203010e090111030412 61
    0x804140908894540244143c5c1882501e00442e1015404140c140d810050660f01c80880c500003c812038409004803015000c9ca0650b007103500200c0072210410780300f46011a4000608003038142c0c2150010600032160300120b070702245100400300030840c1402d91504503d8010352419416081c03e1280307206091500704040c200c44140b104c1001c0040a5440300c240c0440c54110b4104020614903030458889003102d0804080c03e030707280e030010503500303c55409002940351911060f01d02819030440d0303102e141080300030040d400b81c8480e40c1e840800254400d0800c000f00c030b0701103810031440f150291061020540d114420300519a00020120308480e0080e140070030075a5035003401c40706440740d483c550380c45200010700080b1142d803021003102160755030103001788001c0c1103104201135180c84910303980d002140300021400300301c0c16200450708412803100321200130340c0260121029400c260700150320b03008014100301808400303000d01d150f217026481000f4a1071030030b44d56030008640c2c803801600800851302 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 590331519 1250 590330269 590330291
    0xf02030906040f1a040806010303180510021b040b09190e07120309060c020906040f0b030a0b06130b01081b1308010b0f0406060e22111201080a08030703 67
    0x44211244140c024100c1c9030703143d44444880301d400040c0d104036500d420350b201c0031826072000c5000752000d0b2131038100900020392841d1411107040d80c1021000c07403c2d41c86a00c00180300d503a01c0d1140510301000e6005003489a00c440c084142c14580000c1303c82c0501e041021402041e900c0d1100b144c3e001c1c2121034001d030351025200e4044020711165041c443c0300d104038607012907100c203941d82c041401b610130b41d50524500d44500c02190a141d2006000750045100700c00300d2490b01e032640000d200604099400a40c015403000001d20b07040c1c10311410303110052510203215490409000011604145600c14003884d204400024551a0000d058182c8219004040150302212000300da200c000b824002c0b07030030f42d6103c4004034020002c480c8800e01c58904440914814141030003480708032a06511155079514007201403004605104100c2152240030740c1c44046813808500c208012041400525030715804420300446681c04103810020f090740c440840c60b00020014000c407644410286404240da007040 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 590332769 1250 590331519 590331523
    0x60618090f0207020301020a20031207111c050d05360309030a08030105011d010807030b0d0215030f010f030f020f0319080a1d03100c05070c0905011d06100f02 70
    0x83d40000d5055000284600440d584025202c140003051900319054800030406541c0c1c038410040550051517683c8005060940109a00030313440b41c5000a4a04039903801c10b0000265072181c2050001c02d10101d80048111924808c07554003540520340b9241000b800401000b4004070038805200a42e00313011102c908001c01e05c00e489407050080d04440c001c40da86c0c5804201c030b401c240221400100c00e4400c180d13800f0000e0f84140099081a1038000c0030f5110f014080340917041784c101580e041030701c515041b0b00503115441401513100c2003540c40c1c3c0c1c5900742480c03c030207417020603402103240100e081400d00214000a54a03c0304590407198013003800d0481010a040c1410401c0340c02c9480c1240d0754807001d03c00d10800804020402c1d40d906050303050810550011000450700356901640726920f502480c5496612030101c542c40d9041a03418010a50b5071030040742000d42000c02d150381c0b56001044400c072b8611b51a038159003922040c411520304100445c181003c08138020042100154060744100e0003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 590334019 1250 590332769 590332777
    0xe060c06010306022802070608060303030403230c060f041a091207141e0706020f0a0b040507051c0201020d0e06070b0411040216021824010516060b04060618090f02 72
    0x81700201d03030703810f81d210001944550443c0300c0d4202223404200001d10a240100c1100c2c40385034542c036124078508040c20483d84520500c5428609070030108083e1600c10020090300f071061035042c4030058145801d1411009040341c80c0c807800301c5801c012051111079503007c188414881c10f00c1c500381e52034285130f04182e003100d1810071000c501401401c0380041c135001100d6a41a484075070b18200c5803072681e10081243d40b800b06420950043d0800300101002594481d1002d4125001d002110b8075103840e400045c69000030480c4003480b00400303413528001c550301402030700b800c9c03071041c100401520300702e5000c1440ca1090020091501c04d90304006010080c102c0901c07a03441ca00903008545560a550007141c2403003401c5810391084400004600f18404c1000d1501d110f4009a0285c041c4d400205448c00089c501800c29181441024000b14081c060050091901c4074047d6030089104140e036418401140c0207a04400200500c1c1500409420345a200c043c0882d5240740e00010030024141221009002e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 590335269 1250 590334019 590334067
    0x105030c10091721030a27060b0a08121902010b01052208060a0e0f0c060909070c1719021c120906050405060609071b110621070e060c0601030602 64
    0x1404100c44004c001040030707502c01c0161202c100040c15101442e5180340e000504c000141300080907010000400640020900000c0600944403250300d40205a0910112040b280d05010010401e04202c99a018a40380302d0502e0340002c01081c80400700080141c86090540600b4191001c151084407038a4000d0b0130040a207a070548126040c107a4110b400307441da00d20560064030a05505050303041c00400e680d41c151074014000b0346031002e41401d02444410041c80c05040c401c0300720003c0301080c001100700c48042500c400283e0b440c040090340c80350f15581080b850301154890320300000031240081304034805c0031103814924990107a0341d120002802c0080c000420142c00c120030f0004008000a00d00c0c0240c1044a003c078041c0e1f41c0384002c590010078501103404590844e440311001c20024a9440000310000d02424503080c2c00e8880b801d24101d039218085013030421181004a00384c1d01031030029440004450103440c1003112108181d8402040c080600210341c000343e05045000781c0340682c030b0011 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 590336519 1250 590335269 590335303
    0x30a02012d031b0503010807090e03070b0f04141606050c010b031209010201060b0703231b0a031e0c080903010204121113090b0a1d150105030c100917 66
    0x400c056001005807811080b61010032001c3ca03410403180f80500162410388815a00420085203440785400c0501500c40d0781c02c100703003c10845013010441040529101f084000200c2c112410a807804182800540e4140c80d100c0d00700c1d10403082281d042d4808042141d070030349803013a20ba0700306070240b6005000303407404554103105010450000c800c80c41d01074100e2440c00d800800840d036440319041c0c0070703205002c1d0003400035500903040c2150403071031081e550380e03e00013040b010b042101c5641500f0a4018911020100d03620001c9079404240d400960b0b1640341480340c00110f44040030384030182c62081d1504008045030004a00301c001d03514258161070051102188403603070300301c4074202b0284640c03070041c003036001c2d150a07121155940c503240511108036500c40d0600c4403d6840000b001e004011701c03c49a05490001c00c140408884100940d082da40112000c0c643c0030f5240904041c94046200d1032140a1900c1084240015401803216030849500c0700324548040c02d440f0640b810101030004043d1341c5 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 590337769 1250 590336519 590336597
    0x20c04060305060a0e030c0604140307151a0301020c0c040e0a080a090f05090610180f09020d0509010c05070b0711030301090b040c020c10030f39030902030a0201 71
    0x40000024464081c41c0d00007003c001e0174000c0f040c0342c0d0f160710881803000c0c41640410040f800040700c28140c0700802d503c2c8005d4a0900540d07035100b40355901c1d010309401c8802d07110011804604d4907209010012a4110021490491103800c290384440040034010301c04c035038510000600603401d1040b001c0055002c52040e81d0752085020181c0011034502505030000301c0c20a0208031070a0110446024000040c10108190606130040355008400e140341000d44088031000142c1030415100758010b41168540540c9811502c041c00048500c02404141c5aa05100400720040d03000760807581507580281010000c1c2d41e820070191656846030b010342c5082c2c800000005929090b90b070154001034402c0760103102c422941c0f00100d2792851191034103640411110540020a8026031107030b08004003541001c54821000e444044c1d01c01414200380c000c442c080b00c00049030098a0010422020250030300300807016540d000310b5519180480000d050010140104080c09510000b02d422020310849561003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 590339019 1250 590337769 590337773
    0xf1b03090b011406070807080d0903050c1b090c03060109080307080d0507051201230d0501050f01060801031707021305070c02150c1005041b060f17130210020c040603 73
    0x104500c0d081510071240007400400c0b0003640c5880e610a1820007800d45041c00180e4640e00034607071022000301d13941d800402040c01e000e8418082c4207842030003a20740b1901c03034007800d144a003024281c440d1148103040f540c41140496482c2004242c020728101601da4495840b8401031b81e420070542c1040f09284800704103042040f082000130441d2010b001c50a00464a4001040d0707001e005e900017034808011000c00602103041094a0002030110805409802c09115000301f8107800c00b0700c2041c0d4559444400308400c5c1107401d049a8010a21031074120800c2d071540d2607584100c0b085810240032540000360290a560320041d0090300507403200000c10141c1800f0b0000b5103001c0340e0100490042040340708051401c05110305580837440000040d0031243c0030496000c000b054020400c5440340c064032400c0c10302d02d0111400c00c0143c201038403603012030764410401074810380c00d80c91007003189140c1e90300f04088516224200107000ea81503600403421445090141c0c10082d001c91440e4205191100c0001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 590340269 1250 590339019 590339021
    0x906020d052208060114042007020f0f061605011401030c09020703021204170f010b010c0f02060c1507030e0d17040212010507030b1503060d2604061d0d020102100f1b03 74
    0x80346d0001240c0400c070b607a825126403944000c42007407039542c0e050140200c1000d070506130146c9a04c031500030241c0101d070450f60005106504030038184100000c81520103c2004000d00c078000031030051240d586010b62460741c99517840350490041708256900815180c04241c000c01a0352041c00815954603104ca8903100d1504580c8060318410000b0311940c0300100322450184298132aaa4040e540c46030140d455444481440304e00402c2244c001070100301845000c44140440b100324100d2244c01910f50525542c01400c5c1c9101084421a542040c841c2080d1075070050041c610584203d044002d103540d440c00060104402c3c2c20143c4125400c1c0420081d031140e25900c6111401c1c806c440f62410310b2070ba92952000c41c001100c0c560707013221001680b2070104d0130408040c10840c4082c41c442c0b0381e01e0301c103c0041b00c140c2c1042e804040031a4848045044412099040c4001141d0a451400d11242d03d900000d64078120065a4030409649080301d4240010940003c50002d540100e00f0b914600c8102c8014 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 590341519 1250 590340269 590340299
    0x18030f0312050606030c0a170a1d0f03030a0f021c020a20030a0c02030f190c06050711010e030304030f260301080601151b0f030906020d0522080601 65
    0x1000100304091034085400070740b15140c002c000281c01c082c01c0d070741d80310b014041360b034840403845080c44103036141c800d01400300701c018911540b030f00807000c6082d00845620420100c458241c603480c40c0c204411003410401e002040d03e5011180440210380a503050a03c04024440e05042d15440d40d44507681c0c00c00c1040503001021040481d45d540042904448652941e90b03105145c1c800c82c0d80c00420000d40c62a21500c3c1c6800c0382400201035817190010401003d01d0304460000602c1340090340c45440d01400075800700917005208a04029140c098903a5803d00138214080380503041c44200d400314501a101041594042c42d400810b0302004500c60a180010800c800c00740822100c41384184a001015030066074101d031540c4004046590912103403a000e400603c4081d410410b00300c00750010784101e15201c228060260b40c540100044a040052000c03c10390014000c0d54010780c2ca90040d26808000c0b550320000403030381c0302d07038020042d000a10440300c2603020480364440d40001260014046c2400 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 590342769 1250 590341519 590341523
    0x3122202190e0a0c3207050c1f120c110f0105060307060c080301210828031a091e01170c0109060e0906130608030d0f0e0c1018030f 58
    0x20b103440c0c0e8541d1151411345042114280c0002e040000d540282a00065004904140c00c0104489048104817081c000d0f08400c505448a60000c40307070a0550404403211352101e0481c442100020520740c4001c0d1101c01c042c0554105185d403a4102d01403c0c0c4103d64040c00c4040b11003d40b0588001000018080e10060380c00314468081c0c01800a10305002c1c540004c2410351200710756042d82c0c42d0000d0800088124480d4040e8141c46204803000a040c03000103107003a4072010030702603659030040e15030740030002c07036802d41d000341440e10318501c20702c0800040208443d102141c550149540e031070483c80b400e0100b1192640e01d8030562002082c10850074403024040c1049a088800c00d000e00d0004540e0b0b00c10324444c800c08941b5100c41030205042c00c2c0c00761035110313002a214007490745184202000300d8500340e11203c00c6400120ba40700e078031540c034091450410120711041c0050140c83c8006601c4d03440d160758251280c0c5a4500c225003043c0918440c0340e0310042c0518100640d507590030b142000509054003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 590344019 1250 590342769 590342789
    0x50f0324031006141014130308040303050712030e101a0402120601080709030b061e03070b210609070c030c0f05070e010b030f0402040e10050c09040c020312220219 72
    0x2c401e1003800c00700141600b01d50301b0380d07452150b600c11903000d0600758031135100566004128180800800c0155005100851096807025920200da090809001c81000580000c1506041302c41e50b1504001810401e00244008009440d0150408544403a00d0041c8025003007400802d800818403400c0f0003141c4900ca003070300c07408400e070f452140c1141c985050f4000200181441c0317010460b981082d84034440c2e403080ca0040580c1c01103005002920784101984102c802d9400028031038404403101e84000340307030303050705640000c07a0030407070006848580c00810560800c040382c0b00c00c409042c440e0019124540e0001c4450408141904040d0340303505450141c82d0208081d000001110203c0780212880b410400b6014070003170b11264204000b6001a0000f9169803040c0d58004031014060300c60b00d406890090038055641210001f40300079076036442c01400030f54106014058000340c01c10100e583c00b001d030f206550302c40f500a00044c0010074203a000a5042001c4c1415964140d424000c40820307242c1c00c03d0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 590345269 1250 590344019 590344049
    0x60307051f0f090308030411190806150f0d0b0114012c03030408070f03051002030c031801061703032e0320100f0f050f0324031006 58
    0x3885011050181c0000354040e0085084410501c0358140040380b142e9468002850b035030365220b001c00c940099405a8540005240c2680c06180010b28081200b5036034441407a0280340c1b03a211a01d4200043c00c1011007444070466214541d522800c88804a0000300800d080051909202003060001d001e00640b021050301c0081e9030358020940b9142c0e0701b2941301140e0fa200e441208480c2e04007034621040742c1501c0306110104d8030000a000c0d0b0720150041203d8884001d185007481340c0707131508001ea200003c43c8100140b0440c05200e608807a0300000e44410b014025584200d550b0040c02d9961010010f1052009002c0780410080700450044819112036060601130210029410450401c1d0700030355003a6440420001e49601250b4880ca4003104551002009000220300c0340703503c64001c580050742c1c0100d80404c0d80d0700600d08040d02161464031600b040001c16800c04d107440302030314680c02038403005140d210354440e03d90010303100345c405011f4440052148005c0340181216008083c07803002261 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 590346519 1250 590345269 590345279
    0x80c0402040e13061d0a11100e19120f0b090705011b0206070b010b070203150108101d011401090c02030918040c0f0303020a0b13170901030f05010e060307 68
    0xc02034800ba10200349151903161643d450041048a010034116502074841c060700540c0d00400141c603044c510400064a04002d1501d020102c0100caa034040d44074040030401c54003081d07402400350556400640d58425102c0030071030504030000c0207501845440103501412401c1004042200c41824812500c0203d2a11880300d03c07a11901c01c0e001c1c5d2400034482441c114031074030320f104140690600103410680b402442c3e031614092035809803c0004540700005060702181001c0050a00414128244040d154101418140c950350344d848500351580e2210346100103001031f602b004861400b480001c01001c43d1140c43c3e160540403d20130309941f40d18ac45425800303640080100d03464000d000300b402942c08907200c2c1d25140d0900143c070503951380d0b007090310100d0074482100440c00614002d030000c118021040c5401504040010b00a1070001d0085104030001000020b5000d4480c91110340700352503049000048004115500d0f20012160a1070b0000480710206021180240001d405880d0450340310 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 590347769 1250 590346519 590346521
    0x71e09110714032802100c09170105150d120c1406070905130603170c0f0a1407050d05190510020d0e06060612010311130c020d020d081303110304051207080c04 70
    0x44c1943c1005a004032001051458040d0320030000d40c0c4050600d5101103071240140c0c2409241d4030515040d0fa0366803018840c0705014030000050351781084403030724841e079a41d640d00703e60301500190540502c4801041002000b21130312202594141c00e008444551408101c01003e005452150a000390f05000000a400750356000f10410b40750088114010340706042c071402d005501a01c45030720240110701c548a80000244510300041e03000c0d1040c2d0201d85a10710002e4140070613540418840d01c9611f180c400081d0010848482030781c001d581881d83c81006003401824840860f003a4001d44c0d20018030121280c0559100761010206074080313814a03951003050103003074880c00f24840a502d149000420000d20101c810307003034004c4060100352100568055202c00e035668a11401d01503000f442d44010560390402c00c2d02c80c0600c480c0703040c8a09040169070203010102c24800501007148110610200b218104200c400902c0c000e42640075042003103c400ea119180360045140502486030180c60f03d15103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 590349019 1250 590347769 590347837
    0x403080702010e0c37091107030f1805030610030303051e0c0a120510091401030809040b0111030a02030a112b0c0605100503071e0911071403 62
    0x10070018a0f00d0313000f4004104a4100c62840b003a80c00381c00300c03041c028101d801d0181000305040110700100b038500b0320305c0340010780e40513154102c1c4000303041c8070540219511641e00d591514081c00c140c3e2105441e130006a660803aa50489501840382c00e05200c0008000c40d0500100da011b540c0c20002a1908003000d4000207005090080c0c540507640801d00d00700d011b0740103100482460524610840b8154929001d50b0401c59029030000301c1c1c2c04080080490034081c41c998140c01c60b031185000c1d81196190401d6016042e1214091940d44071034242990149185250145200301202d484401345103000b9520b1340b00c401c0003000980b44443da201c0c1100b0024217210300c10b1405103030103580e0540c011584000091251407104000720a03541d800031a0140c0315180c0544207650040b1055400c20061620b000410752241c200781d0b40361010700c0256820f103500c0d00180c0b1941c1001044c0c01c01d01940d280028014400301411899142002d0543c2c0c0e04000010183c00d04003807030103103070156060140621880 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 590350269 1250 590349019 590349041
    0xa08180a0f060e0d12020318060c0d03020d02070609060c0207051f21020705010c0f090308190201290306130b0403080601180b0405090109090203030a080405010f050a05040308070201 80
    0x5070420074020030740100d809203d600f5000c0d261118030400d80d100c00e50098085440100560000523240c9052200c1030a01c0d07409103010f071442071030008401980f0f655402c094005408142e400700e15040300c150240c0441d4402504a941407040c8801420710038000c22580d21200c025100381c0c3c50029072030401c0085684240d001c0c101881c00d000d0240d509482600c6401602030080d40200321003248828544040c1080d00e0141c00002803404450f0f00c0130b40b1000b82100d1140034400d42042c104002900f4a0407070799002c504040c1c1420034094008241c2c090181c4004504c4c070201407240e00011426040c04281002c10205c040715402d444e00801140415040740c0098104000700340007402080c02038103010380000042c54814044a0030344c038041c4194041d178009142c0c40b90300140410440c079041c2c0f1042d0240503c807100f00685541940081e0b46c07846044541c405010880c000202400b5080d400b000c1d001e0403002d002d01252404820030801072400300c404038045001340011528140c814030881d801d6103 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 590351519 1250 590350269 590350289
    0x5031c15090b010516120f090f0b090a05030a2004050601200f1606031b0f08040804050402030c04090c0c050c2107080106050102071d06040c050c0a08180a 68
    0x140c1000400d50250944019050600c0704c200a01c6605070800d2020380304280c000c204603010f82c0c5d40c088000701000d00b40b85155081048081c414415002404005011500c0b140c1c1e13003ea0303d0000002284010800d64842a40341c0184d00c020011310481541c103404200c058695003039202600b034100000c544003038a80d2400585840712000d110600300100308060b02c42c010440d0340308030312007003521728209519406840181504104008490f010b000301c01100b00b01d040ea10400300705100c00200719041422200042100b844003180a01c20b07501c040b03901074000940150760364501801d14194a078068132403031100a01c3c0411100c180b038480d16003a0409540400542508807a10042000d001400680c140c07210324480342c41c0300c0c108001c10801e0000d04482002041141c581400a0300706a015803003841b14403000c0b00002c154000040001f64040d0b400c0750005401c1519800c11035541c00703030710f400030403a01c5181840014040640054241e444d9040408000130700440240b2018201a1142c0d414134 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 590352769 1250 590351519 590351561
    0x150203031003080d0e0609101a061e0c0304030305070c1d06090a06090510080c0105040b030f1005031603060f09021309021807080f0a0614040b12010905031c 69
    0xc0040000b48034024041c4c2d000304a0010040d112070409000303a82400240e0300c10080d5803444083c0d8050802183c6003042e0213807504c0300f100041909445103044c40a8130f40b84244207810104086000c0d1400f00381084102c0c0d07140c0d900c034a4043d2280c1c7c030941050f2070320884404000344008240c0b4007030564800c011440210b64541c0401e0000c400d2020b01201c0c1d80903114100411001224442d240c4205165164203170a00e03c3d20b400a400c000c9d407001e40700d0400c54104018072200340c060f0304a03074005508901d00800c55542e0203881116203160380110383c0c140200c0101c0300d1851810301c1164207403401200108281100701e0204802c440b20014001d401140000b582450038143c0d52120000314005010850f40940514640801100131202e00700400e03c40c000b40319007005a1880d00c1e520414035001007141c1d0341848003c8518034120042d01e4400d503202c0103150255112004410000c070003000003407044444a10344240c407034002c1d49200c404035418400d200c07a00c160502403200206d030028442a21 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 590354019 1250 590352769 590352773
    0x150c030c090409212105010e15180901140c090a03030507060612050303160201021206240a0504052b02060a0e090f010e0711070b070512040906150203031003 69
    0x10341401c0005895000e0107a00000e02c05014013040800314200d42e861001251100f030044080c2801020b007210b025141a00601c2200c00d02200d0940112541d0149142500e85600158903402408017480d81c00c061401400040d030415001400c03601d030354140c00c03d4180c2c1e075a5191441b5008030100180e201c4a6901c0403c04a070007240100a9075000b40008108103845000328642a415040c084805600000400c4002d030619080340d505000c1902c000e51905100c0e40396421b0316000500f605101c0c02440b03d4007070010802c11040c0c20b5800d03d00503555121604644040c0c925006489201e009038050040d201210402d900b03980418400c6620801092405800f80145030700081c098000780412058814125901e078255227204044460020a1075070600c0314002109030080c002009020403189688090800498514166140000400d46031440e40c10034900c2d16446042840d10204001000716200c1316603044007058444080001070541031920f01260f59110031113002c9c2018100a1080c00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 590355269 1250 590354019 590354021
    0x9181410020d090b0a140a0e0f010c0c0506010f03080403200d06020c01060e0603060114121b010314040203151504052a0a020709020711091f0519030609020414040302150c030c0904 79
    0x410036050130442e80409d0042ca505801c407602c0c0564103021801d44841001000760410607203000d0010303c00785c01c80d22880c568a040b01402540070080c5248030020360624035500001d80c050801d2001800a8404501760415070029845885148110350030428041804c0f4034514019000741006401400541c0c0b80c43c41002e4070781c050205a69104260a150b180b560364100206503900103030200113130200303100c000058100d4075801d050343c080e6651101040003682d03003c5948041e844038090800e08968450b8034000003442c0600c50654080d183c0701c14010806001b1560f00070300917200c80004c40e0804d80760280318030350203200da4050041c2c1c4204c0d001d0041d00159005041032621171035403400343e803079044005071020300201c4000c0d207c1c21008015509200034200020010134069554180010700d20045805010b01c07804050105c0d91202d07a11801c6460b541e0101c0e00310015103c4581c085e060030300e40251558a18220148410303107841c0403481038219403044a0003251480800c0e4644985502400 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 590356519 1250 590355269 590355281
    0x1a030d170609070314010303091e05011707020c1c260d1505150c07060914040908040819140714090a0609061e09181410020d090b0a140a 60
    0xd004c158130780d50810034600000b8607143c0079600c030340c0b0355074005814854505181d10b15a940408a00101c0c081000390380d82200c8103001050307607028284c80c5035680c0e190030780c500b5a20203104c58103c605020740740c148032035280c030400b0418881c2c03035a0549020104459154120602003802c2214020080254500c040e0780c8030349095202c401150300c81e15650710000f062410400c0b01d20000c12030000d0040800d000c140503200c007400c16030030312440c400d051903a0415980c0446070202d0040f42c2e668006d006204c0c004003a0f8004020034000c40300100441c0d2a01c410b0b03d010f0b03c1c8225511070903c50400c0002c04040f4550003a01d070a81030313000c4d0543c200b40800c4080c21004d0400c02c226641d60707001060744566030041401a208801c6103940e92000c180800040c00c0c0f03a03a000e40207080c0380c8081641e99943c501501e41c2c8541e008032030241005c919111003400c0014419504003d1880028a0090303101660000c01c3c02600566003c1c8003655030180810071b9480b0080c801c800503548030001851010380768000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 590357769 1250 590356519 590356531
    0x1b0d0618060605090907030c060f020106181b0912020108070c1b21110909070e040b2203090e0a020417150919060216061a030d170609 59
    0x12400c00e00c0100300c00d2a1452420080d980340d600c441003840315051000e00260003441100050541d10b2450b00c1d08101100720b4041c01e000c1000c05519403442910035000100540700d07880035250158810b540c0302d00100401149000b02344007510b20712007154040c039004400c40325101d41c3c54503021020784c01150403600050490050040141e00c000118044805148000c081000303040c52060070050410714400310154010b01145981ca40f020000e80701d140b40700b040000580e2907094a48a00d100c0380e041030240d81201803921907460412050100e1a030403180641d86603044024039000b180780d13099940c004440c010300440d01008041114080c1101c54580c48000c8013401410903854100d40400100c904110004580c8007001110004c2c810b0380c4d0300e5401204040c0200022101480700070103090003000040d102c940e012030414a1540500760104903103a100000300302c01c10b8007024403090140f071855114040d100780c1800480150140003081420b0403c401c511405030344030802c101e0550001450 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 590359019 1250 590357769 590357771
    0x41215020d0f0906050c090315040c03080c0303010e0106031116080405130905063601090c0909030201060602122a03070b0f070906050f1323010e031b0d06 68
    0x40405201035500c503840c48016401000b046001c4503007450b04c10703248054040360000000b0001403410703580028402e480590900c0001466a0301c0d070410100048655002a1a2100000700f150300c4142c040011070507176060350070482280e601c40a049007107035a100e1981070b140b1020090724046008144400000d544100c0c3c00750f24103603e40d8007140c8000d555040c5003040d00e0300e50321150100b100030700c44d09a1040302d203c103210301c0114030700c03070100a0519584000c01840ca482d64205041b082174112a088580141d00160402c2d51443e0920041820f194180c006503e440c1d80480c40310310219101202c41a454845410721092000c042c00380d226842c480ea0500402040069851313a080c000351000e1406401819420b2030310301903501210900611800811081c0b040a1021540000550b10203045944d40e083d00d03000301c0c0c201c07144131480540042600c0301c1d034842d6452100240060710b2100c0c180030b80c0c0d081c0c81c03d0920030038503175601c04c05628544c0842d402d03a403194950428548003090b0a0040030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 590360269 1250 590359019 590359027
    0x50c0a060f020414040212010501121b0918060b03010506160c0e22020108010e040305091203040614130b130e0c04090e0a050607050c0a0b0a14010b04121502 69
    0x155100c1111030840903184803903000702e01008244005100381982e213034140c03070551600b803200c00c0079400c012050142605001d4008059192500c05601c56070000c10780442c1c031010505251130181c01101c06110344600004aa03c050400c0c0c0c85a003d8001114442424642540d003400c080211540002003c0c0406d1b054091503400818492040480207105801c000b08584c1401600103800450390030407400460f203900d02540c0180d80c400c400703604460040d14540c002e51254038084640d842800380b601c2d8003070000301650480d044040018412200c41c0e480304034496010300d1300e014003409860100c91144034059001c0103030070000d0008060701d0060425544845480d8070034069044419100103402d00ba000c2000c1c042240c0601c10002c1030030710b100c002d1015003810b503559a51100001c0c100c00c10044040350b240c401c1c0f0410444000a6a4031000340300c628600b1031850f50041c00c2c080707564144c0d2071040c0000030f100205c240480d8140d60404203004001006520307203507011150140d107203500c00d074208 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 590361519 1250 590360269 590360273
    0x609011e050f1c061e030b06011205150f040c0e060c1e030a0306050109080a0f110307090515090402010c0602030907051c0212190b06030a0605251806050c0a 69
    0x40c00a0880f0010a42c04502d88210f0001252101e40180101c81004244400d00210324442e241c00c44c0c2d40718160b04c0d015605c40004881d019801c04030030b00c1060a020501003d400d850110001d610300c2903400d4016605031004000c10385000b20340c200c001c00c2c0305883c41c0c5414105800208820840366041303400300320000c2d844c0d440031070500341c0d2498550804200c8230b1070030780e060040d0300c0107140910309496641e051040841c1c0b506002d4000404228030300f40c500c400c100c1c00540c52003e112004040e103180903a224032000140c213040b684c2c0e48840b2425210388281e843c00104503402290182d4480c0210401590380000075800940348456900c03840c08009101d5803403003004104058403000354511000188148a09811802a4031100d60401d03030310300044054440801440e01c2e081074002009840d030388042410440c0500740a00814140020010440e100c0c136404500c8014200c80d49041d00c01c400401c48591031002005103c0b190240000c004481c8107001501c0740a8828099481c492059 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 590362769 1250 590361519 590361547
    0x3090d1d010507080c060f010f1d07050c07050411040e2401140405100c0302010c1d0402160b010617090102040b0327061623040303030e160b070209060609011e05 71
    0xc0f16000ea01140c0e03080140f00e0f90000700606001490032018003106d9240203001889600c0004044bc010414041400300d48030008102c804000c0c60064000c100e21100d0000481c1135078407038007420000340d00030000f00341480e01e5010600d140f1240e0403214140c0e07141190045460340b02d06c080700c03c40c50106000205003a0707100b0950392250f1140c0d80301e0702c1030300705185030207820b40d0203010185041c04441c150240c2034005001105000301000c032401a85c4018600c00d104200d069100c001d031a00164400200ba1150004c01c0c4102210510b152401e41e0340d01c81a60500343d01c114080c0480e145814004900c098102e2440d0ba18502c0d030b1b075075403207624541c10a01185441400c0b00c40388803603103c0c0c1e000c000c00c00b50800b00c09840780301c03280854100380000c010291068803440c88018201560317400c0041c0c111109210b40222190340d09105e904090343c81d94180b03205d0300003a01c113a1080100801250742c07880e220341112205103040e11070500c207483d54400c142c002d0a8515100c4107004040264485c24110 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 590364019 1250 590362769 590362771
    0xd06020c03090f0108060306010e060a0e0f1b0703020a020405190e0d11070321020c09040f020103140103021e0a0510050304110303070308182103090d1d010507080c06 73
    0xc00950b00c81c4080340811806a000803185414030000c0018000541c801083d5035040d00c40c84d11240c005911074401058809851798003990254180c1010b1080e00c12071441d9a50055180841da4840d107080106141810700c124000240540d001340c03043c0e070050420350001544941040c41502800103640040d01c04d0350304c0760002107581c0e04180100340307010b9044020080f8030480c107401880064150703520300ca40000c504d10380d0030800c44070414a410030b03407003040003540c005d03000b4000c0752560400cbe103895010307800c05150032800b0900f051a409100b070700c0c1e1011203040b250000d0040c80414554241c210500b0481c0b92129000350158038049500e0b11002405207294100f5520a980c901d090b0030a070050807045083c0324801d400420030302011951000000350004002200541d0341003100c0c040780d183c00c41e0032803d40207200c0f84940350010f000014002d107201d50f400310159402c25071211400c031002149020400106649019241203d5208034041c0029520035654907244c08883d0a07641d1030204 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 590365269 1250 590364019 590364037
    0x20310121703070c0201030f061202131b020a0605010816030201050a02010e0102040f050a05030a122a150e01110d020901050403170723060a2304060c0e010207120605060d0602 77
    0x704c0f074504002156414840d400010100300c0080010f07500307000050500384910706010b880b03400410600e01c00ca141c81d0740070780c07000c0042c0c0d02c2c0e86524030b0380d4010107501e4086103541612624941400002d11000100f44085886101c5451070b488505642c01950190450001780301150350f10113a107a8409000d20040003d01f250960214866203400e0400c16a45002e401180c000d070007054030840050310700000c6541c40107032400c0c6902c09204044138000c00d0a6040d181c03e02582c4170f54078080c00c2c00703030600c0520070140f4100070500160f0284a112800d807440f0101205207010100305124180c07800758082e1030420b005150183c5465504d4580028641c8401040c1800d1729000a02004100c100c1c610400c03000c0901c0c2500b10b0034070808a07455141c0300d0040c000114103481d420300300040300201000b00e42958002c000c400345c905003410b14030010000300820030b001c50064807081c04d540d800007842404072242420010202507442c0d44134405030102502264114400421100000340c650000c0e08902ca = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 590366519 1250 590365269 590365277
    0x14030702210306100212030615070f060b0f0103200a02010624020f0a0c30051b06070506042006210c160b07140d0e0d0302031012170307 60
    0xb082003400c100d252800c0131201001d541c03007103a403443d0303444a4038256503220300105e40100d04459001e03107444891154500042c0310038010240427042000d80d91002003030807801e482c4540c544003490015400c484582c0d141102420381e0880c0c50200d208401c0c0240402c0c04a0f10021550642c0c0c0c11305500502c01103a91064a40508020b01f080b4990420500c0703603448200d8000c181301100750302c4400e038160150040001c80c845200221690003552005a0000701d00040c4d0030719820014203255403070b145400c00c2c84104010001d00350f041031400700c0690790380030707088009031402d40c075580d5a10280d044884031002c00021038607000d11190f50ba400181c42086403542c4030700b05219104002020b0600c2c000d00d100c940704010700401c150b40f517102c00b03401d401592101450045840d0282e080d150b0f00240c9140c1d031500080000c0b40a54540315400c404495850401207c507044800f10b0700354140c1c081212028005151808100b1a4080280728041040c0c09600c1042c400e003d895007208880d030046680c9030100e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 590367769 1250 590366519 590366521
    0x1f1b090312030c050f090102010213270606021002030a060b030705030f1b0d09050705130b1302030c03060d11040606031a010c05071203120e0705100f140307022103 72
    0x20100d1401c8140108207107240800c07a202c00800003811034011580443e00002011800c0840380c8d0003581102d0940e072216000c0b2640715034540040554034501082da119480c03100441110001440c0602402c0e111140c025000c151803003128040290130041c02e8002c03042e01c400300007400301d80681c001d601543c40e542d00c440d079901c1d00c0842402280c0014080c1c00c0021001910446403056131005c1c1d07010a80f400f280454003211906107585031071071035000103900005076660200d200701030f5400074808038000d0380c14a0000b002c43c0f1007a800c82c08102e80b80c0004240810004066241600a4049151103026500c0502e82c07078402203011100030750064004a6030303500e40c4031010003d550011000c0d460928240b14591900d0f50381a03103a24083c071801108010603e2200304045c010248402c1303001105001700640d14010101a64909482c416140503619035060a5501407045403801d012540303940f80d01c03008200c21030000c582680010005030440c010802d55000001c41121000843c03003001e500d0a4403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 590369019 1250 590367769 590367773
    0x11b0c03020f16030212030903011505030c010e0d02090702030c030a170c031003080901051c06090501050a0f15050706020a08100506040e0a0b0d02030a05030301091802031f1b0903 79
    0x30349a40011079804950040d512262510520440030b402e43c1e078180ca070521000d408000e411f1650141c0321816500d1750800a203142030104050781c40d421201d04a0031200007918503401500d400c144c82600e1a00203001241c40030160400c0314046800c03000c50320440c1c6c80c100280200030708540000860000043c4c1e40518046420b0600c29040d03000f0740c0c148400d5103503080885030004a074501d40f000900c01d200204004c01168000c20070b4a40c1c2c01000400303219104a480c0d1524024071070744c0150507103280f41000129450800d0300f400382c1641c0c3e0003411180607604180d2002c4080341c04100184c10000104150000980c00f8000b50410151a40703400c10103050549003c8041c05040d0401070003078a082c002007000c0521361803a6900150f58100c0003034140c81150200e511844a044003940510a49418004000700000154101c8a041004005041010143c2d140403141a00c0180d072561104000e403c2ca60a1101ea24040d00c4c028200000c80a620000249032000e40c0c0d058480442c1da404002c1007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 590370269 1250 590369019 590369023
    0xa02090f01030528201201080f030703030902041514040c0513060e0d020301020f0a0f02070e0a05180d03061d0615341203050c1b011b0c0302 62
    0x840d2800342418007051510b00c28507141c0040308411020142c03060900100200c025600080e849098031405404807143c4a10790003c60f403000d6002010038a2400002440c02404601e80f48080340042c043e5240a5464808030701424000078286e9120799181c0f0310106450307088170b035400140349155500d0520402401004221102ca403039040c1802f60401031010f12a280e402c0d90384c01e4880a0401404034040c88002c00e2040c94a1407000f9010b40c03002503500e102503035070300183c1046262692041c1c6800348074101242c03200c4440c4540c000000e4000082140c0c0d5625800060784040c000b0180700404e00002c940c90328260099881c40007080d51107005200c062a90003820007428900b14a1101501300400031510980b0f000c1da00f9040810045650010800c080c50705540040340b11640e04d20000f50000e1600708016489030031503901322095650708213603000e170041510446050b6100340c200001c008403808542c0e80100c0d03c40d81075590b940d200d110681405000d901640e480c2c0e5440c0c40c25681c034900a4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 590371519 1250 590370269 590370289
    0x409060b01180f0909080f1201030b090703051c022a011b02030705040c051201090b0a0501031506080601030b120606010813051c09031a04051606091e0e0a0209 70
    0x4200c40700e00050603c1550840c0d40c08004481320024000382c1d07180a42400d020034018840c040884003000180403040052184103e8143c9001c0c8442c2006511001401d556074140ca1100401d1074001e210411080e410050301000345e03001ea40140c0c0c0080c840b00c660b030000807035091414100c1c0251040d042d841d55911954008164034401d2f01d6001e8824a44c001a9a4020500c5050f115039180c1324100d909903c941c007540c450200450000419584411101c405042500d100d61301401480c003001134107600c20b0150750b40001c113070301c3c148002501380001141c40d070030000c145505140d100d200c200d145072944000301d000c18a01d480584510f05001000501300380d4064000c03885180c0841c213420200f070020682c0c21030740a0058542200784407030581680c0b42d602d00e9001070f12400240c003032194150f801307115482c4030328400e400b9154020035008240000710302ca1f00454000441c2d00b501480001c205590942011440c40403c01c0e07103903a90110000e89041c09c488001f141500490346130160f0a00305025 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 590372769 1250 590371519 590371547
    0x6030b0a0608031b03120a0b0f01030212060103090201021204031506061110020706060f0e090d0f0f0507061d070f050d020904081e0a021f0606020312070203090409060b01 75
    0x24020280b52241966690140010514030000c0c283c280a800e2030040044175a5261a032094000c50700d003038018100181000c088080c011000c51041e19441d61091085510190341e0055080d401c0d240d02d40114000c0c42440000ca040d80700b441003200f10341c2e102d080544001d5108585965000d1a0f0704480000d480d1594400c1052090084a41c000e40501041c4042d00d90031680005850701e02900b41400540042d510484090514070340109504445a465500c6070780350204440c3d2482c40d001c41202d9205030324030b402000444002e88102028803800c014408a4082d90740070940411001c1c0e014585001803070081d00341e5000340c800b0020010709488440080100f1184003440001d1500454900781c40280010071814001540781c02400f45c46a000f224000c1c20800c072911502c6561020703540300300003c03404842c00000c0c0710000f0b07442c80900455055a843d5405142005070252480040c4900504a4030550000340302410050b1214815400240c1c019800451041c2c4120005080c4e142000740d1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 590374019 1250 590372769 590372771
    0x20c030606010522030c0909020102160e0123061201030b0108030f0f0a020114010e0709080f030702040b0a09150e0106020105070804021e040515031e1906060503030d06030b0a 77
    0x1c1100c140c1c2c0100c155021000320110004800007031103e0700c024a10140c00083c281c4001d080085100001b070b0b80b1411085200380c00b00d640a00c81800e40d0707c02e5103040d02c14041300c4031030800180040715040c6912080f001d142034146500e062840000b40b05a0003e81c003401002d10b0310001041400b2280708064010036080b0302644c50040d00854045040c41041c5034078a144400284140c946031003544502c151450740062244503503100c0b481100440002e6072540009800c0c96000304007420b000c1504a803000d4428015031a0000b42e90a010182480140c0749610008445000401d0309844c007900611440c03003a180c40140d270410a001d101e650040e00a58116890b010420013401d40240c241504241c040752080790340301220f40c2c060049009150007942141c102400e220001c02405081002210701b1015121148100b004002c18201000120301a07584004c0c1d16980035010060b081400758050040455007580702d00201e0715540c8a803101c21420390f41e8820800520501c008090b030008a0048 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 590375269 1250 590374019 590374021
    0xa021504030906031104050907021b1509040f0b060a0c05062d1009060b030618040c0b071b03050609060a060b0f0309010212090d0201060905010303140c010e01051303020c0306 77
    0x400030032182c254050b110030700d0b03a0360b102c01d030680442000b13072001080003e003400c003603180c01750b0003c1d10b407140001c011740a45826210781c1090700c4c02e031040e065405c180c074031180d00b0030340000c0c10000546094403004044941d03c04190035291107100083c01c0460300398540c0e061250083c500a482c00b5001451500032045240418040c0d544801d00c0340428074984450003415200c0800d000c0290403250b00c00380015141040008a220442014510504080351041c130326428150440415180c03c4400034905e0038240c105014404001010707105107401040b11400461020489021030b040360b400580c0c807680003500b00706ea04402004800da01c0608000240040303403501402c00102c2c05400000d001e19080130002a16100e801d605032680300d401d00003030955a0400301c24542e125140e80c07031854015400e01c040492540c1d140d001d03841c1282e40c555108103203801c01f90481800c80d00403600d400019501c80b00e0406214400b4010140914200f144c00d950f9428185806482c0684075103d06000b40c0000c4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 590376519 1250 590375269 590375273
    0x1d031b0d090b030103030e120607090f051002150a0207080d0f0e010b0f010c060f05040308092a060f19081806040b0c031803070317010e24060d0f020a021504 69
    0x403c1c0e80c11a07905080c1061001c0751000014414070142022102d103101700400c1044050340542c020b41114800511079616546640600c46000d5003003000c8009684010035141c1c43d81314209045501103e21980181002842d54400d82d16034401ca120f80700c0c1b69240c00845810494901c14403040b4440e99008101d010810404180e03054504104903040c002d0503001c400c1408216040b00a01080d1f040080100340b0f01843c010780003400030342d107140700b5200300348280c0ca0384041c505004810544224101d6090822401004180c1e40000744d0b40700e10080c144565141070004d5890b000c03061000351502c409a1031b14040c41a00140d503580020041d40c0181c1c00c0c0004980c0f008500c640142c0014513113650f1b81c1d5603d84240912000b644003520f244000500354052507030107810b04108200340f448110490742d8035518020444001d451a0844000c0360203c90f05000342e50081419022015001e5410408002010000c0b07902901c20808131940004803080e6840d81030150707207860407550092044a08080e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 590377769 1250 590376519 590376539
    0x111010212070e1201110307030c020a0f08031e0702010911010309111201060509070c110a050609101803110f0303040b040b071a07110105010602030a121d031b0d09 72
    0x18040d42c041c441d00c1c00502c0344540710906010440c201a074020b000300030f01110150f0713941c0d100b1220300c0e001038074124020021601c003141c01ca1b40301d034000464041120441e00c0b8a140c0e5030020308005500d41d00c80c510079070070f180d0b2a19100c2c0b0034425900001201900360400e90358000d0103003c1e02d41014a000c0c405000203480c40c0d1078480084042d5080d03020030342c100c0542801041d46400c000d07030080c84001082056540941c40c130308418800d03645442049102c60a002410f0342ca4059180d010505015940190401ca1041a8684514075120202c81c2c07800c46945c1c031984152300300344e600c10b411000c00e4070103040140102c1d04904090b401145414585004110300307016034042d01402200004140090280a17220084000401c9205080358141058058600b00e150091001a5400d04000291040c00842922003a216a490304001080508071010040c08407540c202104c4130461040441e40314100090305444104200c81018481d1800c045407500729034143c01c0c0700b004120b280c01d10181100d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 590379019 1250 590377769 590377771
    0x11012c09090607121d01090c0311041b08060a03020a1403060c12130f06111b1209040f091403070b0f04020a1a090432060d030c08070b10050111010212 66
    0x4c2c00140daa00d8014200f03440c007030710000780e581540c00c0c131b05444113020000d03102c9811640b0507100280700300328080c1480f0a0f941810241c0d14043c1140303a05801d503034019004280e10a4000788054113250302d13640001d52120141e00824103900110105030110304007000f0103900032000004890030061107224a0800c120000c07c035401c080c84000c207140810200001c01c4000940c030034001e002651110310000690f4100a8010410103880c07201540e4060010801481d4002d26042c40c516290461050001418100901e03604440d520003525020402e00d080b100030500c50701c1c02450751120b0604008400890292110320581e04980c00e000040ea128070380c0138200c0391000c8110301d100c2e1785c840c584540d9014806420b03400034100160351070074010400c10300c607180a0220185200301e0f507007541c00c1464035007100c0c03a9421040030320704130300032a0203a030a4005141c400c1e8030075803408046a5504811a400341c9800c4084031501070705010340d40c0c0004400465031481c42c021810458206644001c0a40c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 590380269 1250 590379019 590379047
    0x20d0e030a0f240c02010515061602041a030a061a1008040609061d0705090702011814010204081b0103060501050307210e0102070c0302092211012c09090607 69
    0x1080c182c00002c0807074414100c200b01400f054104050700c04030704040d010344001c80341244030700101c0c0b07400c540610b04507060b40c80c682c0746070308180010741c456420b11000b0034022080c5628072580300032403803080c1d40c01c0048404051140001007042c8480512210504030b100e902c0c5132083d20030000e00c605150b800390320903601940081b0082844107140c00c14000038400740c0502c203889850344141c4112020001a082c0485109031020861941c565008908031007407045105e4041e0b0280c40084007041e01442058074820b005000140307025950030b4031601c1c00450310540450b005d00400059031968051080000a2800b070900380d10354681460000c000c0e64805010014034400f184074032034404056444610040074090085555504605000341e001d1441c0c40304a125203003400000380a110300c241c0ba0005174030700700803000c0b000205550390081d401c4015000c40c1003200304010201c401e0001541d90321f04100c2c10130700c2100420080d0602c820100d0082c60300103964488024401440d50203d1010000c1c4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 590381519 1250 590380269 590380283
    0x4061d0c0706020723070f2105010f141006080c03130f02090106090816031e110603040c15080610180506040305011409010b0d1112010c020d0e030a0f 66
    0x7080c07440c10a00a00a542d405441c0c01401040b050300c078100008104190b4076000c4c00c45452680e28103410f100c009aa02928070804003182440d800c0030040c0d035140302600d1040d0008140101a1170b0002c0c01c03500803101c0701081040c00420302210030118400280a0405490649614a84480410384c40e03c80540258040e489109844c01840450401e08904c984e00402400045d69611001407058105004508090040c2802036894180c140d90100071a54032061642c034210480f5038110000207070078801e460407100c0711910105a0b84400c01144601d1141114100450515021032401c0d0312a40100b81482191422b0000701c0c1d594005068141c802441c00d4942107444400c0c0a1402c002d59000c5a0013150200303010003001b83c1904005556a100d1000000300c0d41c5078081503003a030701c0080c0d000390031159555208012407500d201400144102611104040c0300b0201001c2c00c6404156802c001604980c049089541d0710400c44682c490007113006003503c260549821032104281c0a0041c148 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 590382769 1250 590381519 590381527
    0x60c0702061b03032d040b100b070609110315161209050319090f0e0c040506130305060c0906180d0b1f0603091509030216090b04061d0c 60
    0x640d1000215800040007020105602104014940e500c4c1c00a6601e86075544151241d15088403242d134107001008440f01c2c0034801c0c1e44403500c440080c0407010309800400303010703c20302051a0a42c1001012814801c4400060b0f10215041c000301c1c2c110204189071003500809023000d120340389645120f07084060b0491004c880248606d00350340920400200218003814514200144000800900843c0c20710001c140b0410712055000c450f89215402025070090407501d040c030180300078207841544000058459840c158485c1d0008150340c008601100e400d070781e60a81070003040010302040760400c0740b80000a003001c0d08030000480c140030340c0310344014081c001c0c01c42d1030042c1c2d42d805000588070303000040d244036030600502c8001d40403031000c81401c1400040e0310000e6603500c41d200d001c4580303403c00d08805410f0740d0508460040c1c111807000360214401d80324668844003903052943e008100303000000698503040c005003c2030719080e500c040d03003104100034100b601d084201c0c640c50b80200c00401a41d55 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 590384019 1250 590382769 590382773
    0x3090d02060306180412030f0e031812010f0f0501050901030807111c050a030306080102210c0721170628031b0e010b07170307090e0f0601182402120a050723060c07 72
    0x180c6410040184334a6081680108441945501154400310300100510481c0c1c0c95100b8011402070038400200284000c100c1c00d400320344a00341c040c07901440208180050f20030fa412007080300821440c15039050b0040c8801d202010741520400d401400040003c1d801c04480e0307562150044a090850381d50842440d0010b00024408030403a07441ea81d00840c0c0ca0002074955101201e080c01f20700c640c80102e0000c5001e003000580b5149618803c20004042d811181c41c0480d88442004c40528440d58010389000040001405c00580e44204140300f403541c0c6895103003214890040340d06912400f010b0504101d040042000b41e0100c0140e0407000c00d01690307070340f03076041d045404040590044003a0401c500900c03402104180c4500d001e15400da039412801d100740310003032042002d6807040880c2403110349444000c0b18404007101c40040b11900542e01505a081c034088090b600c01400900007a41c00246941000036820200c0741002130805010310324000c100b0559502d9401928420a68001003804c2d02 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 590385269 1250 590384019 590384029
    0x504050d180509130b0f04080d09020105070b090309040c05030c0703050a0c0c061e03020c071a07140a26040b0d0b04090b0a0b0303090d02060306180412030f0e0318 72
    0x40146000341c9810003a2400034400041c4d4007040d02c0440d080c0c1c5842c804070b2101840310400a00881e005031141b49400703c0c8680c9180242080b22040b8144402444a0303000320f030300142d015124001040203182c2d1221044204011036600901e00d078148941801801100001001941c02d0b1907418100140d903075003040001d4030600b10760180104035080201022072000d601424030700302c401d85940c140c1d001a00c4144181e0030ba02500c40000070b103a1000308100f01d21902c01034144010300480c4001850042161250b0020340154003500744142c2c00444503004000e000410380c08944104200d207039000c003015003250841e02c903070303c1100e11008021500c9035400742c0b140d001900e0110000c10400c40701c0340900c1d03c5a40180c084405550341440d000e0141c2c2c15040100c1103840f8008010401039140045500f08801c0d40c0015106640201c4525516240340f004140c82c280500d0050f240783c002d0001d0000000d060311811740b00c0500c0141468041d2030103032400425615041a00005c11a18510140c0469 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 590386519 1250 590385269 590385317
    0x9200a05061308060c0424030f090b0f060402070305040e0c04120b161e08040804030f05071a09010f080406110f070c0b040b04031e080a0e0f03010504050d 68
    0x540c04480020001040302d8840d911100f110000b509403440c41d9181700c649000da004070710883c00440001c140320300b4001c0510601164110050800058142280356008110744e072a44c02111500012024000030245130031659a001c201258250b2a042d40ca0354000c0641c0618405d62000c4461a03000c1200742801c00207031400380040041d080ca001040303040541d03c0f280c040c3c8007206218011850500510711030f00104894a100d990f040e00011194002203d0000c401001950701b01000d00c800310000340b0000340824042d02074001004410705188040c0d4a076509207005180e105020230911400d070340c010941910100050802120550f40c0c1c1c209407014001c480754103000d2080c002034598201501c000940f03440f81c05a0b07810304c01503440d1141c240c2c0324440c40c0a80c048400d828001000010103080500c80010248008600031100703542d0381400c0d1350007010030300c0046814244140410308016079040b6440004500074011820309480c1c11b40c9410890340c024080005098649508115001c008 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 590387769 1250 590386519 590386529
    0x621080c0303040b0a0509060c1b0c030f16140907080a090f0308070207050d0834050123060a140109080f06040203070e09060105061606051003120309200a 68
    0x500e68a260a1520f44c02c0000102c40078640d852404020071254040014003520134181002c0742841d28100400c0c1d103a581c40c1c4500300916a2080c603801ca0030f1502c06101ca03403010b20f5414001c009060002d26400740c1c1d04041e4200b902403280b8810f11648690780d21100d00e800c500c0c203003031044283d110840340a01030914030f035001d00780c500b05c0c1007080105a4402c07001c40c49004940e0a80d460141c80b00c04001d402038022001502e100d000340900000010070030b10b2014680120300c50482c00801000300742080c03aa100c601580e0303903590780155580400d07010070184d0710382001a4403000e007403078035100203842c1510360b0044c41a803100120803100035034050030502c005010050308a5090b510300f0403a40355550404c0350101d002e0300403044005101c03011b8010090052403084064a40c03a802c003801c2c00525001107110b61507100c0191000350100f1058890036025a45802100300d4990035418194202c2180c00c900c07901b09441c1c0341c94400803890b005d09010703c0e10804070150007400858800144149c05540003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 590389019 1250 590387769 590387773
    0x150e03120f030a1d0d0908010c0203032202030d050c07121a100b04030c05030d050903120c0a1202011a060306030c06030a0b030616020c0f0a0b0307020708030a0e0a05040621080c 78
    0x525001030001c5d80191002e502c1d6a0b5181280c0c0b281905c0c0e09803056048060f002d6403083c40071070307042060380315802c1d16444c0320034042010440a8002078504138205800e0004a81d001a4800d00711400740945005011440b0017400c5000c076590390031031980301800552110200b00004200074a02d0b100c0000c00502d120750704c40340c0380da40303e04040d036141c1010312035144284100c260046103617006109480b48008000c019004841c0c0b42c4403031b40d901e41d2048010400500071049071701d00090000c0d500c0c910340e401c00e5000103811110708200b9031560000303400551090005100308400c030783e00001c08410030a4141c4000382c9a444409284003e402c00d82204d5500d070081c90100b004500307200c085681044040d0b4211080c0b210090b040c0b04030030303914046141c0c010075001d0044c00326021590086803c01c080b0720403145000d548100c480d0540c2c010745000300c0014100c90b03005140c0d00e00407071190f0140c501144c1c03c0100c107281c4100b20fa20480301842d680c5d40c4480c0c0600d181c003444201000c0c0c403001591102 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 590390269 1250 590389019 590389061
    0xa090b120a0c090513080d0b120106140405131e0302010b04140906100311010507170a0e0a1a030115110a0c1805010806160203040f0e011503050f060402030a15150e03120f030a 77
    0x1133031101160200400714042c0e4a008005801107942000141400741c010030f00740d443c002c0510034000c001400d208243c0c20341d902c845c2c0d82840740d102c82c801c55400e580d0b603046401c0c403070a0801044d41081006444440001c10513401440414181c04248814032001d00302640d684586241c566070582024110820848003ca0401811504609050000c1c4011101c0c80c84183d20f41c0c1d058440c5414601400601400500040c042203034500b04c0c83c001c1302c00130304180025102d010200d0341b804c002d80c031040740d08264407074040002003042510401c20080d000030a010b50b40c1803003c4107564000c018452080e200f0400000e54656009000315401303003050b00b111042140d103410301303100d41680a00c15409454400c15900609034801c1c0b01c0c00340600c0740840120340c1c2da220713141040042d40000d042d0304800c035a0b4103030425107481c00502c114014401443c140c0080d102030312000d0b00d0b0803800c60580380a50840c26140043e4020507048071310344011581050b4480d150300c4c00540090001410380041c400c2200 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 590391519 1250 590390269 590390279
    0x181012020f03010f0807031e060e060411010305070c031b020109031203061802030123060f0a0305090c04091205180405090f010e0c0a090b120a0c090513080d0b120106 73
    0x110082d810380b00b0700c101c80203a4503601c0b13606598806452001900c00d61801500785806481a81c00f54a10f5020750340208802114800a6091200540e0200c45860001d1018403a82d40c05001d440d620940d00e08080d20940d946490203480115019412950018510403000071a170181541e4801b540e00b040c0046401c5200000180c01000d650081904280c0c07080c1b00c04802e6141e40c002c4a040e10403031046032070540e103954003850003180d194010590001c4244103101c002034040d0040c005400c403569001c1060308001d400e042c00c00c583c200d01d00d03001301e04003c031040108041000350712042c01030340b4020380c0e940344880c0081c510446402d042d55000c3d05003021701103100b01c000f0b030a04050380340d840200054074414001550350304060400f5034204811180030404040c1035442824292009040c414100c485001a40d08100342c01c0c030211101210340409114060344c600c0346a034000c50106022007044200e8440000500131036a0040200381c42d9500761440303880d640b1b4860807101e01c0c0002070041704e48034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 590392769 1250 590391519 590391547
    0x14040b0108100207080405010f021c0c0201080906070206040b0405010902090712150f05010f050c0d030e07231314190f02030c0f070804120c0609090218101202 70
    0x1e00c10098507100b000c000810307a010034800c40e0940303030703015614071300d407514000054441c000c2d001d40392030650042c00c3c01e0000304810703412103e00305540f035034903100000313028030014007640c0c0042c01040c0701c1d5101d202080b8510b50005240c540241d000440704445030b84600c0c1c0607000d0000780303000a4020a80d482071100c1c0c203402140340214403800001c02d000300c4141000d00400324440c0d1054603546034040c041081507501454000001c1c1c03040b844d280c3c0c030700902c480d2010300c0d00310140e107030000003940c505041407440d03800e2287c1c6024080c05c0b01c409403800c59101c082c0755490304066441d403007211444410401c0402c980c4c419440c40300c190495011600c0d00400118034610140d46c0608218100205099440210b01c00c8030710a514214000342495020b01c00d40c04640c102142c200ea003a80c0c10400411480060692081d0161003000c807005600e0614400504d02181d660045a080d401809040074003500d10300e481c041550191130442e020561004100c0d0790b0030802c48540380840c03001542c4002e1401c1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 590394019 1250 590392769 590392771
    0x60d020714030d061d0601020a03080603030c1f06050306070507111807120c09050901090c0e13020a02280615090e0622050a06020901230d0f0203010f0501110114040b 73
    0x10034010f039156112802d2183c00711700c0044070080d005801205c0b8a1000078000c02401d074000c0c0b40941181c1c20850900074403841c08101d00c10051458446004d8814007980500541c07000d400141c000d0704140c1003045001c2d0071401244001080030500081c04980f07502e07207036040c023a0682266000140381c1480c4c0700c085c0541c480000f210040d1410f0032665101903004c0c0301d200c82103a2020f00640c901c1d1b882e2840700d1006040b4440c14004004441c5007003202c40d9603881a0704c0300303480c0d11000144d84a41511010b442c01d00e80d281409130741080201c00703561400c2e00c80c5003c254070350012000f1492140401c541c5d8600342c401d03049100b900d03240070300fa1100c5184c0041c103148110042c4194a41d200e1550b940c401141c4200e5400509550040e1907190014590350054519000181000d00c8141c06204194000c42e01107940300d03405880c00310341007007030700e246001e072941580102d0421407075075040c6a81c1809507081c500a55040c8148011541000d400c00d6000e16009105e07400202030500b800d28041c0c590001c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 590395269 1250 590394019 590394029
    0x10902070c0e0603031e090a0303050c1b010e06090103060509101a09090c07030e030d050a02100c090915090f0204060f020c03060a0b1908010e0d030b060d020714030d06 74
    0x10103001c011034080c80159482e402403100800441c1409014440503c481c0c0340d1500340c1e021100144100321030b90f1140f1040c03802640c03090f01e400b522560b10301c805500e01400c00f01080c0601c1d207801001d107002d0360080e100c503401c690203a40c065510b143c4100141d0242401d9448141c110307100c03074100301945442c00548410341d244c400d460460098031003034001c03841c0a5008200e512005120100302c416512400400700184079090100302c0710003101c00281040c0f000068403000c200c0000c1d064940c0d650506c08900b0300440d049082142016802d401040c0700c07902e0058404441d03481d00341500020b80480c101c80100141402400100c00540040020b50091712844c40410341901c0400c95131400400d0a05480310301500800903550340340074880c054405261500c4c2c00001c900f80c0c040841080c071440780040d0841c40c002042890301c0807603881c58918008540340405103016410384c15559000b080324001d0b50011030140c0c40300c0e02c47c1440500b00901100349070aa1100040b0b40b0001011a00a1701c1194 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 590396519 1250 590395269 590395283
    0xc1507020c030f0607051c0219110f060118060803070615080d0c0602032e081207050a080c07080706110d03020918091002121f030c0e04170301090207 66
    0x188007105240d03450b0141d584505031600b0150005409a11920280913804895814442c030080080c80b010f00702d034001c1401d0b42c484000903450070325117a00a9402c400c840205402440d40303010720360350309440b008107008a0404880910022107500001e4018401602c03018040d242e40300007030700c0d01800070800802e602e07150103e5203d001840e00e001181e044446030035501c1d50310740c402c4590b5a20340298802842055120018038520142500e10200020058440c24105296a082040c854501406081d9204d001d11081299400044010582c0450076500601e465242c0000200d824144001c5400180300b0b44917140e000070f0b18950151059400c01002419500300703140c503200450980c4140200c242d004100320701c111442e2400800600c2c2d001c0c246005841d0102c0d0594a00d02c00e0382d005041000c181b00d54541403014028184080302d1044040c46c00540180e45140c0d00c3d804014141e110b030240140501e000030303042c00003607082c00a00c4000703000f0b419565031f10745003004001d4106600688070740b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 590397769 1250 590396519 590396533
    0x1060f05040e0309100311071e0c0801021e0c01140709030605100f0302010e0a1802070c170613030e1005030a150b093708060f041112030c150702 64
    0x850b001108a500500000d082c82484140e10881074002d050750002c0081c0c808030401890001c103126600c2c10b5200245038403140b400c00007504200910030030540007c142c691040240b2194003820b44030181314050807401e07442d00c9060301c1c1440ca0042901c000c1c94984100c05400308281554000c84100030390341700f0711040040342c982080003071040c046401801643c3c10788140c280003660080c03400c03009aa400034a01d2205030b488284010703007400c0041100e040690046861410000c0e04555500600914000c1c0105c01d0885003055544850103440b8248001504400c1d0b010700d4441c1d040000f00217000780c40e0140e11101c3e030100601310303032084075080c51552824809248501c0415015400c81d10036021441c1841160b0080220715140d40c0562140302e6020354030607500081c3d810200c03030540030400d81c120b0100c0c507141d001d6003845001049024402000801c000015411700b1000c6c101d0034060343d558403c80099842d007440d5101e0032141741a548030f800100f13032a02c5803e03084a40306400e107a0940f0a1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 590399019 1250 590397769 590397791
    0x30702090a0509120f0c0a05010606021504020a1512091208010e07080a0b04020d090615052b08070b240415090c0201060b07050105040c0b03060906090406020c01060f0504 75
    0x700e40041e02c43d0f40d41c81c2c01880582655400b2400078100700c1d18480f040d14a001d09001205142c111500412280342e516410304000711a010300200f64a1751460341043c03954500f5600260304940d2078050008005120080d0b0000203100340e641880031f4101e81c0e400c101070711070760805000d03450700d001c0a000000c02010010401d40000c1c140352b800344859031a00142501e0b10900c400141408060b0960426401c3c000301c050cc0c1401d0240c881103e02500001030142d403108906198900c103a04014011046081d000310707501c4a48082c20008640c80761050001c410910f02a0180d108020001c4e140c0101b0070284100076091411280e011500043e40f2480c140c511428441a5622421001a1a2410102081120b01682043d440c800c8a03100000700c00340c0f02c40d0340c503c240d0055401503406030340d60320801c8104100c12151002070700c045c041d4a030552070944001401080c0040a5900992508010130300300074054041d00c45601c001c1c0001d000c82070f102d44200751102d102d40705662003541046080b01c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 590400269 1250 590399019 590399021
    0x9050304231c060504020319081c050606070803340801051c14160611100b060d0207060b0429060304120c0c08010f020307030e070e1f05030d02030702090a 68
    0x41610540c18204805100e5030300c8031002481d000f8401e0707800d4094141c20050113000c074048241c1480c400d000311500c44ac60000d000c4481107403280503c42c42450402031003030703c0d41d800003510719080e0710120322a904e0303031200030b0a080d0041c42005103103046d14804031003054002c1e2203140396038024269640d0703c0c82c3c1e90f070b80c0420880c00c4101800c0c006a140408018000c50700c000000070060b0485000c1301c41b40b1801002c041515090f69000e01d001480808590031a40414050036005034035001042c4503030140403000a00d07070310800d1402c9a9040d400540340f030820034103402c06240d440c0018030030000641c03204181200b4450f07001d510985001d10180c1c451503441c101003500e0041c0c0c0c112100e8801820224025200b801d41190705655001c01041c002544a43c05d0081c681c0c05055a903000d6120304241c0c90180c00c0d036800c120380020581045000344031501c441006290f004642119007504103410382001488000c6903000b082d05805141c120380711254000009002451003902c50300c029035503a50320782e0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 590401519 1250 590400269 590400289
    0x60a0506031f120c0302010807081015020c030f010519091205070201021015050a0801092604050904111903030c0b190c113d0905030423 60
    0x5648890140040703009107503140b240014204180b1900142c050f15000c485440400c011022a04e0810401042c001c6590112405070000c0150500035143e00301010100c401c500d050140d0083c401e004083d034102103100b00b08000c50844090150303807000004081c594041d00f01213a4181195103501a42007010110340f00b000704840d0805c0c241044615981c1040b1110f50005400b0707070441c464500c0780d2201e5049407280303841c11481c40780da00e4023442c501028040b55405a030700045190b40b41c4881800030a040441018403520010040c800f01001c00c008110140035035000180c0080e070a60800081002e001c004030800c140803203c03030b0442015480141032590143c0801000104054940e5000981200e00740303401003054420240d0608403412036104848810b01c98000150b1070b83ea01a140b907800748091580501c00d0508244902c50381c00c04d040c68076000c00389000980c10595000d001d0a00304e40d014004140d03200d003e5030b548030383c0e0303201100100c150100030200c0709a12904520240c60810420 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 590402769 1250 590401519 590401529
    0x706021207030c0b04030c140f010606050306090f07110f07090b1906050d0902090906150105041a03040c030501020c0a1103060403140c120c0a0303060503010e0304051002120f0a08060a 81
    0xa1078040e1184c2d5200d800780c441c0074108509024000c00150000352200b1a00d4014488050080440980210b41c00d400c0d11403c0e07024800340034007002480300d940c8810140b1070340100c0000041d9000d40310014200c0700c4070070013821b1003214080d80d440d1425140c40411031004440f44458244403111501c03040044182c441101c004000c41c004100b008200d00403000b030aa0100305c80030020300480c3c66000310b81e0311001120500c1841d006003040003034001c03a0070540352042a00b86006400e240c1030541048011a1100f2a070307001c458003100060422482c00806c034065039008000355100d061040d8560795905140a04583e100c1c42032501c1c186a00300003d50521a641513030315406400e0070034561100507400b070101503910740280ca0301c81090644520081218141150050140c5c80d058213004080700c0d969008103110380d04180c1100110303c1c0010a5900b924001ca40d078102c00f0b0003003642a40382c000c800c05c07400e00080c0c000c07409401c04503400c130180100c032482da15400459601c03e400c00c10780c40c1d810b0042c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 590404019 1250 590402769 590402777
    0x12c1207062111070303050a1823030c0a0b0402010f17060919060e06010e0316050411040906031a07030c0903030e0a0f09020d14150607061b02070602120703 69
    0x4800c1c28100c62070404003044162200c00a103200040f82e01d01c03c658800d850950100740ca0340d0600c050740010f4400c04a04550410300d010456105a0302c0314901588085e00c840d605a01c1c0c41c945042060900480e00382e00009001c80c3c241b08441c1c94111201035080b50700341c1c01304092450b42c03004140506143d07105000400c1c40070141e0b13030300e040400c111150081c1c03882c0c1202072040d0f44402d004042d81700342d401402c0300620706000352a190b000101175295900700d00740a07402c10409002c5000501001c1c8003610421140400c0d2048090801c0c24240500c1c1c0c418041d40e13003000c60001c14400c101d1001e204100303d9201c00082ea40c0c80d5181501030360300588903140041e104042c2000402d218642403918880000d001d4807002d9900c081c4c2c140300482c190004200b09500103030804030100544181e103030a042c4180580e1040c40d01c100b20003801044a0403541c041c80c0c0c0055280e0802950f82c2c0641c0710308168425004d400d1500e060029500c0d01540191009071140d45002b16141d00a903054401319a030682d2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 590405269 1250 590404019 590404037
    0x20c071806031718012105070206010e0a0e030d0207030309080f2107021f0e0706021006120314090a0b030109050a0c020f03090d0614090a0c0b03061e012c120706 71
    0x200446188102d103042c1c00540100c5802c85003146c24500409009041070f500030038040d41440d861018003480640115074a900c0c1000c44c0c5900788011050b2903004256610044c2c44d602c6605081c3d01405090380024040c3c81c00141074503580d0902400b510b94455460381250440e4a1a0b20302e5491040030382d80b800141e40821400c4c0312400c40320300c25030120303400c401d400b04480d03503141203007441d150b500d80141c005600000301044d0721401500c5000014040e201d803507000190030303840c0a05204942031407200006000a501074454031800c41c61001081303950000e0740d0701e6a40b000c0507001414142d51480090703061a05000340c3c0c80c03000810f00e40c0034088001641c80c0c003c0c110104201c010310068111000754070b540c107614040e00c03202201842192544058110303421301d441c008414441c030340c1061207694000d20038081c0c1c0e40c8600345100c6111300860b580d504130303400e1174005850203c540c008000480f4850501c40300d800480345da0b44541c40c481600d0031800508410182da40314034131400340e5000101268 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 590406519 1250 590405269 590405317
    0xa1b140901050607141b150a050415030b0d06021209070303080a090606030507030308040312060e0105060708090d110a0e0618040212060a050f060105030415020c0718060317 76
    0x4001400c0c00e80c0b10f00c1190302000300d00c1050f06e040c20602103a0407862121582e000055041201104d50b24500c40c0003a01d145c0206c40e940a492070080f4000e6440302c3c084122903a11580c040d40c415100480c004000307010031100c500d8980b010b948071414a0400911810100e8540c45c0000742107000d580e40360300c59800e15034071461104010994402c003510a291038050010102d142403154901a50090f40c4800d160b1800342009000d00e100b90502100c0245840c4003040509031850100341511011a01c01c1c0d500c81007400c014885020710f1f94055800401c07800410100400300d58558014003007600c180d0b0300ac581e9640e684907522030031130b5000d41020100d2100320f41403105150131a8000d10003410000b131000900344240c0381c048200d03160303000b941d03999040c440c503208508000c1e90f101809203091851860070b07682d03610811815030310990905402040c031080300803061003080041c240031100001c82e03004003c01305020300076034481610200d0810300e00e10b031034004400c1202c40122081c414100b00341402 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 590407769 1250 590406519 590406529
    0xa060c030905060f07080429040e01050d0602070818121f1820010305060a0b0d050919030203041403070f0b250605070e030d021b120a1b14090105 64
    0x2013910f03000e42090070000d9800190084000c0c0020307100103418460504440e04211800400700820320358481d200b803004001d5120100c4507d070641d10f043c0c070b010a074180a40741c242c3c064051854000e0071b01d80081454540e440c0035585025112404403840c9404840094003036071035540764040380ca01e201d10110b4150034011180c0000d0031349a032130000128005015281c0502001515004000d071341082240e078181503926014568201c9400c0f505810024985075090074144914076100390010b4a420000f40000000e100003480b194030071104590342c00e4030746402900c03a40300e40142c0d01d12600030b2060320b4250800051a0b000c0d20710541610405a0501c0300c1e06200d1b400101c540104000c00c1d02805010600b80c09400400c14403032240802c050404c2440545440003600c0d42c24026030058504144071540010070340c002c0100e0301d4210200300310a001107a0f1044010984400511031420224100803003c070894050000c0c4038042f14540c0c3e111400100303000c000b2000154050b0b40740005100c2ca1401e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 590409019 1250 590407769 590407777
    0xe011e270f1217010e010609030312240305070b1e0d020705030406110606090610180b2107020a05030a0503070302160803010512030c1e1e07050a060c03090506 70
    0x510715042240c000d0380d9415000400c9210102d0000c0e0b41c41102651491403071080783e000d0100c07480704d9a160f40c184440100004480c0c88060300700919a141c035124500c15500519244445120400e0390f94071114444076101d00300e00c8200d4051181d59800203241c1400c42c140c0f054081940e5104001c103107401000c41c215003026007510540340c0d0801038980040c2040006000a0100d82c44004090340007101c86401c04a00401c2103000300c00c00c404004055450480c0c8001d0100c50b801c0c280f02401d951031060186e406613170440e010803003001a00324a60300408801c00d0445502001d904800c0d5240801240c890700c1d400401003aaa0090242d409145e0042c1e001c3d5a01180c10302e4018100b01d038600e41d00602140c40c88003a0f44481000005100034140209035144900601000b1803802c0c50080e001c580e40c1d58807009600303112200c490409803110301800b5941e01081001d52074007900b010300c00750704d458035007500c0340c94811000c1c41400164640100a60f440454041d211400c05030b107410280550307980 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 590410269 1250 590409019 590409023
    0x215060f03100f051e0402150d060504050421090803040e1918030801080d0912060e0307080301060f0c030f080907050612060a06090b0a050a0c060e011e27 68
    0xd00c0c103074074050400c0f440780400405001034040789070f0421490301d20720b0607800106403d8030800300e0304220142c3c95088078240800d40025441e81e43d0b8174201d4003000105200d400c0f89030301c541007506100c02e1000d54491040402d540b0403e102a42c800590162044207051180c44942d0300140310410200042005a0364041d201400c1c01d86128421740401040700d80768524000c1300c401c03000298007499800a650b0f070142100074010080a081c01c2c00141c40c10740c003441482c82c09110000007204001702c64110716840d868030720859494280b1450101201d41090140c200040c8800c40c0508030188900d000c04140c0b900741d21580ca1110205404440c540300041071601c8500c6205030000301901c9000080440103160b400c8580c0d24107041040061010382907000f0403c0000c0040b0a00c0f10103c0541201c04500090801c0ea940d000507040544486403103910117807016240c00c4041201030019000035403004010455551940d815011100884012828051850403003411407407142da4010203806e0554 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 590411519 1250 590410269 590410273
    0x150b0a0513031208090c010219050312010e01030611250201090803040902070b0603010908040b1c181a090303071d0628091d06040f050c03160215060f03 67
    0xc1075141810000350440d8800c84050b2120794400c90b105911014140d041030910000c0c0805158200000356100505240301e8100c0c180c21000a003006010000c45c1c0004480e05000c0c3c9556a5480007481c510b142440103844040c10b104030381500c8017032542141c1803030600c3d038039807844807a01c01055015507800550803818065041d10228242c003080001d44000e1030405400341e038415191402c21003c45000d0000ea001380c1c10004503d00150740783c010380341a43c20f4240d045450700300049120100c1304480c440c5a0005191048503000322034145440701c100c50140400364000d00740190040e0420700101c880d1040e030342003440807030102842600024800500107403080b0105904000207038203a41300000020a07060242055001031a00300d010803026025800d28a040030b03d030070800c5500410480c0b40c81c05010750000080c0195440380d1109014066240b000c01082c900072072090341e00d40c404e4402c4000d114181c1b41028070584005119800e601398008824959121340040c416003101d81c60290b83d141c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 590412769 1250 590411519 590411527
    0x2040906060b09130618022127060601120b0d0b0a020d0c090b03040b220c0317040b04140d0209040f15270201050c0d0918150b0a05 58
    0x3148160007a00302a101400107655580300d210104100181c00c4d0310541e64141c01c0c51020800000100c00d8013134040d0050201517655103800420ba0034007196070030502c000e12105400e01181d14240010442e5200001d100a9951480f2401c101c0c1e54000442e401030005a52030313000180301442c2e401c038140c440d80103012044c2a00c0a0740d61500c41c660121181001141d0100b03001c001a2030300c0c02880382011490400c00803007814210200b00c58400240068160b00c00b0002103250244484580c004042e183d1252000e1081e8615021050100500c810b550003240c071030380700c090160701d9802c03601112821404a45813900e0039031041007620030280142d0380b0000a03004180035880b5180c400b0b104911030000c0d454644841c0c40c2c401101104210291002840d028940c038402c541190f02c101e030780070702c0007a81114503501d10040342e261080308924403290052013581d56047d07400103004c0c4207841122612801701e524040552007241c001405000041b40010340400034a95007c00929200c005890150f2034 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 590414019 1250 590412769 590412773
    0x2304150f020d090c0504180b311502040f03020d15020721030507080106180b0a020c040f1a090403090305070605030114010806150a0221041a0703050313020409 70
    0x1c0303030000645204140c1d10396901c0010007402441d007101800084508000e4503001c01341e224203007040c85400604034003508011440459a050505a544c6403032341d01b100b404a000e107400c60025512804c121801500f45940704160200c600039034003518074250f1403020b62071941d001c20220038040c9109440321903d0511250200c0711500042c480710307004060551050001e580c0f07829140700410039101c00c047c0703070800b4480070540c454080750464043e458181840501901c0240000d01a0340c0045c40200b800181603240c15000302d03132501444803c4408008890540140d0301c01c0d143c0f0360081032149061303469124424502022010781050081c030f4103a8205480c0e82ea03c1e40f074181d0f2504504042540400104031103e02d0f43c0c0d003000f4124081c80e0072949800c205010407560300d4820701844c0c1c409004254488c03001c0c403c1007a1440c030a8030824140003403c0c800c0c40c100066200f8001c8210071103801c07200303458500b8860100c0e55510b501d0740d5098555134410b1390700c024000501c002241c0c4a900c4001c0000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 590415269 1250 590414019 590414021
    0x4051303020616031b05040302012a1112061006032a141c061406120408030c07060906060314070303050d0c0e090a0b12010c050f030603210304062304150f 68
    0x40c501d0317525100c0581d52030031800058145c5c456000c109004c0840d0503443c0300b101c032a1540920b026644600c100708804072035030010300c402c1d04641070541d882c89010b00308a40d0655007500d81c01250f80540303080207400f0341159256406444560049080200803185280c01ca107d07803203280c282c2c80300c3e046a6083c0100d0a2007581050804c4624030011601c07075205002925010041c1d8040c0e032402c80b20340d407600002c0d4100045100f0014005003030088040002a4200249000c071000140d001804102004c0307103107447c40007800140000d443d076440d96402041c004a0005403c0c00b0f0b240c0585a150406c41e145144001a1543c2030500c020040c402c0160005501c6000e00980100e50303099012400500c01800d0000c3d080c00740c0290f442607030403e54000403240e00102212940c1640c055141da0701e5a40070702080c46c0090000310507030b294035840215201800c440c0040d41c0101d1040c07100b0301c03840d40344050207940303401484817080925132008045800603003010401508800c1c480c4011800c180f080b800340d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 590416519 1250 590415269 590415311
    0x8011a28110d1d01030b180c040f12060e060402090103060903050f0a02010e010e1c080a1b0908060f25090f232403040602040b04090b0405130302061603 67
    0x42c01080c00d0790b8428540070400c40004a040c1c000303280404c506041c5c000040c51041d107182e00200e40e100c16038042806580c890303007100e0241410007030301c1922954825410144110780e0320251015840c040303210400c0303000420000d001c0c5800600030304141e400c58a4040007010581002c0b0f0074488100180d5900040500c040d04d41001d103034000013000c0086143c0c090039660b18002940341c0350066010341c1c4a1001030100410000b1701450603190580d02c409030a4020004000c2ea1039004841c0c1034105401d99002291409541080d8191252034940019850444009480659000f10582c2ca03000d24842c0307036100407400c01c01e14a00035030403564480800284d8010780d048035092064206110300581d02d00c0c90f69503002e000551b030402802c0c00448400a800341d04901040d00300f40000080740901c0a2074060324064450030b00103603940d981d1250b40d44e009003101c4c10540d01407420800095040808440000c1c080d90b09500948140e1380c81d6210003000a04500140050640d9440c00c9064500e0304000030f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 590417769 1250 590416519 590416543
    0x120105040206120a0609110a021b0a1a0706141e060906010c06240f12120c03120203090106090f0902030a1101020a0b16080f01060c02130e0d08011a2811 67
    0x38640c1c6522340d1a0003030500c5403140141e01c64a681d90350104241e00d030040c000040318458044801007030b1658600c0c41c1c29118440340501490704200103900750115031040315014074111510541010b5240900349441c200450301580c3c40400c04000480341d5014140d802d01c414468040050061011032200704006c44803007640c600c42041090500c000480c4110000103040e1949845200c4042560382c207600146800c440d008001e8981d03d0201054024030030510a0f16080c40259124130f89501c000d8028665407090102a44c03c01d07020056015048c401d1034030b0a6006805015481c01c0c41d11228103100f40c005d6014114031418034013001140800d0b0b5414010b17012402d080e4403940000c02300408a85020313004c8204555140300401000b03800c6111500c1c20b59060301d100c4042e8905400140003010600550354250281e2102d2070101580409400d05030742c8103003000703404012141001e0360a4007403e4038450f01001e43c201d44d050841c1400a00d0103007865a8070b07110741420020004141044065441 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 590419019 1250 590417769 590417801
    0x15030c0e091303020105060303090a120c150305060307140f1009090218120607170604150905040309090b010917030412030f0822080310051905120105040206120a0609 73
    0x1c90b0105603080c024190000001c070019800e041d00301d000100c178a1043d00c00d8080d232030f4440c0a114104144201084000d140031902d601422988080160140004880843c440d0194160129400b092800b5900a40b4000791125500400960600006082c0e0603e448207020171400002515a054002003900e81200c5528540200900050020320346910030f0b1040030b608803504101031542e0041e610881000280e007541400c1d100c0b08081401800032408540280509990200340f04030150000303401240300c2d60398105e0140c1d0f140e508a048902983d06680080d030b010804005480b1101c000c0b03180f0110329030070b40703207041e58510790210502c3c0c1c1d05500300c000c2010b0908580c1825000748a042e44911020000905c4800040d08082e44502d000c00c001e1a9041c08404104940d5440050002030500070300340444940d40646031751059034047c80b440d8420724001c61210309004040c01100d0180d03a015140a082c00105d90f140c0036210b200409000d41d2660312000080c0c000b2440c05107010510780703212 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 590420269 1250 590419019 590419051
    0x2b0f0c020c060301300f030801150f080c070203010b18040c170303130503210a0c0306055401050607050c060309150414060f0115030c0e09 61
    0x80040d04048401c034985104a40500c01000240c080c2460f400601040c403e072001181c441c00004200001e4004000d071a5555005602041541120100b8141d50100118180c0c6810080d411210101c0b007039038100020b004040454001c00c1381402a0801d00d1000700003240200e40c01000c6209125420710007201e2081e02411b000a0040c05860704001c2d164a050044041c00510456944c911002c0d01c0d00701c00d0110180c1000c00e100c014815501080c6191002e5160041d101c546860b031400c05880a24a1920708022100d0650007071042004490b030203000c21060360440e140310b00726565a03c078003520314814403540d51135507500c400348844c02c0500d01c520302d2000620021440040801604114000c101c200a1503010610010b5004400c400842d40c80f035890b940c0340181420844029000382c0303401400e07001c1c0001c0000303c006c4803400342c03400e0044404680c0e40c15081c00034542e00384600c0c9400814190780d00c0b40544a80c108001c00c0384c940c10141c00c001306407004103006450440f4802664040300d0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 590421519 1250 590420269 590420291
    0xb090705040518060105090a0207080c0f0c06120c030c0c0601060504060e0f06030a0e0c120f0d0c0807030f14030c220f170111030910050c0f2b0f 64
    0x84180b41e00542911a00c6801039043c9000d84d0761408107004582c800d0007180001b48405483c0e8040301e1050347c4c00038450f601e0714882201590754030100d540011860040403e40c84d0607050003025a54540c28282e08020180c8480c40f840249a2010f000c0c00300b42c80d070404c40480e1100c0300704559402040315582d001e41d114a07103500107082c40c00c01000c240c881c800c10600d4015558495043e2500421801e500050020590524600c0c0c40080c840e2190009650072500302c840c1000b00d603070307600440c103601614004104840d04031103040260030b0042c5540000d010340c0010900c501c450210031080e50505500da100c1402c011525034000703c0d4000501c0b580042d8100101040c540707008400500d4142c2d1360407140c100050304601c480f15015030f60000540740d40c44001c00109403c4003442138502c5603e03e07680e00341008266110103d0420f503502c0e80d820324010070303c1000640205d07080e401c00e05281600f0a61001642103884100300718016039042e0552090000111900c83c85064150030600011100000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 590422769 1250 590421519 590421521
    0x30c07061a0409050a0521040905070903290a0c1e0c06050c090102010e010e1906020d050c030f010803121305010e12041a031905060307120f060e1b09130b09070504 72
    0x79052500710f5080c42ca40c5028109a49002d423001d03120315035008078040e56282003c4801c482558805040340700348080704040d10901c07210903400f601d207284045016a84082400741641c000c0c038035810000d00c2e41030304804a081e0109020b12010810b02d4030310081301068440764255074040d47c15101213040018110519a0244a1642a40c141e50000d001e070300030200109403501d2080701c00c220b6409100b107003c0201b0071a50304485041144803020071550070300350031b40e00ba5a04112140040c80302c0120001c43c02c0e810000c151910a40103204001c010b5440e01401050704c001c2c0c040c01c8a40d036482e400c51200300742e414410304010f012075612807519640b0b0601c04030180e481100c003d25010f8020001d00094100e04d1401c0c084480c06180085110340318000030918103007156000e9007000c40550054410003251003148901c9034000c01c07050200203214221142c03036100340c0c5078040002c09050744810380c1d420080b0907180d0214100300722050404042e210b241c0c905100315404001600504c0c001d010030302d06 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 590424019 1250 590422769 590422783
    0x606030516180b090411121501170712090503120403090f0815041b0f06090e06210708150109050906010e01030b0c0405100507030311030c07061a0409050a05 69
    0x264a0250360107403000c00040120308050003100c203da41c0c00a03841200b511650011001c145d038241030300350350300301028920140c4041910078000f5004d26503000c030034030b41c80f0b5016a8003540029021011b1a01e0344030301680c00050811898804c55120103a40002c0b55052011300000c01c81800e003088a032406160051036031400b90410800a0008e02060251040000300d000300d88003640c25290780c680312810640ea800c42e0070010ba054803070100d48041001c01c401850041140c0554031403980094440300c011111341c50890715160403952103420000c0301350300c2c500f07180c00048151040e00c1896894500303250420071052142051012510010460700310700d841855441705460005d071055504154620740740e440188800740c4801e0215000c54582d000b000d040340d0003804000c1140401644146000d04260032001042e00072a14200205211034202d10072288106a14014503261480f02d5441780000c081c0240d01096105802c120300c1c0890301c0d0351007407040040c0608000c06c1c460780c051414500e0211307 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 590425269 1250 590424019 590424061
    0x60604050c040b0d023a05070311090402070213050a090b01090204241e2c0a210618050d0309020d060e0c0a0b1306020f0a111306060305 60
    0x1010041000f450f003c10042d1002c00c507a808000d0381e502001b100c441c1d40c1918001e40070081c104050700e0440d0350081c0340c5800d103041100c044244525a0b6004d0103504a80308030040100f1180c040240082d94a01a03001b071510a02c01800c10800f0410b8510b40002c0f5482150301c944800e640e07020070402c1c031900d400b0150040071000c3c000e501e05420000d4030304c66100904c001c100701e07a240c80c905071003080c0141d2040c0c3d4003d100549880f00c100150100405031032038000b6001a20074410005525505846070003034000f140944146541d034903100d42c0c2e00c55120b088811346000303030004514500013481e0b4003400c05101215400c2c008000c0c803904005003007021300e4807060241403410606900681320340300381140b0300e50440da00141102c0404109803c050f20b911940313a02c54007880303000c0b4600040342d029094070382e0700d1600003c07115151481030b039590742007140082d05580811160307800a164500a41c1c0c0d1000c02038020314010354545640020b80318941c01c1000885c1d16541000342500b40b128032200482 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 590426519 1250 590425269 590425291
    0xc0b0c0d0c08060103200403020904020d0b0916080c18070201060806010311120607080c0304020409440706050a0618020c1b0d060e010e0706030b0a08010c08070507110607030206060405 81
    0x80e605400320011b6200300c1c403000740102500350004003503560317100c2c0c82c0d411a03421500c24000c80c41c21031179041e01e0799000e0f09914281c0d06143c17008a815500058181501c2601810341007803030740042201102028018070301c10440d03494040c08101c8440c00e00a15008510030f0907201d00c1c0e80101400c20044400348041c0701d045a1000f01000b00302940b00c2e034071507040600400301035903d40712800400c020f0040060090101840c030b00c00b11141d008040807541d403140105002901ea42482c0e291a00031585010302840698818441103000c220f4540c0000e070400441e400c00515155608180c6426681c1c800640d10155800311b00040751040600400603044032107503500640e4064000040d00f83c101080018141e243d450380140624902580580064111002118030107981c5600007400b819211610341d02400017100005030351407050061900c03100c650f4540b03881759600c020080300c1d260001d103810354181c0310740c140602d51070721004024180d06003ea03016040c1072a0031400e00c000d44002034a022440 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 590427769 1250 590426519 590426561
    0x91506030d0507210c1a010605180f10050309010f05040c0b0a0e1c02010210050705190203040911090108370b0603100303110c010c0b0c0d0c08060103 66
    0x55500480d412511490508010380c41c3c2043e41010012890201c86400a0303e101041c0800100d0300210510001c0c3d1003106456071011141c0c0062071280400e2140101140007441503400034a145d480001039180003401d0061402071080001300d5003800d6504103004101d000040c041d21543c28000d41c1003406a01d0380c02d00880c14141e5420708280a14810001c5140340480c034941c0440c490f070514110400b008024010011040c0d80c49071440011041c103d0140c03084290f004d26129960003650b100306075030340700c16080c00c0002102075800c1c3d4030261403408600040001285d80b500521413696190040041c0300d80fa04c44500026245400140400000c242c1c41c0598082420000144001c0400302224000c2411041c0421001428080407001d500110100411004010040c0c0d511b003103a002c0d0f1b4819581648400c0119181c1008001c101c0c00100602c0803040403030f00300c003003c03a003103004070f1042d502c0c1c0100c2c0013a207801c48406107080ca00050b56502400250b40e414040c0d8410158002d08000e54 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 590429019 1250 590427769 590427781
    0x50f06070c200d05010e150c0403171c0504021005090d110f12151008070303030c1202070c0e18060a0903050f0708071502090f0111010b12060915 64
    0x40c038a030044001d01203501c0400500032031a00e11007080380d0920281c00d050300c0f080140762040c060709904c110b13102d95204007046000950310510707440703000303030540d6010500d091704503228400c121000000e51400560200400da10202c810240b101c2d000c1c1c1c8485c000603045c14184100710180c00042240810050309000c0764005940d41e401903845140c4c07012002460900c41c4e0041104502141c0d0f203141e02c0400942d404d00c9400002c5220313480c20082076440710349956100d03c00c4100e100c1e00d02417048983d02c15030050000078041e0b0302a510b5130045081c40301000c075540b904039050703a020031030489491030720440400211304030080240d042140c40c0ba807902c0c0650b44242007541da605c0203140500d407507201c2d2980b90905009204441a10003500c3c0050750b1130010f810400055803126000f1103001e284251007402130240d501c02d4481d4550000c0c0040c1c3e4003d40e80300112101c404003080700710765540e01e40600c042980c41d06800c20400c42400301518440c548418507605024802c481c80802d05421010803079 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 590430269 1250 590429019 590429027
    0x6050a120611070203030a030515220b06030c0a05030a0f1b0909181b050306161d09010509150a120b1005010215280914070315020d09060f09050f0607 66
    0x1f22480f0369141c0041c05544101c0301e80c80c0c80600003100e542104130848001c0fa000c01c46c0b8265040c10030001d100703015020f600c00034021148402c40c0d03140201c036010702c50300030224450740042d50070407108074000c0703510322941d0343c1c00041b140343d000700350050341c1d144802c00700090300980d00100800c08990104280001400c0652820306002001000f603d40c148a20380905400d4440b8809480003404844c02d52900c044003024482a001c10b240104074032240008000c0c3c038000c4072103240c0802425041c150303441c000520a251a014101c1150702c07504410b014940d0300c0f040c41e050300814848000046100c100c1c20440100e02c0080c2c40c42d0707000000f504090190740d03000205480ca00880d03944403405075451000b88068030b0854466488501d0360700b0304c01d0b107848070150031074071a09006a080d003440c6040342c43c0160355100c0034400180800328509455580c2105980500a542007584010940d0783e000c0e0707158400c940381c3c280e50502c0159905009402e01104000000603c40d0503002094241083c0b90050 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 590431519 1250 590430269 590430277
    0x3010b101b0f050a060e060c1306210f1a010507020a031205070c030f1a0f070311040807030812060607050a02060306011209150c090b030a0f06050a12061107020303 72
    0x5010000c001c03885000c00c11070703070790004441c0c1d080703019075203800e81c4c80c034110000e1301500c0b90382030391132248802040300e01c541c04084036503034045a21880b030494a440380c16201d841e02d404030481c911402206112100f5441d0160100c0d0003800700c000119a500080001001d07804c400c1207a04015060204070300684a06a60350b013a250400380c1100d110400180440d194802c41e41c00070010241d0420000c100300160140410b00d0703200c0c01807040050980b154030079442c0d804841a03030503c110040882c150350701960101c60049a42400f480c80e080d26010035900d0143e61390700c00c58070040005086909030907000d24180c0c011404861040c5454a99161a9a0b654040c81701901ca0032001022070801e03809510303400e017581c1c0b038100c1c24414080b560410328240c2d19000b1802402300e080c41e8000c2c038201d00c20700a400503512203100341400c44c1c0700e10745d00b50001c01c080c0d02100b092a90300e00000c20542d4a0300d0401c0000e2114007840b98000c4007500e495420380380b81512000051100340260f20050340c003c0107903 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 590432769 1250 590431519 590431547
    0x403050a0809060723061b07110127050f030a030c1b09060e15101b0609170301030302160f0306150b0d090308100b040612020c190203010b10 62
    0x500c0d1242001400603400348211300006010313880700d0024486a1004e240c0b010014210f8406640090b0389440c0311801e0943c820b00d02c0700c14503200700212000104c0c0000d481580383c5041c90183c1c02011040300614036502c4c050440c04030402e06080800441c41d09886018000d00b09a0140c90244001d036005424a03100700e00c002d165080c8000381d081003840c0115014024071707112905104d02c5a40e100780ca049160162102d10003441d1604028070701c1e0400041d0300380c00c00441d6461008000103000c031803550a5071194119880c0d034848032501c0108210084d5038000301c00c031074001680c2e03504d10b10700070380341c03500080310015540070b20b11082045000381d002200c110785e00510040f4801403003c0b091a800010b0f500a084010008100341c240030302d45600203040713188251206165a00c503070b07a0800200140341706e84c10038200104802d008040c0b0070040041d100d0280840903091020400e401ca061203035012450070301c11340001c81403055107024007404003240000e4600580d03020601c0b0000300069a40c41d12 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 590434019 1250 590432769 590432783
    0xc031e02190308071e0614010617011809050f0607020f060108010614010c02040f0e010b0a1a0a030c0c0f050a02151e0a020c03010f02090a060f0c020409020f100201051b0403050a 78
    0x1c071809001444644030704168080c46c100012509040c110842c10001e0003078800062612041e080d10395006182c0505940c2008041c0100c6052040400040c00f808181154980607030801042844820481103004a169802402060f0038010241e0f05c1c0c880160b2049d50244e0500342c0400800300c481c995000e50400a103440c018003e0580041070180c0b040407148030009182030b140361222070040d800701c89594011581180b260f40d840501d0034004520b04c200e030020100c20080700c40447c0c040d42c080500302915003006020155152640c00c1e03c1400e071030050b20550402c111480031886d00501c1400c0d00c04920034242e0030001c8403040360384003001030b565010008800203881c0c0c60441c020051200415401002030080840714264000a0340000b6000da024440705200420700a00401041800b006161f40342001300d00a0b40030080502504203091340c000740d1300c07210f4042507180c08294084440181c0c0000c64a42422111005e0174800d80c0c031a6202d01c1420b01c001d03c00680c02003212040142c2000c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 590435269 1250 590434019 590434043
    0xf09061312090e190506010e18150d050706030f06060c0210031d031b01020a05161502040305010504030908070602030901030f270b0105040209060306040203040c031e0219030807 78
    0x7510000041c2d0048070601c503c000c2000800c40202e00810700720340b44c083e014066601d85100540d184054002000d92060032100000800e40040c990319900a110841541420050754003050b20f90811400130342c0d0a821080081c8070054041c060306000104c1e909040101d0340c0b421500174954007917100c0c003d120f8080290420030446c842d40042c04101c809100c05003c03480d03140e540720384d2640071140080b2140303000e0108000d42007061081d650040324076103c0b5440c1c040601c41055032134418420440b00f03c0c0306904661103182151000d800614490310002556050a0074081d05034001c55011a0042d80329142c2407003001d41c00300c203440c003a03542805d020074018001e0240d03401a0005800300d83d2040c1600c9c84840c100e2005105040b6054002c81440000e42d0301c0305c0c1031006900c103102c06e85030041d204001040082c03c080d030085078018001c5042c0c50347d80b922a9140c04400221310101407518041030011f20540c584120368110306000203445002251950f500d0b48494002c404000c2d2903158121 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 590436519 1250 590435269 590435303
    0x20c010b06030702150f01083d06030605100b0d020c07050312041703030c03040f0f020904060e0c04021602062206170601030e1203070909020c03030f090613 69
    0x50810301540c0d00050145840b441c00603802503440b003081564051080003940402e03100c17125072030428140e8903400054202c080081c13a03c2640610449032580700303100300c1c420705020a1840034050084d126900004520fa07803075404d103142034600c090b2000c4101c1c00d00076010800d500010f811182003072221800540c0703649104080a0420440d40d01841c0c26016000303200c00c0c0c0f80201da0080058503110a00c3c3701c08400203100e1555030b0300084821400f0084c040002c600030900e0b1820300d0400f2031291a10624101050380454480942900c0031101280c9404005007207130428000707640324201c191401c40c00c0891b00041e201c50721503080d2001e80a40000101c4111552441216440b407440b085800340d001c560300d007401004141c0210030b030207009034074002054007580b1a00402c40c0284207180202007c8550800c2e84401e039101412802c24020030981c005080d01481c000742020241d803c024607120728041640010b00c1000411290080d040715042040107250426521011504403c407010402c2c130302 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 590437769 1250 590436519 590436521
    0x1092f0706050415181e15020c0a110103020c0a020405090312041202010515130f060f0b0904050615030c090a0e13211d0a1505071115070303020c01 65
    0x2014024150341e051904000a003c00030f900c2d604c0b00780307040c0e0701000300310030710341c030072450110203060040844c01c0c0b5543e54600c000c582124503850307a0144c0e100a551660a00340302c03040740c2c08079401c200c0300e400080740c0f0707402c1c41000e84850040c031500b03003425403411400403165a00e6030301c00321000344110350301d0000c81c2040108109444001c07021210311007a41c24281424280e003000c6004a00042d801c4c17000081d4403120b4240801da290f0400341c200c014150581d0f040f480504044002158080d03a1074000040d8540400d54034801071400d00803040d0390300030010510040e40c1000308924080c1441616440051074401c2c103c07a07000a4440f02152103a40c80800a4a2141150720800c0c601d684142070010000e20803020190f03003031013124420109800e4012200c19805e085d462140800c00603030031071403400d2490b804045044001030101e0320444d200c0168240d240c665820900000360040344c0c000070080340e00b00e050003a000072240140a440d096242d00c03c18401c0714001400c240e0041409031030640b003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 590439019 1250 590437769 590437777
    0x90510030506010e0f061008010b0a0e040606180e0907051e10111c0e060c0705030a060c0f0302040305071418011e09091a18010501060504050901092f 66
    0x20220581c0c2d11960341e444070107460707401650b5a456000da24800702d5424a801101e0341041a5141c440015580c40d001070712005410041103c0180001c5d60f6045040b40d41e5031142c0f1003d000d0030740340c440765040d540c448200702c00c1954119445c08080d40c0c0601a5000d03000400c1c4080743c104580c0c0c40003050041d50000141c180ca6154907802064000c94101c3e4140c104000450f015031000c2250b201051040e9107040c00c0c03890301442d00124011190f090042c0c2081d0380144a0390601d241100c400a56644c00719182010100b002d681140c0c1d0b03280740d801100e91004504c86088160b20f8103609003030440e01c80b1925503074944034a00042d01810701c10b40160700c800f19900302d51542ea200c80f4041d9170352442008a08842d691001a01d4042d41002041801080c03040c0c00286400c070401c000011070150342415500c2010300180e0b040d501d04461101040c4007402554003a16607030795442e813a28640010f00405102c180c00c040f020038209800060307004090303156000e00a84ca0805017007203030070881c40400c1a00c1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 590440269 1250 590439019 590439023
    0xf0c05091806010c0c090207060e0c010f080a0e060f07021c02150a0f020703090f0f030b01030f03090305120a02010b0907020a121b0804050f0d0f0b040213050f0f1f09051003 76
    0x3203585d0b001030402c80550140c01d0450046070107202c03212005d100c0c26264118007107001e001c502c04003400b2007043c1c0728141141e40254001c800042c00c49882c12210300d010411540c42800841160400140345e134180440c1252101c0c4075818041b16140f40e801035200c18024030b15071103c0441c0c40c00500388030002e811440c1c140c421505c0c2155960200e040c010b10002030350159190f4030510000c0003403560400d1140000b01c0340c000314406c205034216603403aa114500c5003c10780402a408801001007041070043c0e47e51104002e90641d5120341c0814080e0a44640d09a42c9104094140401c0001030300410b0b50303034405d6403216600c018031800c0303141501ca440c1c00501030a5400340c400f40120030084480010000d45078200ca441c404040240c081180800318014014803141011030480c0000d003620b208140c00c24801041010600d070314403a980c1c1107850403102045004000824091184404510260807040c0000313a039050414a000301c1070510b24034419100a1903442c0e0000340c415408021020183d5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 590441519 1250 590440269 590440283
    0x90420160f020a03030c03090803030105030a0212010b09100f1d06010e040e1009030207230108040f0206130e130b01051c0503071110050a0207151106010602010f0c05091806010c 78
    0xd8136805c000788040c1c0c0d040400c80c0850145040450148400800d0728102c030801801465a42141d42c03d10111207812414a40036640714405c00b5043c0da56000b031b9034400c032511903445030f05030310b801410340b84081142c0c004201c0c44000540071429100b80c012242e0700140a081c20006d00c5440d202240041c41ea60b04608114090040711807a0140590003481d41d150190342140c1000d0b45600b001403e0300c0308240c0441d011402d40d070592415502030b08003182d20501501c941000c0f241e641e00420125840069442c2e17510b03001c0c0303009001c400d03181454140c10480e00f5920300383c6a000c55846c1040b02c0740c10701a036481440010328916010558603102040d584c0e00c40107403a00c5214a10700031000344202c01c40e0501c5242101003130718199208805883c400c0d00554010b01030f55181c210711000080703110303801104200e58110103405884040080c0c0b8002c14bd80d42c0005402e0380101080022220301c0c008800400604002c4030410703170303201e200300c403a0505080716414141e265800161a11503034900001c20507 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 590442769 1250 590441519 590441539
    0x9091a0105031b03160b0c010f0e101d060703021b0114150d05032d1309020306010504150206190b0a05120c0a2301050408101109060c03090420160f02 66
    0x19111b0050244c2580000003401440001103502d000c0d0381120018114a50001000209a104c0c54115040245042800c000b000024a10301810800c04803450400b117038000441020940c1c0b040c04400b200744410b0020480b03401c44c9000c0e500c0c21a005014000c10f14000c0c3c5807008981d4071040f010440305c0e0701c40c04981d600c200c2036070310b01b241c1c07000c0420032103d03542886068540b8088140440f00444011540c0704500d9080c26160002904042c1401d41002418000424000780315030446d2072040e00d42d0020030203842d01c481420641070510a620710802d05090070f00c0401e84a450307814054400807554805000020b0920600e00300c691201140d1000040e1030000740003082041902c05000600c018080740032a40b00103480c10721451007008019440100c607040315669660207040d108201c06030390b615101d2040001401034004e0309080c0c0b02500001110383d0546041e00c101410200d0391480400062214400c1c0085400b41d00ca0b51400031072b2008030142004000e80008071115401040e00c02d403 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 590444019 1250 590442769 590442779
    0x6050405030a060c140d1a10081f0b030a15150203121b12010e280b0f04020406050406030e0705010c1502070615150221070201170109091a0105031b0316 67
    0x10300528461140020b07046140303203103181400080555041920703100d0f168180c031080300141e450802c030048030340c50703012b00c90001c590b040c90003000b076000308003030000480c0f0209071014100505c0b42940c03001c44000b04c001401c808598010059411000c00311020388401d60790680c298811100002481340c0500d070000e20f41000107000c004140c1680d040f00e0035020240c1e81d4420040c031040112030903034450803901c48000c0c0c40c2c403803c0d0461200340ea070107410320761504444800b0400fa41c000703400c0000403417004613040c800103034503100c0c14840084100061400a180c440068109925180050040544020348086040e80c43c0c04490700304da80140200180043d40824034060030356802040301501e814041405414800941d102e020b030f50304c083e1840b08114011140086d079020410881c180300c0c0e269800100c1c40d540c80f5040e03009019100d4040b41140c030350b03d801d072800320307070030506004290700200144140e44001074182006220031851280040200c00064900a008080c02e0303c0f40d9180c03940455 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 590445269 1250 590444019 590444021
    0x1b031e05040317030c030c070f060e06061c2a18050105010f05030f010512010b09100f08030c0d080c0d020d0b01031503020303070f1b0803040303020706050405030a060c140d 76
    0x1c1103030700a0240d014615110700c00140284001d6401804651003400032490410f8241f00411300c0a1158410100c07040303540d038a034815030705444001007207a000042080801d0414007920241101700c504c005a030b1201c107644041c0c08011244104c001000034101c10010480f0030f154000c0604403144116902040361035184000d0807003401142c1c0060300c08000d003002c031030007001682d018200448103280c0c01d0f82000d040c00742814001038018210341d02c81c81c1083c1c084d1070305c00c0014020010700e10b25040050800000c0000b020499003c02c0382d0354410040282c1d540381c04074400c400301c00c061500170b40075143c2e803400280c2401145651014075200003102103034003109030b100814000080e04c3c01d00c00107002310a03008682289200280d01078204000c60000504114803a0f41420b1207441c4000120824490314511003205030003180e1190b00c0041c0c1801855010080a0010400751904a02c1d203810100032945520381311034002d00309034403108824081c50052400b64a55200c00c6005a01c400014203104 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 590446519 1250 590445269 590445277
    0x20a170303011d190908040911030a0506030c010801140a0e0106030e0d140f0f07080f0c0c0d1e0f120210060b09030c0918030703050a030f06061b031e05 67
    0x10b0501c04018800034007036424580080c841e01355034001802c1000c8058840340944000142154200410000451440c882c1d02c51135025200740200c0c3c0345c9078905409843c00700e51002d40303040c0c842d42c8079551b526031680c1e000a290b41500c5103401c80030605080003010038482c801c01d0b00085100c110300e400216090b68581d0103003d4000c1560200c2c1c1500e0030a200660780300d0080c9840c5d0050040c04c120801c4001043d1004100000604c88041d1811100d0744076464182c000d5144041038a00006203c0e08a9800300010200d0304811112200d81c00b019a64090000606403000d00c09280154040018800304e5a116085190006800d9004507600c5100a4980d090003c400121a10b070000200762941a40c050313402035031000d001071600f82069001c00240000041c4404650704280d0b44007042c942d418405009481c0c4a40c8031242c403074580346005000e64801c08a07449085107411000c224040e480451207150702c0704100102284601c49c00c3c21603203c410444140c40c0012584100300740198000020 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 590447769 1250 590446519 590446529
    0x20d030306051c050d09260304240207090b060d0513062409091a0c0d0207030c0215030f0103030e06130308090102060c03250e0d110a06050f16020a17030301 69
    0x1ea0320341c402400d4150344101a0340101c003880e901440c000a40781301160601521f20112508982c101a41c900010040b41c101500e51001c0c09001c0b221800d070260100480c101904283c2c03401d101074955140800c000b805107001c00030701e01c1e46a070301003000c0c0c8015282c4190080d402c0300b01441442d803180c040c0440e080c005101441607488036080014801001e10886014940c80302000c80c000d4545480450b000e00003410700002d6090421040c11a9095440104500c506c25101e06a0f031050600405c52007195014164080d04810020006014080800c003030540754541054500880f01c400480c07281d0040030b040b0504250510804801d00015401800401400342e01f160565070751b220b04a0403e000c240c44080e00600587c4072030032108030521820750414540d01c0c00d0740000101030001240016101002d40795003050581c040d20318181b0907070050140070507041041c0b030003180ca01d01c000305124202d80000c4000f580e8580000719503440900c17200401c440c20007422425056045c168680d4828810 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 590449019 1250 590447769 590447773
    0x1090311011e0c05040506040618050d1e1b08070312030623031f0f110a050f0d020904050f1608070906031a1e0a05041503020d030306051c05 62
    0x280c855003a01401a590001d49030220001c1c108400808480a4070070369464a051204c10300001c40ca0b0707201c1c03034042c04c0145400c0e0b0b2008044114801038000d40710799a00b103140915020340c0b441c0f0100d182d60010603024070200342660b001007600d09100d050421803e5041d055040e00c0000000c0e034040020741541500e0040c9103030340703041c040c00006500325130291003a4010300400404240582290180d1304050f0ba0014059072899028110020034000b480c1d0209440e017a030380c0007001202d260501c201c12829500c2c418030780c07814440300006840e03402600c010384142480020800d035042015010784951000240c000d0089003080040060001c00880f8000496045491584100e0b403140d0749090140ca010b8944002160501034128081c04854085502c070714109120f000da15190017505d00383c21810080c04c00c4061003e0b0007040804107070f0381e005520850801c80c004241040352082101200e50450708012070103c64901a005881550700c8564000340d6031327904d90000400a00390304001071003042 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 590450269 1250 590449019 590449037
    0x1207030c0504060e01300308041a0c0301050f0d0c0e07110102040302090601032307050405010914102001050a050a0b01030212041b0e1006080c030108150402010e060c010903 76
    0x1c140300440b00113115140000c49158010820403c088032048058400110403000600c100e5a040c080e201549404400190605082105004079120b02c2d2411040450043e0b1503820180c02054007400107004084c81918651a180e84a40d03c0340ca03070160807a4442c40400a481c1d0b03d1480b08071660044800c40c0210b982c12040c211850710610231101640d03030040a9103002e0b00c4020044004084200d13440c6d0000c00c210707103400500d401e4000700e0303803141c0641c0d2355855565051000040207400154804410800208450480c0d03540d58211030040c0c003400c3c6402c2e034030368544031031401d490000001e031110b26518210a0262010540d04843d105510680d402d004246084c00114100e11a03005614414200d1f18081000a001800240a43d0745910204a55540c8034102112800810f480c020001003174840d042095540040d2083c6e4070081905d43c460466142c40ca81d56241e5045c4044102005a03d8000504580c002c00c1ca81d80e00d100c024088030b40b607811180d0082d00802c2410000d07800310302110 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 590451519 1250 590450269 590450279
    0xa030e07080a06020706020723120a020a0b1e0a0c0306171b0307261603020114130b0309210a0c0b04020d05190317060a150c021207030c 60
    0x22100215503407180100801506522000025005540b045925a400700030102c040b0b4054568448141a15043c181545440300ca085181c0114003891680400d03080c0880c1c6146d94000c2003010100c0d4100c0340c0365103955103000114418907019481c40e12004011000e110209946502c000032090803900c003000f5141c1c680303c0f290b4040e800070703805110507408503011150210341503008071041c0402030101c0c0c12550702c45800314070903020040c15030340c1d01d101c0c003c10500780581042404000b201c03000031740c81c207541942c000801080c443c00044001c11000aa0704c01c04402c030b00c0e500b0000b404903149007900c5c0e05002503121340704d05440d01d21803040c2c80c0140035030303401428090840e0b54100441c0c54403400d4a065a46203050f65400030300a0382e00925450096000c20800e1000303400641003105e00251000e1a40b501601032032424035041c1e00b00310200100162521a904402c0585a1000c0c091101e8003280340b086400c0803042200039040350105480ca425803a0001d914002c1c2c0384100d070900005a12a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 590452769 1250 590451519 590451523
    0x1030c170102040e01050d02130204060c021801031106130306181b0e06040e0c150301081614010804021c05071703030c07110112020c0a0b0601030b030a030e1c080a030e 74
    0xd0b02641050104e9840100110b140000070040001d1015009182c4030305102500000c07a0440c2d4002d801060302000f15204614002440884040c441c4003499150350440d11a0110209501d031210700541002030b41c00c41400316602c185004542c0100305103d0f81c9003400e25402c0d4190007030300c1190f01f0f000400352014041c11042c1600c0a0300c25125201180c0e6503103d0810014102081c2001d81034001c800a001d40c584a48501a4010300d503491401e1356940340821140c41c2c4201420410100c2d640c805061281c0300720001c00c41c16601d030034a809080303510350b8000110030036030071544015615402c845c403004004001c101c2400f16940c805094210304002000e464580c40f04582c0380080c04010000c3c90002075100c01e8801d903103070741894018140608440004100d030300212558003d644082da40d10304102c0c0490310b00350b00800a10f010700c81d85124602207541c0310364065000301400080c02a00c030b11901c8026212003000351261a8003c50100343c03e02d0403482c3c0c098409500042d041c001080d81c00000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 590454019 1250 590452769 590452777
    0xc0c0617130b1506040819050706050c070b071e03030c0806010e030a060f14040602040504050a2f190507050c0d05061821030603070504201e0301030c170102 69
    0x40c803010020343d505001514405109180c0b254000d90500c0041204a01048011014500030800c25900401c80c20028500003280d4046030030080104100f207209e60300410035001f202e00b00030140340c41d01c00c1440c0815106c1c64203000c1d81c0704421011600d100f4143e06810080320124140c440c218a51074890045401c1c072041c5161580680c0a43c80440010302d480c4d0148042000d0760a0000e0390b44d914010844c2c0c11041a2800e40c2c05036000b00f030030300c0346103840d204180e004816120104140194000400103250003403903a499a40700d441c14181d03031000d20408441c0c40070350102c000d00c02d01d1442e031000351032900900406d580d03030b200b040a154141c1c141107000381141a00300000342065590040c2404941c10403104142da40d015245100302c0c0b24241c4501c070101c1144911036680c0b070f4941381062501d0030740d059010511641c105000c0361901808070f404102070240c011103003603a03500200031151110f1400348640e01300c90000030001042c41488443c0c1802d442c040c070780d1040706010b0016111f00340c3c01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 590455269 1250 590454019 590454023
    0xd031109030d20120307110313060507020f130e010e070e040f060e03190e040b06090f06090a03060b01080a09030e101701030b012d090c0c0c061713 65
    0x2010100c2044164080e4039450710183c10001584020074105200b0b03070902c030185242c000d046601106220781680c21081c542811846e8100031800c0c0483c42880701801c04c0340d8492401030050000d0b2241c2503403200ca4590b4820100500600109841144420000e0460a03000a1294603100210000c2031002c1030601c04c55003000c0c03403c1c5081d12a600c0380c0f0508900d030703081150015030fa0814840c40701e00c1400604081c02c01c80801c80c3e45900d4a160242c500300c080603066200340d2400d01200c0d0f840d034607902604e1808000791418030090301c1003404242244203807403c0c2940301901c1c400010400c44103400c5008148021790360528107480c0c101c20701041d103200d1400100460100790642c083c90a0080840c4419001442d1905803c403400c00c1010b0066002e81050302d0f1031702120700502c42c0320b40400705408481311000e11894982d2050036011100c00c1140a4500195280c094034510f440c807c0c21841d0701650452800c82d02150380d40c1c0041d2403580e4134072101c0b000718404000105000d0140c003501401d00c1d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 590456519 1250 590455269 590455273
    0x10914011d10030c06020d110105040c06120e01021b0f0313050402030a0f09060509010b01020f120313120c060501060813173105030109050319020715020d03110903 72
    0x100c400700c1c0000d88040c0102260300c2450b84600010100d081c554905008003410740280c454442407000c01001d0310103880c004144c1d0307030400c014000050203d56150b0119000d070301d0031030326904420481c00c000d0040700c901000760398004201100303902c4c2c014a029200c405801c2c102c0c1c44219082800b02c2e242d02880d071441600c4801d0080411181c10250001c0d0f0348002030b04d40c0001c12856400c6440115068000103a40c40380d501c82c1004200d034024420802118401d0000f009402442c40c0c00d41c1d9202403054a40301e44540c040b020440ea000d480882c400503c0e071003840c0d01040303003180100600e502c4c0664416503485007020700018442d8001c2d01c1c1203003d0009180035036162003658840065401c02404062180c080412410b100340768541c1058880d03425481100c049045400c0441e01c40b20542c0e04540d100b40d14080b10100060b030000100c6907140c2c00c0300307220000703a00e000000341d090103910360025a00a00741001900c140e50f003c10f00324003c04107610708102d07048441031200c01d140103880c5099019 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 590457769 1250 590456519 590456549
    0x91801080607321218010f021c0b0d020d050307030f0302160305030709030b1303270e100306021305011b03020d03020d2306180912030702030d050f01091401 69
    0x40c0030240e404801c160032952028984203c808070100c800c081190512007030f28558844658445c800c3c0034000c140c3c0b010240c15820319055180388000140c850501824055540041241c113840300500b20500b030b6002400d007602d008450401c591a40c0c00030104a000540c900c43c50307001d50b80a4070a0700c1807034010107504860a585940d0595142e880a040303941070050f40d407000400185000c000900c00c0030a101c3c48080c0054510f80600310f0b812421100c80410104003448240b41000c064141c111000b4039000d41d1252194804600d000005030005802c00380001929111040d400644100300c440c2070341c0d60072111140300c1400c1100030290700c004005030070458900901f03d01c2500030b0b1810b0161200700103001c10030f620346075003680359408003014420038440410019150004003403d011000481e180c05525010b00e03101d84400400c00104011708000c000b00d00418400c2054031480480c01200b0070040c01e02000c144001802440703000d2805003001c411070090400b11060358100c4094a00c0003120b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 590459019 1250 590457769 590457827
    0xf04030309030e0a0b04090609090b040609170d02070209010b09030a0605070e0d0f1a160c030e130501030c05180a0902180415060e0412030b0303091801080607 70
    0x29101d2044290200200d031542c0005940e40c03100c52200604d4080a420707551803504008009030782455010440403403802d84d181c80460545688143d00c5076000307500258814251405440c0c0d05800300701c4159244d0041403503641d014144d4005d100c654000c403914200c80c0e82c0c8815401151059402e074079010b8010501840002e901038110603041105d030300301082824126400728207000500001030361703420f0062900c60b091008007814400700394600301030010300d40307085050f441400c401d41411404002c42c2e50846001e26101c0c3e1101d618514009060030440300d8200c14910280800b804140c2d1016600700d8001103500d4000e01100c0391080800d22540d465541314148401001d240006036000000143e514507440f0035100720500c590b03c1014000d40000c50b03411510b04541040e04102d4110f9603817400c0c03101144030030000c00444025440c0100b01d021340f4001180c11406000b00f1207130004100b45442d0b07138400d509200071307040c2c40c59801100c540c1c3c0c1d10610121082241d41c107504031a910081c225183c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 590460269 1250 590459019 590459021
    0x90a081905101b1107080d09030c0b07020a03031202090915040f0507020a141219020c0109030209040b100e0702070501020f0c150a02010905070e06030d02060105091f0302030105010e04030f02060f040303 89
    0x261300c031058065030718650351403042e01d0505000001c10700000e90900070905c100881d1083c0c0b44080e2000309070490800740103034082034690300b0500026003800041e80c2d60912400741d5404481542c0009401c60085043c490745041586070520301d40c620442c00c4c42525110441144180d6100d4000780d8000d0038044182e03250100c050041c01603154085c0103660315070345602600d03402408a4100b4034443c00610448540c005d0500280e480c5a90402c0744042080000da600c1082040e0000d0704684810103c0c5c403503801041c8082e0b681d80c014060410401d003003000003600850b80382c00712030082e0203407440c04806000742034603801e20502269202558111500e512011000500030400c018000000c0f4609282c898030310b0034046034441040c0b40300c418104102d50405020382040101c15000400e00703541400000380300c0c902c0041074020b01c50000b40d410306004007400800f8001f15000307002041556101e40c10f1005016040317030240c01043d541c14040305c00f1480050350610030026403240348490341711650110 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 590461519 1250 590460269 590460287
    0xc0306150d02120a0b07140309060103060c20060105181006050703020a1a07120c0215060613230d2607060c08010e1506040b090a081905101b 62
    0x80c2c0c0041c0e084500c80d43d4010208089102c240c0165506525403134202030043c092000740c0c24041c6080e00c24002d00140e208005000340c1520b600601c0842c0c14200b40c2d404807100741404c00c08400d281d004049400341000c0200d05c20b41a90400d88207400e0321011200e104130150340c155110540d1121541080200c03070f10450251030480c1c801d10640d442c0007496100e00880016400d015540d84085006006400340c01c079188070031902c00351200340910411400080d465031108000180f09030016400590265250801c542c0498080b44111180d1900c46030020132010b244904500283e40a40301d80681d407030900004a140350740446040008841d16002c0c42c2034000364456940882004d0008200241c000c2c098040740c228070756100c004a6140800d02e55070080003801500d20070803c82d444101d1925a001101d040d5054100030a5032031080c0d03000b25400c1041507000451500075030b049034030300e80c055022182d85540113104442546505445840c202c40408443d45a41411506451794a47c0214815 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 590462769 1250 590461519 590461523
    0x27020d02010e0d150c110a1101180609080601090605030307060f0603021f080a0608190206040e0106120c05040509070c0c05100314090f03040501050c030405210c0306150d 75
    0x1280703024088801003007032500d03001812141c030b07140d51134903100070b118911400f04000e07001c0c0340841c0000e0b40c8100a40d200c01e800076002c0c0c80c59998090402c86640a195888010000381d9850100d0039030390000107203590b00500805400f0700032040000341c0300e00c4030300505040c1e0300000c001c0c500c1c1041c0c0d59200c400510101020701c40d11a2034010000150741d039a00100701011000b07042035003080d024503006049980c0103080040c1d403480c00c4406d00880000007505891440c0003107030404100c01034000200030707000300e50000e090086800c00105800b64001d14030210300341c030039800344841000d1400940380c601850196a070031a0f441c800007a043c502c50401c1202c3c4900a04c0c40704032003915074000c40c0800c40303801680303404a130f03c41903444480050005034580c480d8109000d41641c81034804082d8030707803003103200385410000c0c0441d40038515403082c01194001c10005102030090802420710000803501c5201100e242e002d2a80410f100e170402045403489903884492080314003031307031000300003d10341400d0003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 590464019 1250 590462769 590462777
    0xa110111040603020a02100e0c061b1e0601090618050a09060e0705210303041112011406010908010c090306110c03030f0105040c050f032205060f0a27020d0201 70
    0x902050311568401480540407607078001d680c5040c00300001e85040d804e01c44208542d0318145441807600000710316035070100021101c041d82e580000b4101d4415248012a50166028000112080b4401010310b0b459052280c0143e800c50307aa5440724030100c1d10107206180c940b100c0080c0721a002525940030f1544001c8540c40081d460301907468000484016161108c0950301c181401d1060307203000c00601c616801d4800103e10740c103100c82015500c2e400040d2004000c4660348005540a40d03c0049454442050710000c00c2841642c0c16241d230104402d503902801310b10400408182d02c0c1d0f045c01282215240c030b8807101c07042072a599800d0014603040c00c9091102c5024008030750482c0f81400114080d10030303150415103550400341040101e0700d484865000f4040e04100d40032104212006483d0311070307038511f08229170b50078410042c03070351041414006100340160001c2100140010f070100707000d054140401c025681c0c01da900f2071b400c00851010740c152044111201d50051900e03c100f55182881858 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 590465269 1250 590464019 590464031
    0x1a0a03050417072a0b0906031005030f0304031a06010c120201020f120612030304030c0807020a03060c0201050a050105010f0909020c0c0316030b0f010302010e0d170c07030b1b0a1101 80
    0x1902450f6000310f001100c3c0c1c003090124260481200c1c506a1400340038060140349914900b140f5550b5030720402d54441d006220100c000346140b00318020b00c0c40100300c054141d98009500b035000ca601c0e940700380021610052000d21001280c1440d03a4921b1041e42d0684400301c800d4490b4445001900c2107a0b451421507408029087c503071034000d00036000b000b909100044042c204502002010b40c1199044513540d441441000701007907001202955442e080580c056940c2c5083c0041005010300f5080036086504002120042507815404648900540b14081090340d88900045400c0213000500000007000c4840510180e00d8940c02004594284001c1301c5d0f8601281002c42d0030440181d04c401d41d581d00500c000c00a000c0c0c1e00400350350105880050720341c01c0d81190b0018003041c421b014040d0107840d600b4107400821101003142c00118001c070014603110440001045c0d61001103000c202e610300004004a4503104c1d851080018803240c485400e0304000400608075020001160400c0d025901d0761 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 590466519 1250 590465269 590465303
    0x13090203010615090b030f0c0c03042102040506030106030b0105040f060801060e091002090d1e0b04060e070602030405091816061706031f0e031b010b04061a0a030504 73
    0x44100d2000308404804070103c541c0c00940038082c02880e40c04040c140004008126501c1502030009901005100b1103a4031040c3c1d202d8854a98000c07a045070034034201c50900a01e08020001001c1c070300c60303c01c40f0240405d941c3c0409042c00c1e80c0781403200800704100c074070041c811842c0c26002480003144480f40002d20716511040c440c00c0d50029480988440402418440448014006020301042110702945000c02c9030012681c40002e041e80503229281c0c41c05c40c03030701e4a42942000342c0c01c142c0040c2d401a1904041c01c0041c005c040d4001c8101e260302c1100000584140003009440843d00018004011071703a0311803810510714032615025000740201c41e800903502280c100e224010b45800e43d914903020224030302140000c2c00141209129500032040c4021031740d174503041008459403100d40450901c1860300030914501a00b4101d01c403640d0f4511030003015072415030002c40024002c0b0f5045c44140e54989001c0011641070003640c00003501008811049402604001d0b0010711914003820546594 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 590467625 1106 590466519 590466521
    0x3020106092703211a0312040f05100504150e010e0102070e060d050c120606030607110d0311090604031b0608010302012705061606060506090a0306240e01090c0c0c051309020301 78
    0x1007441242d200d4490740075200143b40b0a6041e40c10002e4500010b0807011049828030b001a8044070b03807184070341c0700081a404032541e541403c80107498078400d203c1c00b001140419150703441038111802d01521811040c0d03030102c0035000504050b0601d4020035007040303406001d00d01000060003481110076408100303802c40c064107041c00501d0000c41324611001d40140759420764400c0c404a000803c0c40800d105400140101d160419400744d140c16065400020a01000e400982c056200034520035032503c0d00b1042007800480304581c1a903c0c00042d0712a44045a130118000034074010004000c0d89002c0d1a010b04811141e65043c0751040c008078150406520001c2c01d82916000c0c0c0113080d0640201070340c030740e0141034032050001d40c46400c800d100000078843c100d9164074214920002c01d128400300c1c4d170400d5200c114003003114501010820325858550084003c03da0300c060030001640d00f = true := by decide +kernel

theorem cover : BRFrame.Cov 590287769 590467625 := by
  have h0 := BRFrame.cov_init 590287769
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 590287769 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 590287769 ≤ n) (h2 : n < 590467625) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
