-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4188
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:49:06.702427+00:00
-- url     : https://prove2.me/submissions/c90d0bb8-56ac-4d1b-a395-fc36447f4ade

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 753057553 ≤ n < 753237410 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 753058803 1250 753057553 753057593
    0x160e061c0f020f07051009030207060c0510050f070806010306050d11040f0501120311031213170c0706110607020c0d1a0f150d080a11070b0d1e0506060f07 68
    0xc0d03002242e6103083e441e003010713000355010b014681d541000907085004409003641c2c9030f07028040d29030500200f82c6505c4010720041d0b0b000c0c407601020302010109486018019040ca00d00308400b454200c50040c107009006140030704060400c0010411501c9074079004d080b050340540c04911207400500481c0013005d00d402104c101702d0401c1d000140300103142c807401d00d903603019a0b1a103140c03e1000c005569244074a60b0010316007040c403000100050091892030340c00700c0c45108400321105200c1150003954011110714100d41e00845000c024064112944100c02d0a442c00900b410b8541000080d41712420004202c5c0228001441401080100001c4102004903010051b220381050403e4050a032800c44050400d142488043c400303a107001c0043c451a00d40c000c26103403411419550840754013003100380e114200d00c41c00c040800c2096401000d441407460310f01001072080202d14221038904800c07964501c11701d19041c24060291210f000711a01c1c0c0c040e030100f003540c1d14002d14064600203104800000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 753060053 1250 753058803 753058807
    0x607060908030615040e040206090409020414100f03052d07090633050f13080f01150b0d09080d02030a052d0610140301030b160e061c0f02 61
    0x10800c503000780514003400054650070310554480800b001030384503e0003842036905800d03001a006241c09030041411030009080882c00b20940e6022405544a02c07070031840304c1c05071400f040715840810030008020702508402c01c030550b146444450300c4042680100401d441c25010300c8500c103d0310000c40c501e58030120f0898140725510007485000304030f14012036408110ba030f0a24070b0803400c20050040301e000c4814407100c081d4000102510240d2000102010800051040b20440c0155200400080280801a2201d503081300b0356030342144e25584010401d007000580502240440f503044d9401c100300381100040f040c980e030400740e03100e0042c10400c07402c03140000204125506190000c030301a0702e1005041d80d500c1c20781008134142120000485410100220008a4616111f80e484003a00c40f58201600d86107600002c0307088544c8260001e8591020800900014465105010300e002d065442c2c00c03205601075070b000502c04d10a8900301d40d840840118044495080381d40140c0ca00804407030115 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 753061303 1250 753060053 753060071
    0xf110114040803040608161706120d0210050a09030906081b0a0c1101020706021f0209120d020c03071805070315150e0f3015061f050d0b060706 63
    0x640c3c2c2d0740f245c0180000201c1a0011410701001a074805607000003984640105519100301d5a906800080c8034551050085082c09000c0f01d050005400c603244990141900700d802c40c4444060700c0010b0980745ca11071500c0d501c140440d5000c2080720a96000340703885c460b241c0b105080181c81910070141412901000141d40c664603400424590324144110720b1013400080500041e43c4501c00d03442000050380203104280c103001180d1425081106074600c00506001149012400a110444c02c54013254862224581b0360358041002301c01c05e031401c400400202e414800c5070000b05082c110340035443e540728400b082d03c01e07006c0d4001d00340400c4202c07080180306030b81d40d00482546d00404180004600c0110038800c9a003001035546505100242440760380ba0b042d4a40440b090b10040403d421403002c0030b051030b1149106000c00014070345034901000c0c107030404104108034080d00c02c21a841018020303074024543c40c2c1290503964200b000800c00140390082101140c150b200703841000381428507203401c2c1d03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 753062553 1250 753061303 753061319
    0x2030a2a090f050a062d0f11010507050315060705010e070303090f14040e0c30011a0123040b0403140d0e04020a02071703030f011e0905270106210f11011404 69
    0x9150307d00d09030f41c84681c0c1e11208a0300a080700e2058507075200141081001030500000200e03007d04000d00540190b25240d1191512421105540d40c0c0180a030041c0d02c040040c164081c90b00c0c0041d10211501d10101c0b45062128400ba45000003414012030b1104040794580d6400e009400d0510f00c0500100d1080b0f4500005120315807810318226203d408841961b0142c520501c90001d203c0020b800301401e15811000550358001030300080d0198046440a43d9072910450380503000806e0780c0480e140e15076045103000140b02030101c0c0300c6440b6070702200f82000c0880e070224410004c0c000a940c0143c0d40d0326503030400ca05000c2140c02075041042440303031201e0542c034000000d51290003c0340c0c0200d10b590b01d440780170404821744401d00c0e50380d044140d81801140e40590095410102014210303100090126800307103c0150907440c82003a9544490130040d44050302c0742850305c0c1000140038003648041f40c2e944040460301400c003178010100760302d0301f0b0102d07405130782d81c0811501081286a01e45654000c4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 753063803 1250 753062553 753062567
    0x150503130804030807032d0e0f060408120403020301140408030a2703020307150b22020d061202131815090602220b03100902030a2a090f050a062d 64
    0x780c401021000d0b0f810200f8000c201422205070707c0c041e6a4400c40e8050001009119a1517141d41d5501c40740070440003c100e102005414001203c940b045920350b40b07980105421200e500c0311903004003072200d080200064680c011aa400b44030032070300007009103c00c2203a46002c01e144948085002142d0501c8061540020291403c0c80c458003159041402c90195042521501c68515421420811001031480340a0941984800300918010b05100103080032400f66242a40405543e681e14a4040c3c00e5041103511a107232a251000140a00691607000180c400c40b0707090090112292403010311480041d54100c001c050303170007401c10740d191040240c0321100d41c461280d8441d1041f81100d000902251800c06580c441e5441c14940c000e81c1f49410b80c0c0601a50004080d04182e9548007140c0b01311003d20642000c03440c03911020301245240300070000d4182c1901d90403401818860030400c00842d5a0034080c3d07410b4400502c2c00d036441d04003050b4000f904140031106804008440812000e001e507001c85 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 753065053 1250 753063803 753063827
    0x201060911130b0f121305011b020f0f03040b09030c060703090f12170901021504030f0e0316290c010207170a0c020f0d0f0c050103050115050313080403080703 70
    0x185400c425030310f01682070a8891080d454403821004e002d504031a0040c07208280d4002c000684038110000745a0b600360031103039800561404044120384007045194104002d140d0f20860100428054465440c50740d540e003d1413040c20cc00c050001002c0c0340c2e41d01d09000c0d20b0480d0402070311207529160307640380161100b400c41c05024008008400005104c10300c0315440c03048660410380c0c1101c1e6a5000048001310791148984606500c1084d4a141c001c8441090701031145020f96504003180c42a403400074400300c41920902d209521044500002400034081c5074211400f444000074980c583c011800ca440440c1c00818140180100302c050720341f0720640003014034511590a00032056030440110304d840c003491007205d00140c2604031302801420000c04040004000030204121410140d444444c00a160101203c0214494804000c6543c050051a001d0058041064984001c0d008000c005020003000d0117042120b0406481c140194941145d010b540c010381c00076500c00646c10060100d00090f8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 753066303 1250 753065053 753065077
    0xf041205040b0301090234030c0204060302031e06133815040605011403060d03030605030d120e060103020303121009020c0a0c0608061309051203010e040c080d050a0f0201060911 78
    0x883c54800c075000340a040b000d880040c02c2030120401f01d5403001c6032107514015003282c100741d40d1400400565810815107810902c0c1070b044c004124044520241040e1001e010716031005501c1040c2c00028000540300788880c4400c65207a10180540b081400c24010300305010409503040398207005240e100c54460050351202980d050100568900045401c4004142001c4a0361414400700c1c83c1403400f5080640403d0003450b020805985900010f820301c1030841d00803020410500d60036008003098080c8109420090004e41165803560300443e0f2640704107103408041410901c00900c0300c002c08110760029042444045465241c8a051140e0b40d00000340d041c1c50300d5044c18400030780c241c400d40515216000240204c0c080304094051040508000b00046400f400791006a50700300400c0d81c051030003003041c04c4046245050504052003c2c450f40d402040c2c554001001428400d03800000300c03410055146030610301207912a0303040f401003589400210700b00d810710383d550f41d80500c5071014084246200d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 753067553 1250 753066303 753066337
    0x21090105091903050a0905030d09080c09010308030c0c190b191104060513031b0509010815040210050d1a100306082104030f081206090f041205040b03010902 69
    0x10030546603541c19440307030099950b5000018000000d00c55000740c50940000d0800c1c1d801a5203c0c40080d0510900041d20707030014803c402c0070843c0e03c00400007984034540030f8030540129419a220f40d01544401403400e1804070000440758400f880030080e8031030340c0170703c0380315454220010b02d8090807141040c0c42d241d58918404045040030180c2e48910648000b141d40c0ca203250034a00b070401d40d910780000e030b40c1d822140004e003000004141c0c09040040e00710b003041001242c480c10242085010341043c0c0018059a00c00e44080102c42061002103030010b80490350740c1944844003400b2101445403c020888860034800d2510404c00c1040e40740c180c00704100c0c3c1d064030400104500301c0465400d4030034070780b155000c3c0e03c0101862440e800e000030ba2042410700d5505e0035440f502c0300c0b1100408900108e640c0d4600040040b4070820941406400c031030122521502c0d401d044032036810035000580040c084c00e07040c02103030541502031422200180710b230b0002e81d0346940c0d655404030001e400156010324141c1c00c07 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 753068803 1250 753067553 753067561
    0x613020405030304030230370b1012050109050609060c25051f0e0c03030711031e0c0a050405270102270a06050423010302131e0512190821090105 64
    0x4015a6400700c5912324071526804030150300d030340f0329165014005415080c1190008625445d0081203010380707600036400800c51901c586001880c101c001080100c194001800b4090503441e0784044030301c094200107104016044c0504100800c48440320000c18074806c0c138a41410280001c0044404044d021400300b00c0d00750b001e4811610785000b04000c40d0316810030006400000c08501036410000400350842d0890341d40c1400d507146d09190324108000300d52003c000c0c45160f01e00908400d000c0e203000e072818032031030405420150500c03000c00000d21084001036510095000c095040d6041020300031102c40d25085030b244e40c6164400d030f681190b4091158084c2c00b0032b44078007035021502120301e442c4800740c005001f000119600403007503c0050426408200300c20700c500d03156268802030034400c1c01170118841900241007a401140e44000d002c2c9812056030700e40c0716030118100040040207580480c0382542440c1040caa485030110110060712280340c000210071400d01c0451040103100003c1140c0d881d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 753070053 1250 753068803 753068863
    0x12110d0905100c020307030c0f08120f090703080708031b030118051b030112030e040516120903050a030f0902040c0806012c0112020d050c030613020405030304030230 73
    0x5030b1031006015174810040d00c000030748504a1504030501070b034111b1041c24455035401c001640200504c0c140f0050507018021081000c0f00c4480c0c02042e00001400c44903d1507407541040e00410388040c10ba20000b00028810425401c072146074294103c103603035540d43e150092160400758090000c00b14034030b0b204c00078072240106203040a80310003020443e421a071902001e108102071403003007201000780044001120b80c54078011f45000343c55481807035505089251004150506580c0f044821a041c05c44280200380c200b400c0742d038400305a04d0040766900401801001519a809000390070615004003000ea5a91080c2514001e0100340d9440d220701c661400c041ca01042c004030040020a40a0380d6122203600901c3c6008120040c0305000d42402d55288072101140c07001c0340d004c3c281d60000000c002e070030315102101d074003660742c039400850a1504110100383c0e20b0043d4040203002d2850411402807180c42112603501d1050210741002112020403104c903140d00034184810030010111400c111046 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 753071303 1250 753070053 753070061
    0x2030c151003020f1512070e0d0b0a050a0209060f04050324010b1605100b03061602120c1507020a06050c121f0f060c151b12110d090510 60
    0x101480007005480c80c1103408216642582c5051342d81e01c252205c43d50001045860080e00181c146881c1400d01071074103d0f006070058010b4207030030b0310a2101911603000901c5003000d0325042158250001221b654030110f8000912440040c00d60008002c0360789642c45000800038001c1d03400580503034420101032112104016400820012420902401401000041e201900ea407040c01d40740000442926228141801d10404036502001e403104400b400c039041c10031102e80c004107015540d4000d00b078100e10094841d080e0040ca0061580009425480d142c0100401c443c1d4050380000d070305190602e404060740d90040da0780c0032a012030030100080c48001060302510620403100032400303011f40d2001100c0c2130001d00c2e15078104503440c00c00310120b82c0154048101001d02885d44070085042e416040202c4035080f4203800320781e214280510380b01c045a1030307012910340302c0d40d40c24548070803019240c9500c094a10f00b503107000b526a0124000d00c00da0040d8010040d003038003940569290300d0301c1a02c4a4291 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 753072553 1250 753071303 753071311
    0x60f03290705070f02010903023607120b0d0206030702030c010b01050702100309150c1211341b170c0f1905060403080306010807030b03071710050702030c15 69
    0x3003501800803c002c00e001482a0302d12510524020b01c3c1c0c1900c90780010a407280c0740c20400e041620080781600d4046c90402030030002c2003900800051468070030801882100c1401003c45944c0c1c0300d401c03181460f00d41e0800b500c99141d009092981b2440c1412000350349030040007556401c0d44c24110800465405081215000c80c0c0140507020750400d00309042d8080c1040e14812a075900280e018003404225520445c004083c032642c07184040014005804150b5000921070a403012080202400fa0441c45621351002100124102d440d00c0400c0c070107400d0048840e5001d07090500c0c0480310b07500c40f090240e0460503204080f46400007080a8410160340e500304e1000c0030f400c83d010303204030401481c02d40c00c90b800307000c14509018009600e480c0400d41e0b5400aa004692000012007800740543e0040f25050b402601c41c82c2c02c218000f2002c0010350307075414511841030080700000781900d025909011480c001810150309101030700b81060000d5a03940108194916030080850b0b56200717120a84007203000b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 753073803 1250 753072553 753072557
    0x1120206040603020307020a020d2012060a0902010c05100c0f0c0506061c0c030f1a071b0212011a030f0115090e0102190905030105070305010302010c0308040204060f032907 76
    0x1d050402109a00035800508910190b108121b981c500507610003050722034442c46091b20100e056011a0f011a00200489100307100c0d08054a1104400000048155010000e51808945c0f01c0c418001640c021303800d40005880c0d4014560101440b641640181c42c1000c031681d5115100400500c0484200e060014010100e40242000c00c0d818641106d98a1042034140b10b122000722142c0e03141d00400c2a5640200d8406800d50320103828048001400100e840c1000c52441251030510001032060b10000da14120a406802c00b083c19034480000c030a0070b40103000c1c020088800c860050355020145caa108c54400d01c5201c1e00d0a00b210340c18085d1444410003061025440d40c10300d85184054078030341d90700402d99942440f07075040e08210410346030400e003207684500342820b040400303042c02d5882c02000234007403500f05801040185d0b8000c442000f0160917190641568981d0701c0007501500d07080d40240117140200c0301c08814040c1c85003841b400d411a80c01403044103080384504e40c80743d220403034010b40 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 753075053 1250 753073803 753073807
    0x9090201050a1419080f07020f060703110d0609020306040e010218090c0c19050106060318030305091c0203090f030105010e0c0c0709050a020a081014040b060c030a05070b01120206 79
    0x608a030098142481e0380c45180e541608100c1600b8020f44201441d00004c000522400244560320842c405034507004806440038192040d05c1038503207607580001800d80c030304055442102c01001580d000c1a1190750740f030f440047c0880780d49c03440007101035041603030b02d148124a0301756446c0680005200b101c0403045401c0d101d486104240c0c003044003100c0005c107070801d0301504000e100ca00c0d01d0148a401941c03c05c1e40188042a40303903041541c00c41e070305a08541d05040c0f615143d100c10f1415043c15280c0700303501d80740214055881190701801c00c020100307604021000d5000e000c0500342c0100240c0140e0350181d80300901030595404141c00d8a8080c403036520014001c0000c203034440203110042c85440110800c40d498140c0c0c0303141d079004a5004441c4481825070210303001e8152603001c81d105802c9241546e02c1c00300213050081c1c44c084400e2240c0f120307210326a10700740070100f905c03a075080c0c0364204500820399403a0554010007811a5102c42c10840d00c00d40d25900201d0f0100720010004401d54002d440741b8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 753076303 1250 753075053 753075067
    0x29010801150e01200a0c0e09190302010207050f03041a0301051c0503072001032306010e010e0901030609051c08040f0c05033009010c020f040204050a12030206010909020105 76
    0x103500b84000c4444a810841c41040401c50300f8800e0070402030311080a001008061802d00f03110f404141903030040d903440b8011105000d241c21000807018507603034507081100f140030a5450140e0092041140042140c00780c1d040c0069140d07004000f51045031015a94500304407001000c0300310610090203901c0d4401a079070402031440007200500c4c400030740710b042240d1600100e03072030707050840c80340f081d04048940e940000001030b56450700503150701c0c0541949000c0e2002c908103103072000d154020030a604200a40354160700e660b11070720100050580280201010356103d08142c0064100100152858490b46480101100102e017403980141410750381e4916a40340d60303484003082c940211040c1c410900c180c0d404035090358284a152011b13040c1040541544900144008443c0100c0c048152070303c6c0180100040340c2d07000000140e480d94101c40d4030f450030788040001030080c06190482500140c080d200824100d1028038044440c502a4007154000da0703a8541a50956000220090015400f0b000b08 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 753077553 1250 753076303 753076307
    0xe1203010b030705040f0e090c040501080a11040f06171905031611130b030708010b030307020108192f030c04030609170a0c061a010f050f0c012901080115 68
    0xb550700030500d454028903107661106540324481c02d5811151156032241d0a000d4000d00c100104024110299020700a81d854454480d80ba05480c0c00c000e0900358415400e240b403540d80c0c1c0e002c00c601c9021042c1c00c00c101c0752140304403040291255141d03800c40c03151800808251458600c051420b5500000443c82e103007400d02e048606540d1104100d4003440c1044580c441a5940300c11510b601c0082d03d00040c0078070a66042521f41400c0707620511283e4985881c9003602d4402008613244e190f0282010422501c8040c15264000302a52078030030030900c3c0040c07410000320468103481d080301180780c484000c20580c51107034850348000d03900004210320820080000501c90f0b04100402c0340100c2c100c244c907543e841c070340c00c0d100c3d071043c440c0a000a00d142047d60811015214261800003801c02c41d8810110310000070340000e50604c1070328140714001c100c941c4d0080342c0c541102d50350300b00d4000903c6104100c0380e07642c024076181d80c2122000e0543d00000c0c8500c0d403195144034100e030444c20740164078014110702 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 753078803 1250 753077553 753077557
    0x10905060a0e03040512101a040b0a03030f05090604050d030806011103041211030f10061a0306090c0c210403031b0f0201030b0d141c05070f031d1e01030e1203010b 72
    0x103030441c02503880c040b00b011503603c29482c8e5900c2c007400003581102c4050400007103c4074007118510a002c40102800070a50104841c00c03a01c00d04c0c20250346d04e00708031000500c14003859201a03400f14030707289508201a48540d8090180703030285c859502805401c1c080c940c0341d00075070142808254030440381c900459400c102c254642400507065601380d1100920960070104040d107a00006c80d111001046030100c00c0e001c0c00f1b8007c4064a0356804c509100d0001042c0c40d90241c941a140600414419150b00d82070010400022880c0708110440e4003040016813280c002e4070040d008075070700d47c80e0007000c45200d0509842880e400a0382c4011a4180d5005500500060044030b03081000c50300c030300000818490014144144401c020280e5481e500054041d21840d90300807010001c043c800d480016003904070038a0303d968541071110703540380001711000b1640c0c007040c0040d0b44070f40140d40c00d4006008030340340b40f000000207a80500955540400780340e0795140c2d01ca5003031120301080004200b42110400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 753080053 1250 753078803 753078829
    0x42d0b0606131e0f051503040b0603030c0a05060f0106081302120708010c030f0c051218031207030218060327070801020c0f0607140f2a010905060a0e030405 69
    0x110714901152a0a0641034200d100a10340c0802843c2d00c6084c06032442900e40040100780480b400d4210507072141032807040d070001801c024844144480400c0c22030b5001d01c1618030b04400d6401f200e04881c2d007810110b40d00d00060712441d181e207c0c020004220140b10710722861045090034003840d8000c6280e800c0c40403802490707640b042c160240c0000410800000e0040e28001c0742c00c2e60b004540c00c0f001118080480d01da030f0b10400280720040000100700303006034150a034081501150341000117405c1141906512079100080e40d42c185040401000325015405040095204c41404a004000c83c0500c002c9100540d034902004d0102c03008060003842601d4256064501d170010395503480d6481c2c0000782a60011090b012098101c0100b0307a02e207040030022a0b500000d14540f002c6008012402d008191207010854005900001020341d0090041070581540c0000340003d0454046101702d00c030700a1880500c226503901491003c203e00041c10300906680d40401e4001d5880c262905080041030030080c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 753081303 1250 753080053 753080077
    0x606030a0f0606020f06180604080f070b0406050103120306261f0501180207020d060c031404060c021b03070608090708070303020616050a09050402090f09042d0b0606 73
    0xc070140762100d080c0680380040070250020080412409415810104010306070818201c80c141044420800024400c0d003190300302c2141d030b41d100c2622441c0c1d0000d11803910b02800c581400340502c010080301e0751105048034001c0c02e6003140341da011041101a00d542e4401c13110700703c3c2ca141001032110040300d605c280c2809198100c681510750004508400031218880071240d80d9a40b0041100302d4040803008140c0600c1402186071a4503580003a03e918203100c3d014200540d16105400300d240a9446640410002400d4142510701807519202a05464003090b0060242c0300382c0242001d0030200404020800501404050381488022143c200b40100401054403d02c000012103000c10701c413041c081c0d402a40503144e9854101c0800e6407004070325141e441040810003040c50450b600001c05801d64008440c00340e0740e0301050f4001420305940703501c101d41c861840360602007005071021038040c0c140102009800032007241603d4003da4084858082c3c202440c6c00d000403010b103405002019420010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 753082553 1250 753081303 753081311
    0xb030c0a0905090a1a04030201051303090902180616030909060323120c07030303051501020a060b130606030f140c0301090509120a0c03020606030f07090209030c1504060e040c080606030a 82
    0x94440807040ba1040404045c001100d105000034140d080c0902d41c0d0000648198507000c0ca403560b4002d11003011072050800041d40400c500e41d10740c461418500a8000090000351607091980328a41c4900903400200d0102d0322452001505a500740078801c00c680d0030a00c803040302c1882010312909001c02d940031003024042d0340b80210070000140043d00d0500320200040c101c1a0652401a042b00d001400904104801a0b9106040e80c2d00080c85403459501c0131000c142d07003400e400031560402060719921a11400c11101085441d815482416401c520340c2040c450745c02d1301d40c80340d0464070080d5458221640100300501c00301615400080c1c01241c0e10b41240d10704040e20181c0900c64011120420014090807030641c01c0c142d04210301500400200c02820a5014901d600355407035031103100e10075410f40c020511040e250b034180000040702c2c5001d0800d0b40310b54804d01031200d03250701c507018840100b5040d03008540282803d100b8030140d051030ba01c40da11a5107a000800c440e40c0c0004002d1442c007515 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 753083803 1250 753082553 753082573
    0x60803040311040b0d080d0b0609150d090c1d0606070302120708070206070807020f030d0e1e030102040603020a0f0e030a0201210903030518060609040803060a030b0c040303030b030c0a090509 84
    0xd698070848545c0d0080f41d0381138844a185c0780340c9061301c010114407032051038140a541543c0c0d4401b40032030b0320103128800041d0f482940100142c064040708101800d8141901c00004941403035824030541e00f032001c403080030036a0f0b4050401545008952016005a100000c0c141013004000014222640960170f800d0038600f29600040003071f80106000c803400c00011941c8400c501300b195040c0080f52080340a4030a02003400001081c0041c0011120310074100f41c086003180f400b620b40c4190340c031000600259511901d460b006406988240300c41d03c002940b9504403042d55104524843e000c10004020301031182c0740303800468038038038100203034001100400c0810442030120b1003036000140c4692000300b214a00540c2c0c5c030600d011325000704401a000801081440d5440c40b1740240c0c001d80c0060705075180d84030900894003001041e0401030101e0820424000000c4251010340222442560305001703407250002032589a0501d03401290308001e018009004602e440d40240f60b11183c074070100c4000c414 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 753085053 1250 753083803 753083809
    0x2802090403170a060e090c240d050f07020c030d020d03021c0216110a03050304090e01110a110c100e040e1c21091e0302161401030609060803040311040b 67
    0x60140c448900b4599100790070003005058283c1c203070703100d18280e001e001c2c501103903004940c0d4040c940d4207510b203001100200d64032801c0f001050342c89e0728503282001c11141c13a2040c45075181080a0383c000d000343c0b00c1c8111380c4803140b80004004070480c003207034050302203010b4445041d4007a4114000100c6441420050440c00003c5480503041203500c44252515880550a100c11113081c20b44800c1c1c000c101210085c4042400001107404882c840c590004a01307590095503801001000d10004a2a00c0050741d095080d50100050311402e100d00140e07004a00d0710020040740305a103032841004140512103200062800b5404800b038114102c0540f040d0b911480a480300031041da00000000c200001c0c04810441c01034241501c00034a6520108840b0907241c0b02c980003040da040e81308140950039403200d02014424800741003020024a8006840c0341c6542d0400c10344010031300203900003442d00c0340c0040c01d410603000710022519000042d516150464456425005081c1c0e54160006c0c4c6940c4110300c1e0f03071 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 753086303 1250 753085053 753085097
    0x5090121390806090a080c1204180507020109120c02031c050a0806030a0804030f0c1e060318020f010507050f15222f0406060807022802090403 63
    0x1140d05410030030380781c108410901507099140c024250581c00b6404114003620001501d403d003603000b904882e210040090464502107048102058042c0c020a00103450b103101d01c1c00304d2400819080c00e000998507480101d0803180048009800c2d003851682c1195842e01600000b0b480d24000303401d40b90090001c0318021001c5a2041c0580b00081e00041e01c0c050203603100b920a07030810707022000707000c00803200e44034011240110300025001101ea9a481c008000890140304000c1804241801c4054210104503044004611940001c203050403030f090500c040070040c40395807070750007440301100da20140c004680c81e0704501400ca5075403159481c0d000300c1c00300030041c1081e6078221000910040c6000000881d1005001520340203018143c0c030102d0001d001034010461000703450703040003400a082d11001c540c494001c40000d801c41d107840e4000c543c00b54402c840d40d00c01d0129808030f4101c000301d0181d032402038401034060b0429541c280030b1000180341110340c031500b05010740740206510306020b18031030401e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 753087553 1250 753086303 753086363
    0x705031b0916121b180e040b06060417060403031a03061602010213080609211e07080c010906110f16050a021203031017030306041104080a0b060a05090121 68
    0x4c8502d0000804040f6400f4808500d82c02402c10384500f040d2070300743d003905801d401a10041c40403542000148580d1682d0b8191001000c0041142c2d11424828003c1a111a0141c40503400a41041c3d411509900d4001009014600250082015544030419204042c0743d07800d2603c115502040141d20980b20440061301600c0c40401403c05d5090001c00c4915040402004525000002c80c0c07020f02c2c11070300f2050311064051400d844c40c06001503054210039206480c03008000e080b005c11a00020001540195009813080e68204080401d10300c903040c2034090328040031810030040100100e0804184044074646106030110345003801d90345d0018600603000040554294008010084040d0a2900704001490152480d0340f6920480c80da11392288401002c0c01e0146440d02c2c2c20340c03801040a400c81d40200a0b5806803a511354940c54041c1c817108042e5800c4e48900064540403d55180004405040314100b504090311054903280d191010f9821050545070340b0402481c001c0100b41a01c144810 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 753088803 1250 753087553 753087581
    0x2031b011a01080705070b0702071802030901050702120d15030210081f240207031b140a08060415090818090703052206020f04080705031b091612 64
    0x10341c1d001191155441c0440184150401000030240f240d03443c3c02000b21240542c0020f50301c60320ba52001003d0345041c24039840449042900070050040046030b5001d50f019200c8600240810340392580201d81c2c401100c602004c0382c0004015071001440143d028144840e15801d002c2d070407503a41c1c0c0000380e03102400b000310004074420004000311801252003c108080300880c03503c180c281044030300d1822401006040354804405890701410a0081007038100840d4404110301d414904000c486405d480c1a210b2040310013030442524a41d0301c2e0400b0080b050300d50700001400a03507241d4898510b0f078002c4000c0c2c040c0070b43c0d4a0003501c01144001c4018804e9240120802d58107012010038000942c10084c07090081620f001c1c04d2101c4c40681c40c1941c007074001c0c8000d8005070440d40d424032400030f20503011788580d5514001800111220b0200b01003049030001c40680f0500001c005440306086424507080398030201000010742f1400c2c0401d200c07403201d081850110b01c0200c006642d1000c48000e1118110 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 753090053 1250 753088803 753088811
    0x11010e0a05070e2d190920060f030f0414030309012c06010501080c0409061e060912020103112104051204030317060f061215040605010c060b0102031b01 67
    0x842c401c054141c0f40c0040200c0d1012514400c03894601c081d000385481c002c0700340a03925010528000103100c440b00f1001207000708101b40380031440d04100440c0034581804022034520841c0c0918035208003a40c04030f10408034098516510741c4161204218028011180001701e0140700c104014104007035442103424a00000d06c1d070b00694020340780902d201850200768030b241c60700903024007004180748e4111340302800c100c02c641e164801d51900c2406180c218200261030040000703884407142d10610f03404910041001122a1034101c00c440bd0f1049000300701684080720101001544264800540c40f83c008207a68203007100100c000903900800d0200d208858480d8050105120041c050350310090814081186000d1850f68050800345010000010400081c400a0aa0b490702d841d4400a00c5009007419a19002d014100c50340e0300d41623031443c13400c00028544204500300f522440080e00c60507101d1443d0340c40c10fa0351b0f840c080c0c441545600c6c11070001303000441c0b41c4c2034507101018407a100000081 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 753091303 1250 753090053 753090059
    0x6050405010912030507030c231b0103050402090c03062b021201060612090609020301050415061406030a1d060108101803090b1305100306060e0a0302090711010e0a0507 74
    0x40210510b038000c11843c0c10100d81101c0025007040c21500d081c1c1e41414020528071582c1031203400e0740000c102140c0d1021080e0410038000390f001c50303101c200000801a600558a42400443c00c0b101c007180c4c020f4000030058003080002286001469001c0710040c1504d01004506100c005604065034614201c2c0c180d25004004524140304c84600002d8504003c0200c030345450700042650b41c3d003000d0312852503512403000003030000701d401107100c142d0060f000f80a02e00302803900142c2103946c1c807000c141d4a0301d046004a4035000c0301c0d00b0001400d0008000504503102c400100000384112a86040c0800d42e500720030a08000910242d402070880002411004184d1124201551301e0210b0151182c8001c42500c400690041d1745241510030707858a49441c0c800228403410b0280d1907400ca03a90095060551b085280d906810020507100795546034040e81001c038003030005244490000030350010040c2c1c00070707402e02d20a40105010301241e500110b58000f803651498140060315400381c4890300103108c24 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 753092553 1250 753091303 753091307
    0x2120c040f1d0604030e0d05160e071101200315030d020601061d0904080903160311130b090f2d0718060c080706141003121815020a0c0605040501 64
    0x40707405001c150001d449685001d030760080c060f524010f00300340304001f8801d901c03003444070030400c144004079100e6603284115114944040c644c03034101eaa21300001d00042140d5010300040c0601e16291800c6002600310b511050100080750304010502c0407641d5111041d05800d40e0708000201c0b900e009500540795550500c5401050350000b2508100e01c031810340f10701c0c3c080e03840b01804254002d412044468507a09280c0c002400c1618030510f00010420654000c07084c00208814801c640314112000103c001c1041502e000751410010215407094840000410442d036040125921890742c1c03911101c0200d5525101c00540003944e01840702c002040100942c16802484469914440b00020001140307000001048100081c00c01000e550011800c40100310403608496002210180002e00b0383c500f80710f1240300c0c0402848103403480d41c01980c142603130a0040480103601c040300009801b40d0350030580c210f141852001c410004510541d982d0b03d001c03550450051700500320340d42d510f6907103520305800 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 753093803 1250 753092553 753092591
    0x10303030c020f0a1205070b0708010510030605180c0c030a020309030717120f090a090906060603112b1404060b0a12030e0307150f021204080a02120c040f 68
    0x20503002d651140c848000104400103d01901d02e5001c01c2c00000401202c00884490064000c010410b44e551000c0c005015046404981030f40c006603441101c0780074040c0101d0640d06284a815048a0390030030110040101150140d848407010080b545800322594625296034020100b500060f000840d402030149814496031005000303082e181801301092540c065180d80c0c00400003003140e00f0010b40e00244a00340f100b9104146002401080c40d595100b00c0d100240000030030840b00355250920103d10f0701d00a210740040d65052080b95400c01c2001e5007902041d00009120301503005164502c50765980e5940104600780c10351050008541c105860b014068800070849a480741610310824001c9411000c54817402a8240c50001c00880c00071010a0a0009a41244107003d6a0b100680081500008a0085e800702c0754202c0e14039821030050791156004901940d030258008070f901074050b2a01c16507170003d182011080c2c03000001410006001c41c1d0b00c07880c0d841d481c40d1302e90072a8000000d104207 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 753095053 1250 753093803 753093821
    0x90c0207050312130905040c05060d090c060906032a0e0a05041d061311060904090f03110c0102010b150c070b04140f091306110702030f101b02100c0e030d0801030303 73
    0xb00740302c03901f403940e034580490b1007174041d6502410001c0744044041d0600d400c2a10b0894001175106035258035100c1c014030100b014012200443e00b004602541c0c04420301c00b4401c1400b500304010182e0508000c00c5400d0665a8441f40e40219008004506a81c0c2d503c1603003004c4c940c1d12005185803910000d80f50030904010844003510728000c1c80c0c41c4c0071030000002d50703203503440450b0b2085ea10b0505074005401071420b0030014000c0e05e402140c071000c0542140c03c00b102c5c0c0d0904001c8550741028540120300381d601c005181030b08805020300012454032100c000c0c01500101c1001e0f18119500c807481014150010383c0f1031406001544080b10107400c00b00300c2251100e005a5980c0514900003484080b040e00003100102030641d00c80c6219940ca488400f540c2c2c0c415801420f55002c07030618080143d98001d00c607180d80d4228600f4064400007410012190301c0b041d00c58000d0701c6030702281c01c200da00411501d148a002e020740c2d01030685841d034050144021150890321404040d5043d41030080854510740 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 753096303 1250 753095053 753095069
    0x30f0f0614060a0206010605070609050f0a030813020a0302090a1803091a0f190e030d0924021b0607060207030c060605040b1509030a080313030e1504090c020705031213 74
    0xf01d0403400d0b9010030301906489050400540d903106070326007840185a540c3c4094401d001d60000c075100301c3c4000c40e01056540c080c1e40e5942d00c0b42c9495125008101111710029442180c2d1581000141415502942d0240c080382000401d25440d10082004600b4007004400241001e2018081241404180034191019102071820114482042d001c144901a007007501d40340a6aa81c12100344902600c1da4034135006015220441900003002d400c000f102d000e900300a0030000700070060030602c01e00220004480c0e80c0205501e00f0034116410800641044441e0030840c01c002120110710280010012a03100750b6413141c02900c541412012038035550025481a03040030110091070303403960000c140b0700311401e5403183d541c490400001d1a00300e030341a00400401c000320402c02044c50742c19072005002d02a48807003102d001d05030100302130b002105a2040a00390180814850140158028010b0381903a004030380300580c039000041c2c54055002c4c0f200c15680c2000841c030403046482840003004103602 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 753097553 1250 753096303 753096307
    0xe0c122416050c0109080d060806090109020121090b0c0a020609011104050f011b0503040f090e0a0b13140105070311070b1303210212072c01030f0f061406 68
    0x8140e901e06064500050401040004070700000421400e500044045a00c1046195036540c9103070100007418a9100b13804944c015040050304810040c0540c01100307a05a44200a0f1101f007400d201e461046c01507640c09056a600e05040011044082580500c2031111110f45604071110000e10b0030070020320110869040007540480d10102c00d06640070b03101c1c1110223003440305207580102c845000010210304122203c2d068102881008401031094890950001e0030507502c4440b003030140c030b01c80740c14000d642c0d11075003100000c99540004280c02950401c00f1071034520840d124a6000702543c056008581d5448051000e8241c05104e807030140d00105e6940341c00e03e034141d02c40d02e1700702a004103209401d00d807200ca0360041500c240850603504000018000c81c01c00b600c5200c0000b9081102c40d824410840e00109440ba80110411412846602d0507140114040400721085029103203299051644519409060b0b101c28080c2004045951400003207280c68888502212003d6006a500510003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 753098803 1250 753097553 753097561
    0x604021f080f07050c03161205131412010e010c0f020d0503040803060a0f060203031b25020f06070302010b0f010302030c12070c0602030c0d050c04050f040e0c1224 72
    0x1c080300380c1d0700241040c403107000380d03940c450107407020310445604102902000800c203130261846c443c1c0d0200103004600007400020307ca001a03805101b00510104e4038204034004001d50400030050714414800a84000d070001c01d481142c60035143c020b41d180d1803d945a041003520594000e2100c2012403c910061001d07400701440035000744009080a813507808008002401c60702d4032900b03c030040c520080300314056036548400030740700d80042d07541c00307034140e0701f200d41c0c076035488200c1d0681c1c441d01110000d64041f12400e2a4070f02d90010fa10b181240c00078016600b00940d076403180054000240240c002081c403101c48010040120296038001d41850320500500c408800c2140a59a03603074003a02012100b81c83c2d0040945140034014802482c50380000108010310526a014000c0032000c500300344001d0315540c81e074003071500031401039540281c451280b07050f107440d068001c0c40d5210319210a42d900d070105030300030414242c5c0194620391594001c910f6140e942482041c2d03070b043c2e1102185a14510700f0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 753100053 1250 753098803 753098807
    0x9180c040605130f1b020a1106031b09010309080415030501051c140c0303070309050f01091802070213050c04031b03030906121416120216020105130905090604021f 72
    0xc00480080f202d55a207141002034000d09034000468924a0b41ca01183d44c1c0103081d000307544000031a0121825030042c090343c007a50402100f43ca0042c0380301e14180760302110000704051650845041a410903465010480102c0c0c0300100a201a1890b2044404040c0038404090706440c010f9000318054450140d00d00d820703502001c060024654044515030300d0160001395145420640f0600c076615000014149081503005088102201c1c42540e0a0401603032400064507452086c0c8541c80604002c16030480b40440c455000700006440181052141c40701d0f02181e2044030002c03200b94200c2c01001500b40140302d1010140308030401da150076180240d003141e600901c83d03a800d00c610300901558050b10702d807503d4183c1102c0809105d903240e0941526146803104250300c0301100e13400203d401c0c811190794442c035a008985c080118080101040c01c05680110f92681c8801d1008844003004d40003c109501c40303004407401100d013100144090704007801040100f03d40c81500a84210056114048050f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 753101303 1250 753100053 753100069
    0x20a0c1206240504180809040504300e06120103080d0603150614061c0c0e1201060e0702070b040b13030c080723030d0804020f1206040c060503060310150509180c040605 74
    0x310083d100840c446e1620f24200c08842c20b203814030306100c5044948025080d42111807000d4004030f544da08035640020710180370399841610404519081500c0050000c22441070051412107019100041c0d4155a0f480c0c0d182c10300000766890b07005030f403140810400c200c0c0d20039200ba980c5d02c04641e181d1901e00c2442000e800305200500d02d0720200d0302d03248111460303401845a1070140e00040c000380c0320b0900400d416030007842180034032035110300e940d000b1402071031000900300c00303552a60681c0c7d442c1030708250252003c2c0e04025080103421500c60008800104c010920000502d1090010491117041915851024200411a2005440329000785900f0368000503001c401c02d8003420505625252400403500582515050a82282d49c25400d410060300024150303106600800036854415107812040350140303c01d5400381c0d450343c0415409081561103038010101c25400040d6208035075070b288081032940e1000c0358000129a5121820128a03000340000210404100d9007000014103000c0058a11 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 753102553 1250 753101303 753101317
    0x10b060906040608070306031703060a150e09040c1d09100213030b19150828021215070509010f11071a1e0304030f020a0c12062405041808 61
    0x1311560001c1001107000360311040156401c440322115482480b400181e455100f0f0303c519005d410b1415000503c5210580d12004895040e80d4003080c0b0007101d401c002c420000548146c840b0030000c5000561464850384c4140b440340b80410b55812880c0460380c803402c00030711004e101261030040240f086210072401d4600292540807080c8107203038460a8074501c0100300158022a01403401c0c1e01e018201c0030311121300e004c0341c80460807260800c540c01c8010b4400c007510300c10310002d12080482c020052030407510044000041320200d40543c7e14403826038020040c203841030008903100003007119003564055203072000b6021a0425508084240b00083d607184202c1c800c0e14503403000f1042003c1ca062541007100c8030f038011001c5000c0c2c24554040302c000264002d0b01d00b10085880c0c016581c081034000301d02c03d84403a0300000400091172a10561283e20f012000d001c0f1341983c1d0310b00b070440d00e1940802c0918407064010081004250900d0140000c80b8890004e0200c03920100700c0010018249001301c0b088 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 753103803 1250 753102553 753102557
    0x1008040b04061e0903050309010c09030507031202030c1515031c03020319110901032007030c060204091d011d03090d0c080613051c051b1608010e010b0609060406 71
    0x1560603d0000d100c505040a52001030b810f0a2880c500b00b81a40000036500828503c00200607000300f40109a4002025200051490700004010404140d1122001c010880d00e401076915041190321400d08003d020001020007400305c2e02804811141c44845031651f10b4164014002d00e5030311070031440c02043c40300c503a07402c25070000300040042c01440c8a0801c440c410b80410310483c10341c048440c11607040100e0560010b403400056a6900000c9a542c48800d801030844038500003031501d003241c0f107201400003541c03926020000002c807070040740b20702100b1221280d08142c8100284000c6400e4030b810a1102e14040c9254044001e80d40c3c0100848000310070440b96441a00d4440c9016214844540d1200312030f401a81d0420804030328807885101a140300700203907503400400554407a036040081041000050081c428507190300f11000082d50800140300880d124851071550b11030940c80c007034001e40036594480308101190102401070710980b1000315002418084050041007a034080d0703209002c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 753105053 1250 753103803 753103811
    0x20603131703331509040c0306030323091c0312020301270e07080a140601060813020a09021b07090e0a030c170708040612050c030c0a1119021008040b0406 68
    0xb8031500e00b49416845100064024120700540c1c500303d04e00d58010070041400b07a81081110280107219100390030940758581c076010072151242030340141d071006400b410355460104210349000b9030303a5007d081740000d0b070b60026a5649556841d00504007c40390b442c580443e40140018005018003540320a0464000b440c01e00d150881c400602c80544030410002003513014480020640744400b00d400e03110980a003034400e5a1401141c04d079070f601d450900c5005c000a0380703070300420314040d0140381c03050019000a101e50601c40e226088801280e00482502980a203a4514400103420600001008110000c8100700108400c1410b1303413200d50400c8020204505040103034100026034446001c0c2045030070140303444140c0d610b0b10b8140355000d1702071031001c902818140c080c0c0480f507014641c4a42c465410942c21a19a444032100300d8202ea121082400980c002030b0420320420040340c0100043d058608068280d40e0050101d440c0d40440031104101c81c0c50104400f0981c0d903410103070401e5001d14002 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 753106303 1250 753105053 753105121
    0x1609051e161d09040302060103030206010f08100f291c05030304020f060c06010311040515010c0204110f070b16050c1506010e09130b0612100c050403020603131703 72
    0x30700440a01141d243c0c0c080c0b409028441030580c0006d645069910030f03002c441c2541d80b20f170181d0310410800e00c11980c3d554840112014188031540016502c0146201c0c003040c1100107207185004001e02c2c1e07a140721191401040c4004a190220361107040e1846048640082007113a06d0310360322440b004101901500000380c040001d51914800c1b10311751001c20040d80d090f543c4034a8052008c11101d03502038450350424011940f0007205070348a11000d44141c40e040400e0115a09010180440034486040a4414008007c03254030100080c01e005224001c0c5580e00e16000512402c41c0050180220402c9400c0c0310340c00000d003000440d83c03410710700c0f0480315010b50394800c0121241c517001e002c0160030405107001d104031005020f9000c240b4501c00d55a404842d99070f0024001d1841201900707842e10340c442c0141304143d1141ea4042c1c1d04042480c80c000d0314180e16a000700c0c071183c0c82650505a541180d103550014031010701410300010101c5210b070f5240d810303d010024041c0032160804405044608800 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 753107553 1250 753106303 753106337
    0x150b10091e030206040314011b020613020a0f0f0911040b0409021c06090b120d0207031719020a03080a0203060f09280e01181a091609051e16 62
    0x401c01107500408403603a654613441c00740207160b88541c0c0348689609202c01010030003203242c400c412101441c3e00401c90b07640c82080e614000703e0800026038010740c0194011031482640b0101e800a000b42c2e10b10010b2261514008030110f40c0654444501014203110034000510560119000c40340800005a2200d82c60421301e10100c0035048243c0e1524500a00082c001440e1707005030340710b000c0840d5580e241c00340010595484240ca500800c0041e040a5002d100007810061301c201c801c4500941f135428101880d0b0311070307842c0080850f14000344c0e0102e8004020589d02c003404581c815017510741581941402808513524019414203244070381001c0001031900035060240c41c40302100e80345000c0c101a18541c110380148901e46c0081c14035404c00d603a0000300c1701c050142c1b0310090390106e40009030007020a000402c11502074094807282c0100300b8540540f8160383d00c2ca034050042c07202d00040909024110244038840d0b049400f1107035916004024043e8098110500b00c0c80c43c45c08d140711510708903000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 753108803 1250 753107553 753107609
    0x106140a030e070f17010507051b07080d09080d050a02030702010516051516020304080a1202070e1f0915051201060b0325080c180616150b1009 63
    0x540c00702d40c881c00000186000302080743c50216013070410411142c1c01c0c2440c07064203030f44040700e100010841c2040005000c0540400c4251620310700401c0c0c2c0c50740c1361079002c02c90422040f074a0f05000501598018002004140040c1a1945160514502c1d1026124019440e4000c80d800603050010205035001e08a500340341000c0714036031000036200d46040002901711001e0040c2e0b414210a08070140c6018450300010485d82610320f00401000c00d4a4203584210f913000d41800982c04602610000007000000342e08614050b2000c01c1c1848021043e820640060301c0e0140d11608901d0b02308540c001950382c14800300815504160389a602101110780e00a0240c951079002e121818400402c000c5100c40603100018605440c4103208444440e41d40d00b20303042e05040d221228464405c100380001a200d503a0031681546020305400d003060a09516000c140600d107070306545901c10f004021500008034414000942822544c540809582c40700041500d2154040c107101c80551561418994280c140 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 753110053 1250 753108803 753108821
    0x7050105090a15030c0e01050f161712060f0130020c0f030c060a05040c120303111605070501141c020403020a03053012040204140a140105090106140a03 67
    0x402a00b6036603d5810003001010b6000144000a036207000e01c1040d07620480c125210a1f480a04d5039044c124519542d5240c0c102a103811112000444c01c1c4180c030f589618040d0003030783c01d042c1091031540b5005c828010740b5408481940d04001e2000e041c0380f00c2d180d000c42458252000d5903d844540c0400b40030400092142c0c0900c80c0c4240304140b40540c1c81000080203100c0140d1a07004e6840707940710120740c1015a181540c5c01801c04030010801e21a0000243c80414400e01034540400d0b40c0c03a1191003a440383d8407012044004000307015042c1c00b409401c116030300082c082880c01c91800403202808a240d40034100d905100706d075074100d0007044074660790142c60156400804100c0c0d407603500d1610643c0c4541100b03641c00130110000080d40f4407110300d903d071043e6840603a1264030301000600d50048544005000302d80c403a6031000030980e984c668001951050141e07074000981c101941c4480f00d203c140591115114058100061055940c040248003440a00d0318007151070b07980c8080180c0c0030349a180 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 753111303 1250 753110053 753110069
    0x30506190f0602011406010804080a021204060306030506240103090c030510020417070f09020919090e0733111203070806030c010c032a0506090c01090807050105090a 73
    0x3010840480841c2064200c400b00d4008001c810190100d003510f845040b00c5007404a2a12070008020601d004003e2000d00120310540c1d0050000b0040384103e40c01c5038020300c000070354608040c000c1100030404c843d084a600000000a912401d050b81c0c40306c00100c0d6114100342e1510f03111802c0000302c51840c0095640314080d80e1189140c1d038107540003900544114032074406801c4400c00011000302c2e00d00180c842c0303005000015402d00f024440a0f610810080783c019200010415020362084034541c00361084400219a0b00e42480320b25103040071640103080604180880c800c90054060b101408a25840f10000020340000c5c00503503016110503001c200e50b015044040003a40e904074000c1d84034864a4442030307100c0c0c44000c24555282c4484949601203030805140001180c0608855596803490311101c414801000e0711951850502e4442120b05034450070074000c00c00d03c14414140c1c40c20b0203103000f441243c03400312001c1d59451b4512605051010001d011055a241c0c1002500600100 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 753112553 1250 753111303 753111349
    0x918050d0518090f160809030d022811070b0f09040f090f0b04020901120b0411060d020c030d0f09050a06020f0712020d0e01030c090611030c0613031106010f06030506 73
    0x24444c2440c3c8142101c01820b60211007001c40038160080c5415805444407400440c24648105003850003980440a032942090704000d00195401948000711010a200c0e80d8601001c0c800d4002c0624000300394003d400c5c0c6081c03d2080c0464800721800b503e01c0080111400f20b21805004401001842d0841000d840d48200400a10600c8420b42165015600c280d03500d005e070340e0344c4200704c42492000d46801030500605401142c04102040c40c0503071f614400a02580ca4110300102e840200d81c0080b51405c2250400714074080103800c14481c140016003401803d01026203155038164840200b1000106a15400324904025203907010075100983c1d44440080c1203042c0c07150019682c0c6030001c003200001940e2800d42c90b8254442e0207000c0000000742c8484070700505007001603502003c1050b400c1e240344004e1046202e0b110b010030140e8040c9812125400c1ca4030350508004244140084503c40c9643c449030042003d07698200c200400c8654501d0700080f40d484401c0010300d0100c20404685020040c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 753113803 1250 753112553 753112561
    0x211006060e0114070204140f0603030a0c0f2a0816050a1a0906160b06222004030605060a0f060507080f090a0602010501080c0a0305070e07050408010f05010918050d051809 75
    0x31f0340b201c0d8010030000c1881c0049075034110815170303244107000c864800506020002c1c40003400150300803620790700c5800f040022402d05042e000e88141c40094100d0b5520700242c0400135072101b4000d050140c024005942140c0e801e003400318524560510031441c0082e04d80010365046144031080e20800f10000305400d6a070201d8001d001e03014045400151211800d0001054851600c07070080143c00b40005598032820001d08142c60080036120700d40303109c44903410311105210607514000c002035171094000041a0909009000111020303810804084c85094400c0c01515000010303111081d80c86403040356102507242c0c00c41c4503402400c4505812a84c203000c042640e071303019007205040c0c41d08142115402c0ca41c0e4020030041c0005480b02409a40100c00107104a0b04581080307540300049041a0745002d0790b4000700c0d42120302d01d120541440341e84a005100d0700780f56000310100340701440104d81c9000300c240c44264580c841000700f001800000544600d80c040000c50002044000030480480e40c54 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 753115053 1250 753113803 753113831
    0x250e04030c3003050906190b010e06030a020a0206010605040f0311060f070606150e0916051201121106042303070909030305040b0c070507090e0a02211006060e0114070204 75
    0x42c440400c8046402c1c4000144d10004c0043c10a11980080da2501c105006410044d00140ba458030306c03034104603c24103940c6d56516040300442c0a0015240d0040c0d560740b0f5024002e0070008184c00c03860800c0410081080603c8001c0002410b407500310840c42d2807801c9040008805110f03100c0110ba0508011402c00d00b03000255108804070b400e0280340c81c40b44601100d048503007a0800000560000c484404a84917040d00007400b0020700b51420114508803946192810781c0c9004d0740302c040320b00629200141004600c43c1241c110910594601781000e040590600c82882c0300c0012007841d122402460030f02d0394042200d10010000500200580801424001c000d402d0480e003d513000d05c00b070004645090780c1c000803074080c40d8004029040e01824401c0d440050304611050310400d100d0091402c025a58401c1c0c0d01c43c002d403100c050301d01002c060701d844c0360500c007011007883c02d05d034500700041200075044400101f040009181c81107110040d00c1c20142d40b8016858060742241c80c0c07046003c580b070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 753116303 1250 753115053 753115133
    0xe07050f1312060e07090b0a0b03090c0d150c080f06040c18080313080d0504050d0602041d07031406011e020f07090222060207060309021809250e04030c 67
    0xe00d9204c181c5e904070340c464020720b05445601c05420307040f0780300080030410b804800028580085840060b43d4100d02d4200000b03468000c030003421780394181400d8000491840c11b2142000c2144c0501b0203280f54540b1107000e9000203001003101f801217440755140c0f858540b00f5402c0240d4410303851024071049450706507081d581d800c58024207001011401c0d01007131401001948180c0e41c0c40590fa25480c09051000f8080101149042240c1c6980c0034000415441001840c00c0800d803100000a00c0171700c0c00c401d000b800e5a450382e080310398004040c018068980d9004002d0072845107100e0782454106660f4030201e02d01081000c42c3c054030300400c5030101d4540780c290000d28070340110444100541184040e00c910014140c400d00d00076a004000812046009400c4020b03001c2c00100240b031010f80c110090403002400f15030200d115041200f154042c4100020740108052111600710910f60400355451904607001e0805000e0066815a680070002c0090a10566024807042000342410301c2c0710481e052 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 753117553 1250 753116303 753116321
    0x90b090102040623030a020f040305070b07061d060a0b0319110114030c041202180709032001050919120c030203100507020607030e0c0312070501060e07050f131206 72
    0x4c0c11802000c2200301c607188500a40303180414600e01d10788840020100070740c813070122004650000d02000010800501006000740040385001c1d9079040300d07240041c1142d8401611a90301e055a0303d00c00752240300080c003d0341c045002c0a00103004c0401c040000c0c6408181468107140c803068400d0075042110b110888504401c003a01c61541034860710b00034030b100c0c2c001114000700d0010180f108100c03404c81c84840011090000e071407600011090750000a120b4401c550140218184620400400c411003144115011021000903403038041c001c00284244035108004c1e100300100460311590035000f4900c10010440c034044407034a80031030700d000b81917250700c0d2006034428019111911141c000070300407640b040c0300c5a8040c04196584030800d400801d242e400e4641244070309008520151002c21854200030080000c89881c0d410a1500d14291801900010a0151184148816660007106aa1a90098404d065103034a118403440072451281d50005040c145450340140030301c09158828440c0e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 753118803 1250 753117553 753117557
    0x150d0c02010b03031905091206150105090a14060c060106021b01020303010501080112030c200312190c1a010b0919030309090c030b060c03040f1d0a0906090b0901020406 74
    0x1009058201a0700701c0d012801400c0d01a082080040d0b80e0180f2007080c1d0f4401c030b005050107030800c01e46501140c103649048449050540c80241071103400c0302c40140c80c100b100c20074a8401d241501d030f0804a002001144a1600504414505e201641d6a0001601ca0310451034048500305c0d0303918540250785d40c0b5040720182100a190103200d04239440441240d050381d006031544415a41380401c1c800d4900c1202c2019820000c841c1d82100016001070318920070301c0c0d6112001142000c0c0c0748201800c1c140003e050080034001004604403005060803074264040e03403030912103a09151400d022240c60342446906007665255800420a8100b0001800e25100d0582d920800401010002822503842c2c1c000500411850309007000544402c0d008810b2510140c0b4000c074160030301c035001c964150050b00580c0c01c3ca800c0441d0510102c2c1c0400203e070001d05101111040c1c090102e2050030100d04040c09691245490310215018010326811641415074481d08502452500c80c807024000e421038050080 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 753120053 1250 753118803 753118811
    0x6020702090c03060f0108060105211b04210c030525171b060408060c0405031c12151508010e0c040e06060d0b06040b070614040519020a05150d 63
    0x928202c01040d60301c2003001170701d2101243c3c2100c00550b08000014511410064100700c00c0c000c0b0114070208070401c80020403292010f0a002101020f40a403003003103d001004180f004100f2184109400103040000c48000340720350400d070070705440d0401c840c0c001400074480c1600c14481503102c1c01300300018a6100301d02c5112036880c1c0f03041d85400201e6400421055022140d210b58808020740120719102e40102000d1420750303196203450408408840c1401500d2000c10b041041d0308041c01801058440841d0060440038190406007080354050002149250794403042048001e031043c0c0200501000c2d8500a2040340c2207500501409090080c45829007620300450f041d00302000c141c909540703c401c60400399581e41014000c40380c1014844501141c0c0b03618950702103440d0038008001030f040c801117940c3e407680c07281000400d4400504002040118060401c00440d00c0454802c031010310070220700285100f1400000d01c200394941090b603200002c40100300400c410f0100400308001841c1080c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 753121303 1250 753120053 753120061
    0xc040603181101210f0f1521020a0f091b02060106020a080c1e1e12040303080405101b020118020a0509070314040305090f240a14070602070209 63
    0x8450140c1e0540c01051801590103400c81580120700c08040700742d010a120481d10911249042550203c0180c200283da40da0f10004603488180641c2c00a05c841c1e000c40000176160140b00c0313082c150300041c000c0340ba246060803c400c540ea592510750082c0a411901c9025a0701e40e00107200400b900620300c00003464601641087c20700208943c3d04980781500030f020440700c02e481e104500d40c0240d1640c02e2074001c5507040407408400502c0c00d042004c418000700911030440001c0c58184d076080072416940d5202040c204812f80d1030784100c0e03080d6503061408040c20340300d80c0742180c5001010080c1c2e15086040081c641d4109800c05814609603c81c1c1d402480000350798501c4140351400054040c0d009041c0d0141030010303040411400d46c21032070b545000101080702084513401c0c41001c0d18110005040090f03803551031b01d0708032a46045080c1c00c81c2c0300d40c000e02541c40c800385220903841c04030885d03520215501c0300090003044607160707018040390b400c0d98682035498208020361002030304905c1040c000d8003003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 753122553 1250 753121303 753121331
    0x9060e0604060806060d0203030c010c0c0b09010912110f30030108120c070306090804030b0108030c0a0b27070303110a03020a1707150c030612110906030c090c040603 73
    0x26803c840400c000344c081521901d0501807a010102c809a03018481006018a45002441800010046555002251210361030190f00428002d4a240b001da030404c00150042444003000001c84d5080342031000f500d254480c407290420030401d0580300903006881c4070309540c4207003500d205030300c0b6030403001c240240650000c100940e000a016041417940b0014810404080780300080c02020840b60442c0c81369560f80d034584058921502c0c0840c0e01c1100401e082080140c000340c614098000720020f1400c02c800000c5c055550407080101910b60180580400c0d44c0c10444102c00045060941c12948150300451643d660b8440501c4200d0004244c41282001d01c01c011411940890389503000c2d28118400f038483d5000500390060f0000e040710200614000118070844100756015a56008621450103c0700901201c41c580d0200b8888d03044c2210000004d203500f0703c079011643c2c00316a56181d40c8c540c100440d1414000340350954020f0381070300501c000d01c1001d90251084070940e40e0248440c814410b04 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 753123803 1250 753122553 753122561
    0xa210e0f060910060e0103080a0903080f1c05040f26070308090618062802160c0b1602130f020703021c0f1403150402041503050c09030307150b04050109060e0604 71
    0x400c0078001d85d0000500019000a005158102242c80d00ca203e640d01c0c0d4a600c80c80da804080340000202e4005640303030b803403504c0030503c04184407045800c011384d15040d19042c03002000020000c160004001c1c070790700d104039036948442e0500114002151103510750714028160503c2580e1a407030520401b00050014120b4400031416096003c0180c11161200d0401021186141c1c51408070410440445000100740d40701030006000e01d489100000140d07800d001040b4071540d0001c90720f0340d03c100b100041c2d003c058020b09446590540384544084032921803403006228200b2650301160000450800b03050f40000c068200404c8021403083c02c140e82641542c032648a841c1c00000314025036a10f25404014001644e4016200041e00042810041c0017034100d9020350850f06030f40c02042c040c1045564188559540601d409401e11b141c1244080040d0380d074010a54020110383c1c1c1c004070b0013074008145d049915180381c0a401071005507155111680505514001c400c2070310a1080055100d1030a805 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 753125053 1250 753123803 753123809
    0xa0c032a05030910140402100f02120a0215010311191404051302030d02011506020f190503360301020928120501020901030606050a210e0f06091006 65
    0x1a450403105101509488a400050501256024201c13504500500600801102506180c0d5942e00b034a010310400c90405020000c50b0200a8051100440d281e00040d54580d0b20f8000c2d8070103500d41c0d0750724400700d1074100201d00001080d14504000010062103100c00c0ca01608100c9402001c1c003103100040060411510644d5030701446024200d03c1414150300841d04841320381070400c0b005c4101e80129107030010101c89100141c0d503e030890f500c0080000b0000c070203800c0c988007500c031810422400c40d58418000d6000c00c00a200040d0b05001c0050400880f508000342203120f680000000d0400d40303d08006102c0c0d01003078480749200382054034061003140ea00150060081e805d001003500d0380341204401c0f2400321050b081001d400b01e0205c0041e941da40c1e0f40c512500000d40d440e01400c00040a6600c15032088040c42002d0059104180d008925007082d070403501681c40544c00e6008820003d0650010501020301480c003400d0022080414424451200702040320382840c516070f81c0b1800c41d003e603c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 753126303 1250 753125053 753125111
    0x20705180402040f09050a050c190303050f0d1d0a0308060f1807030b04090c090c08091005090316060c09140d080304210c030801050103050c090909150a0c03 69
    0xe00060042c50700750304c049540c1ca03c4400c001029111562210715029a400742910b066011510302c03070320351411240c03803070821492030440c005403071840d40c01038800c1c01128244480e800d00070511807040c240c00d52140f4002d08102031400d00540081131703020340700d0b81e81071000e0700011207600004085040c00d1004241c204006002d002c20302600c9092403070101c0003c1c0031401003688844500600f80e55a00901000364041d08448155030b1030143c5190885601d10707078190510000d1401c0190b010f1010491404145041101098a81e00c91120904611034041002c82e003040c3c200507a01442100c0e4005a10403646882d8126695242c0504100d54080c6410645d440414512628005004403002e1500244a24441c48010800b081c020070700315120307440840065183e1441009040d84034290b00d004001c01c0c01c0c10081810f00d41c29130308881c450801442d0040c58120003054070074100704880c0790040040c10f0300c000f0900380145000090040c404500e400030742002c012151a00c48407601017050b4141c6 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 753127553 1250 753126303 753126349
    0xc090105060a182c0c0712170f010815040c0603090203012003061c0b27010518011a0f0907090807030f0312020702091902071a07020705 60
    0x42088680d9106544000402080c2d40d10400003d400ca403002c0050607420989045081d862a68542d4003588090300b5020685410305015580c100307001217403241508016100c0400712186400c5e200700800c503545100c2c00b00401e04020a070302032000c102d07040c0d88009060b50703030f5402c050010300102c51007510040e140107100442080518009da0010311458070181c008a480d01c841080348004000c258462060000c0c0081003110500d080840140c0c00c3d640c07013040c90030b030302a1034640e6084640010441d45c10440c40b481010860040e44000812940031040213102d68a444203014528007901540300f0000d60030014003042c0e000c184800000303000303400303071440036061011820031440c0d50780034103140140010241d0200e00e10341c040c41a0b2000e940940f0319100102041d1800814142404411703560040c814444200103a071126201a0031104500f040942e034406021808024400e494009040071039a80d4402c108040241815220f60199020360f101c1540d64802d122509a007103840e04100780c1d207 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 753128803 1250 753127553 753127559
    0x60b12010c09090c09090603060f050c041a0f0c0a050a0b01050303040e190e070806010f051804020409030e030d0804110a0b0a0311070c060e040e0f070e0c130617090c0901 75
    0x21303a210000c408100c1c505138041a0b0740c0c56065040301c040d60415103401c2e0326103090408403102c501503d034001e041ca460700c51405103040c5c01016200f01030000000381803000125003800182100991316a5800310741544c00c65425407a02c3c80d504d07291520112048a10100002541d02d004403c2c0e40440c1d10300208584903070340b98605003012061400e4105032403503690001600c41c5c40100100c00c0a02003150051481d941046080006200c1d2988214400c0c40d6980c0182910844e003045c0c190000c1c0d064601084204062a080e030780c5420750440302d034047c400d1650074050303168040e41030f9014501480301e4141c0d1000220601600c12103e00503480038070010440c4030501442a40030f040d46170f104601803800e00348299181800704002e41e200400207000340b60702d00706900d070521130941d001000d00c0061007419000c000581d282c40c0a8071400b1070f20400140041d4068130300b4000c85008a003501c0c03036024520b03166103004d0b044031018032404103c103006500081e40c480e00001c00403000a402001c01400760704e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 753130053 1250 753128803 753128819
    0x1505070611030c1305090112110d140a0b0f0c1b070e07050a031d1b04020d05070201050103031d0d020907020a060507050c0d022109030a050a060b12010c09 68
    0x10008204031811607940d941484a15400740241d40150a1064040ea44141c100c440864600780d9400c40d41c4208242d400421081d6101c0b11085030b25a40032821a25282e288000203040c1c0f0140540a070480401142030003500303c0104030405402d1044076400c01a80720120050b2102d001240c1655000808200000030400d14408060340e8100302401c4074119612581d55000f0740f4026035807030300822404100902d0745900360207180049101d000200d0900114683d0039aa03d9400100030210300c440780100314415200e54048545890001030180328605103004001d00821007440240c0025500300c41d42d00d00d101ca042010948100c00804240b81441c5540800006030381c094205000d40c4106000c0d1400241e260003080e2045030030fa102d0765280d03102050302c2402c0690b000c0409086400502104d00c0d80c40348008000703030110314100110346411070300340031078984401c440002e042481510b01d040b08026868100002c200002d4902a80c41c0002c0c8281501382c507101c00140c0c001c100c00420510540e5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 753131303 1250 753130053 753130057
    0xf060609010b030c1902030a03050c13060f1107030506041e0c05010f030e060f0118060305060c07080f0c0d03060b0903060f06030726071e0b0d110301060302190503011505 75
    0x20074428050b46001420000c151074100420701740b6001da040414484070031505032064a07800703808001c0b080c0c50a20b030b0910500700c001c1c0ba8010304007800000e80070002c91903c144441840032041008a92005442c2e080866560380b0488080310343c41c0d9461140c41c0d883d40d14403920551190300c0210745071914204001564031b040942400810191b582c3c1e0b14200920040082c1401681000c40714119541040760f030541c4801c80e000702020103410408200700042001500c070fa80034104c51003050b00c910292602d0366640c40342e043d0030320180301d0102e86414030100100d40c2d028191040e44007008069611105001e041c02150a510342c175030003401c0040d070402c808001c01c90b400300340101903c422617158210010940043e82c400e038140c20180c60140c4401e803040100e007014000c51207010800c80c002100e8204540018040c1d00c0304020085803280b649015504140c00400c1c101d00c180b41c4a45c2c580c80000c0003500032060074501140c10760144800c190059080700d040c0d80c648464656034048001083d2040c0e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 753132553 1250 753131303 753131311
    0x30307030c050a022701050105031e041e2f1315091a04050c041a0d020c01110901020c042711030a0b09060106090609030b091f0606020f060609010b03 66
    0x30f0041550034401a40c0740d03030490b424500d0000c1c00744800e070342c800c0b10a03200040581000e418441d042003402041550500d80c144d2512038001c803402d4558591520800c0c01269501603401c005c05a0310b040100b00501c0c0300041003030311480c034500100000c0d400340101205544c2da0035030411016806c1c20641489034100703d5a010b440d1160000e115a81c94200085401021a20b503898407120354000071494107000d4a42c000b904102c10b1802c09040901c50702040c80b0145100b8400340c800034540d25000000d80542d11840c944800030000e9400c1c1400600ca07a90040e0b85a0b0b0042c0600c50505145240c00d2040071060680302d0200710050304040000e0049401065050395115003c0600d401503543c100070300320b8414032588400d191410800c0300e01d4901401078001c0c03800d01c80c01507810703c0f6560384204150f00701c075007204461045413151084c103070605512500103416035a6070302035161400c501d0b0b0081801c641e41942107400401803003580a0315003a0540b2182e0f40711251200403c541c0b504d0001079508 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 753133803 1250 753132553 753132563
    0xb0906190f0207020a060f09050a15201504170c060a0510030203030d0b120a0b0c0f0403021f0801060504081905011e0b0f01030e0d03050901060519090e010b030307030c 74
    0x2a00580d500003035100440e0b640000c6c009000030100c01c10499102140a0003841c007980c0140da86410000402c00441040007440c0421a841c4903440b9049250155030042031600c13015101e603c0c079030080e0440314110448040d10000c1c545501e082800350740104032040d086e41c8401801c1c95482e11104c54010f03180180808060382d203581e0000c1b001d07075014001040d2060301214001410070509007807000b00d4900e0749162800f600402c08110100390707022250f0f41d01015840d5100d641d491a41d40030340c40c0d8025600080d402400d03521600e860768841a00c2403112030440e48884000b6a40c0d010222402d200d503000c0c0d88016040b0798050000c0e0040341c5103850010344240c2c00480d1a02500c01d1403107401c544610042c02c0380f41c89540c0c0415a052812101e41844001e1070103120000c507443c000c0b41ea451240c120941099a41c0c3c0c0040e80c1c00b079080d4046405000024020501005005131440c1843c51a0103407100191528141408200301440346844510020703005d1410081a9201070b159a1030303031a01651 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 753135053 1250 753133803 753133807
    0x3b060c1c1e0f0b030d0507030503041502040902040314011a0d031238040c05090913150b1815010f030204050607140d230c1e03070b0906190f02 63
    0x14100156004420b010105201d0004618115000305490106030380b4209090120400c50b0341c011035801002c0300da10607042601c07804400c05c0200000001e104991000010900c00301c0d010003004503141306810120a188000d1180302c1e400d443d5078006070b00714180c00d0341c404005260b0800080c06006201d0711211120400102007a45207034850f001c0c4035044501c0c207070100c094640741d29012585124880c80009880402070712140d14005017486c8501000300f4411000c410004030882e4205603840e031b545a02c6080700800c00c10108028014110f07100c0381e1403180501d008203000754802015503600c5811100e010750481e550302001550103030106088175082540802000c103164079000300404403144684843e14104503402c0040d410458000d110800300040425407003104c801c4d007803007140d210752034400c020b69560071614514a8001c4405541c000100000d0f00f40201080200141403960302038001800d066854542d440e8441c04120361388240090b459405c4920308945030702c030010b00190250014 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 753136303 1250 753135053 753135101
    0x70e09161101150f0603060e0735010906050409050d0c05030d06290c0705060d0b0d110f24070624080111090a03063b060c1c 55
    0x40c00d42e50100f10b008248100349900700a68500035203203000400641c581000035a08100d00ca00d420807020300a0b00412a6411048100c0031200394400d9090303510000701012211000c2c041d950f213440074030829919600c1d08400040c1070401c2c0c028810b42d1340d0b00ca4040c282c1103024240548001031940c1c815102e0380720070300101d005d6402d01c2c403601001c5c0c2001c5402484640401180500c810040d02003c503144206200342810004001209000e4820466080d5124070401d442728009040e10038170198000510b820b0007042c440c180c1d070054519002502c5400940854005000e003603115000ea0b0051031201c2e002e201c407034050b90341c06088411b114110200d0180c4a14102c8141e40c50910807a84a0350100340301001200f90074425400c107882401c0d41181018000000030758404183c1c40080c044c9501d0741c4140c1c028452004140e800d4508012040d40c010901401292071000391240ca8609441500041800340080310140d0303041803044400a20b00032800345050b03016005010381d2600c01c5064140d00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 753137553 1250 753136303 753136337
    0x14030301030503030619080616120c080610090602030d0e0a080703120e060702120c0f060118050901092d0206270a060207061b1b030b070e0916 63
    0x460007540181c0c01075480c2d041c0300f010800d0050300caa1100303811600d0410200030005011401c0360340000f8039005107048109a0105403104060740c04c40382c41c940d241c580c004003401e0300420712502500c3d0a881b84c110001280009903035803215400b562025910a01413034540b1445074014031030b070501078029101002201d40e83d00110b0f4018040441c0410965002121414110b108401040c041c00006103001c0c200a20040d4440f0b84801403440241800640740740c02e1082040308030780c003203d81030850304a582d5480c08103140c68524074200800d035041102081425005004120001e40c0100da51540c0d0302d0500c4a0701100800d105105a0f00c038228402e9101694a602c0600307090b841615410b19111558203401d00303803810050b055881600b0951003440003643c00900c290685600b802d01c40c800503207028021000b1442583c00508d29072803200100700641549070704d070742207030322603503201c03030f10b9120503000f541c0741003507503030065003141c0c2200002d4030081c944808103840c9500c508080e10001860b00c0c007 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 753138803 1250 753137553 753137557
    0x40911060318160e090a081806040509250207050307090e100c0e030d02150606031b0403081201140d08031506040902040521061617072a030e09041403 66
    0x24442120010800420013692040000da03800700c0c0090241039003800d0b903980d02c0341e68000d60108442100403d00120b41c980c40d80821203000c0c04000b00f890030a4a40850402c440443c039480c41000069201060aa1280009a45020b5860040142000e641481014002005403901c0038605110b903942040b0300868601c508441035049540305612000c1344401e051030442c0400c0a101190b1100700c4c424100d407151408280c0140080382c02c240d890301d07885000003001940d035003540045800014000104210381000704103900e030101c444100350ba0703600c402e0040070300c034001c086800034004030300040001c0c4c402000399805070000095a200f803502070080356046e0000c0e009810540e900140511661820800699944c490303000d404400031388109032551100406040c80b42c402a81160030425a4007961003145414090031903499a0b117800580105001d26000400e2484500f002840d0030380328140c5040c503043c80d015201c600342500c1c02d0f0140465144002c005489001c41c1101030308000b481840 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 753140053 1250 753138803 753138823
    0x1d06210601060e06040b1b010e0303010b09010e0405090303191d0f010e0105070c0807061103041b050604052107050a03031106060d02130b01120507020f0c040911060318 74
    0x50032a5030400b400a0001d03042d18010030304c10f04080c0020071076041100300702e035040310490041140156000f200140540701e00000c1e1300c1207000201c004600240132101030011146c00741d172401d1400b104642400122038055a6000312a0001c200207510703143c00300c001d00c80d40f2688050000c1c4110303806400e06901040e05030f61000c150081003603801021000d005802201c002c400003000b490616403000381c40c4c1c0009180041400e1742c0403414030140321481d0720800c0102d111f80025562031800745482c1468940c1d004502402065100010429003014410345094800c040c2010b10001d0181004c4048801ca10040b600e6601c158000800c4944030f83d2100401940b10b5114514465240204a41040b600812480c01600c0840c1034002582e602001c1c0e10303c825500800007002d2080e000102c07403408640409403038060030070061296013a070000760306038a0000301050b9032161008500b00025200318420251503104564003d008a04d0300100a54010914101e01c220290341c0e881440d0070481c600b0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 753141303 1250 753140053 753140119
    0x10c02030607051c061214010609050c12090109030e131506020303011d0903040e07030f06030506061003020306090402040b180406060e060d02031c031401090617071d06 74
    0x8500d9520f4001c2d000c3c02500300300d0384050140f10190070001b000d1070f4080c0401c40500070205001864041349000e40c00080074000c0301c0410300080c0303468048044035512104950001c0444c1c1c5001030304201041c40b500e0354042d032640d100d641089500003000300703070803507a1506d02d50584d542c591b0400501184100e10004c01064026607103030742c0741c440d00300258083c418410042c3c807203401c1000800c1001100311815038000c8040d141041d140c6d144210001e00d41000103010051030200080180800003403001c1c072404007100c00c041d080700c8030f00d4214164081622855003040c03008010800514254015010011000e40780881041d600d0000a81c50b41080d207080e641c641d941c01c003d009000340400c005610003010345c0e000d8200c0400b81c1c00b183c0c2c0c445200344030001c03103c5c1c038900450031640320b03400102c04184a0003145046503110100724008103072600c00c00080e146181e00702c900c003000205890089031102800c881c2c00781c11000110101ca80010130847c2d00400341181e200a62400d0702e5a04a016011 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 753142553 1250 753141303 753141307
    0x806090a0b041b020705030d0e010c060b04091b090c14090102030c0d0c0201020c010c050a030e030118080c010515060a030b0607080703031a091909140a030c0b010504050f04020f010c0203060705 85
    0x129006805c04240790041ca010742c01c5506042c0c62680c001e802080204403c4c42d00005249081c01d144008040d941c000aa1041c20034140006101d0150100d407442582e1402d08010b0a6840d01d0a004a40958400030041600040301404a283c9a00030700740c0440180140c0b071070283c5036030400c1d041c5031032000040003184104500401f03550341005000e807104801e003007240b4455002e40f6010b5958443c90b00040401c20341100e0b0310764a481c20f40117000f0440305090211252391442c6841c01c03041d0020107031003a2641ca007400160362900e40540c014800c1d48007400d41403410708060300c21400f820400b004541c02401c10450342d80010020002000785a000c0e55000607000c02c210194803890303d107000c0e03c5100d0590101800300d050a216070b401d100e0a45180000b614103070304d2a0048945421115000329806541d030420145504601040751840c890080c40c2e240f80c2c0c83e8030802c001c50f8000d80301d102094100f40b00080c018248440b84c4c101030309050500e80701e94919980001d1030400c045030120002800 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 753143803 1250 753142553 753142601
    0x5040810020a0c0f050715110c27070504030b010b0a030b1012090201090f031103071d010306020a1e1d04020c0a03140408060a020301170c010806090a0b04 68
    0x144214149004260000d5207000b8407030342d00400054200310050034407210407000e43c040010030003420001706650800b181007240108001707000b40b103110b1078001e92400f0b1090b42190929084c002c03031558030391900d4040c0c922200f604501880a50040070030f824000b08000102c0412120310905000b0820b503103180d40e8031500e0b204000d090310f0384082036900035002e440081c0b43d9103804c00700c441103014070410009800c0c031050004031801c911035440b108007080d003c0f001100340550040a083c0c415010303000c46080540e282c5a0070b0000c0000d0440071060200800144000360241d001086a401140f90450a00025481d05094107021100c558007240b05103051401910301c0244101204004550440c00c01048a003500d4488519403001004c001c800c0d102d02071200582c80a46028011990403107200d860b010f01150004d41c000c0c01400b252000401c1010b64501c400680340440c0c01040c0e480c40e000d511a0414060101c2000d08030000c02926000c91400607141c0e440340c03000402d04401e01d050f030062 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 753145053 1250 753143803 753143819
    0x1704090f1b080f0118060512010f0e03030103030215070c06020a0e01021218150c0609160b04031a040507090216170a0c140a020d0b040209010f15180807060504 70
    0x503608107040c080c8071030501000811140c43c103650381102c00511894508020300f0468400901d40380c0c100961048803420748002d1a42e055100349120b00c10300070304000f03451415198550364002403000400581c8221095088056144c0400e900a51541826480a015a910941645c200ca82208000b90481c0403603520396038108407510800400c10075541c0ba200e44c0081c088540002624154007800c04100b07200c807455410f2045910285102040d42e801c1d05040d990152200e0703810948010a045603032000c16000340741811101107a0f8000c5c514840005088445a18080020300a60f400e004a00c000100e03c3c0850008040d004603070441141d41642501d014a04030a104210f0010390780d05129000d10707142c01c800700843c0160018500f01e11010480302c014500460000d00a4116001c070300d00804001e5141c14845c0620b1088030300d26020303038036010241c18000003881201c004002c0b200d111a00c0a000300a548050300d0841c10552885845049082c90240c050b842400040c000060402001e0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 753146303 1250 753145053 753145091
    0x50c090405011a100e01081b040e040c05090705030a05130c060e0a080307050a0f11190303030b01020f0c1302071202070812090901180e060c03090f010b030a1704090f 73
    0xb10084411980480c030959004103034000da250700c141400f0300c00c00072542a0361540c00da40c1207519819030f0745540b541c8911a0ac40e8142040e9006c4540101c404404250b42c42e016048910410081d40c5450030755a541e070b41c0c0c0c0090180507182c00d4a4501c0c080402011401850741c4038050081c6480b1541c00b50300300020300030100c255a00044485d041400402c00056010400c01000c0c2e80100c1c6594400780903090041444001c80c9542c0e6114a4101004242c24110148241224003e0f24204201e5125400598840d50070710581c03543c0d40c0015030283c141e46000f007000440d003080b00d140141801d156030740310740c001d20340b42d96480d001d070303000300001c004400003000030719020441e560285042c011040042003c444043c0203a0340520b00c41116002c40c01c50540c0403000310300d1440115495400c1070342c4908855807040d201402e142c0030f0795210810031034050103a580e000704054010070140c52152545a0807201607805000406810040002c45075418010b00c01d00f09a01714000440102d694002d400c14 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 753147553 1250 753146303 753146351
    0xc200f03030c0a170d14070806040b0901030b070210021812030f1905091905120c06031b040f27052511030706020c0609070819050c09040501 62
    0x80e40c030811401c2d42a05000c03a066001c1640300c0304a0302c007418100c1c56800d0700d000d01c80700b606540340781c0b00510750741a84207a4024001c2402d030b1944d40c01da171a40710601007511000f1101a4204030b0901c010400542c3c0411165072000e81481a0740580c00f5801300d1005070380c42501c2c02211000451945035481c034000c2070b654034441c54040190310b4420038042d0310215010303907480382150710307070315150b070b20545008804490004100038011419000034601c5801c0036000f0707004450081c040030805540c03980001603041140c210042225003199141d003002040840003c4540c2091441800000340c040340300c01c803c0c005044003c2c0c2810341c00a8170348002d0a0b0000031582450a94203000603c950320407800d00c01c2d0304004e00511501c00100c038003401500c0e00c40ca910400e800c184400900301c000d110555000c0c0c40e4180c03902c3e00307468a648414031299a00c00842c02148229004840007007101703e1480c00d400071407403040098484007641d07000040c00c60380302140c042ea1540d454201c000d02c040c0d00034003d9102 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 753148803 1250 753147553 753147559
    0x215101802070249020406230103020a050702190302060408030a02060c090d0f021503010618050402120619080a0303051609060807030c050d02030403110601090203250c200f 76
    0x8211303a81c20340c0720000024006950354207506030818868403048140c20301540243c4207201240c0d60b0f03011151070342600140f400c410038540c240500190710900844031074801c155141d50810304c0783c0d000c210418482e40800e140010b01002c0010060300c03000082d0000b072030900065510f851704008060f0810100400308040b11b84100a61029640e40c1050280d005070004500d10320201c10703201040030b0908011640c59010008400003503410b5200100031203071441d00c05181e55940c0c1d200700b88003c1e400f882080c7c3d50f01d01c1c000c500040f103e05180200190f024055a17400c59441c0c1e03648e40300303410700c04003601c240c1c006501d51007040403140000d000c040722a00c040ca0700ca11481d29014005014210140044080584030608403180d01d205d00150344000e2102c5408560302d05281c43c0280c4141490740c0801d00f00d00030394000007180800b40c420740b84a0818443d4000301582d08000b0b0f0602c240c4585040402d01a034108001c002c02d20081c282e423003991001d41c140c0207111001c4108002840d074552007501c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 753150053 1250 753148803 753148849
    0x60c080106050310090902190f0815010f090903180305060f060303031003060e071706010608070206090c040b0604030b15030f0d02121305100c03080c070302151018020702 75
    0x3004c40f90380202c0304580203414005081940742c80000c05911142d00c1c050340d00744040001081c544102c0d1b200004441c0c1e00e404980d0403001c0c0d030034110102c01e03007440742191980c034050307040019029541150301214400d150071205e002c1800303a42c0344500520381003600d5540c495400c00000108030401d860304241c044004508600d000e980082d00c034071850000070003070f64403025000000c0e2810003010002e08600868072407050031f102d801d0340c1c1d144024414100052410b81c0420655030000c10b6550003044142c000c3e01d10181447c040c48090000010309a400010070000000421452601070340140c02240290850620f100e0426240200c107c80c030300c21030f81280f4a007085140c1c0010b01d00703030720000e1081013603121800540801d865101702d23403215800842c1c07030b40140c0ca0710764032484001d42c2d00c1c0f082c2c503600d000744c0301c280340c041d054018920001c0c00341e44800220800b03540d20307a01c2c0300d521000740c0500109483d11104071a448842510250f0265900481c00000310b1404004c1001e045425a480702 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 753151303 1250 753150053 753150061
    0x20d03020c0d0f05040909050c19030f122006090c060a021f02041a03040614060d0308041b0807031104111204050f0a0f120c12030b0d020d060c0801060503 68
    0x280c50b02d40c500c4294081c48000103d1082c0c041c080c0f0152801420410340401050495003401170320355018480f081e00ca89510b560341e01000f080c004569040c0c0360025102d0246031015a80c12400580f41900081449410010010701030702030b1003035404c16a1140c0203040d403401e02c01e48462a014241d0700ba03c0c4104000c3c050f455100380c0c00a50080c07181490743d880c0d4070050321030355884000d00c9250014914001401c0f42c0e080e00c0c0c00ca40d40158065845943d0401c4803d107600ca801102c0e450030317254607074004081051034010902c02e072042a0041d01640c194240e0407500c100903003590410350300c081d10703a030068071040045c4000c80d000940703520010b45050107248a070300c019031824444c500d41c00092104110100e02030020822079150103149d2081112400149820042118041c02004491045101808526551003880030303000466004508540b0000c0300349007034010304078940209810614160065000d40d407000d0100c001d45008040c0010000c0e50404010a010f01c160400713401e00500304148 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 753152553 1250 753151303 753151327
    0x30606060e10080a020a0912030c140a0b0a02180306010f290403081608071b0902071205090301091a071b0809040b04020409020d060609080d02060a180b07050a020d0302 74
    0x115522131003050300142d59800c40101a54030708002e030480340822038030400e404c0406400c8420780d07988034007680b00c3d0100715004072a45540c0300380740403004040700c01c15004034880e04000e0b005071013200b13807500c40c1444680b04480407a01c0ccc0034090784106600c036035002d01041580300c01d9440c621440d203100c0000b45049800d00802110f80b1841c48020844a400a5401050500c500c5464442d5900041c1140d85040031308100101d226200800e40c120003101c0c0340007031001103610890b01022f91000e0110000d03801518250350a40284400075015502c40c034844000860b9580c48030f004140e0020f400c0c0090601d00d00c000d140b10110217401052001d00303801c010115140c1002c1d80d0040034103c6000c669040d550000c00c0c0139015540c440c1900d01d0000c581c0c48070b621240d80103801a1103480da1502019039644ac250f1790707580c203e0b4081402507005000810900f0b101134010702c0c2e03800180c400764a038403074450360f0b0414581001c40d1160005040031501d422080c1d0705000004825119150640c1041c60302c00070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 753153803 1250 753152553 753152567
    0x15020c010e13140106050d0606050a0c02040905010209030a030503040b011d041202100f0c110105010506090607020f0d030f020d0503041a07020f07091a04050c091c080301030606060e10 81
    0x107081c426154414001c1c0c6801580c0c0008039207070615000402a942d440e100039100e50032281c6081082c6003014400302d45644500d05440c00a102c1c0d941e2015014542d4080c0300081c41c9004081d11b0b80d540030004858951803c01080000600c25540c8503030b00d01d0a0305000c1d0030002d0680010710600c942c0c050034400b020000221a8120341c00410440c81c40c845000c4c10703850b140022841c0f03907600f82401c8981a001d29913920041300b90441ba1540c0c860a9a18075401e42203031801d0040603440041400606240d0130030001501c40750b4030280c602039104282ca00003594100381110100e00081c0c014605e07030402e50303040c844d1070509100c60408a003075040c2603503480020040d0303907005c90003e000d40002600040c820000b1203082c1122506035448a80c441c1749501c094440040d0040b14a05244000401402d143c800c02d4495150511458102043c500411000241c00d0785051742c4032100049031404070318100b00860003503102c0c0d000007d24500e84100a000000081421413150b40488509041d507500105 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 753155053 1250 753153803 753153827
    0x172208030403031e0e061b071d070f02100b011202040b090a060c0203330c1b0f0c010e012a0201080a02030411010f021f021201080d050f09040b0909010615020c01 71
    0x30306c441d2519101d06208002c1d0000040c1840306200701c8900282c0b607420b008070030075000d041e10039480c080c1c0d4900c1c3c803d541c241102d103460350040c0c1c003c24941003400c071990301028100d40145051000120071503031200c1a031700150421186100b0000d10021540b0b840014000180300a04050310030312507d0700042e807601010b02a050f031170404214002d041342d40015106841a41003c000703609810a49402d20094106d0614464000900080c0540148000500c040b408640400070905080d07000011564002c02c089014144000020010b41d0210f040700151140141010b81c40d19245850000402d1400c0140c615003506204000f403001007440c024003510801d030282046401030124400413032904c0c140e800d600c90403071400c0860441e02e0400c0e40051503d00400c005041d49a41c94007050b03a15001c40130301500200d1030070000302e418500e294002d040780c0d200c018000a180c50b0070745c000c148520400c581084103a50b588106114031820002138000b00a0148000c1001008080000e004c00302c02c15 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 753156303 1250 753155053 753155059
    0x1808030406150e0a1b02070807151e030e060109050402010c0204090201050c0d02030301050901050108090a0b0601020705060711030607110d0c050a0204060e070219172208030403031e0e 81
    0x2842e140700703079042c0124039005102d0307502a10814074000e6003040c02480b0904002008500103103105034850320000705d16040d5805c000c042e0042501e0401852103440e00e4074400014400d164003000540d03807119409c0c050003012a00e0216100c04844400350424105800050040745818148805070341d001151500a07035040d900020103e0700c5000503030f241d0041008079420f41c030030a48141d44599021002d50b0490710b00392230b8110180d8a880064401c9001281d200e20f00c2e620141d07000020545009110350001c50600580341c2040d101c0300441d0751a8003040040e078100001044080d405c0c00c08200a40d405001803030700c19101450008405e848500040710b032405c214a041c80d41d010303c1000e02000b07694580c001c1c030802841e40d60302c080c44040041190080003500421180b9584080e4804180c5002c03903210780c040e000c8a45031201d01c2c260342c00200c00c4810003003e2140c240c603002411503600d0003400d00c2d000107544403031561400502440c0400d070300358900e1101c58201c501c1681c0102c14510318160031 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 753157553 1250 753156303 753156311
    0x604150f050f01181418060105090c160f08130303110a150e0c09040c05091e04030c051f0e01060506040302100503130818010e01020313060509030708060108010f1808030406 76
    0x4504d0000503240481e00c01101c000d1410a020903400d2040e94481280d1481d4141d80309684c2c0c0b40200140d682c000c96084010384001c21199000924800c0a00e41c03240c840d40525220714032a4488c01e40c8c603048040b010041c080811014400d02d50810300038504050084000e0900030010f54511a20b81e6204a481059949410511558450521014100001c040c0c42c202c41440c1604054080c01080c0c400d080c016603070780000c154403003103000c00c03401c4640c074080c03040509494a6500704c5590f150042c040e213450140c14180c6e0145008490004c410381c20128000c1011041d0b44003490840e90541e02180c8170340360401007007005807100407040f54401950701b00503880350b0b1001c0484009010003100180340c1440000c003040822040c0004000070407080e0f03214190813a2100059999105080d41000001f2403030604000075445100201185803020b03080c1c8d16a155200c44051820000ba04111066511840c101d46040301d40c0c810b034102130120001201c15008a0b850703c2242c0e200142004d003c1c1521 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 753158803 1250 753157553 753157589
    0x90c150d110c010605040c0c030e09180a0f0b010b1c020f0403051009030e0405060609100201240312020d080a111c0903080603010e19140604150f050f01 67
    0x1680d4801140840000070240c1d81c1c240740080756009000754000c0d50b00ca5864054000d144500c51460400035607272544401e20341182950030030842c000002c2c24550116542841d203587c080d42481460700b000e01c2002c4208203070040789000d03980020160000d410049040c002d00c003ca54141d2420130040c203182030010380d0307001e0f0140f244400c0d04c1242c02c0a401c1c1d11418640508000d45035000d184141c0c02680c0305401000c0420402060743c0e42540d82c1544002c0a00002d0110701e0b02c007529401506c5d82e4000050b00740c0094101000d4081480c1140081d135034030f018100140540c00075144941e011a102400b00c8045009020700450b5001d44030301d004603640c6e1090071a04100d0421074958042600d840201011040b290b84080c0a944200701e00180310711001c11028101401100005181d19010b00842500146415101e107022030042c0c604441403098410914000c0c0089406540268240502c0d2800c05001c1000c0d5a40d0350703a4031102c1c614003000c00540c0f007080c1c90914156200c0f00101d004a141c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 753160053 1250 753158803 753158827
    0x7050d18020904080415030207030c022710031509260c03040e06030d2c040f14010806130b010e0702101103180708190c15030209010305090c15 63
    0x30840250070844050a103c2802620070107801203e03070a500c2440c03104001c0308124141d001d480001004241c400c0804001481c0408a00c1800760741c140007100e0407414003140b10f4000006032002c100d03101155034103205022021401e08070500040e101032241004503954a0a0705034000c9400e001c0e10b000c40003a82e00502d292003102c02100850702101c0d21107494030307503d8448840644440d44244591612010064020900013800f003024418420381e400d10b550b484248494541c00c0b295000d0f2f0342e10303140300d4400f04034410a8010040c5c155038960310740c1440340313244c9440d001402d442c0628040f280c0600001e5a0011002c5c155461880030b1a0b40c2e80b41c00744160b1911004001c4a2591814041002a4403440320040c40c400d0b5150103250618007085540261140041e0181c52402e400c0f4101644010301254007035140d0310300c9030340c249a03807680d1006e07429040d9100310a207a0001c1d400040c003405669140c016940c1090b50b071400b40c040c0c0c4101c603001801034104082e0605500c0808140f07551260 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 753161303 1250 753160053 753160091
    0x6140f09010509100806090106050a080c100e0604030f050f0c010810210506180607050705100b0114070b07080f25121e051b0708090a05060a030f060e07050d 69
    0x3007041701c2281c4250414807000d5003c2c2000b030142c107004001141c2c000401e1000060224500c01c800b0b402c1154448407150b044591045980209800c82d0080000200140d400074417480018000c1015181c00c1850200d10341c10815081c4500d4100241e40007400b140c0120b101c0048103e1300f003512002e00101ca05006c4c551010741c42a000380280c005c00042224030312810f414091074810850656095690303a030025992409644005840b50b885814101d00008441d444000c0000301410003081198201c0800710540d40001421503880c1c420b4001e01044540210240c0d80042e6038a942c1000b914104040c00da1000100b8160164a000c84407445240c0b40030780d410000c0d040819109000c40400d01707050001c2400701c02102c100c81c82c941000111580700c510140e500341d1070f0801c105072903c000d503241c140090300f1015095910001c0343e4000503541d038940300108a0b120158501080590100d013141d011035a01c0d034002c906001b41c400400c03d15651040031158001d0314900300040d0f086128035140008 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 753162553 1250 753161303 753161309
    0xb0c010f1404020307061d1909051602010b01090605030a0903090906120212010903020606120709020d0605040b040608060112050a02060c1f0b010507020409111306140f0901050910 79
    0x5500c0d1100180a101c00100c20520903402034044130302070ba0341c0d60700c2240c10070200350341c040d141c8012150f080c8240c540400d409030340c0f11440080300665921445940b01311102520721030000210140c00c122300790b40a0180988000c42424004282445c0241c050041c0c030000701845500c6940e003103c03c04040c06146040e0142c9140340c020803550740c658401c1d1039800c90802d8103a1040d01d400d192030092000500900d030840381d05902030080b07a2110414054403c40302d01041c085400707586000f01d80d228451024109610f02c2c1c49000c03030040d1401c0280011070340710800c0c070ad0242d418034405100402e4005036090440310340c252001c040c01001c1c20401c0c20560703440c8009500c20390005045405600020301106a0713864550711001d5428803138002c00c121080c3c0d64410703005c60b000307010074005031030300d40c1c404d92825010340600028000101d000412004503100300458495407000c00340881510104501d060fa035080d40c51020b616407850000e024494144a214441c1ca0800b00007a101c4980d00511001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 753163803 1250 753162553 753162581
    0x203160614030147030a0b06040f150507050a06060635130b0f180a050d03150806040b010315060b07140102120408070215031509040c0518090615010203040b0c01 71
    0x30711100e0350031301c00b2035604c291000201d42d418420a1146441d00004132801c44020240c000d040070310b860100d004900b00c40002c0350500c0018021900860300c20702803030b811a0b00ca82d10000c0c403541007040281200c1d07206840c0e030740195440306c1c425040041c0c0307124921800d0b0800400c41143e0380d0783e4031404030207440d003d001401701c02c4d10340500c482407140103e91405152480c400c9680c41c1c005002540c0d07605802c5001820503032114007803c2d403041c044e03071100b080c4080c09103007500318076101d4022070300e44502914111568180d0340010014000c240d0400f101c442503001050040720301e803c821140394001c00c0d101400400518840111400003503049075050100b422010781d05141071706150a99810480c416405a044826034a9038441e000c004c4910032000510182c810404483c00c2c8101c1220040084030302d510800404070b103982d500a00310000c40080c4141066034540020b240d03050120140400b0036528440420f040303683e030040190740c285c1e803148840988070217a41c4030080c054401030b240e00700c0f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 753165053 1250 753163803 753163919
    0x209130f2a230f0409230c090a090203010305030c0c06040f2c071e140a030e0106050306160e1903030c060f020f0a020d080114040e0a02031606140301 66
    0x202c3e0340c1019108850002c02c080007801c00700340901c034454044030a806003455501000540001c000800b901000764042d000d00001e584525480c3c0490344203130810340e62a8804a10b10400c40010031040030500c8003510002d0800b4509064089944000c1c003070f03110003442021100f030103491410325541160004a4401d031040c1400203014110038000822414245e007040c4600c0c0c0c80714015003202e105c580615246030702e081d84512044008000244202410b035494100c001080e9400300200c48c01002515441e2070350031aa00409040e0140000e2168051000510319030100300b1602d0417481240c1d01410030040c044264a4544020700b800d021100c2402d1020407244106038810000d07041c040005c1c4c00302c0312481035124080d203010308248030701c510140321892f0000860806400425081056030101c0340030802c10381c0064105412203407413000303d40c11158104a100da0006e07031705d40a94001800d10b465541081c01c2810044e02301403800c0403549080c4003c18212401040d01c01c41041d44a030100 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 753166303 1250 753165053 753165067
    0x70618060c0210140610030e010606030209120105090a02060f07120203130b03190f020d050c07111005030a02130b03040f0b0a02090a14040209130f2a23 67
    0x1824034507000e000500c1100d100000e440700c01e2240444a2801098400003980e0b114100310101c0702c200d03101402c00d41c03170311240741c1075450900440e001380001362400f60700c601303025061000001203450a51810f80c14401030206484000c900384000311707010f503107031983c2c2c03088100981c802d03110b0503000030301c26402000821800780c0c0c00310141820412100c0d030702d101e05a880800320100e00066442d00d80c100402840c4406a803000c1e40404c0203004101ca01504140c03882801d102240c40032100e40b0304000c5c0014101040110b54564187c202c03c0480705901804408a00140f05000007402c0342e80d001d0b070016514075441c0c0c0002e2880700030048403000641e079281c1850640d08505650b0402c07590744e001c80740402c598401c18000d940304050041c0c441d040244c42c0c02c40500c3c0441600c1b062070b4000d54200007081c0c29840d0141001c54081030580040348070500b412016007282c000707007002074001c4d5007400075030117103101c0d0159000071424902d0300701c0141d0f90b842d125501040010740c220f211240001228 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 753167553 1250 753166303 753166313
    0x8040602030342040608030a0507060b0103020c060f0907170a03030e010501180f0b090103080c06090118060b01030f02160201182d05060f03010509060f0a0902070618 73
    0x15032140c616402c1c10380108420340903840a03103d007612509601140e000106540d000482c803400da2040c0020301c082909996050028119480340040340005031000a00d0001c0c080070740a510301240007880d0851800c42e011000b261103181c0030b0310b152220f9a03010081030301b078002045040b01606220945500e25009075000d10340d0b44c0504002240880d0601188031145034041c0f00b554101c0d083c0b500045a180d02d0f03007054070000c041d0010001246ca42e1102d181510303484509016001c2c5210f01809561820080d0b0283c0c0f801034010304e000426818103400e08000103008603181511a032001c0d0100310b0805040050b0040e05100384a640e03028804621071842c1520064280d12050003a2508a54000c48190611144002f07010742c400080c0c4510201504500d04418030004508010002d400c45403500300080140d41b2105551010100100050146180490140390014021200507c0e1309900d0808100c0035000d611404d080300b5400300c3c0c40d609116903274100c4090382d90507240e0510015940e00d41 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 753168803 1250 753167553 753167557
    0xd120e190614090705040b0a1d062407020609040902220606140f0912070303090f080102030907051014160323040504051801020a0206060907050901090509060d0804060203 75
    0x306890890070500448070300c4008a03081802009050040c200007400c2609200140103946c0c01150060340900001401c504510b20001040756900c07000b0708541030607010006080104045046071118080c018020650707427004664100d40d045c8c82d882d46a000176000a001007200b604040c1d00960100e02c1d8950b580c044500840c00b00f21404010400a52075940469403481c0342e109050396100c04100c82c98004840740e01401e0341c114014514049035502030740d81424410194401c9005c80c2010400b8050305186041010103061440001c604625001c02c41ca6607400a6101c0c03c0c3c02018011242e410b001d1180b04a00c9004000000141c0c0e01c10041030000c41b9029202d505a0019845014201800702c140300c40341c90050320341c041c150505040500b08001010060602c20841d95600044400e498003030001d8032007440280c014000d9032601a051040a040040c07980040003420401d40210b0ba8010044800766182510b0251a0350355580202e1594480c0400c080e01214020400245050b80000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 753170053 1250 753168803 753168853
    0x120e0d08060a0f034e0c0302070506030a09050f010e011803051605120a05120703060e01152016080c100513030606080706090f03020d020108090a0c1409090604050d120e 74
    0x2060410f401c05c02013119003d085020040050b041340d00204618504200955000130712888001295082969254645414922000f1840c0d459105401c41850280f08116034001c075811040ba40c0503850390010f04910400b10b080e8818040c00008400340031041111031041c6c08a408400e82d07072641c42c400585a500403010394000c0400392400200114030038000c079070440f00d5800c6594116420800b4071003e003089030544404000d0030b401003908841b15180d0788101d100f45d51001d007039001d0b10000070624142c03d541040501e58442a540300e80740e1035911a642105080346051602d4102d50080701d201e80300282e102804940c100400824050340c0452801c007180e06030307102c220a40f40e0300c2c0403501071030056100280d4000585512240554003500300a44d01540c0101610b25182c6550745805082401d60454160250081819203860070198400da40005503440189403500d81136a82a0b540d4101d014890100710031200c1c50100b00006400240050340c0030410b803074013007104036201c00b12101408 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 753171303 1250 753170053 753170183
    0x403030e1e120903190f050d03050105090f150d020102010b190f06140906071118090d0c0803010909020315190b10140a120e0d08060a0f03 61
    0x34548400d0800c0340c0b084036030314400038010305410307200101021110b40c003c01d400d603982c2205d25042c2002500a00841942c24126200080c2c15410300c424801400001401000005100c2041c81040094042440d1004504a8060100001600c0104c3c0507105d60041650000d507080d80000050b0f112039002e01c103075140821601d9407555503c80854541c1000c00d100341034954100100c1d00076007403460040c0400c40c010407140880801c203130b0114081c00d4a40b00000050118041071120b1000c2c00c1c80000d0080300f2928003405664443c0d1500d44540c48180709000740340307503141061821520280040a0242000440c2c50000d140081090002c0095240001445458038054104524107034014084002c000d0396411910089810b1a80ca2030303203e8417414080c8200181584450540c50144000c075004000291501c401012000b4101c1c41d0080c0c195813142c02d0340074061003951180d40d44002165042034201c60f0101018441f8070040d01c60301c0c02540519909100c042c0741c09118003040c45585541 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 753172553 1250 753171303 753171313
    0x2180a1503050609010b0403033c03150509180a140a03030c170403030509120c0102040503070e010e0f0403032306010f1809091401090c17010207020a09050403030e1e 73
    0x72400c000c4c41c010240105088500c00f4001400802d100f030780e407084040070544494200728285007200c0000f40843c44920102c2c08891580c400e666894091300003840c085c42c041004186c01c200c001004020000c0a1031110b034484070320400442400c003c0f84001c550801d0070701210030144181d10352a10243d400540c042414000e10030380701c0307100e14a00d010f102d8582e00c0e0021035480d10b0350220054200540321355018404c819415060303400100c001c1111140103000141d030f41d49400c080c5800d01080d54880d10015249c980104000e802e40301815910000210b6041d0a40d612464198000d009030003c0e0b40780071840c3d240c40000565120a082d02925090300c030b6403844c2000d510100c6141c848040e01d0100c032030280b00200050107154200400342c504c02e0b4410401c0c0b5035440d044600b110b0ba00c50041c1c1700110b80c180d0800c940c06000001a120440d0407000390315000041e000b00715024070920a10f1140fa65440000e000d00d4070a40c00791039140300f54010382c1d8404407030840d080300c0032420313440c07210043c092 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 753173803 1250 753172553 753172561
    0xe031f15031415040f0609020114030703020403061a060a08090102070c030809010305091b0f150a0e0108070c02221d0106062705060c07080f06181f02180a150305 71
    0xc1c024844e100d5548001c0860500003030b5950307171000e8844684128180081072a55804912200c0091841081180c0d030058030740746141450010b668540404820703150010b040c18034292100b404450320345851f820862440c2d101c013000b00f402131180c604e028003103108501010042244443c02407406001c241c3e814000b86e19080381c01030310382c2c0020300c461051461810a2040702d091004954040d200000d00c0f88079003201150603805507030702080c02e1100080000c402e040040d0b80004055401c580580360450004a80394040341503266486a000d021811145085586016940007810b03202d14510171940701940a242c9030b40a801507001d880045000c034030f105903c6106048901d804400145040c60383d9078540010710105030320000c030b440f440c0c0c0203c250200f1135403400c00c1445070100c8040000c00381450b11464407000b04500300801000d640240807582c202c04034480d0400b03a00c052001c00169200200b0704800c10400b0b02d0742c074079600640c038010000740e003540902514030a20000d440510040d90707 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 753175053 1250 753173803 753173833
    0x360b042c131709150304050d0807080c030a02070227011a16020d020303210a020f090f122e06030206040308090a0306061e060e031f150314 61
    0x50115105449240c1d040c00420200b86002d400020b0084180c244030300d000e2001000c0b801e03c80003c900c10b80141c0c400824030003000003c000c0544070704e9451a00108a0600d90402044c12001602d4800414408008103c0110031a0f0440c0d40003503000340b5001c4a2440e00c0e2a07040f80a0030b11102c40f00c1d44142e14000604040800c0c510b880051690b140d5a1030042814000c0142030005402643c014800521160040e202040101802801c84101c100d01300c0600000f0261184001c1c0911b101034014008a40d1b400c203050700303642e03442c101100d40d540f849541d071000c585030303500c000390341c0c40588143c6031203440300703403100844c1e03d110320b102014040250700700c1124905a5070f0030320009410800c00c02c0308101080e0410090409000700518510707032103a0720786620059480c5038008070303070740c100118a030065040c40e41c00110040c030340e90401c0c0d00c5000c042c10000b03803100c0b105900c424a2007400035200310b0100c2c055001041441d20b0140c1d041c4069160700300041100d407403070140c440d40e2040e8480d402c01c1c41 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 753176303 1250 753175053 753175139
    0x10e06010503150916030b04060f15090b0f04150905130804061b080711100306031110021f020c1501150c0503190e03010c360b04 57
    0x110050014200c40d18942d0100e0f80828004010f510203004505241075151260201c03000154065140c40b480d9040c981410300c12079031b1402c0c0c1c4440551610120541c40c41e8262042001c07500e0700c03580001d8801d4400c001c0785611314410640b035805850f007464650300100103212101661b0305080c082104e50740e0300c0030001350f0000c1403c020344442e000380820021180302d20407540340303802d20321507101007944690364100c113941020300c0440b455014607681c840581020342805521070100e140a0202c545551aa0590311109400c0f0300e0184640d103441280c024020003108c040c00302800400781aa410100c1b4220094020240c043c032140106000341c0c0c00c04030500d440318103840040b41d007141920a000d105440801c000d4408807a680001c4c0400041031449246d244910395940e01c0700b2121812540c01c00d0300b151681d100040c01c1c0002e032000641c80341e83c52004e20307064460840b911000c40c0c400d2180e00030318400a900295911600003404200d2080c640d01885004203803d100e41d06441a070380c00c0410704 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 753177553 1250 753176303 753176309
    0x180b010603060b1e0a02030408160302100806090403030e0a1e050705010807270b19090f031e0201030b10020313091118060918060f01020f03030a0c0e090711010e0601 73
    0xa41002e404103819000f04001805c01403080c0c01100e140c59540c42c1d000e800c0c000464450200b80518800c04c00540c10005400340c00e8607030500d881d03100c03454540000342d0048000781c409805c15641c0c000900e9a440100140c8076615080000058032041e40801030b0410b882c5e400d400c654074042c1c2a40052954002c90030b03180900d240d604c441c90700fa08403142040381c0d2200c50130303106042cac0011100020311000803001084c42c18850303140d08a040c0e592600140040740281c0c08229180c0c9040001c101207011640300f4000008000940201c04400f400102c2c080d1140c018415440224400394440250300040140400c140d40b4080500c241d96940701182241c910090506010700104005450003c2c0e24540c030a00403001020b03507091400311400706412070000851038481c00d4400f024454103241031500d10360781e0002440140382c07915600710000e0301c0b800080c2c444000f00703840780a01d540305070088841054034071014008442c549130885006001c0901c25030510125460160710090b52000840da003030507 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 753178803 1250 753177553 753177577
    0xd0f091706100819060917070b09013c020f13030605101d060409141b3c06070f020f03010c02032209050907081005060f09060301180b010603060b 64
    0x40340c0b41301d803a80400f52204032401c90300350455482a1514030071490140251030b0003920340581c54a00003020b0ba0031900c20141440381c3c1a0381c280141c10b19002ea4400410040c8002d106440c4071080300c03040e01c003901a00001009121000c10003402d03401503c190700b4122401024244030a4851017042070b4200c40b1070240c0094808401d070808013138600c06141680101d030142c400204c5514544800340100e1071003180d052145c119802c1c0e02c2ca4080140903090030301204403030250340410880c54243c00540b940c845001c0565611111024400c02070303107a80305000c40031f02400c2d9501e15601d03141c1c040c040400d00481c8200d044895092190405201d082c3c60203000b60029841e049a071012555038001020083c001c940000c075010a10103c036001d414001d001e1140242082801c00d27010b00c1c2045642215206004e240008102c0740d5664210b0454022106849001d9203850344000f003405030400f41403a0908a010b201a00d00f081904c0552604845541d0381c00c02c04a44c1b160744060092048002e0303032038 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 753180053 1250 753178803 753178843
    0x6080309060c150702060105130218090c04030501090c050a09051003060e0102040f0e0f090303100911040905040308040501060f42030c031109030d0f0917061008 71
    0x4160500600520303000e0b444104480b0b51074032a42015811071003c4400a005800c44001000f25092400140704110500f1030f0640c18519400603c5609184140c0c0e1140b04e1f40c944004211081d01080c11038016540100080c0006240703400c112905007a64030915018158060000400340c00320303c51640038690150185c95064903503103514015120b400c15050265501308000a400c0700c283c0001c0d001080e0700a24a0481d26200000b0f51a6400003421110f00750010820000b1400100500409540d281200056810240d9803d052a801260001102d003403400e002d01080c90341096620707104500c075500a20a09865041040c6005440c0c410f0b031a050740402e01c03050405092101d211154046035070044a010740e80c01008100707170017221640010964030030700b02c841a5418013910240040240d1014608031035440801e80d252401c00c441c40030080f00e1a00144403521601401300103000e000154081041e09001c2c2e140c4868085e1035130050250301c4640040c0000010540344600e82c03407002209 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 753181303 1250 753180053 753180067
    0x6080711030306092e14040902030d0807030f020a020a1115070206090f0303040605071203060b1b07080f010b03150c0412030e18041e320a0b070909060803 68
    0x2094140014206001c0520100c1103103400c0d40d14200410841384244400b2505107141c4a1b01d00d403061500081c0e20700a5080600000258030300080026072210645840c0e1029980c4500440c000e04201941300c00c103500018190310440d60004044014034000c070b0380103070311003091001c000069005240c8069103010500c484409031920001801d0f1403440a8400c0e6039215440001030f0450707201e40c0010000c00c00100304502400901020446450715604042080300d0500040f840d07a8002d05030070500842c1e03e00110135140300c1c2401500010800c0710102c4045500451040b0f02a200c130f00503c900920501681c0c00344910703042c500034061712064507054074040c281411220705884821054081c0325405280d81c0298561840d4488691002a50b40e03120782024038000c005408a2100310980401048150001c94220311400e14048081d49441601001810010801c00c4111600385168080e0714100d0090215141145100c0c40c2195140014a43c50386c070700c241107407118001c441d01c2e030344148049 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 753182553 1250 753181303 753181309
    0x6090b07080705070f0f0902070506160302090406060503160302090a0326040b04051c032a05060405070905010803030c07020108060418050a02120109080d11091906080711030306 78
    0x4102407402511442d280c00742c191a014502480350303001c15840200100708000006041d204e000150080c240154980005500e0361030392500060009a1031580c5c7e002183d5000707011b40c1c112040d042014100f8003655548120203460303078100b1902008818039042c490200350f80300b88200c1c1c841c41720041680d0440d60031900c80803228103c00418111a80c00a00700d01d4402a801c030107007001f07181c0304c0c140039901c81c02c003c02d00caa104440e452144d03c2044910540c00069001a00e410300561030b91240329411a442095501c011400c41000c1c0881c0210000d000611501143e220203440d442c500078401660303900500c0c0d07903e100843d00f800072042d003809003600543c4140c10702900000018400315039000700a40c0d1641c0814000ba00b00c0b00360780100030440031030410582402011600b00020009030a141c1c0302c0f007032075200b00790216680690307a1845c03c0d80440300c3c0f400e8070301a170302c0a400340c400c009000102030241c104501a613004142817200244825200d0700d1300d603060b483c0d28005542140c40c2c1d5018 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 753183803 1250 753182553 753182557
    0x1030605012106030506090a030f080108060a110f0f0306030c010f0813030210020409090606050102060c0409021612080405282613030213020304050604120e0307060c030f0201050106090b 82
    0x340c500540d03c64a0000115034200083d40c020301a4101502e81600c40b450098981c0c1c0ba04080d49040c00f820f28010004c0290216500d40e01900003040031616921200f09400319105000e4031f81d1300e00d00041703566a55100d500f0040c40c4034810a03411943c21a94103001940c0880c501c132128000182d183d800a002030b4200781400d01414840d0040305e580301e024085900c00c0c4e070070a0704520001030b910500e0b80c06100c0a03014500c020082030000c1c040c00c0c2070840380c80f04a0b03c900e000b150400e80d000554514070801d01e008000c01e09801651200c400300014170010201c9a055a041d04c0354420808460281350103144030180c6540715052140d800c5a0304d80d201c500c51554590113140c640c8a229440000115541c018140000c841301902080c1e801c40c410020511211940d8a100ba8414004c00001810010302c00360000d4000d02030703050316102044215000b0650442c1240c06000355200000e209420a0321081054429101c142066000110480c01c0350301c01d01c80c680c00204440f200300180743c00350700 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 753185053 1250 753183803 753183857
    0x5061507020d11102106060813050c06040e0105030601150e0f0316030c21080a0e03210304170c1c090504021c0e1605011d0405240103060501 62
    0x203120100000c1050010b070840e4140101280031411805c0c14601c52400041c550310031112540041248034101407000340010790040480e0030100c060041042841001c02080e030380503100502141e501c50b198806044100b01c01c0c80b50a000c0e204220021032100c048a11020312891540d0700c5114076443e074001c01900c0600a15000e804d40592991510300284080d001000380d40030340d203901c600350b260408480800000b644e5203a02c00e044518030000159402c4100d070014a0213140010040c0410400070303040044001684010000e001803010b10400400c01940c4600d00810410001102203844000240700d59154454617800103001142c4481d0201070030082400b4524144141a8442c2e01080c00c0780c0c8210100442c83d42c002c60640340d660400d0089080e0144000060082e005e0800d0000a4601c0c0600a080c14001c54404859125070314407144500120010020701080c108455a0301740d00d104480540000c1e0b80304120215154024040c0310110f400c1a0350300e405045e21490300c480103000c108 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 753186303 1250 753185053 753185063
    0x30a02070c0b12064e012c070f0303021506040b010c020d0804121a01050109030f030e031c0806150c0a080c0a0f14070f031101050703020708100f05061507020d 70
    0xa811481a090b0264001d881307110100321170750f040c000c200c0036109176548104441c06980c100340500d04c0004419000448070314401426403440c49600000c2818031407550855070021003604800802d1590000700711a20000260880b404c9860358024403064902042c111400300c3e0801d80c0a000600f0001c01c5c603002c0d03500a44100d82080d4071100786c0110813074220380030b8800c0303401071120b084440f507458006401044c4c00d082444120b46142d503624400034080300040d06109403980080390741c7c0c8081c010085085040500440718008514024090b04070a4400c5170003800c4400c03403c03110304018801c442185803814010900f0460b10750340c00300d55900141540080340160140701e00003440c1c81080c03000c0b5500c100070311100f12507840c1c40d00e07140070b1055102201d0b14200c00c0c0c0c20008650010080ea204030020b107881a591056402c05a10709402540175200724270036090510a903909550001186a40e035203802e10258403100100712007905040e042030321010003040200018a0710385140d145c1103202e5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 753187553 1250 753186303 753186349
    0x40f050f040e010204090b04060506070b04080a140a0305012105120a090b04081f0b0d060b18010320040209060a03151508040308070f0c1e0602030a02070c0b1206 71
    0x741d0b186030030380e00154403040145840303040507259071411340140302c0a8202605c99a0514080761603109102c000a84060720442d0300186900101d441140728064003001d42003140d658a00c2c0d0100180107142c24490100c01d0391190126088038ac041d03801d003c007030300c1d041401414907041c0940b042039a0b600c1282d280e014000801b40024044850801030002005241d000d0a51441210b0340005d09111071142086561701e4039101440c41d503150b480c0781e900d094001500041207640100414a0f0343c81220192160000bd00c0001040000106000d4102081c10300076030b13030b42c081c2d200501003a40550310100313602683c2400001c542c50b100340d200309200d13000d000005030300941da4040c0b20110941c120010f4001001c000400040c180c00c0f1201607000b03141c2d884c028440586030352000b4048030a1140050401024808090300710144603c1c61801e517400c440b0466890030a414100c00a500c40c0300207e80c1102d1818000030100300d018241c44018142d05240b804551718042040295000c41c11200f48006907 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 753188803 1250 753187553 753187571
    0xe070216080f0d0903150c27150e01050d0b0d0213020c06011403030307120f0e061f060504060503090a0f30020705060903100e07060311040f050f04 65
    0xc252034400608405014141410002c01960309001030307549030f9070611041c4101000000c806400f004142e120802d4000f4000240300c00441d00003002c4091710090100170280e003c0c8d0300880610040c212114600d0752824454075560a807803904200b19060301044007402900301c07090703644d00100c01860b1300915043c9001440e03030004914002650b2030781e184070360208880990382401c1010317030701600d0200c4400c864000312100080c2d803840002c01d80c2c4100000720010403c0d114454000840d061400e85041c800031a903818101d5035180708171900400c0010340411070801d4201424808142ea00d140c0d00c140c40c084c03d00130150381170752004c0c0002400703203c0d803260b88010880c1088070300c2d07000348108842d600a036000d2070844201c07a4030a40c4644a1000100c001e201d4980010b4280c0840d2001c0d034195880f45854000681406e2107003954010f0309041480c134040e0b019020801409940c41b80d1000c05c00b03000c00d15001341007406035014000302d107045400244020700c1c240324105001c3d10002c101182500c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 753190053 1250 753188803 753188833
    0x1c06051011060105040501030f0305071502042c0601091a1c06230f01030f09021801050310050402030a0f210206091b0906040209130504031809050f010e0702 69
    0x100a1209000112009500e5101e148240001d070b004040444040c0265410b54884002821440307400500b80440001c0032820041c40c0c40c0e0601c1c11110540d0119103950703682c68107480064606503041c440d5102100303450480c0100d02da10134060081a13503a075183ca400e1014941125104000c166070010084c4100d05500200b0404c1e03060b0110380c050f021a505280c18a990005c000b504d41001300071f00d5001c0e40d0304241e2901112310000c680300340b90110703003a0303807440320040100078100c3e01030740004100c5400e00d440e03501c280100341222001e4003140e8140d941c541d914002c072441528003d41c180c0000c521980130039030600d0250100d500503907240701d0308200c80340384a40c2c02101c000c1040158004508110320340d079050002c00c1420400382e1503550a0000200000e401c918000d0100d84526170100d1100d00035110408000003003c2c03806801c0080d41080c2c01c000d06006610070030031141071800e05020603203002500500307008034280d000390b070b050381d003030518120000307400408100441c407400c803101003088 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 753191303 1250 753190053 753190069
    0x1409040c0905130821070f08151309060504020f1e1509030109030809071d011a090d0f0b0c0403050604021210060b090a0f0e070e01020106090606081005151c0605 71
    0x5000d40404809007600480d00aa41e4800a0090080c0080103424147e03a0780c10a2015078803150044080d404131860f50002000e20450480c147c159074600302d038a00401855501660081d0b000300c500c040c0306618481003140c212115414230320703a042c10110b031408506040c3c034000e001d640105445400e11844901103400c588615006400095404060140003001480b24101a00780070183c402c6406105c0203000408006202d1014401580001d2041041c40d400690fa0303d164000d04210503281c46013030a0350526040c14050b54103401c03200c04903608104001c11a0102c039800070107000306556035007c001c24001d5024510301240150302c02c10201081d1841401d020340120006503845120310360912a04045a070801c1d402d40162200a0241010154015a1204092500e1203841300300e580103d002d40300c2c90b40700d4002581030010100e0700a40000905104424103001c00c80c1050b501e03401c005010210380c00303d4074804810410054551070080080d07142031856100411816914004034200c6 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 753192553 1250 753191303 753191317
    0x903120f060906090606070f020a03051f0608280c080f030d110c070308030a11030a0203060102190308010b130305030f0a0813050c1e0a0602071409040c09051308 71
    0xc00484003041601e151600b40150410743c262140380365450a580400e0491050140180207404c020781100d04641d5411a00d901440d8458141d07079049100c40c00000c18220f00090513042c5600b07003074000c54048800100c8101c01803a410310007040c0c11401945600ca9047ca03882a10303190450040490301081c208140c03a541c1c3c0c1c4c0c1c0300040d82e0b1080c0150740d50040f50482c01104609801c1008051a450130000700c01e0300740c0f50464030442c0d603915400c29030790003020b48c5080c1c000c00303040200400880641c0c6034080e520238842a000d440460b50700b03108003001c0840e081e10041c0440c004a005100801d010360140c04591401d5135060a0182c8a0b22041d2841d000080c0c001c6e400e89000a00c0d021403544501c109801c400407141c0912904c0c519603840f0384401c04502414001c003c803031120b007003804043d0b06290007060003a04004e91191903880003903d410107409030021100da25441a04c40d8200200d40d2442182c004980405450608181d1005003401805c40e41811842405000108104500900507 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 753193803 1250 753192553 753192571
    0xd09021504150e100806010c0b150a0b070507210f050a03142125020c0301051501020a110d0b010603050a0612080a0e01020f0f0609151e090312 63
    0x6940c907203008a51900e2900b070110341000303840801c400c4641c883e501280255650360402c3d51036030b034641004031401249090042c0c805203011042c0040c10035003241810b2600401e44038818200c0d03ea07071100031244240c182c009c1c4140c0c01030390100420302d040c0c101d100692503140006440303820035440e250420054000143c0303140c0c111070400410143c008551a95200c00d00c51454101845200c103403070f00e0a0400780c0b4040c222001d20004828512045400301140c0021114100080d041ca500954440c003803161140a5860305d0b012030705c51140d110700ac03200d0303150582c014020317074900340d8411098958690126811256500c8148001110649070340d0107410320341d900103664134242403c482544e8482c0d0000000815a5401d1804581c3c13010403107959940d035040034071040e668000101c0c58039002104400e442d006030194429802d40109005010302400400c50340c0340c02c0c00341c07408190b1a03400c1c0c0715040d911200f2020314107903600c96000e441e40a24804290303800c4c50062000701e10011030441305581 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 753195053 1250 753193803 753193807
    0x10050a08041407090b0a090e0d0c11040e0309090f060307060e040e03030106020f0d08040314030411120331050112020c07120203101e0f06180624020703080d090215 72
    0x4482c245208800d0084c2201c41c000e00048c0800c0c000103440d0400e2900e400c04002c030040e0060180500c840250780e421034090000c2090a803821a500d440350440c2c440d50380b00f144442c0c02306220300600000c050103202c000300030345821403500344180c82c80b03a0241751145d00241c44c1d03c80103141c0c140c03d101550081817507130040c10b144a03687d504142004510400f03103083c4070b485424400440c4e4010400544030388600e5081c0e0b6a07407200d04207416031036045498113501504214403403c20b260088098054031022070b55501c605590b8502c00800f034603588040b406540c001c403104020303940c4a06501100542404001032804010340005801d1038250340284465841d011000d20071820304100c5007141540c403a0381040348540c0c240f144002d500e40d1042c051011030310b9040104002c2c070294081c000034070001c2c101c00d80d0310700b00383c2681001d007003c1e124498514424200072140e041501d104142d0a000e540d005d004840e0569542c0300041d045001c800d45880e580c0d224900050b140c2c035410f280149401000a5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 753196303 1250 753195053 753195071
    0x30b060d0c0f020307030906080c070f0507051212160c09141608070e120304120b01090b01090e0a18320a0c0e1e0c07020f10050a0804140709 62
    0x5092400300b81c03074500855004201d0480030035401150300c0291405842c100800da107541b003000e041d50240c204080c0600c860801c1020420100061a2044074425504120f00743c64034441c40e521000d041c03846846400007001907842c0030301c0712000c40350150700c83c2003182c01c240d4981c8101c40444419402d0801e5800c8044144961070003503054035000307490325140440d80740c90180002840d400c030700e2101a000d40115803e0048a580c10f00a440c0600f90300402032254030183d06242003611401c3c0324859842e490403015080740d500c503c1c0110207a500007103040e0150303120030040340010168401d00c240c01840b584011000541c0c6620f1810500358048212580510100b202420000c1d20300e000480f140d0002c0001400904d500c13080004507069040e003449550780303c0c58000b030081c2c0c200071420389001920080102030751000025044180c02a10b135011000c1c1035005000d01903042e551710074085070b42404810019813085400d241d10911a040e90940030212240e030340d03c0e10006d81c100401c1d07140c4590142c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 753197553 1250 753196303 753196307
    0xc06040b0609241011030c010609060501030e030301030f0c1a07020906011e0507051e030d052d0703062106110304080a1407020a141905060a0f030b060d0c 68
    0x510f4005a50b084410010750164110015403410107901ca0300404008105007220783c0242d01e01d11141c8403170016a0382d1a44018162802018180106030200703141070703000f098551182c4580549203a20310015032960b420758859080d44042c2610840305401090300224a600e08956966034171144088142c1d1288258810000c48034001850103040010b40140030360703c040d10305020461400c0c6818481c0e600c0b40b660515500380a140322516030312210400c00c03a40b50f410004000c0c0f0400b5890780c81044070391500c8000031080c0c5450891090750040016101c04400444108983c0062080c180021680d43e604801360304d200c0c41c9100c900c43d039600465282c05001035409000c00580c5120202461890581d0350700c0d1060080c15504401c1100d165601001718005e0011910907903001400188515502d4120b01c1f6142c00c3d00500307500451010040711030304124042e440080d24001002a4100f030741080044030384944000181c1c041544580301c07443c10703807034030b40042c0840030b110540032a50000306480 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 753198803 1250 753197553 753197569
    0x1021309052401120b06070203011401031209050307170102070609150e012a02070e13031101020304170915040e100518010e04080403080316110304031a040204020c06040b06 76
    0x8084002d910381407103084070340c1e07010f04c000b00e07005541d0100103404480d46005c100980140c000081d0150700c1c0407408115400c2e490710280c100d03446041104502c04030601c0c102c0340c2c0d800714401c090705070780910018840044501001c40c44105202c000604082e19511043c080d56000f81091b66212001c0040343c000300828050450f400d000f0230000d10442201c020343c00003414503981c6190003510289490084036109116032402411000b00000941c2440d040d0040c2014010b201140807c4d0180d4181c4190788060082c3c81c82280c0180c046007503940e506401c4a41079020310140b40d48004512402006210078002400150200d28500142e92400c08001c90041020303030005c51003500c054602c0d1001c5000702083c82c0c10340e00444801e032241c0d151458101038500036508000c050103000b108103c42031080c43c115801c0c003c41555640e21300e142d400070310340d102c0c4074501000c1c2100c4104038600308422100c540c15030b04284050401403070810350101540c201201070ba0304680c40c020741821b0103058580070300 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 753200053 1250 753198803 753198841
    0x50703030806041e051f060c0609140609030a020115030302102703020a05010f05060d15110f0901081f090e16030b010303080703060e04110f060c210a09170102130905 73
    0x10114100d401d2807c003410b07110329850010b20903911240c005041150540101c1c41c0090b820701207030764505012010742d450390004403440c0015032038496840f54242c5503401d80d00840303400d81c0203080c562682d200000003074041d5030740ca44500c8a21401301100680e04052841c21035000c3d03030261005003000e02e880d90a40f060000f00e03141403401c0c030090080300e0346d0340120000c3c100e42c45418030310320301c4124000401800301407217040c10090707000c00d2400c9403146120040800c2042641c40410720b80d9801c09101d03004101c614a110342d03a140708800c3c000c1e4426a441b01e0b40c1c1401c0e00c0100c441c054002d00d840700000d0540e0308116046050351004001b0103400c4011660401080d0506108c001d05045003400e030a94010700140060015582c004180d80b5508005007003072070040c00c096900c00c035040c060780d5510402c2c800e20b4081d103d480303d4415800c182100391504503015540b44d80e100c62404120654540b840000c00c4550355081000d03802008070034003600000c0071000c20101c1c4904d4110503002100c0100c103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 753201303 1250 753200053 753200101
    0x6050a05063f1b1605102c0d0e1e0a060203041a030106020c0114070f06150b030613152c06040213030303021812010504060e0a050703030806041e05 65
    0x81d1403a4000d03014105844143c56000080103011080e0b0403c42d203026403401100e60518600050b01d0300f40d0390100c0052500c1055401b070001d94840100403d035850302c039200282c0c0042c1200e00307011624500681c04200303401e01041403d224ac01c0d00d0000411400303240d4802c20140c0d0001030100311003640c58101d040d9804445802a055601d0413001075201c03a044075102c1d0410010b044005859002102514219070b006810b1002c80c001c2031810f1401040c43c05111000340805c100700050101c44d0900302c0348a00304c09405c0b03100d00c45004600784040c04641c00240404461240c01081c83d04282e152100003052090020b4100b6681c3c12412807080d2003d0700362402540100400d40c6018040c01460701100e5040c68016a0b8035801681088044c1c02d9842c0781d940819101c5002030301c2401504100d000e04d00519013080100440300b40070751354000d9400014003a070000f07403003040803d000e120060341c810b80207000400c44030440400c162101a81c0d00c0c40c0c40d00141d07a0b03414801240002c0548244410b804 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 753202553 1250 753201303 753201331
    0xa0c020613030c122a020f030a02010509130b030a081305010905100f090513060e0c090307030807052803020f070b16110a03080a030f06050a05063f 65
    0x945000f044a101414040d1032180c094440d05282841140350041c0402d0000d440e00b15041041900212a0012041a407003029540c203202c1942c0780202e088034040743d058407804d00e0f1600000c207000f150203103401e04490181e500c01c200b0f096030704c0500072010f1142c4644000c80d035507002400c00c81c001c102a9040035041000c0164240000d40b0b0307403c03614182a0b0031b800e00000150381c146045a403030250740c00464110f4400010740302507168542140064940b0304000240c940d0714003144408901420715081d91690103c0d0080010404100040c5940da0040083c1c81311420306c42d00d0300e41080044002128450707032070182c100c140343d418080c0c0e81c0e003107502d9009458041e00d80032859489009260b03000741114a00c0c1e54000400070181a00b00010078080c11311320b141a603a080c2900e05801410a10003ca401e00c2400245e00c1054401c170000d40e007004000301c40c154108001d0041030380100c0340d082050142c1e0250b440c40440c03030039070140c4c0d00e4030400c0450101000102007e1703101c81002c1e060002901c15 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 753203803 1250 753202553 753202591
    0xe2e0b1216030506100c06150611070509070e0d0c050d1103150402010827070303050a0809010207030807030519110301051507120c05071e140306070903080f040902030a0c0206 77
    0x24000d2241c017400c44138540120100b005051030700060030020201c641c0b6480c4601c00003103013500041c805030840d03c10300644881c02c5c0d403a0144400c5980c01c031100c0c3c0005641c03c002c6001807a04206c40400d850095000e98513041c2c980c004140032000404003503505030725481e82070146240400c030030555000c0d440c904540d1030401d58006001c2041c0501807220070b640380144a0541c40b000645403010413244411a08407036540d080107410340e4002c5003520b002030700d484c00140c42c5000c14021203520707940c160b41e102c100e91380e00b103002c6006020117441c15084c910341041d0070140d0360250042548000340701200c641d43c2c2d40f40004010b0314030010380d80404011400d001e1080441c04048a034003031222142000c0040c18041d28000b0f0825042d0b410411080f0b020030100020b6051800070001926050000e100541c0d99540c00c140d9904030854040d000140f03101010310005101d40050700d507400c2c0174881b40d41401d85170034440043c1d8004440c6250b03120342d1a845220388681c1000026008001c2170110490424 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 753205053 1250 753203803 753203809
    0x81b040e0c09190b18010501021207031403152701120c14150a09080d030e1c030b04090503071b08070608040f2a0e2e0b1216030506 58
    0x4002c0450810f030800e80b8081c18450314a03041800d48000050840684545990b21844203101c20300500f8018490552441450000d12007120390700340d0140c9600748050300d40d407080070650340000c14a40d203a1404614400240e00c0d40300149403021104590940602030500740c415282034140c1c0855032000c00740c00268045000030001c1c40c20b5515116001d54800c240c0e80100d03492110101101184880000d40380c101281e10540701c1040e504914291001c6510101088050f00e071808100001500301e490302c03800c03d0700c106007040000182c40c103002c01c012100700006000c03121000f00a84403a0000961b640802524009400d402d01100c5070001c800b90030310914541d00c83c014000c2c0801c0c09014000305040c0002e450001d03003c2c0e54081c820f0b1800d2503140030701420500403031000d8034200076004400326941c800103503660b2046842c001c102030b0000c4c4034000202d89450b540701982910f10507030000f082d16012440107040c5903440300c1c0d1000850034404038000700400c0d40d050070001c0510b8603050107210340e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 753206303 1250 753205053 753205069
    0xc1b050f010510150c0804030b0c030702010c030207152a200a05071a070c060c121119020112110316030207050d110c0d03020c040c09030206031f081b040e0c 69
    0x920246402c03c3e815817180313003084603403282d0381001d01810004000c10070201041c000440c07251040380c0c028081034605203400c0d410b1b07024042008268000d00c0102d4102403c030b5510404103502c2c44908850303042d0a5032550a03141561801210000e0a0221444902c02454414581c1004860700800d05440b141c1c80d0310f5110f5030540519049103490400480ca001143c400b41d44006070890040d0240f242e888030b020f070640003806022109900e400d113803e003102d8041d40c542605080171902600c07c092074003d0b0440b600c218180101d05000085090700302d066821b1082d140c80300d0018601903a80d08202c3c80f514500003941c0b042e1810907004221a0000403004911110f103000c103418502c0f0080702840101c0d08280d8440c1150781c00403015070403401850350008070400c40d500705a8082100c0c802c94542242d000034580800f0303420201c10404a11281c24540ca800f410750990340c0d07802c988d43d0316540d9590602e8280b208c04c06c9800d0702d50000807503a1406200b0070355000e090400510300ca60200340410880c1c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 753207553 1250 753206303 753206339
    0x11b051e04080a110a080f010605010906170103080901020f0105150a0807151d030105150a0b090a0b0a022e1a01390c08070b07150c1b050f010510 64
    0xc451080c1c80140313a512003c2c5000003400002c415520101c008003110b500900c550703c0f48a0000b04070040024030303e80030f00804010b808100d40825096800e644501540360321201d6024110701c1207000b82c0416480a110341030203113040035114a100b6032104200000e042254220211580010030b0402150103004540c1080140e141405008261641060110b403031040c03074a5a059401c0a04000241c003c2e980c20194580c411030381c041420b9140c00640c20385018910045411a00d480070038081720305c1c080040d00c60b03c0405d1044800b030030020140030a43c060310440f072841c9805821030b10180104503000f902105103602404081c1140420002015aa100c00010080b02441c052404c2c40300340891510f5a0b80ca06010305581c030131114600f0070803181240c8100304840c02000c10110b6680c03942000c58401d1600301c0303008001e032003030044c0709401003094101c0f50342030045949450300c0c0380606805041c1b880b40148003501400303103044441802d54a0051071105e9006400b40140040c00c0403000d00318907 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 753208803 1250 753207553 753207563
    0x30c07111507060249020708120a05060906090f060102070e011211060a2705091315050603190507080303040602040f140d0f0203011b051e04080a 64
    0x300412030300800d150340e00c8520121072aa0000420406000da103070000c15a010307240c81003040030320081c003140078100603602000b00e903480642411200c010250910080319056071100500d0400c590744d812240d980300c00c2542e4068010301040008041071485103da221805451800480c035162001459001d0300816610315088541d0201e02942d01c02c01c100006031000079448180746d41c40c1c60405008110b001402c03550701c41c950010485900b000c0d002c1e100c3d9000d26407241480b244022100d0344185000440d6440c584420040000e803a42c1c420203414001e40405c1c1851500007031030708224040300c00d1202c03046501400c1100f03000440e100007518040c00c0358114201c40c413684c500d00e042e03810700f42c4540c0601e5540c8004014001070003410b80c0100219004c43c1e4824803456640c5140403018078501c0f0f6025441000c51421002280c11500100401440140001002c04c0c5a030143c0d8030b061442038050b030000d840402c1c48400c030302005820081c83e1260b8130095003051314241e012a0b031540c1310100108 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 753210053 1250 753208803 753208823
    0x6080f06010c08070f1110021b06210a140604020a02060106082d01050a170303010b0a0e03100b030106050f0f040e07030c1e0f1d04050c1305090c06030c07 68
    0x910001400f42d542150b0b105c200c5030003481850138a030062941340062030b80301e00c0c2000c001140d0303680005030501c03229180300304944190000c002000080c0d08401c4003500d50485a040e01e4420592440700a071041201070400545900450b000c001c0c00400140714038010345c81040401c0321160009002411207030342d4a8900ca030384d80c03036100d20019003001b1405400780c0300c4400540104122a210068140d501c02c4c1d417003846540d60b807480c01222104a11101d49030b60810401031084400010040c00f2545860801e20740000020010901e0500081c1c03d0072001340c0d0310400d04641d45420302503500144011a0076031022401500010904a503d04540b803281707030780c0c2054840000c030030b02890008503000039021503034a0380c980130450714050b0905000300c1c581c0c0052010400c40d0b4084140415140802000d140c1d4000900c02488083e001038410344075881603031422205aa210785180c81a843c6014021a40342803800c1d80c41d20340142c80c920544a000140108040071030500c05a5855542101044c4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 753211303 1250 753210053 753210077
    0x1030e06040f0c081e0c0117370e01060522020702030f120706060503340b0406030903140a08240409080406020c0a2301030b21060106080f0601 63
    0x20a01d24940c0213210754080e1024840d0702942d82001500c0180900c0b007580d1920400400464544840680a643d00c81003400425082410600c42c1c41c081100400c06aa0760340f164404508051854442c0003440c0ea29420315140000c400c2c01104014401610320504003c40008285400c10001c50508120741e40880e0840c1990390403c180072084030341000f0760303040c8958424210039650200300c0a40d00e250030543e0000344c90a00103a000c03015a00442c4040d03a900c0380040700481012030400c1c0c0c5040503030740940840d045c400c500040000b4002070b1800589800c4a00d0003a00d80704940580c2510007406002e8800255040340019078000c0c250f45c500c011411b0780f01240c0340302103905503965801c945007050030010800303414010026240c0c1602103034072034980c1004000380a550b80c0a100261060740101c01780104000464503032800c1c0506011070010200408038031221030700da580000c070001d6010420700074070302030060b06d024144a140880c0d039842c00088400d079070394015002c0ca0402c600040c482c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 753212553 1250 753211303 753211313
    0x20d0c150206330d03030b12060408030c090619050309010c140d0903020312070c060f02030603100b0102010608030309010603030e0a06050406230c1b1909050c0702060708031501030e06040f 83
    0x4001d40f21001051103240f41003504000300140300a40a080c010300b009450303540c80c2640003c135140f250782d0040900c0d14603690b115400c0c003180c022090f440c6d0040d4050040721001041c00c0415241c0300300d00e40d00c00380c4a16058000300e09540c4510400f03c180402004041d5506003024211a0000e80f01d01c40480d0490303841c94102d00d5072103074030306508001c00102d09100c61250300800144505024440c00e1041e4105001c1c00001c034441550f0307040d41540020108040106603400504090a050000090165444081c3c0d800c41e44203c802c880140d54501090003059042030b60380350309031800e0311864030310350a01d0006000c80c0314501170703401480489000360762101110b00e000307404184026810f41d210001d0200d100e64850144400d4a1003460318080c490060914206204168503151103441c404c2d4940000c01c0700070f107806405020b61aa0401c2a0f0000d46c82e0715000b0300c0170512545d4119580e20b4034680c29a075040c032480c000c50401d0708051822050010000d59550410741080c10004644054580 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 753213803 1250 753212553 753212641
    0x1109130c080109020102010c09260c150d1404020607080d060b040909060509011109040f06080105100305160303050f0901030f1e060f0305030a1209020d0c150206 71
    0x10003451082002180000040d00061030882c801e030001d005c1740c40300081c01d031040b103801d0250400d040407601008071902c00001846c03d80114540590f103082d060b2a000c101242d800314003001d198000007504500c4480d140c490f00d00840b4282104a2040c1840d0380050950320400384040d26241000c501e007040c1450990020000308405003205a8550381d0350343c03070030203001c21031825038016180100203000b140060054140205c181c0340b08600d880a9001044014480e500900f610303a9518040420030345024401c0a028580f90005200180d183d480c02c0c0f0b240090341000000c0504d0401030400001e900720703040d50020fa0010024646500c04000103c0c010002011006540b13401d041101e2141d1040300450001400c15000038803000d500c401240280f0880e621005185a00c20401c801026101e03403001c03041d0401b020780c04a520358a0340c00084108100c62425500909200c0d4100807103100110160304515042c0054079103440c0c80b20b011002c40c0c0c2060039810002d400b00340e148100d402c00041c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 753215053 1250 753213803 753213841
    0x4050916021504032012040603020f0409090609051e030a03052203030e07060201091e03050f0d0510060e130b01110106080606090c390a1a131109 64
    0x101e002c80d903207028280204852200700301d00503040368881d02c5552603400400c010300004601103c9510b01850840114002c1d41718901c22640c0000074040411038a1190288030780540c05002c011800303080c0350500c0c504100100c00b0108840510310040c50312604044146d41d443d010a040000d0700d540ca0480300a0440c1c403030103101d19084446d90365081016003517070022102c440b100040b602c60707644481c0c040c1d00300ca80000b406420100b41122072044a502c09174040d000700d00c04c2c0707407541c24030155002002d1070350041c1c1c160b0620a51034008001c1c81d0040640108020f14151403c04045040c41c80400c800001030085801299140c2c5d0002d03e040c4d008141c081a8030341848000c00805a60700d020903200e01d0290390b40d80c803a01610000c43c1e860b20341e440541c0c402c203550b600000c40300c60f07000304010488140c142d880c02d13003205051a21100a0000c0c052003514900610f060b40d084400040c1c8000000720013480142111103200c540c40124500d543e0507a80003105032020103264580040e600c41046030a6 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 753216303 1250 753215053 753215083
    0xa03110607060617010e07140102061620100c1407060902040b030d02160f0509070f140a0e090f1b090d0606291c020711030111130b0405091602 63
    0x40700003d2011055011002e4000d00e8020307110345680398034988c1c8107003440c881c000c0d00691012000c00e010020b100032614203544981031021030700d044100e00610f18039804241d40702e90b400c0700201545480290041c030050008a1030801c50603c040ba83e1a40c80d07003c0c010001e80450390340c5448404640b1103501c8840c003a0b030011b04807142c000c1800307402599034440700415081445000c40014104d0b54540b5400300b1b80303400401c2d01040fa692524200c6001c40a00f80110030003a0000c0c00c9074034088a00300802c049412035031550507068008092180909000e04600481302c0c03d18100408001c4803403403414107296101d1101d039142d00d581e0004070009032148018081d40d20b0038800003195034142c0c4100802190800c41c4100c1e01c280b08110311443d0088110b41164a4520301d284640c2d000b0940c028030720280b28440d01211200308001103400c5402c880484d0912050026000d0b84004207000c049008000d0072803503914045c1400080349292502410201c402c00880315040001402442054490442d0f0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 753217553 1250 753216303 753216329
    0x9071b0506010b1c0504030e1c170304060c090b0405010309230d020f0d080a05040819030501060e1e190e0c071208100b090d0614090c0a031106070606 66
    0x1d129240e0300c0d9880400850902035021341c24180c40d00c514001c092040c0e801d526241c0d80e6a60301c1d01804801680c600b04150341d07100c005042c00000b200e45000a408020702c20f501c42c0c47c0d1910b8605a002c948000b0000810310551003c10011001d15004841c10f80b00c3c04e1030007049081c03039840c129510981c0d0b045a03010f1940c2c51607107041c285000081384012030456500f161001a140c1c111683c442c80d6100d400000100d8000000b17a207000d00340c00071f0341c003c2d02c1410084c1c5045444a44c004140c01030002d4140041d44400041101d140c3c0401444100182160500395904a92001c02e5a4102c0c0000b020b02407110190500040c91018002d440201f410194240003840c003ca15101580c1c0000800c5600542400741c641695101da4001e41c4203112100240e039000d82011110758036074203d180583e51122450310080001001c41c042c0124410a181c01105030b81007a910945c10040405d49082c081c1180203410804030340f60f80c09410213550309075221541c541d200d0825101415064016200583d00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 753218803 1250 753217553 753217559
    0xe0d050c0115080307060c140403061a180708010b1216111b0310230402061603020c15120114040204030206030708060a14030309090c160c06080106080609071b050601 73
    0x2100812100741b25420400c80320074402416203079100480c0a42e200740e0f205100c140300050b0198042104c0d0324034100f0110200c01c032100081c004200301c00b14040c034124400d06114141d80c00044040c054401200070b142042d903101542002d40e00001c02d5508070502c44004054414042c076814081102100180ca02003001050202404007400c003000b03001c0d02c545100c00120500c032b03110784046481004015040d02c43d0500b51060301c00030280c000e9074020020420391038030190b04203080a03c07603c01d4021b00b98011406040216002100e10741414003403003004150302c2c400c1b181e4015810340c0d01c42114100400a1540464024051703908003c6d004603002003440411900440000d00c60320084a0035400705869018030707a40d86034a45070032a0035620601075911189095004950b102a40100030341c1008a45000004512011081610410581c0000b4000e0a0307200d00350901505542c02d0111550800c1c40c0400e0b8035142c0100a4400c0000665119070800d10f1780c942080d0042d080000c4903c2561 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 753220053 1250 753218803 753218819
    0xc21060e181b1804211112030c07030f09180f05010e040f12170103141c0813060b030307032a111c05070e01060e240705031204080d0506040e0d050c0115 67
    0x28070701465450134416020650b1f1042c01001c212842109403219103818880c40755000d6500d224043c0c080c2c01440b20421001c942800c0158000c121080a80300201b604201e01402804075081a0041240a0b202d901000081407e58441c6100e55502198a54070b101054600321042115961442d64001404e40001b080c40078243d081c01c00f100503282030b40c140750000e04c000010458420586004a20711200141c06140286c011100d098020400420b081c0320610009084d0382c0030744411004148031088003895003085a10f440b020340400c0d0144a407144180c0ca0380343ca00c3c80c9020425100d1051a0700791040003050000e22024550f0150486507000c1d150021241014024040c01000921120359141c0314603003104803441d1903540f100d00c4081507203010b840703040715880703035400759428407013002390804200c1150003e61180c3d010785541e030f4407841896240030540e04042c090303900c10350600599070030060020814181d410250f042031680c52480d5480306014051040d81144c8091903801d0028a080c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 753221303 1250 753220053 753220067
    0x61e0703171305070e0a0e01180506060d0b0604020a0302070f1a090d05180a170309040506120c040b1c030c050607030c21060e181b180421 61
    0x80342000040b0750301c0c00c210116201500038050042d5010500400c046048018025086a10114041040f14401600358290358100348402050810010b0503010300106028071508140125a0206240015180c00d1112807011b0117a1344540c0e8000b4071400e065010342e041742d0b00e01e5404032045030700402074100040c19040a01081c650307030b00e465001900490740401c4032980800c42c0c0d12014145103100084c0e0017640c3c0120030680d0021141d803c0400d0142080c09208250400d080042d952041c148040c0f00c01d84a01030030060151914801445a071640403444051280c0f065400280c1880c3d0351000460010409400c0540500c0d9444c41c001031680c41586c005000303014504480c16600c07110821000c850301111030b0350009041e52410300803d10303c10050800109500700208450303890300c4101010880c181d800e140d01c181d0103607810003800f506001c2e0039401c8690754035000200c24404040381038020b042ca001030740304000d14001400c10202c0241e1200e29060a0729034032a41c0d0350345030051b10350 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 753222553 1250 753221303 753221327
    0xa0617010902240409180c0b030a0c1d01030b0d02091501080609060d020d14030d1b03060e0a0b030111031f14060d1a09150a0e040c05061e0703 63
    0x340800f80452003100041d922451005010381d80100e191500d01049900105a40c4180501d0b850006c1d41802c00314a101d150900a088014403680d82da040c00b00070078003190a55814181030114007003014900e00382e03803402d0192101080c2004201800351100003031901240f118000d501a44140038001c100d41d04002ea070340301d80000c0c0c8604850b52213500821081407001c8402d540d011030f413419400c0c0141400c081c580d0500d0301c03031843c000341c0c4002c140100d82190048070300c18591540d11643c0010000318840c44101000c1541010081c01d8289940d0340d04181005120003003098aa1b110000140c401f584007078102c40300e0551080e240c1c01c015032001c1340390114122143c1003030395180e0041001e4000041c0c1064545004029a140900441280b40600217001d8140c034405425500c1e178070380f40c40e0941058410903070f01074004680d0880b1420003140d000303550000810322802c0d004000000700d14500310000e41c3c00860b22a91200c0c40c3c0380f0011071810b450300d2a520101004148001095080111042c3d0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 753223803 1250 753222553 753222559
    0x60903151d0601230306070f0203070c0e16030e070504020a020316060f1515081302091303090803092d0a0b03190c08061207080327040b030d0302030a0617010902 71
    0x1c150301e007050340e11040460140160717041c0c0055012411440c01002d00803820111b03401a02e0038200540c40d170b0b0501451070f9010058041d020400c002a8618100081e462808c00d41402c001c1450030071407450341c0e552503010310341c040c650006000801074020400e451610703d0380d140340c0d00c400015240c600d010300400340314100241e0920400c020500c1c038440d030203810b848540540d8801420700000c100c91020020b0b01541c001400d20340c44001680b14014154443c0003070151020405000740360003845004603502141e1250000e1140250a0340c0e080007400c0c9803880e140f040010220032500341e07603008070700881c9254406480f44001901c42448406140300712440c1c1d000848000c0c050901c00c0a4420b460707405000641854001812407030b01e88110b041b615218000c44145584500006155502c4148000c1c1c406442030103255901210f50780c16924105c1c20340303041c04000060300c0400d50320141105084141600400040c00c20a099402030004002e0014450500410301d00c4036802070142c4441680 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 753225053 1250 753223803 753223829
    0xc09040f14010636050d050c100203041409040204152603030402010c0803191d0609010c02031605032802160506040b070204090f03080603070f060903151d0601 70
    0x910700340114540e0010484c4102d403141d80c04941100c262403480580c903002255040c880f004991502ea1401c0c1c1d540b01442540140008083c2c802000350700c04100706c00c01e045500400c07080c820003c032804550750240c1c05440031031701c03a2668400200038084a10780720f0302c42c108801c80084c84005060015000502c40e8210b0103860100c1c02e4000d0b1248003c440203808a0420441e1100260b070000080d40d001c1c5160502825041105c107064068a408072200d8400385407400c1426010403050046075000311301c6000030442042503040103500e80c010901201e01d401c12041080040c010107100719a6078112415142100c1c401401214050340c0d690000e080042c0302d0142001107886120100b03006886000300403a00341840d110302000a544800d00c200d0304151603005070301c0010120443c502e04d05200e9140c41d056840d042c0203142c60803c4070740c08580c00641445080104079000541e0303805803034004d441c00112010003500340b40900030204490b1515a0714500c02110f203400450302c10f0581e101200b0404d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 753226303 1250 753225053 753225059
    0x60f010828020303120405100b0414040609020a09060b041d090c0f04090203100209030c030a120f27090e0706020709020c011e0e07060c0503120c09040f1401 69
    0x150764070302101e10001e80480c0118420003202800d004403603402e200904032440c082400c0c00100591a050303d045603154048010081d103030400b03001d420984a0251001c015107110701c502e00240480192014107100d41e038401030029500c4105805000d0700012600b80300c619a24120056990301c00d101c2c0205155900003240c109071541c4c0401800785000400421400046600700620148610240f41d4825920310112006807420f0043d00701e41800003038010b0300c64070450103241c2011070940c0740303610a8001701204400a00312208514801038540b4180ca06080c1c0a40c1c10345d4921818000070241140d087c1280c0d000384994081542039400140c0705003c17107052010000d540f04000e008400160308800c4d000c0c01460460341c05404c000100b0bc2c008211100c0720003a40500b45004402410740320307100e4107940c00c02d80c1c08000d01c034001d02c080d19102000d004180c0b503043d182d0017140c0820442d44011400b20b110381c851a801c2d6155254000c000300130491140c9044030041244101030071440c6c4040c4000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 753227553 1250 753226303 753226319
    0x2030409150302030604020f031e071d070903030e0625060c08010612050903040f06091a040e060f0f100302131d0103121209110112152114060f01 64
    0x524102c0c0d501400814240d107543c0c6c02c0000f0709440c00c0c84250140700d12496940c0c0407003240c450007840a22000074240c0141420b0541c40c40042c0d8140201c2015190024070004a5024100f642100c0e003610700201c03481215800100d15100302950003021004000c07040f200f0062138071807901545e1040000300319101e0302c0e800c16039488a007482900003050900042140510054000fa607011021a0549150a880340744010b142c84850b040b10001800c0c00600b80540d80029083c056012040f1034983d052518142a865010350003c080038054421041e000390283c8802d000070340c103108000d240083e052a003082c0100203402c00c61503400ca116219000081060511a2840c41e22041141020389603086032210196070608d040350400f000b24280d0740d04030110142c8186100c09200d8920f18048407030910004290100100301d40f0a050f14144403481d9102c2c9400d10601140c600701c4c04801041a40c1911880c2c01704541405440440039190a0b55442070125890303129112001460a0b40d0340c8070041 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 753228803 1250 753227553 753227591
    0xf030b041103010b070c0504060303090e09010e0d03020c01020c070603050a0b121009051606092d180b0a0e0106140a17130f0606141008040f060603080a02030409 71
    0xc60401c01008000500000c51204010300445000c0c0170502d10781940c0b6000b0400b11007145c1d006400103581f005044c0540c0758000d45480d04802d80f4002444038040c10105103455808044000301419400140c002002c0030a4050f104243e031038406071003407107030f45500c090301400e03080380c080d80f12510744015030300740b46011061748074646a12001011595545861040108280041501d091251403038002c0981c10418040000d464980d0750215090720708000c640c400038000c81211404030305200c141d1619541c00c602441115186940f595041110366076003030041150b1051647c00040803800400d540317811800384c0307048031115698840c0e045800901c24016014070011640006d41d41b062020180f03041c0015140c21110302001e4013003202079940da076140050000c804a03480b0351101820025451041e4402064010a5401d90740001c29208002c20303407040104020b1640d08080e03170504c140308655104502440d8028070b040d60f1503401540280d0f0704e400c18880c06401c00e04103400c0320003401c2a07541c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 753230053 1250 753228803 753228821
    0xc031406280b251e1b030614010509010e040609061d0a03080c04060f030f0e120d051005090105010f0c05071202030c03070605161b060f030b04 63
    0x4108455848034020480c0d40c0010080000c1140100e00e4a04409144154480002c0030041d07482c582d10700c814840000d4011a1440891403c0b4141c07100d00042499a4501e41d50558030750301101c0c00c4411441c043c103803175a04621180d02403824120110401030103070710002c0ca070589032446403040da0783d610030421507003024042c01c102e800050010400040d0103420400703900348900d90101c0c030010302c0040052400e0421501c10380c903501911a400c207050308031009903003041c0000c0748580350904088003d04111102d2403594200360341e44400c1c000303094071a808010b1541c040015501248003000030041641c011813020b0b6541071900c008906200210501c0b1422610040c1c4907440a03171038000150394450500080c40700340080c920300b44d80040c1050141801401f54036548054a0000d8014140740003040d0141900a40c80314209020082d085030503221950f004250314101d008a919110600040036003100581d049124004240b003078020585141030300781960b0400908041d80100410354072010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 753231303 1250 753230053 753230081
    0x60a050709030f06020f0a030f0b01110607051605060a050118051302041e090b101406030a05040309080318011b0b0606090a080307080a0e120c0607030908100b03010c03 74
    0x401c1000001c0442aa801c140c80c0542d00040c2003013104025540b0f1743d840980344100003035440d0340d84461000b00d03100e0300094500c00c2c030340131041480c024901c9640e02c0c0068640020b02a01140b00305000150444500e400e942c0003050303481710f013400a0b09201070400ae0217031801c0d01d880c40d5030b81c6c010038046114062040c0f1031941d25a504130b4507902400010000c2100c9040c440c2d5800c2e000d2511080300b4001d220000b44609448200c40c035025148000c000d400e9041110301c8008109118026920071090702c3e003049501000040760707151032400707031030318455540f0001c2c060002140790440c10412081049040380c0c00e8a030300c40780303000c11b00c0d4007070039084520030003442c00d1801404551181000300151444c00030140c410b4010302d440c2c0c0c030810b18540003a80c00315041c900014070201c14591188410351081f00580340562042d010510341500c2e1001c0300d031207034001c0e140487d09500f814800c44031800107205110a490007184544503a0015021080d0114001d6080807661a081c0b44244542c80119680c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 753232553 1250 753231303 753231317
    0x6020426121e0405030615120c01050306100203160f0318030203030703080901200409150e0406020c0a0609030e090f0c0906091203040816090c080a0b130c11060a0507 73
    0x1580b42540021441095001c0040107000120341d0761800c1282500030b60036022600200e0075a441041040c0c1c00ca2500d00b4140d4020b5010346d11281d0b084405c1d250000000c8401d4440340c088071004911b10b01804215030200d004200d140d00520085a40c0081014003964a40c140586400c1640702d810b465880002c0d0580c3c400c0100202091081054540113040c000020400c0a42407244401c0704680b29002042c48000250410040c0454881e50004100b440d01685485250035265614640000c2c400360041c0c1d00054500b10b00700051002e2080180d00c070b030040203e403104c0e04000309003400805156000781000008610003a0308410340d01e01c0b41c0c0c0440039440c60312607003100b4040f141d0002c0310300c984c00c0028511582c504041c2400540080d100c240002d00840315502c4404403501200d5005005192a2050b102c00c15a4003494080d40a480d21402080b0b102c2c40c480800d2100c03c88009203002d507031400351800c0300780e80c1c0071082c070717200081c14000c07a603091302d03000300c02022280f040e9940000b01e980 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 753233803 1250 753232553 753232567
    0x3a0503040b2a0d0e1515090c13030f030e0108061f050c060406020a080714040306020a111c110615120a060507050319020c15060a030602042612 63
    0x50030401c00400d003101520300c8002500b0003008000c43e0030140c418082540c82d20513120015400f00983c01c41e0105411840705a801c1c01001e07070409400c507a81c2d89000e08032000004a28020400c111840a001080417900090341c80c00c1c1f86001c2820041c1c00c600241c01054810010761081c112240181e034020031081280151038405032456640304030206c14401d05000381108581c052103420700c06e600481e80541d40c0d0090100003004040c00502e0740c03090000885400814600c0341c020346040d00d500c07920040e601e669000702625840100d035004000b9104e080707840540241c50300c1c034040b10700c540390b211068900000011740d51250f008481e118150040100c1060307a51400400a44d4081002416110540041d488503010f55100302d50304400b1900000c1400084046c400240090b02c103415000c40c14010a441e06940710108540034011805040e00844d400e55941d05001c801594090811544d07155101e240844103c3c03901703c0840031100076000c01aa0074008a0000b007540c1118540ea490001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 753235053 1250 753233803 753233821
    0x10608100b03070c0501050c040602010b220b0a0b1b0d051e0a110d021501091109040506040612051b040207020102070e090c090403081605130b07053a0503040b 70
    0x1000f0114020402a8485000410300a120b954019032000c503039036542d5400d01102070309440030f03544101d000303014141003510b4009504620300301070500104045200030b003c00016030585034503003100410040000c1d99103d005003d468440e030304800e5000b0340d96003510003075017650703a07000c2c0b203c51103241181103107804140782c05800141300840b06810007441c0300d940300034110b2a20002c0c101050251703016a421410900c4002c007028010052070750240240d0b50800f0141080d4040e0600e500c0c040d5850710081801d41d0f03900d80080e4068100311001c040400d44ca4242030781e40d0061800c2c0c040d9110b0b401703c4844214201402147c04868040e002002207031300d40300702c80481c0040202518003e0141a8240c04940e558182c003034042c03402907449180500703006070500000d007241c084030130610004105010220380407490030000c80300200e805580b56407140c1421401e10980d0b00b00d42060803243d08121f021022601a01c0d40b2650140300501c2010044070350690307140c4403e0714060701060032000040c00e104 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 753236303 1250 753235053 753235057
    0x10204080a0201050f0421030e09060a120c15030c091a0f03040f08070609020102010c0822020103020f0f0a0f020309090417070501110901020f010b1f18150305010608100b 75
    0x3090307048214a0247e8070904440c1017000c0c4030041e4a1a036800402c01c1c1810381c004041d1180207011511401d0909115002600355007051141e045041c070303018203280a000d04030311000c1c01001c0740c01881e50300411081d40100284048507448001c1400c844010600c203022000c0e02c9030040b0f03041000c92030010f601c03000300002d07040180211000b03580c80300c03000001aa40006001c080303104500114004001d4400a42503682c0241d20100b04000b8004001111022855242a803c403040c01c4040d1041c450004034040d10654030894840f0000042c0c2c0e5111080703980040110480130340d1001024280f440040b80c032440b441180c66400008400402d001c51668800c072482403201c07240321840c081c469903e036825a0540340d440c0c02106008100c51006503014010800e200c0310a000030410088590b001030340070340070b6403064100c00d031a89284002060260010041804902c1c1001072901e079195007440a00340f010b640c40b030000c0d00304000002c0950092000d107003e001c3c0d002209900b2400c25240190075 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 753237410 1107 753236303 753236317
    0xb040e340806090402241b07030302070803070809040f0e0607090302010e0a0e0406020702040207170706061a2b0204091406060a170901110a021e010204080a020105 72
    0x10780d01c2c00351b4070801d203c054140c0310300e0040042d2000200e019003a40144445e00e0f0301d040c3c0740360000006080301164071943c221800c0949901d038aa03240d0245640052410b4001d0204900c1c0789400c1d00240700c9250561070020340c10040400702c8d0700d800c205841c40300204000f880e040c419964051000d681c045000d0b030f07191040d80e260580074485140020800303041680d0115500b011542ca98044959164102d4a245a0b075503d1295188440e80a504101c810a180260000310203815105140da000032a60b4410f080c0100c01c841081c411811450f100c4641604200d0f003c000480c03071000c2c0024211058000840002190480e007030010045d00d018860300c1e0600000903025408101121400c100808841803926100701a601401080d100c0340c461003400f080c0c0740c142940c0010460031280c00d00c41e841e066807012a0300305080344120b010f81c0c601600b01d841070307201650042000b0100c2c = true := by decide +kernel

theorem cover : BRFrame.Cov 753057553 753237410 := by
  have h0 := BRFrame.cov_init 753057553
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753057553 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 753057553 ≤ n) (h2 : n < 753237410) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
