-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1554
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:33:17.537118+00:00
-- url     : https://prove2.me/submissions/6038d5b4-0134-4330-80f0-3f274bebf00d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 279316546 ≤ n < 279496402 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 279317796 1250 279316546 279316571
    0x160b040606240e01050d14100f03080a05091318020108090102040315050c12090309130204050607060c021c050c060906160e041509140a0c021e1204080709050901 71
    0x380c401c2c4418942408180c043c0c10500480d800d004507050300c0603491038180c9840020700e41e00340091107924484192641c040e00c1e2040c1000d829010300c402010407034240072049896015502801451030b02038007042626907204408400e4808241d40e0990400101d511075040d5640031208942c00030200d00250300e028610b540b805404a00095200001643d070004255400802d07400c40d41d40740900b0355454030504050607030640300c0d07000c2003095220b08200045020488400c0c000e0f0f0f070480b00b00130075840c200811600e602c000751000c2c0e042c0304218080c60203840301c0900d490404852188855079043d031501c0386d41144500d80700c005015180140e009800b00301d00c8120300b03400c3e0b070700c00841441d02c2000c10510314081030203483c900c4040e80412043c4280465400b14a501458441c00d0543c040130080d2603040200d02101c20003400310006810086a60021645401141d48040380340d004541d0301101c40025010150010381101c8142e40269000300701401b01800b80503042036801c0000c1202003403006 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 279319046 1250 279317796 279317849
    0xc0109061107030f0317060406030c0e0712150503010e0f0a17040e0114030c040c020601140d170304030908011b0c05010f151a070209060f06160b040606 67
    0x11421007040100054901440818001800219400b00441d460040c46250151040030041e0f0b010040d003a41000240d05454103000d80c4003207a800c4007807101d00a0402c800f9541064000308084107201d810040c41c003035440b851282c040c6480740d85041d0100c4c641400c0401d420745903201c034440c0403640701034007207d0038a0004c2000070f800c0754415850314841001c0c0700200180e0280b5805040b04400c850000141d121228295201d100800c41c00e40c2e040e900c00304c00b08011034415902c89001a0300c4540140650411000311000099008000001210356540c9031030035648030148030300211001105000c00c041c0c02c10380500140901600030b000c0410700051030310580f81004800c9007080010301414043c0502036000d03141c4280083e0080c402d120241c900e4815000445c481c141603e0840c4aa0501201016056423030495004142124541340c1d801040340c410001005954040d8081191020040421000071101840364807440100e00e494145002220b006501c401b401e4903c0c2c00a120f40c154025 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 279320296 1250 279319046 279319049
    0x30a060603050103020f040c021c0206010e07180501080601030608060109150803070b040204020313020418050d110c040f0e16140a05030303060d0c32010201060b0412030c02060d020c0105090c0109 86
    0xa03900010048040e601c01c0340340181021740b2002110324ad5000d0700300740b0fa02092840c141c0f002e002441c0e98507111000e04580300108900140c520350301e201000d00003503201d41c0500790000c90514001c50380946503084241407000c00c0e40b04010b01c5079a952800c40100120503510014440b050156085c08403a4503040d490950041c40248980d0703001000540c50210b081c0c03d041465001350007088584131880704480c3c164040942580c1c0340c0301d9507807054862840f5205515900c5031540240a1b0b981520301480040d05d00e203a82c9400c00c64403411844507100041241d10b00441c820140188014585209681440d001764941030040342d24076000d025544001088030303040340003a203152800d01d51508081510b0342e801c2d001881070000c005521300101510440c001041004020204414a00140107a003240c0c40c6101e0040d0588040c002040405038140000300094003c1c1070903078203500a54005a0075a120140b0890102e0313002c1071601d14290709205169100c00c1d807030010041103c40d400040c0041155 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 279321546 1250 279320296 279320299
    0x6180a050a14091b040501150c020d08121e010b070f0c05150909060a0302090f1504110d0f0b0105030a0f140c091c080f09030a050a0305030a060603050103020f 70
    0x100c40100c0d40500069202400c8101040400780d40390800c1d5082c00e8543c10600d031a40c0b040310440e030b0606841d107000d05c55141224402802c101200107000c1d41500c8850b5107010599001855204142c04284c580b8020021648078401c2c9015034036108211051040b602c11821401c0202c110050044403680404c5903c05500306909c060b805200c0d15080c201e60125030450380d0011890413603c0c10200b151009820301c03400032900b02d05150380300c906220005d80e9a10010f94000414030100d109284880b803071f40e4003c07824030701c0080c80c0448400414181c0b5035510405441140000e1032500350311251007944940440040240a000c84240000344503020280641c41190390360201d04030f40d800d103944040c1c10703003140320341940d054500b8003c40e040581080300a0b502404005a0045101d050700a50f41c4200e40d11a403003605090000c0e81c0d243d610b070050101e25070980718500a4402054082007000780280c880e96455aa13441d1011000c400e440040d44100305050509005000680d9420b2010300750900 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 279322796 1250 279321546 279321551
    0xb0a09110406030b030c1002030d0e010504050705011107230103050c09030709110903070b041a032401111f0c02030702010e0d03020a02090c09010e01050a050a1805040c02070e06180a 80
    0x11180000b82882c1d1100f6003647e102c400c0106424070340f9004000380c0901d500340c0408100003980d48403036500361001118005d003544c00000040c4015805100d07490b0f9a1a4058111000580c480a4120300b194200051414200c00302c1c0f020b90096a02d80150356105c0c44540009090400b50320109a94480354090124203d03180d140142c030300c030308090135a1801c4100408440c0000d640300d81440140d8040c2c01000089000c5522200c09038091400301c0b401240e0702c004503482c40b446011681c44414100c0130150400842c1035000204010030001c01e4410650859241c0c0d511919048400442e00a41c20f02d10945d04103000341000341c0e0704900c00300d1842d1002d5543d207210f1101c52508904007142454001c0d8410043e000f40203052820302d014248002e402c0c0c81e8a9a11142c80c801501e41d40900d000c00c2c1c0008030100101460103200e0884c8505202014006200554030f607000182603c480e104ca01005921075802004a02820031505810000540710003d220300c1204028203600c1c001010b0104d4143c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 279324046 1250 279322796 279322811
    0x30406021f06050f15130b18060708070b04020d0c03060b0109080111090d1707140106090614130e06090c01031406030312090703050307150b0901051c080d06090b0a0911040603 77
    0xb100c5d40c0c1141e620491020742c010099440c0e2203442030b1604400a40c4103481000144021710781840800c40320f1240e00301a0043c01c1c0883c540c0d0710715004500400480c1c008090b031070000c000401d03d035816030286114040104004a00f100014603006031680482060b0b0704045203040b0816039181180c2598205030303044458000d050400c000c00761a9900f030310904500008008040c440b001c1340012031880b040d002072214540c0da01c03401060b21411301586135080c60301c80d04c03c80c05242c41c640204d01c0408081700403407542003000c01242000822104078aa0303800070300030441c0c1d0750307858810030b03a611074010003d9100b4204200480c1d5a4013a240462103220601c030041141c0d08001c1007010019644070040381d0340d8a01601e0200b20141307050f8502200b90741840b41c031403028944143ea85060b01c5018000d10000101401c0d0851418640001a24506400c0040800c1d12000380104405080b50350f00c0400c40b5100c940c18803840440580c0003030703d80c0c0e04d4001d6131015980308804940440d8500e240110744c0ba03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 279325296 1250 279324046 279324079
    0x80405040903180e061807080a09060b0306070306050406120b1501023c0604030e061c061d0702030c0613080f03040b010503011d0a0b18030406021f06050f 68
    0x2c55040c12010340490f441e0005040741d11114000d1140e001a584e41c1040622050241001c0d00b003030752500f0200710002c0019011810960112807500d0181c0804103004046d000841d0420b035050781d560000a40300e500500c01800c01b4001d4074010048400503171840b80854441840001e0041c0c1149101e00721884007418581c401c101c1444036518128000b0a40507a10181002d03699a20510150000300b52030710840188002c60b90620480e055118000034000040c20003005070320813150020000e107507640c841c100280d6885040301810000d89101c03502d070003c00b148481203000409650840d40100034020b204040820f590750850f0181d41c420040002a1801c01c2c074900034800e000740180ca021041205000b09160290f040300d1003940200000e03402d50030206030119000c3e07802842513004002801c00203c0c0f01c2d1074550302c04071103280421800300341d206c00c03801c5612903480709006038403548001d00030700b80174054402c1c43c4041120401802e8079000100c0d684c0518030080510607076200c083c0040300e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 279326546 1250 279325296 279325307
    0x1308090303040905100501030b0303031906090617070b0f070605091002030a020d110c0d050f04090e160e162304150806090c031305010902150a030b03060103080405040903 75
    0x41120040a99840e59210300d484401000c040726080003005600400241d554000c4c4181d0f429018040e01940c40c542e500304204041507520450281c81695400340090a40040d204d6140070707120b91595081c56001071020381b844e003c169040421800c81c100089584800e0750b2007240e48035544a000031030945d54032810fa600708142600300d1040d103400001004101d9410754024192101030b0042080350b651011880605400390002200907580405d00c081d44443c000ca0241070365090304601e25107082d85030201a0309440380d58100021590024040940b0482214442806446042070518a0345008902081e00100f01944042808000703c02c02c2c52101004805900c01311014a190b40c1d200d548115045c90302d06c3d40e03200807001541e0b810100c0e1440c540018064003c00542154900f180c450000d000c001c800710980c1114150b5890000100580b01c0310010300743c07000303080001515100c031101c01030141d03040c0556103031003038000d80e005000298000f01035030706684041d280000d10682d18503003601c6 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 279327796 1250 279326546 279326557
    0x121813020f040906081c12020d06080a051f0203040503070b060612091e0105040506040b07121a0f0f150901120609020405030d09061b1502031807050d0b1308 69
    0x62840d8002404900700d0340f160022002c84040c2c0702121841c0fa00800390fa14107040003d000c0700001c0c00c91001c0202a11560050201c141d841c0000191700b42e0348440c01c602d4940600f80454540d00895001c11003440004040f42d0040c2074a0000c1d4a1032a1556819441c0e215181005180c0205400803c50a031183c03420385440921343d500280c05428506200c0f942c0751780004120030008141d01d00750703404c650b06005080c051a40030005241c240c40300da90b603448000d4020500000c201007062452004015401801e00000418400c495500c84c03280901c021781014906090254040300e400c0700c1a500c505080300b1aa2030348000d000c1e140d405120040760940300182e01d00c82514104840814813100981c020021104110202c1c0d8100e1081030090f0340105c414491100428440c02949000b40300079200008854400c2c00307405071a5445010200032a0020390745a036840c15104502000098108400c0c5c002d0001212807000b01c2c1e416940300106c40c44010070803503254240c10216010404111305442 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 279329046 1250 279327796 279327817
    0x5010323040c0503010c090f0506030703020c03030c03060108060f09040b0c0f040906092307050702010201020706090302060f0601181e080601030312150e012d080a030212181302 78
    0x1201410141840b210b900d000d4011248203520b068a0f252400740075150305403c65804004002e88203203044200402500010f00f50010b040c0c0070815561029014001940300d511300c03000d0b01c0c0e01d83c2840300006001110040005000703d0f45540014007c1c0e50368200c07140e0196001000c081c1d41e580708006c006443c042e2030003004201ea00032030003149241103a0400002c0e10074144080104804041c074001050801980c600e078031010610118132542c0c802c0b0b0007440b40c58010b0001510700402c581d40d14044501c00310040e401038018034240183c89803202061b503007003082441c26039403106001601c0d61243c0b40300c3c8a521410b00b455090703126075444801c0c00c03c00608400e03003640e100f580e4904000d0600802301d6903408255242c00d81c040c00f070030030031840402601c1d488102004140c2c2080d0302424286c0040c041c071600286145020305101000d050602d02030300b400c90190444d41110318001c7e103010701481d00c1404e1400305206440400711581d03103141c1c1310401102d840740140148400000240b00715014207 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 279330296 1250 279329046 279329111
    0x9062b02092703030103080f070305070816110f01121a0414100801150302150c01110a1409090f040c090204061e0201050702060106080a151202040e0d020304050103 72
    0x3268410014a0441001d20300b41980010701808240e201c1c8000d000c020840b4100348136000c030b00e1a000b0064880244a4101a882c0c10f555855205041c0c0180000b4544900c01c100704100b044101685140e09802c2518100c01300d07641a00003030603000c99607808503111541c1d0b81168100802415601550030400ba0040105080c0d5506080d50703030901f283c000e40720300104000050503200c14400d40300d56070740c10810200090708660070409240811141c000c0070341024412005140e5082c46540004801c1100c20386e9210051000909040910300e42e68400c143d0900c900754554603000038080d40441c0a001d52480d039511440c1c0b81d042c6101e65004400b80a1011801042c40ca42144018100e443c504441c4c04c0c40300808801242a101c0445018005801010041003000d0082d01c001d0b811121190012031001100d00100814881a601c55000011166100401c0d81440c0c4520450801400b000c0c085c4600200d102954034443c40c4202810903513a00d08113040809545600e5004a80900c0c01 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 279331546 1250 279330296 279330301
    0x20a1d0a030f050a0203120a05070b06040e0f0604020a140a09050c0c16051c050d03091103150613020327101a090a0605031207211d09062b0209 63
    0xf1507032140340c41c40490103441800d041c420356695150503104900c00300d0341c805240c48040d40d108903094502821007070300103485880304240703620b040c06000c51842e1010300038009854140100200015030303900000780c400101d80000300030f03180c2c10030309001d6944400c804030b095160002c3c0514a8490b1807010351150007942d00302d40542040d14010000c8550854110f0098146c903583d00c001100c450b8801006903000300d03c102c0c4028080e4004104441c006c5500c10b0000100b1404681881c1d0319241422040b0030003c20420a49032118007004902641c0d0000c50031403511000b070b212511008401a2180e0a96902d8031120000401070841f490318824414480d001e0312028105440000300c40d00c0b8400c103044400290254041c0c400e990803a44000d000b81400c202c44c070b080396540d6010b58015603c0d5858900305010440414030000701005646e900c0350b010610804095201c3c070ba00c500c64a1040c4400d2003804515900c010040b40550301782c8080c00e100b00040c2340340785040d03c02039a00a4010203c01c04 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 279332796 1250 279331546 279331553
    0x5030912060f01061704020409020a031b0e0903130e0a152c060307210b1305160f050f060d110a030b0d0506010b03040510051303030b0103020a1d0a030f 67
    0x350a80a4030302d191901d001e90362116420785403882403001c00c0c001801810000f501600d042c0e0040d10869001500741c038405a12078613401c2e40d040e56065030000305004118100043d880c280d811650044240c4041d50424840024840c40b800c0f080c450040303255600790203c5e45504042d1b220144a0801c00040c1c002d0903920030841c80300c0c0b0303449407400e4807074480c008100c2d1011035506182c2d48541c0c00100030304019810045400b10f100c0701c4118401c81d0380e001c0082c280c006400781150724040c603da00b05111480c40c840c501240341c805080040506403034034220410800f03003000d400341c00b0b4410440c1e016040c04801c5000c83d0f81d50040400c0e240d01c450400c840d807501340c0445001010b00d0030b85070ba020702c01da075009818045840b9002e4001085640040c3c0104111101e80e00550380151160050740c0355000c03422a6a001c0d40c50507940d0308005003c13550144c0816070503104040007000c00782030550609140e1800a44120741c038801d001600c45032080024010f5491010101c051a071003400400d8000d071034107 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 279334046 1250 279332796 279332803
    0xb04061523040c051c0c0201090501060e15180604050711060a0b150702150d020c0706020708100b0904060e030c0312010e010614031303020a02060d0f0f051b0705030912 74
    0x81c00314021403405021810480c440d20803900c20b03038990031403010000038003420000100140c59081045550b98898040011400e0284400070840c05c0102c00700760404c415032245a103605001180314000300200c000051048918250380b100c800c540008285c2e41e80c400075507031104804000e42650023500100320866170240d010a88498098070030440c031070742c1148402c00a1107040d00181d40300400000340500401840e0041c01201d90260016090585104095242c0b00551300400056089410306002e10b1030101728010351400d1044090108002200100c0c8803a48080e0010300159124a8040c1c3d4110007001200c44030b980d641c040300c1d99a204141380c0e041207031081c022441d01c800d80400008a180c8220400d480c0441d486805a2075900d501c203120f0603a0b10803400890960081003040009039139080080e00c5e04004241d8045020b039014041d01c8200c0f503540310351504251800081c4025120301d0000922880c400e03102c115550121403c0c15451800f81c0c0704000d500184001c644003c42c2c0c1d020 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 279335296 1250 279334046 279334109
    0x103080a02120906070807080403080403030809010b1c020108072304170c09072304120506062e0203040f06030e070b07020d1203200a0f0207030b040615 67
    0x503400d6603040311110b410070b1594814084000e50000302409074001003903140d001440307802d20500456203404c0e9290340381c43e05500264001d9011440a20030400c0705142030050344480003045034642c401515000648990700d0b0400030103030400c0440d000140b40c0f18000c0060001c18042002513500071440c20490300ca0650290003000c070182c401c9400c4401c0130400007100f40344140010428201991062030480d41414214618000d491942c0e850042822040e0f00900140c161b8070a00c03200c91400381401460200054081401181c1311111000f1b0381d0090110040340105d182c44617684403022076070492030760190f90048020340310300440c000b409507003543c805e562110080055411481d51580340110b40c1c05494006904550940340c2d04002550129584594865606002a417221034152407150081003c0b24003021030400075051038242e4105c1c1e0101c9011225100a1800340c2c1980c5d40c0208040005e04002e24031906d40d51250907c024410400019080580c0b0b4120006444c05a09080c031007030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 279336546 1250 279335296 279335317
    0xd06091e05090715020a1a060a2903060402040801140f100602030f1b010f090c0f060e060a0e1503011e2115020f0309060f09060403030e1005010308 65
    0x840e400d401a4001c41c0c0c800d80d404006410102d1038122090300b0144050b001c0021806419680300c0084d581c54480745071080214103900d102e162000a100301501c11790802c0c0c500c0411003000400410001300046d107515009444941c0780e46410012a01900858000034541e500f081e454503d0707104100c80f442d118001c1042100303016200d104014290403040c1c01100c0050300104074104113980664000c0c50988140340c80200c1003d10349440300e0071665041005200651140800000d21a401040703170b000e0807012103401041da1408001408031144071007281d00070b14011520360901c03070040d001c2d00310180001d407005208100040000a0710b0b07009015074518119101c040d25280b070f40c4c0e0b0000c041515840d81707054a007282e0149408040d03c504000446880750b10040500680c20745c2d0016101d00c0c04221074558030390030070074101410000000d04000902c0700c00b90420031000c200144c0550000d8045c1800941028031005003401c3c6403c1c5220300d02000d007000300000801c5207040080100000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 279337796 1250 279336546 279336581
    0x90301140708011413050c09100203090f150c070303020d08010f06171f081608190210050702030d0801030516270209040c0e010f0e150f0d0609 63
    0x50050000e2030451080d50480c001521100043c400f40300c0c00b0850343c0c10f030300008004400310040c3c4003140d01612000c40d8010150a00840c500b24942080c0840b0190210b103400078505103034084010070140340700c14030301034403030181e403440d8072400a41601110702580c600c13002c0c0c1c1c541c40c2c0c41341006980c40e00055100c2c000105510000900c08508030800016241039503030381201c03500c0108287c0480000070b0242d07550200103503031845105030b411344544020b0110f50040e000b920b140c007007d048030300701d944e00070f4800e0b4000c09160342c040602c903a000c081ca960b040301c03199521840d80804880e1400750745002501071003804101c2e0004c81e002000340741224480d6007107801d5052054048074810f003051080ba02e170950900990622001040402c43c00701d680b0080060425000d00c00103010355000e12400d001281d01c5060506071541c0c030140c1550b400c044c5041c4008013061850200385144042caa0f02140343c000414812035449501c0d08440d400207104100b40078082c2c80d00250b00050032041c0100b0940034 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 279339046 1250 279337796 279337811
    0x501080906071d0117040b0612030301050306041e12050424020a0204020c0f0604060219020615221a0405011a0d0b0307051206060a060306080d21060308090301 70
    0x400050880c4a03210b0ba642d0f815054a00700d04814160b82120103090604c210178642142091a506440b8072441c000c240b114039031705008080c011518031120901400b0b0f00304100500c021b84001070311a81090384425824107c0080b212900c01c14024450010103003a104c2c0b81034100540c0c00300191003501c074040c3c3c220710035001182007440f026071407015000168020304182d50141c0b40950141002c1c04041064034103504206640500b02101210f0407030b4519030100d0750080204030005402070300551400148003900b007008181d10340c9141c1a106a00c40c420010402c26803100484000002081c0c103a41808583c55060040045610f2841c1050240345040c0000072822803030b40102800c00104c00c07001e480e1031442010031000d045140b00998041c80380c8003000540b034945c80d0607090711180c01d002510040c00d0020412000c1d00f051390040c3d04050070078100780502e582c0030034420900302c600d0400003044d00340c80368145140c1d04907820b1a90316915068002051041090040100b82c0048000300b103420f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 279340296 1250 279339046 279339061
    0x1020c010c030203090d080c09121c0906020709020309010b0a03030f020d050a0c140304120b04140c01121505060a050c0c09090a0f0501020c010203040c0e091b13060b040906050108 79
    0x74001105d00741050350003110500703c0e160041001c281c0004107004070610700074010700807902840203070785d0f40310b8250b0204010100c189084251141c456082d4035008110350b182c9000250f40b040d081c00784243c40ca0b80080410b508407801d500ca2504180c02506610b01103981e41806055580349503840303009070080c2076040014034400c0341118008459912001c2da80031850f240c1e41c80f10604c41c807404140c0d05c010031010590401c00a80411814441c07410048503191a05c0d08001118441c9054180c43d4821242400030f81c0e008403001c5128080540c0000e40880c03080803030ba02c020881c0d480306030003900c001102000700c3c5d4441d00400900c0040411110307015a91001e11004900c102c42c000001e0300940031000004100c2a40e0070405070040c0000350800c90f0b81c4450600b286e01c250341c1140d40203900c00040040f8601c0f0500e81e603004025030041c0c2000c0d40c00311000702c4500203480d00d55102c0e1402c82c04205a0400d25400310700900b1003403103803d450f107841d1040003005040c9401908c2c045005500002c001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 279341546 1250 279340296 279340301
    0x160302040305070e011814010b071401050a0b030f0304030f0b04020d020d05100b010c020303090904030903081207080601111e0a06020301150806030721030507020909060f060105070b01050d050703050f01020c010c03 94
    0xb5181c907c00d640c403036030310700000d404040d004000d04480c2180c0140d0901c500c184240180c0c0c2c0071fa00c080e44000b40d051b48980c01c062403c030000741501c566400a11042020808a0380e144100c1e0741c00031069600c0c4e598510000c3c6130342d8055080254001030f0035184000327004000a00c8012103140c02d030100100c040c1c0000641e0385020b2142d009625900c00c1004c030100c1d081c45440550003a00c40c1c10240c81c1300c1e03101e503100003207600b2607010b401a0319548400c02002c25844082030ba0016000e0070849404558984071a07151103c0401c00420a04991010080c07141c007004203120140e0040320441d00c07942c545980580c446c00760b00304000080c80342c40101d50a032401040b210300f2541d481c4c020740d2030100000c1482002040f011002e0b0309100d000e00c007190140c3c590040307280c07140300c2d408060f10561600341c0180c4822003000d04505d04008003071017000006800400d4071030544108441c8065000924078080e8079003106a00300400c28080d140e0b0000d075007001500940a14201c0400a000101061008808 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 279342796 1250 279341546 279341561
    0x702102115120503040522060906030b0a0e07080f0120090604030b13020409060e1e0705040b04020c1606080702011a0415051e0406091103160302040305070e0118 71
    0x148900c108108289541c0410b4204840d100714240ca00702a43c410000fa0600200d0703c980010180070a050002c4103c184100c41c040c0010030010000c40b82951078421280500510070080f490ba6140e40134100582004420014000d0350100c900d01c070254038172903018003569602e07540080700302400280c102d1401800e45001c0039016240d02d08080c03440d16600c1109101604a0098200035001e00c0d000d42c80d540141241d0034082d0b080420030b0316480300070500d0000071a00d40d100035481d086001400e040b002c20194119041118042000702407240050b00a100f40030031008188103201c41d0810480003c03400c0e10407191141c0b1040d45556400c40182d00741d498110441d003680c0320406007035059140c10307808000e22941c1d5140c00c414013610b07040820f6042ca80d034000c51002d05100310305543e00303107480c8c000c84e40a090705030400d1181c110610034020150101a08285410122800300e0282c2840390b030544000b0b54000701119407041e070b5401c01c2d02500c00300f80118500409828541000081140101d80 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 279344046 1250 279342796 279342821
    0x90b01091a1f081b030c0403030f08100b1309090c150302030606070b071106070e0f0d02130c0c081804050901020c0703020f13020d0f06060c050c04020d0207021021 72
    0x200c80b0410020121200100109081802d08004d810b4041089424018502c50400007501d207039154218240034008100c0c6500d001c042007100810040800c0c00c00701b00204480681c1000368564200807040c1d400c000380f030f03000301450350328100e00b05d000d010061701ca000484403c0e9041d50b2906000540c1101644021034a464220380c0030060900000c0d0501c202c02e07800f288614000c0b1400020340b040b2820020300359400300020388107442c00c9115282201ca10030a0f810111408411003075a1341c04151803444507541c401006a5920010510074080d03140b5005183d88011025a07415070000d5401e5101c0d00b030f000d83c502030340c54080045c3c10b44005100329104152140c1c000c005852443e400c11403100004130030a0303000105070001d9128203013113001412840b41210008100030040b00148021210305521030b0301003261042210b03001c1440402c0e2012030a805175009640c8003072241d8068080d2051002c000d40180c1d0041601c10055400620200a00140c03403041250b0149600b517101921540403449 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 279345296 1250 279344046 279344089
    0x3040312141218060f0f07180b0d18030201020a020c062104080d060e060f0a06200c0904050307021f02031c0f090506100b03010b0d0e01090b01091a 65
    0x382044900e0200c940e80c416040781c03000c0840382483c0f4001c1c0c240781050320150318405140c400c0c449000d030f0b00d4142ca648110340b494008040000304441e401d40c6204c502c1480d50b4a400090500003400c003580018060310354086404100000500d4024003d6002d40c2001005018030b604c00c914a00d081030407640940c0c003007942100c0005080f0582e240c1000043e008603007401b07040003038003d4456217004440041003400e01c2d01c80c0e14904a01404010000551140c1c4141c15941050004d190499908a40283c080c0c0300b803001900301200d42d81ca402d0700410000c2c0e100344128200020420004014120f82d44290b8568207038450349001d85150580c0314003807401503001844a850f0004410307884002038411040013181000c03020385100200c81800f041a42c00380c000e201080000346010700034000a140038019903285625200300e01096016103e2001c5030b05499a59100b42400d003500406c1060760000c00e00155540d680c281c0c24000e2041c6060482c0c401098160310703081c2c0c5414200510024800b1504 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 279346546 1250 279345296 279345307
    0x5040603110a141c0612020a1509030f14070b04082506030209010c020a090207051c0e012d120c090506030a0b060d0203010303020303100509060a030b0a1d0304031214 73
    0x3205207401c69100b0548503500e0560902d01c892060041000070500200c02c2c00d0b8209241c0103104400f40d864104076680c9c0015070000c50055409480700d800c40b60001c11020120b040c03460004401d8518000030050740c46640c0b40800d0407505039000780704840c8074004440082c0c0001c16405041e5007907615a0b080b0340d441c42d0040040c075009800501401c00c0500d089441801644d001400d060f009400c42c0304403c0c0d01103107400c10070a080100c41c4200c1c540b000700f198031701c10104000700188425640103040024825a10750f43c0f401d120310044000e010395210031454081c4400052040900b0b0140c030911070308120200c4d1213a030040d0041d0080d540003410f9a0310350f650368000280540b4811000580000d010806105143c40781d1000e580a54425070185580b410106448000b00844d6005a840307a0007503c180401952a40d400e039049030307070082c19080f080d45c1d8240d845d002412442103200040301c0d04502614413080210007081624031038407070300d5000020b01c6403c691841050107100c010f40d070704010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 279347796 1250 279346546 279346577
    0x905120604080a3c051903090f080c01050411060403080405040203040f0803040305040e010f080a06050603011805070f08061b07020607150203040605060301020306060d05091c05040603110a 83
    0x7400c404415040c103410b080161109204c01101c0c4c140c00703103019034101d0030070f0125091290650901c1e24941c6000780c205502014840e5168a038140c003441810b689034251801c00c100d4032000e4040340e0b049945c00c1d847d4041c20a51a02134801150300300c5401081e085250a28601345060b41c0540c1c1d081001c0a04081c1002c7c18000298009031040c0d81d102040201d0310001103d003001940710764400c0d903034191280d00e4811001030503401a048121900c5083c1000d000d0b003c0009915009981c0001c4040384645461010078010074401070864000c44d0304403848010f100d0005081c004490015691103180d6035030f155010380f251030a480070161000c600008210006e10380000d403180728002411035281900c107076584200c00e030b0a900a0780c00c01c2d070080100000c0c840e40b845400c2e4000b1080d40250701d1340c41c00c200000e5061180ca401c00c540f00d86d50318041113550b08108100101ca44111001c0c50011002da00041c24540282c440c0000107410070b803940d5424040c500c19a00c11600c07a80715984059948071 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 279349046 1250 279347796 279347813
    0x414010c09060c0f0b0103200105040b070308040303090204020c0309010206150f010c0501060e0117010f05071b0c030204060e04050f01111b16060e030c040504020d0f02030a050102030c03070905120604 88
    0x10400c4c1ca59403810a80c10001c294840c1e94103000b1032164119509030302c01030345c1c03c400409440d1803c60511005101c100b0411820200302c80b00d00b58503103420070a607a11807505400502c103042010b508540302241b1840c4062002004011200f0242c007101d03140d5480c0b01d1281c055035500810580c0081202c003031540c1a5019240c0c0c3d0064611900011900c5d644405e000c3d0f2005009030f001c4002c0d1886003071120030704030080c0700d131320700002040e8402d000310b281c800d102804004141e0318980d47c01500b982c5080a02c0f000c0200740c40919030051003405080d0342d039081d100f28040b0580301030b11280540103c1580800d014452504640e250785105400e144004d100c041d064213410418071507a004491011800c1103892504001074401612048180441481403624102528209500070703840d1100b0300c005666030899103100346038002080c001d4800c152003c02d082080000c0010415800402405130309495040598454201c0340d41d00d5440d140c0c3c034000c000480c41d0314480d40c1f1440c2c000501050101e903102 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 279350296 1250 279349046 279349067
    0xc06070804050103051e13170304030e150705010204081b061c0504030c050f0a03480219050f151b16030302030c0105131505061c08030414010c0906 65
    0x1001c006c41d18426030b041d4a00400c000c0390007611124105a000c1c0421261030f04c8801c007500c248060b641145400e0703802074549149202100d210b80c0d0103462000c0100c104108a40c15294800025511503a540312030340c0d565000850100c510300307404c103020030460030070000303498480301485e440c550311981c0c4c031260302c2c000c22018106400308420310b040d007404241e00300250143c03110030300e000708142e041c0b50a00600031502410700940c0991800c24124000c035440e81d0410310301e4920581e8030516038441010039201910404000c4d0411488980ba00f1040841101182124815215164003440510030401c405080c152005848641071180b090070b40615003d401c1c410030003000b01c65161480300900303940c89406a00c2100180c1c0000f07807541e0400380c28086c46410200007aa44110f103441d0740e82d0110024400c92990080340d549000088480e80c5500354142c0040d40c200e00e180d000803041c04c049603140e108403410786000950641090707550105205840000a0955480c0b100a080090132580107021 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 279351546 1250 279350296 279350311
    0x10804032f030909101401140d0608060a060807060912060e01020f0903011404020906011824030507090b16020a0503030c070602060f04021e03010221090c0607080405010305 76
    0x10305000c4040c0107981c1103100003a01e0050000c40e1200c07003c03c100482c5450040c60905d406180c40020001c000308901480e611007024200803040c081280514612030180d4010407103400d040c03010001d840540440c000d405060400b5060003025200c4034000c7d1750300340c1803140708005100b203d800c10280c03ca00e00e41906c0c2c0751051101140240c07986803070a099070492a000e0070480000181c0b44460f04d024861060091080c8507212824509600001d0800d0030041a85040c810b103c034a040010078410160005013003a8407220804200d41501100400b8250340d503d0b010a1414000c6100580508c010303804440641001c28545030706c071203100e0380074041030780200e801085162000c070b500d075020701c040d2a03d0408440240491403510000a2405c0030240c8550b85d4004910140000350301d8100124403000420701c40c5140710761201d00031a009214070700b0b220850362080000c01c1c00a06819136890b020f00c00801c110b84a0022840400c07006208011005000180c04c0108004d40c2d40280c0041d40d01000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 279352796 1250 279351546 279351587
    0xb04061407060e010501051c0506070f020322031a0f07050f09030a11041401060f0806121c03050c090604030b1f08010608070e09060a0e0f030f0d0605030c01080403 72
    0x8072542da0000703440c1e4400034452580d44840040c425400e0424030ba07034500340b01041035200000315450b160f403900409014403042100340d40b40c01d484240200300f10707400e09641d481042107403421009000c040f00e0f5203000031202d032405003001d01008811650b080d4001c00c8801c81d4822140c650f21803d481039840170340701c00c1d00c0350800d120a000c180c1d401d10101d14110300400485d014600c03440308020485403110b00006030001c00038014043c0940c041607071111608582042340094071020001035110100c0c00c6080785505c20600b84070a42c52501c8080e88070303031003151024803543c0c4030404690310902400c0c1910350860303014001040462544102907070032001041ca80d500007003c1074080140d190042c4c000c8406d50391240c40c1044695020000500200340c5101c07400101e00b4010885038070b03440302500b290f800c0c41d16610828207120302030102440380740320b4000303c3e50703140d220010101107a0000318280340440c0ca0844001070904010a100d804180140c1d60411240d031195070070707141e01f04c0200d00116139a2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 279354046 1250 279352796 279352807
    0x503040b0f1b0f07050706091827030c030e0102212107091706010609030609020a051017010807030f0b09030c070e01031e12030f1824060b040614 64
    0x40c1031400400c2800040c0c43d8450703450b44c641c2441403070040d060303100404006444070304001c246c184121400a110f00030360049080e03420650480404112528942c601c0b42c503801c519420180c100c7c00008260b071080d2a9024020108001641c544c0e40c10342512800911300d03002080ca13050f9210062685680d0305800b00104401010001e48003c3c0072140c007030101c1c3c01d0544c103110100c4500c1c0344904007a00c1c00c1c0203058560600038000e045030b0b424400140540e032140a080119951407580a01070072010b440b0203012000103a000f03000003035007001c42c84401c040500129000380040340c6001901d400150fa140280306aa458a42c0c4d0380000f01504001d00041c0183c10b00c122090120320020400c000c10240a541507040601a100441882440440d041c9132510005642c0034046000c5204600303000802d03003140034000000c0c2909122004051005a24000400114125000410f07510355020750540142030520b8080300c80354010300782c4100c4e09000412080e4442c0b2780c0c555944041c4072415007040c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 279355296 1250 279354046 279354091
    0x11030705012c030405010507060b03011821020106080c0607030207031a070e0103021603231b0114101e080105250203121f0e0103060b100503040b0f 65
    0x155000000864494605104018071001082d82d0340000c146000280d40382a1600002801e284900c40d4010042c5884400540c02c69400307520844081c6081c50072403034001c2141c504481c00c0074204c0c0394501c0b0044c0340340382040550300c144182c1087e035107144010191905004101308190304440003c500318800c204010001540c000e960500103004051224018103000d18081c194029211580d81018030500c90000c01400108100c1e880e150182031200ca98813200742115074544900300702c1855550300007040f044a030806010204408801c40003000103c02c4c03400800710184003510103141400100350140021030001c1a00e042c2c603001d800b17080c129266600c503000c1c250b500071151044003400b24910501c000c590500d081c00000407501c050340c90b0401d001c03c0035030300090240c50f00401000100780100b0401c41014500054181c0e812680c0c00340da13403842c0072005410030700b10403809044952100c2400b9070150741030342d00079988007803420155560801142d10600008048803800e6907038009031101c6 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 279356546 1250 279355296 279355301
    0x602160f0503070c05040e0c0111030f040b0403150b13020a1209030324050a0e10050d050d0f08040b062403010603200307140304060603021806011b0c061103070501 72
    0x45500c181c01450b00c0d4603c508288800c0200d0364440f6026500305134065800740c1c00400c002a4545090074030f0301580300b042081606d5405201130b030781d01440002802160010160019100700d038070078900a12590540806182179485412856400a903d10030364490414190080d08203204107243c60210400c002503080d080e507040d000142c1c0484d0366070b42d41888d251801c1c425183c0da00b014440714a1258502404551120070a12445040c030351104041741e130207400d00b07031880c006107001444031040540c0c50421545a4a0245000c400300310209500140207010340701480c4141c1d04104801c00d940d84410501c400003541030051165450703010b801c1c40801140001460192540c1ea6000803617040c964054010071400800305d180302c1805200300207440f5400300300b071340110b9003049215480b44c1744d030f2030200302404840e08000c0d440b20201c02a4060080b1120303e0a02c2290b00b644c0d80c00405d84100740030740c45541703c0c1c40003030400b041c0b4102c18440507000d5540800003403102c4046a00e800da032034990313070308 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 279357796 1250 279356546 279356573
    0x51507060b0d14010507080c030601180e0703020a02210a050306040f0e0d030c0c11010309080d05010b130504150303140405031e010c1b121106090127050604060216 72
    0x10299400303c002c80000e8024840ca560002603801c0c0700c0940d04144503540b0103408001e11007410021605c00c208041032181d0700400041c161466084060b050000019000e504880421801841001000100280c201b945000a800b201d454180f03402401503013150359500c020b240f503030850307143c4d450f080184402c2d20881e5070040300b00c405050782082803d4010155003a040e11032040110240d01003004c42ca600c000f06440d0300003400c000900003c1413a010106024a40084c00c0c003502c3c000000890704c0c504001820501202000107003001d448104100803100c003020ba562107241050402c0c400a0301900465005141c0e9104150426584000181ca0807200d0f0b0300b135400b07000c0103070403002c0d00c0c080034040e540d40340c0164104190802034841c00d40c1c1c02000b040801030540b94141c02901c15041c02401c000e079140c01407509031242e40c83e000c1d03002400303018001d010b0004800c44044000040c0004d0540c40041d540c084013500ca90b885540380d5801a4106828400c4110100020792300010b040e02e06004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 279359046 1250 279357796 279357803
    0xc12050709060506070b0c18060703050a03140c1b0c0d0507050f0405011206091a01060f02060604020f0a0e13021204140309090105060a121d0f0106051507060b0d 71
    0x6822410004100d042d01e49943c80750f40204401d0114000090000300c1e400d0b4880d41043e4425151600b41c82d40c851113010b9490303001e8100800107580014150300c0001080109160b031428048403404906c1180c412008131181ea24260050003d280790100700d4000d1807a0191820485180e15900c40010303071800c40c2c9640c00ca44692000904101e80c1c280f00b4283c00f04108101d6007000b00b5854644031184020751214001d24440d41d44c450701080081201840580e010048400207031581c40305070281c41c1c81425100007015100b0140010200c1c40c00780201d85200700c18413805424a000148191000e82c407150010342d02c81024554038216651390700c061318207603649080d0f10916061a04101c200c411104a00c0007058008020b88441600e071642c0f00c50440e4015074482d44d4981d4005001c0301c0c041c5050841c4800341e410710140d10f05480c600024108100350b80001c1e030360300c8480500240d080310643c0c820300c1c0c0c0015034405030b907011454013000780c4030141c0200004500035480742d000529442400d00200c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 279360296 1250 279359046 279359053
    0x51f0204080f06040c0302010503090304091d010b030d1d06040e07030222060503010e131a06040c030b10051b01110d0c030c0806190f0e06091605090d0c1205 69
    0x800008400b00000c01408a092019042600785078a941030b220b09240070180c181725001004c992040d0f406c10458008140c2c03854100440c40d5641945203045140c00e01c10b04444d03007410b40041e044d00d0041124002d0810300c2e260800c140da00c014400145401c241d00c45580020240f1002891460044002e88207050b00d940c0141d407014900e0051540701e8402c0006801072201c000140f20042c2c00034100c90541d001a13111500c541d8520202070620440c4400003400380c2c1982c0b01070541c80c204040d4644c000d03001218144040c41484804800710b5803c03918160340240352007032030551a800340c0b00809101c1c00801c050ba506140103100a429102e101001c82c5080e80d00064000d0b0b00a900c5c42040d10704580c52500348120140712000605100024044c40d00c60754034083d101032200d00b0481c0e00001050702009a50380e403035864160f4801e45401701e4107540035500d1070700020180d40200d03142a400c02c646440d4603003058950024008205a0440111a91004034002042842420004e0b024031032164006 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 279361546 1250 279360296 279360299
    0x5060d020a020601081c051b030c0c010905010513090c0c0206030f010e060901272d060b040302211005090a0507320402090d1505090a120804051f0204 66
    0x346000d43c142c4c054841074110b24421038590509961032903841d41c29160240c2c80d110124801c03421403201c040d40b140d4611000030704100b800c0000c540c0e43c200308001d0725800a5184d039000151200e21135910a003000d00c01405d8140095001540820084105403500e0b5903001e0345035001c506c2075032040d2030107641401e00710010007055403400c44841c1d110001352165841545019441130302603144030300e13108110075610f003100744116580e0b010201c110020156008202445003243c80480001501404c1841c104403000c60020880e070122021a80c0c0a071680c02503040a2582c540003004401078a280f0303004d48015164110003038058240198500c1000e000540f50600d000d500d400320b20707408605520790300310100d6400391380d200c0c00f08194151004080e00481340d04000600138403c01e0780a0380d102c05a003040e1401c3c0016940314055041c940c0c04104060740300c0481c0555500241c000081c03d0b64000c1051041c480c0c80340342d0340c47d00300e48203404451503c901308020f1983d480107491009200c0f81d02060 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 279362796 1250 279361546 279361567
    0x60b03010b122809140303150a05060a050405060f09040212010501021e12161502091201020301030f0807050307240b04060e0a0510081209040e01022a010605060d02 72
    0x2500760014000982c42e103095030b0003240071109010821400706071a41d1107030783c44103200c0f01c22805c002c1d510001003601da49142c68155580b0101000803002d0040c8081180030800d800c2803c1200d034100301380e446030340c1098648820001c855010003100c200c80d540502c842d0086881c1ca001804440500c0d0100c5800e5605020009181c80c0c00350b03025480c0e454085003400b9007894049800319002062544441c0c2c0c6141c28032000e82c01218000000b00712640e0b101041c0d074100381c3c55014104046003100c406034003810013105035090380800c0c0009001000c1c95000040003580b280020404d945c419410703a030030194941c5505424862901d005640c1000401560800000d248079000700802c0444081200c2c5041c0900e001011500912200c0341c00e594101190460f020402404020180c000459040b03403482d00001e41c01e0307007207c01e6440c025814007010352460301d01802580c40d02c403030270b0009003100040a209140242060003c11006542e218804280707602d0b03400041021020030340e80941d94082d01c40 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 279364046 1250 279362796 279362827
    0x10020d0b0405060402071106220f0303020d020601060219060f020304110f04020a050306060c010603051204030506150108060d031202040308040e0a020306031207021f0809011d0a0b0a060b03010b 85
    0x100f140384507900c10090840003810000b0500d998020545820b519041d40480070701d82000501c0c41c001400e119001c002454140700c0c6041d00c29603129601f56600706455035000c0e60388010a002e001c0141e040203000390000300500d002d070f80425004640115280c0c030107207070600480c1d000791002d5440c09000c028880090800c07181c280c1210f50241d40462130040da0000050150001401d00c522659001402d07001c05202500080c3c041c0d42c1101c141e0325440c441000405007580a07100032141c0740038190004503152007030b0307040803c0c0d000c068403400001e695220400600c40b0130b02000b00c0c14007800d030a00281c066034900c0540f010710700c00d01001d980d0b03500704041e03902c49600040810ba0164010020803c25440124506d480c800c06140a00d40319060b9100040000301c64074100c50b0020045c024130060300344e101b0481c502800311100204404083c00c01c070b181c82c6880840011605500c0444000001b84680c1011948800348080002c0d0490301d0b02403646041d44282d1045001e4880803c10000490700780c1d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 279365296 1250 279364046 279364051
    0xa02130b09030a02090a020708030c0406080603240403090315091106090307050d1104020f0901120b0f0607061d0c10090e01030f031e050c010608070308180310020d0b0405 75
    0x645010382004140e0780029a20581504024040c0c0042e80104000c0402d03501643da0361076104090648a01c1c4c8035501000c03170341042c031903280000c2c4d41c100030070314606002c100140c010103d9804401c0e0a13180c1c07164501e41c0c5102400c2101048002030300000450340000e051003005c80c501070003103580e0a07641000c2c0d050203d0030030124411441042480800d580005110084881c15100c400783e10346207040c1000d041407001403041d0080c0c00000d114404110040c000d0224401c00d1726032503000c0d800d0070f407058100d03500d485065030091700340c4050000903e4110050f101c0d15114400c08904619045000d9800c2c0c05880d0035500345a10910740c402942c0303450250130201480c135142c070400c001e140c00c001422289040c071000d0719034144903410f8030506210f9010380a40303410346d00d070401440203110001885a0701c03082d4007003055460580301250203c0081990380440e030f00042130030f040500c0e00d002030500d108280d203080e915208942e800710344807400740041c0c6103006007028002107415018080c0710954200 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 279366546 1250 279365296 279365309
    0xb07030c051b010917030328050103150501080303040f3507140d05160305040b071a0a11120907081f051005010c11030106050406080304080d0c380a0213 67
    0x301e5005ca1250171000051740c0d4020700d100308401001100c2125101107104901e40003460034240000481800b0b004528204120448881041940c2c0daa20b001d68030b074002560002e100d818100c00c1d41d4081407a03000030300701002140031101c209000c25a000d4400030b0b018043c03920668400315101d402e104001c00c840c00441e40b5013000d045000c0d900c450041183c49484520b1004103201c210b40c1082c5845103080e107000d0840603000725a1841d460406a0303007803080220707950301c40c40554000b0350007264074010101f40c0b0307440c0d0034007a08101d07002d2094030301c201c001044201d01d03104141000458000801507000d1400d440c451483d84035071400d41e032006680c070050501d01245401401004207036401409010a150030419110760050b1090000e4050171003903020980c480c3c2003801c0461f003040088018800c80d43c03114102c40040225a0040da001452000c003d0071a8441c058403850006400300d4000704207060030320286808400214020341c00000361440c408555003c65501d92003141350490034060315a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 279367796 1250 279366546 279366569
    0xf071412030103021012110409020316110703060e0c09070507120905060406030e15070905010e0406030209010b0a020118060522051f020d0c0e15040b03010b07030c051b0109 76
    0x15030700407131044a1600c40c2d0004101034020662900c1c0b0255000e41f0b0800c100c14202c5c5da0300c1e55600c9080002c1c0d01f060740c058011000c440c0042103201c1c01a0001138210f0071450207400703401d1075a2100380c014000e90001e020310b4002c0d180c400c0c003260f50b90b20b4503d1003407c10f91250f540725012801c0120350100e00f185e00d1030a0000e40e0900740526502c03a025681181c04510707001c24841c055155080c105110a00702c1031100c0d030b5543c140810741d82c0090240c2c040d038600f030361403d92110048040001b03035030171480060b40149131040144100b0010f040117140c00e6807e4000410350312072142c2a180b070700150100035a420307951001841081c61010421803010711861120004404c0039071190fa03201e0254140d4503d0301c02035100c000744070341c006805944c0000080c080c10040a0720500d07001c1e042203640c2600522500c2400740340f1072082c1b812810786042d034500520356400c42c0c0c00d006043c0626404041d00ba014800300441100019004200650600c00380c406802a00909134002410740340780d94011504450 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 279369046 1250 279367796 279367799
    0x9040c20030a080627040506011e050901050411070c0b1b210c0c180403080601050c0307172a1e0312060109080d09050f01110d030906020f0714120301 66
    0x50f4040e64440c0c215004503042410b0304400c081e03c00702c2c4071102e54403501c220144810001404008541c8034120346140d00003007140e901640720060f0402241c01041c0d80701030b200006000c1401d142d070041040c0040030107041e14100540c1c0340d0350740c103105551028801100005000c0c03622420100721400030311741540100107001e190341140008402030340004080c03900110b000404100d00b00203102042101030040180300c506043d0310311640381e0840e03040d008501c0480106089520407400c940781d90031120082c504000c0c0703507502d502c140003085000384000e9005000b602010001e00003481c00701503160a0f02030a182c0840a11410111804c2140500d00d00713400c60b04e9886903020003112405a03074270030000702c1075803080016a5520200d4000359203500c5030f080c81c0241d5270b410254000580b20211414201e40301311500455000c83c5421440e0000c0d00042d00d81305105010350083c4e0201482958007508010004180d196140c004400c2503030303031540b408440881c40380d041c0490042c081c0e94101c29461036 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 279370296 1250 279369046 279369067
    0xb04020f0703030f020d09080904140c0a210e01091209051e0402160305070c050f01090b030a0605060c030901080a050411212b020a0c05040c020309040c2003 69
    0x40c00380035000790915480b8100c040c155203540d4100c420369540ca07102000f0015450801d08d2558101c482c000d8040c0e07140c256015011040b5249940c42618001003c91600d00d40400c1121010300d00000113000c1806109081100d2a05008082807026403400005000001e41404820900c0303000f900d20501029034010b1101d900c0354600c13018500c0e04510740fa694001000d011a00030720820b1070351a1400b5449448004050b4800010851103000300f9201a54503219000c011104c11207600c4940400e078961400c010302401c0d2005180d0000c540c000c001101e5a65902040342540302c1c6000300710581000450074042e40e0042600754201524070030401c880d1801c2e54412514582011029103d00b000701e081c6503030440b901c40300d6000083d6840c2542c13141054100740455072a8020018160007281070b00106c1c55034400202c42e1342e16034115400c190518030b05014000103003041c49484045000401051580f0345650180d0414040c60f43e44450119101c0a0244400380800c404007a803500200004030701c8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 279371546 1250 279370296 279370327
    0x5090601030c020c060703090e0c030c0a0804050f0d0206090706090308090607050a060e0102030105210c1212040b04060207050a0f0608060a080105160806100c080a02120c0f010b0402 80
    0x52000e09000456a08444080e49089058519140c0c0504005008010554000444021561058002040b03a210301c00e0300403844c0000c8850800d002c0082c407101c000188203110b00b90308079000b41d094410380f500460445040040000d0500e015910110074061202c0080000000510051a200146a066544013502846261881c620450b8045501403d001003030100e4440320307a219030100003900d140b0902c40d000c0d401c01d100307131403085415080712300540c038415071410b92070b4070360740d000d440b000141d18204190038405288a18851082d8259042c51240d5040144090410070850030303195850801e0082c903105107504064015109150100210b104001c0d110f01902c4480c1404000e41e42c48001143d40c07e951030740f101d10710350308100c2803120195410480145940c07044d541c1c01c03402c0e030b20f000c1030042425990010000007468004080041161280070b042c04880c5032060380d40b0300200b11076601c95a00440d50a842c6030f08104080f20b0070050921036041038500c01d84095050102d00c4411401 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 279372796 1250 279371546 279371551
    0x306020708040803030108010e060a06180509030904020d050a050c0f030c090d081602040f06260a0f0308190c1d011701090c0315080304051005040806010b0a180509 72
    0x405402052500070040c010064a01800c60041102e40b41c0d0394072015030340604000030f0660010f0240c03d02040c4400607074002d080a491402041900d081007480200b40140001400260a80028841c0840035034941c00103111041190001041600b000035400e130490f00e020f0b0540f0768140003001045250346407801034943c008000d806044c0c40300500707804600e00290000004121480014811000018616416141078000d540400c940307c0401540745c1180c41d28020b061110100c05480c0c8868412948142c64040c0030704280e03440b000345503584a0000903103078000c1300840c01c0c0f8400c00011404050509a589040c048144419140e000f0007814029644140003030a280c041c040c008664094140145109484040f1040b0356079a4400032004000000105d0006402d10b20712030b162060142c07040c1c00740d49000303010310725083c540810000509040c030a603405004062000141d40c1c401802414002e12080c0011a07813105800c3c5d000709614203d0719241c3c11078800c1101440340752265005140d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 279374046 1250 279372796 279372803
    0x1806010e150105070609020d0b041e050709090203011404080901021b0609090601020a0b0901051501180e180703060903031415271f061103120408040e04050c0108070c0c03 75
    0x30341d60312890070180c5c040d1008801c0650000c0305d00245500300040e8819040c4110b0040d12074180507694403400b0001c10380c0440003d842944286418801c1c43d03a15800382c0e192a200400009140251845100143c079049809a65440380414041740658061048100e030f120f400032200c0030100710b00d0008007507004040000340103010840006449034000c200c1c4070801500403d01c45c1461425131282d90181c0000c030340705200501c600030503054035401100030b18000b610404449510310305142c8641e09104000700385100380c2c020b0082c054090001030000c00080d5008440100d1020310328100582901d088003d03866104c4180300401c503402103620180e000380c1404995860030462840a00d0203600f042c4003244034018028414000e1360054541c078801c40300e007000d2248640c6075840400b0340340c000da00030303030001c05420030054138240c50103001403994824032880e1031310306058a54800e9034540d07804440c202c801d40d2281861640702cada00901c0c0c1ea6840f001d5450200034216095031005029030b614032005 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 279375296 1250 279374046 279374057
    0xa0c0605040201050c0109050a02100e0901030605060102191b0e010e040201080403020309032b0504062a1401020d110406021e010f0912031a0906130e061806010e1501 73
    0x1400c5a1003413040300c2d024007180c2c00902c01c104280c14441e454000d010000c900c40c1981903e50810076000710404c000c0e0080003042030f40c15038a5502c4004c041e00004003030b281140202c0c00600424131254101c40c0701c81d0b0040080d80900c440e0200703008007801c00c0f038004c10741003c0307910b0041100076940ba150075482a4203103060782885c0c580f440d0603071031030007980b900580c076014032103030942103080c60301d4440019841140e407240320751150b0383c00f6544c603c81c5009920001c1d4180d2400301421055443c0c40c018041c40350103119440140f41c9803401e07011069202c1c01640c1e5000a24641d03081c1ca9400380c180440310040d81e40d441c19144c400c01a40d03c1910f83c040500a582c404110280f110342903110004007004110280118142c3c6c0c600002c484200301400d0340440c0c030384031741404841c6e044410b40b207401341d02404011084e2511070411981c289840510084d482c1c8411a045900701c040c00303411f004139001c9031943c1d141c541004210303041c0703101604082c40d528821810882d503204465140f8500e00700a0074103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 279376546 1250 279375296 279375301
    0x70c02210c04110a03050c03070c0311030f1216021218040617060115020601080c01080604021309020a090e1902031807030b0414010e06040201081008100c0305010b0a0c0605 76
    0x4403401d118001c1c404a90252405000900380840100280700582d200d503000c025984c0da043c0111101d00040d150030300040e1311030013600b0009000d0416000311742200d00480e801c0c000000701c1c100482d48409444a11a001e034024400961032540191482d00a64005050580400b4000c0c1455015880c840c40082c0a00c0c452100744d62101d60048000d0306c41141c1c1c01d01c15200802645075180001e03c219503040c030701d0102c0e00703c00610105080e0306036504400a806880d0300e8074011641c1f800050301c50b544c059400c201100d09003130070160752030080031022800340c1c641040090190842c040d90344995401c05211042104040c101e00c01ca9a60b49000e540050300c9455070b400c20700422150020340020f43c845c44030040140000c0c107030340c103110754411032a140400c000c18032441c1c03ea410003c0c03203800540c401400300e0015805090320543c0715440141000199039110781d0549442c45254801d50f145a450484860b042d0749806400e0141c00310060491903c22054002020480c0c9100003400c1260390313402 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 279377796 1250 279376546 279376609
    0x60111280c09020909010509010b0a050d022517070506010905090c09010303090f0f030b1302041b0e100f050712031e1a010201050610050c0705030303130605070c02 72
    0x50034510907006440035541c01d0311000008029882518618414441c40c0000240c41c82c00c640100c0c141c0b04030071072650405003c03481c183d513240c01c08409618256024011074002e00b102c001243c1c2c207000c14101c0b034144a02282410b112485507032040c0a03100c1010040803011503400500355044035001000051a81c1d41e50350304905105503e010550b002c00100000401d03d54000b14510550702070f60084080580c0e11031640704030000c0f511000b002c83c00e074280010030340c203106502c100c8072900280002c26649604891107040440321004840410402c0003403024508124a80342e903d0799441c00c0201030301c02c0c1003201400c0f5020706403006012020403d011501d2030b2081d00880c51000b640d00d1091030300445149030324040e003081d445c800d0380c082400b130300701d0400d40c07050094602070070001c1e241e207401000da004100c40310381c4842d40200360b910030010000364580303080002750b206140150f00c125600b010f0f4079280b820341e40082c00300300410144422101c0560780d06c4510703024207c1480c11000903d8807108 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 279379046 1250 279377796 279377863
    0x203270c1009060207050303090d110f041118030d020601030f03141204150902060d02070c08100c08160503010b2203141002040e0c07150e15060111 65
    0x1003030708a4021070310031900540142c0801c05580c1d064013582c4020751140103060b9039008044803140d06c10f10044101c404650701420035403e8401c05040400305283c00300204042d91148502014210070004802e903003c1031242601c281c8603000c4002c2c24500a490358000c3d50340b0018007001c0d25090025810b602014052010500610340802c030705030b1038044a0030035071100d42044409480c9512a120505148911441200412540180010700b4500310f010700c5002900101c2d07080742e910076191b4000c54005002c100139071500c0140d41012800e43c4078040003c0c0b40f0000600740c4001c215041c030003c02c0450708241602e0545001c58003c2d52502c0e2413541008680895448400061503005004400e2001c21400580c0700d08100084440b40d0100103180c100320302c228403800b5100854a400b00302422804401018418090f698000f191100181603d04990b4442001c12095000075005c01780a265000703029803200c0242444a0803011603658151103c100c3c17100e0640031700100501815652001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 279380296 1250 279379046 279379063
    0x601050907021e15090d12020d0605030601090f0e0f061308120708011703040521070e0c07060f020405030303040209040c261b0315100308121504020327 67
    0x290030f080c2d07007811400c070000d440d40118200a4000c0d0f442c2400070f00d070001e000405800c484080d13512100400141305158000b900458080c5001c0c81d2aa440060603a508010036400b030905100001900d4101d44554800c0350315160298500780c01641c00284e02d044007159481d40b140c0c8000c1c002000e14a6490465100e1003440001c85424900a05010358194440b14007410394240e0381180a0b00f0711075520a90380c0780200d22866900c5420030203c04c0b400740501c4000b122190b940c138100c4500e2500c4103c440300d0f0300003c07124521000380c04030b0700b03100b48080e81c0240118160b50001c21440d141c10400400d440340300042000c0d00503400710011038104540c1200120042c9408201d00c468045410080303d4000302c0100d18180c60312622884841441c2c520b00442c0d12044014010415858600c0310a40e5501c0001c0c603840c2c4c0d4690004000002c80c550400810b0f4203030600c21000c04914140e40344c0c110a5034055440707400380b441401040304906480019002030b14181c104d50f541c842600c1540c0b803400d40c41 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 279381546 1250 279380296 279380323
    0x6020d0504050c0f0102030c120c1204150e0906010e09090c0a0b130e0c0715060e01090e0d02070f050f0a051c03090626060f0d0c0620060105090702 65
    0x2480c0400003405004030302c81c9244001150f040ca4000043c0c40126624080c500c0f0000e2940c116070240c003001d010500051034500d50b04426a02200003214850485400507405019040c1c4801240d0860a60040c0305445154040701d20f2401d50a09000091501d0f5010410700c0c0a281d003032000c5183c0b0441040980e481410081424034400d8882e48000340303d412040059032240030700540852088406244144501d0003414045d0400c80a41c0346c08411010a080503080d803556560007041c442000c0075410b001e81801c10000c103080e034140a5440ca0915004101c80441d001f0007410f00481d80b0320407480040b81c100301c0d1401801e03090301d0700050500c281d50340901c0e071121b41c0e01680360601408508000446000341c5a0f00c1d00260341e8035044d1407422a5071190f1209840700b0080209100700310580d9500b004001c1c0012105c3d0b0440d50124101c26040a001e9038035810701e207002c1003941d030f00541d44103000445608040e1100d0f40782d5a60350b40c483e41800b80a1040e250380002800451007080041e034041d42 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 279382796 1250 279381546 279381551
    0x70207090f1404150f0908030a09081201060c03080a02130510020102120f01030203060708090c130e03030f090601093608070c0612110d0c050409090510050a0b13020706020d 76
    0x602e0304c1c1994011500c0c107052600355041c002e071940c3c4100c8a100b01d40f01281c000c0c1100c0e1031942c80f100000d009108040e0122404482803040c1e800c0d9100d4194954060300c13041e1100d0023021043c0c10090080e00300140201c203600d00400a24800b107240c0505030044030740503035010031500030380ba0091b406402034078425400740c10482c04008480b1102c102d01412280280d0560b513203a08e4904c000c0310007010444000303040c1c0e030200f03c80345403500300f450406492600714040040c10020404200d400c5034401c1c2c2d03c1d01e4a0101440c24401d914405114490042c0600c400c01c0040414280c0c1d8030760350b10092200c508012700f8041456020301740c00107070411b04560092213180d5412551904a640721101e0003040b0004090780741314804071076036100350084100b80701c120303a04109541200c400900154100042001010f200c0024249403502403801a1803046014040b1403644907081e00481d28010000f2200b1ba04100f1034410030b40f02c00140d031000c29880708000d640e4800508152029118200b07100c0113151 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 279384046 1250 279382796 279382801
    0x1c120c02101b02031c060e0c0705010b0324041103072423090f03010c02070303180509070813120e010813020609120109020a090e060106020105070207090f14 69
    0x3540460500e00c461020710003000b0144a80450020b0500a4501c000269008005600c0d040c040e6080c0402c0c0205070b000003160060b00d0391245401744100b9141000d012502003180400c124080c000c10500309000d60081c4142000003450801c48a26220450781059080000c6002c2c0300080c0304030100210083c08a0b200d15070340e04040d620f000c1c10400800c00c01040b44580343c408030310912820a0b00040d0445401c01110584480d8900d03a02c205081c1e540060908600141500e0a00500880706c04580140410529500b000381007451003208894400990007010300c12547e03000420354210b4140e14108006540d0003081c00d80500e40d520340600310114100d8020341c4640c0c001444000c00c403013a640c000c003c4e110010761100e0f45446a2000b54809404c0c0300c0c00e0824280b14406026180c049000440c2617003a6030003140b16040c4c0e6401003c01345458818407a15072204008e90790060000384000c000c24035010358001d4540006004100c6855280c090050348021260000c4040409003c4c4a44490 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 279385296 1250 279384046 279384071
    0x1909050c04050102160e01091802150301170708101d03040e040c0501020c0d0b070201020909010905060301060e07050d1a0405160801060504060e102309031203091c12 73
    0x10741292203258010703c05c1800740d040b00d07040c1802e030600311240300790b10b0342d0541d0901d25100301415032080030040c00141074071001d0151707486425044c00d881d80504203ea072035042005044143d01c2500440360700740e2103220104032064000805055841c0d8004c00045c1801a81994541040b503001252120380b101040c00710b262620140114041c501c2951010b2130745a0b540d00581c0c0707407040313050441e074061251458074011400141e034580e806880c91000500c1d1202d03486c0083c1c41c081c002c0e0891400950b580f41002070b6400d09100b4213015000600b403100309490945001032251043d5030b207044001e03231070701504105420040040702c2409401081030095107000041e1003000780b161424000012440e10000490174040c030b046030241c62495403210380180d040c00601c40c0f82c0205105490400c04d912100c101501003c5549101c44c042e6540b074141c1ea1540e0008140c50714002c00d0391500428410814040d00e10000207900645d034003080c618541300c0e203007800705544021440c0c026202079402c00c00b508914 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 279386546 1250 279385296 279385321
    0x303150f0a0801140a060b0703031a0a120204050f040b190f09030503040203150112030809070902270a320301050a0b1804031b0809041401060e041109190905 69
    0x2100c0b074507441e44031039130351038011100f501c4447c801c030300c1210380030450f110100307200b9005080d0b15141c05000000c2030070320001140c3c2d48400f80d807014011040c8941e8807811480e1502a4640007018980c4490342030a00e5250a00c414002070446203e80e080540342d1612646560008154445209401c00080c5a6420040d01552080394100d02c42d0164014140900090300d0b204c078140c582c22019060505282e5034181c0380d0702400340111200c0c1c40b40700c80000b0481d4481c0010312043c0030341c4042e808140c0c100e00c4c0c10701e070502d074007400d052007050741820a01040c0807006886580f80441e1010700011450b00a01000c5610420545d540550070102001161490340d04030542c0c034102070702e8000e821650b4810101c01c401060320001c00190a60800e04c0d0300a02030842c0402d4607000b40455803414490790000303021544031062510312803140c82e0040001c3e9420980c00b401c006010b0340d00f0f0264072801820b2020f94481c20180301e100d0907019940e274401c81c0c0c14161110261101c45c81c03c010908001120b01032 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 279387796 1250 279386546 279386561
    0x161404050f36040605090718090c0e0702010c140c0d051c1d0c06031306091b0e070806060c06190603021201051816031217070806030c0609030303150f0a0801 69
    0x8134142014081592481d0010300e040071a40d035005211002c05003081c000018004255041e2980040b0500224403c00910951401010035030000103061501c1d01340680201e2400c0d4203c0c02070701c401c0c0020800c03a403003c11019240192440c24556507102c84446804500b80010f041200d03038940203c1d4884941c0300c40703a40d0091601742c2d0807640300b641c1001c01c04c01148412140201000d1801040e0350015a850b0400c4040fa4880d4409908500e0701e01442d0300c48000d17660003141000000000d015040323400400d81900070a05030341d018901403150b80030170b80ea40c5010785001c1c080200042840e280c8455076000c140903607801001101c20544560020703000c0e11054901c881c140c0d41e0f10071a00310142d000601c031182c5101134040c0d811240c3c42c41d121016000c40d0484880244550207009401e9900c8400c0304e188a500c0c96103c8580505103e0180744c50080700180141c003440040002001c60764000046c5d0390f20031081c0c0c4018241840400104006d035001228050300500742c1c04001c1403030b4206401441 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 279389046 1250 279387796 279387803
    0x50c010324030f03020a170406030525080a150909060b010e21030d0603061401060906020c060f0403050706050301030b0a051501030c17161404050f3604 67
    0x70700706581824030310203510341d200c01100404240400005032040081d4581c28040e0050752070074841515040810500e00a810070098800541408030a4240c458150400c041411600520360340608003248000488004824403a04400048044800c1d1f00300551001080020b01009903440903407001614820a044030740500342040c0f80f03100c1d44203000359850504014800d0714413504803411031408061002d01c41c15140804c1200c42449101805600e0084d4490100020386103d6581030110000041e0408410003180e201c08001c00c07980040c0240c2188030031614150f6521780303819844105d201e19070008001c0d02400300c00150340b81d0050090340c122030084268081d01d40e1008000340032250215003042840c4c600c020b4012040d403013a400030301c00e8113050400f502c141026202c000342c1200e00700d4a00c0410424aa10100c0b00c5502901d444011f03a04526040d04203420180040c000c4401c030301140303000e80d40701214240608030043c04008075103007203285c00015602100e018501d80908542c00e8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 279390296 1250 279389046 279389051
    0x5090604231e3a080a2c0607140a0e0f281205030406050d0e060406020912010207020f01081b030a20030601080106050d0f02180f0d0b060d060e0a050c0103 68
    0x4200b5000c400035105580341690a0324000780207010f402d586290014210761041940c41c0e200b025580c0c558500601596241c848295084480980407440e12400900a0080000594441c0a0501481c0c29140d02d9001801d140c5003106904004c900b55161000006500c00c4c1440e40c3d403280c06540b00c5170809554400040c2e40329058071480c800080c64001d20000340742d984100001c0210510901c090901480030440209500c01d5000c2c0161524000b50382c02e403043c50303000900c030345035203040d20a5002d01d65a8100075402c1c076010340c00260204e803558159034180014500052001d00740c0c42204503880f0071140899450f801d0a2540c0002892000110003402c8640003038a010125200b05a034810b107016074030096036a0806100301d40c150807001080c1d030001d032155084520000780340054101c0c11848a1035008500c103072403c1003000140000c0440c068181d200302040817030382c1090b0b0f4662212003541c1d03e06038002030b4603202c07006040018003000c150082d034200d9005c1041c086040c1038005400d0342c05 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 279391546 1250 279390296 279390343
    0x703020705010515181608060109090c021606110309101e0e030c0603010305100908130605031918030e13050c07020414071b0f0501050f0a05090604231e 67
    0x1800c031700080c16104071010010344100f000c4c04031312605056600001c1890400d244580e034211010554000d065443c0c05a0080b403880c4039000c2c4404486030003010070f0300c0c00c10010003c40c50a15182d10400741c10702e0241c1e074081c9503004424040c6158050340074109030410050408407070011700c1e0070320308241d081c444d002e8442c0140007841c104069034142d81d008400b034005d00c00100001c1000b0404140e049610030418011300c45624003203a202c0000341025180c060703491400300040074036400d07803214034050b0520b040c0000c108082030520322185580c4c5070034a10100c01000c000107804140a0702c50101e002d041400708170200c8445805412141d100303880a004080c007034040f0301900102240e001c000629034000381030303052421707400b1490380c103000f0181d5615a0342c00c2d44420307007920401c454103240a01e106062000d4038459100d995844000b44018060600301561054035190720440e95400404450101e2541654103111600011300280c130803281c1d4004000c20701d0740750340c42103400700305048440c1c0c103 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 279392796 1250 279391546 279391579
    0x50307021903260d0902010c050708010e01050901060608060114040306090602070203060a4b02030414030a171801050a0c0e01090f0605030403050d05040302010603110d02090f0703020705010515 85
    0x31280b0614900f0300301904002c05418008000c0c40c0d041400d0703041001c07040300003020031014049007026011441c00804c01d00300a401260039034001500c24801a858104100b1480c1d0740001e040b60898400d180c148107004450b03508081c81c0c00f0315000903000615149001c0c041140690040144034030aa050710f003595190030414040b11400c0203074083c03510503034100c0940d3b00380000a41c3d03c43c1a040400300b9062110401c440c4140d40401d111184a55001062100707001c00194420416103000000314508544440000c0600410010b50031910344804041140e440c0401e400240c0310803240d008000e00d20b806c0c0004000b5200b13400c0c030710011503c0e04902212551049400c01c0c1516413628040f03000501c0d124084446900044c03064040140c00d00024555030420b000d1203000e28007982c000b098060440c180710780100383c0341c52001d00c1360762841c0d0208010f0700c440c2e41003544a484c12490240c03a50342d040381503010b0300c01c111004299501c0c0500b00300a1010031030480e580c269099850100f903100b201c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 279394046 1250 279392796 279392843
    0x909061d0a090b0a3b330709051f030b04020901170c040f08070608150904030e0316060519020604051b010201140901050a0b01022107050307021903 65
    0x41c4040c08060014000440903222500030316025509600031101100b0143c00030380e404080c1c041d0aa040240442c00a0207051041201c1803125525600c41d0011300c0d06c80301454056411141035484201040d4005500f030fa0140039038500522000d0444109860420390000412200310b02440100f442d00c005041241400c3c400c2d0b030800b0070180c403403002c00b844020344551004001410075181c00010040460880c50210310a0b00900b54a001030001908081006e0003a50000b00301c41c0c0c4101c2e03e000b04420382d50785c021145802c681c160500d4800d10600c44046070134440000f0316050803240ca0840051001d910030010035200c42d01c08801d060700705010ac0100d0b100c0c02c00f030700c000d0b100c1e60000c11807003041011158031070a4184140000902c0c0d003415031243d00c5011080303580d2000fa035035480800040c003002e8015150610300074800342c03082c0c01d002c40b440c12a800b42c0f9011048850b02c0480c8200401c07000300101c9400035002442801d2503c000440901204c90a004c00c842000214684500950016 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 279395296 1250 279394046 279394061
    0x9161d060715060603113f070f030506010806130603050f0d09090207020a1e0509010e0a0b010c02010f11030d020304050703050f0a080f0901030f0e0106060f05090607060b010909061d0a 81
    0x5014503010004030841f035181d0005010280545051f00a0001508074414250702e1000c9000c00b851107151a25000c0d1440b59844031801c189401c21003000000d030fa00c840640e07403000c3c0481d40c2200d1095880020001404a500002c00ba0b11030b01d90201146640040d8002c0441c1c1d09503174554400d9216603061302a4020000c0081d0080325a900a00071a02201d00c00404540c1c4035a080c91803698a8000904d110405ea0020040151207400d00241d540d26028280c10044203080c1240700302c40325030008055480400180d1f0400c04640e15801c0c1c1e010050080b60f00216403c0700c2551039007058108a52502c0031440200c84600c42c01da1000008000400c0e0010030070340140226041924034a104243c95018400c0c0a04147d61001400e040d55118424021108030a40002031b185090240c0600390819200c8110b050050030f10612809030b9988049410450380000e02180b000071080c0141c0b0542c8150304810b980c0c500b020404034140404074401070b01c1404610b0044450f4650100200494900 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 279396546 1250 279395296 279395321
    0x305090c180c0c0a080406080f06030d360305030c0d020f07050f010507061406040507020f0c04021e0c0a0b010b040305030d420509161d060715060603 66
    0x1400c001840c103100c0d800240ca41450403c0603107051640e1942c401200758031a03000f03480412929005c3c0b01900c2c03280501103500070347c10307002040080c5011102602801031501e0845480d9a08410500003034041c060b9404144a0310b6036003d8031584030b1500c103403681c0010402c2181403040700100d49561740b001601012305c03e9490041c06485050400b032001c1c810f000c02049050000404c264000204184164404420010601c9541d41040c034104402d50f0000381620381190301c8511042d02007800880e064244120441d0300598580b550315440c3c0036040700d01d2103000003100210b001500e103c00460308201251007466500395076a01c1c1d90041082c1d02440c00042d290360700500c190450124583d00410818403402162440108845840d00e0b00340300180940740015071240701648251032201c48035000c0d1000b1240c1300351070300d8420800c2501c20b40b6030712803108104104002074403101d04241402031480010741001c0c0c1e02c1059044c804048175405440180072850729000003905172180c13244801e140306 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 279397796 1250 279396546 279396589
    0x306040e0c01350a090606090c050901081009051f080a0b01030615090204060309050106081203041509201e060d020c01180c050102070b0310060c0515070305090c 71
    0x100d80402028600f036662012481a030602440441c484121405100b410101400310b000706451801c0403e43d05c01c1d5108094481c00c1070000c0280c181c114007514000c0b002840c10303161964403608580c06203911a8400d2000c3d6191100b4080c034101003260105a5030300c0d0408103062240d54001c859034400507910003030040e007840001030000562942000e4484503d0656800380300341c46108440c200c0c1e2059110801003550b41c0c2114040043c20b0281e0f00050a10201920641d00c9844085115100042005100c1c0308804021004002d85a201d544440c2d00312071000807044c0710140c0c14400307990100d5007502c80d03242c188503200c0c00416860030541141001e0007103420014000c4c2908040e4000358240d034035a5403950420003182455040d01e00015018444008002d807a00001a0174407080e83c0264550103400c204000076101200003000489225291a828000c11414503904099883c240151060003800a21440b00c3c0e250f004103001c1c00300c803820b403074a0000340c1041185808040d245100802e0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 279399046 1250 279397796 279397817
    0x30801030204090201020f010e3711061e1c09050d0513170a0b0c030705070809011407200d1a0705070506010305061009060501080a1d10020306040e0c01 67
    0x20142c0001c3d980da07106004441c2c140595000391425207105d8407c41049500201900d080d903041214030300e2501ba220324454101c40c0d034520341d400f1040c60705e9074040c24990b901c800e4803016032296021074550240b900d00c08400038440c00e50090180e0700152200140499058100302c0d01d4450380304044a6030391000090240c0fa06030b11050350302c1c2d008441020710121002c00000707420000d242c12203024512860141502c1c20141c1b83c502490705001d01006d0078000248100041d4503049001c4481176504964a00d46521101c00102c2d040c0b10030b0710b180b6402807000b09001080044095445449035031000d80d900502802100380100d0350008a805003070a00e1146461000300f450200da6a004103040ca0098034202c070341d4a5440c605413081e0b01c1200d156020b01d0411010011104050018003d8a8818000c40b482c14000904501014009150065071601c1c105502100841d100341404081070540c3c1000240314201402034004131000c41c003070703414078079404440b0f103011a9005040030140c48220184 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 279400296 1250 279399046 279399049
    0x60306080d120b03070801050f07081603020c031303050c030105090c0105042601020703180602030415211805100b0306040b151305010303020c010903120f020709050c030f10030308010302 82
    0x10341c400c0110102e0203941d180d034801d050324240903038005004544008100c1d410034220703007880312000030091000c218001c0c00748012580120010354400100b482d000da1150442c22645046108102c3c001c5902c003500c00000040140104158003460412002000141da40e4203405445098000455000031000c010600c17180c0d144d4075400c24108000034191411401d20780c4900d007280d00100054000c5070703440c18152120901c00d103c14001d0840c0c0c0c4042d608041c5040745901081074100726130424444400c040d9440f0030000000c0540c441881c440c00d00245242d00340003010400b9002c41912035010b00c990010300e9a00c0b5020fa10314100e80a001811613540780d03142e00c100f110b0054192284040702d205922081da81d0503401855450011800142551442c9401b81c80d0602181419040c881c0c0804104049109503107035054007129030a1140718440041801c03414020950040d502c424501000e000d80242c1c41b1001e58070825821501690b15190440c9032010066a0311000300052066401403005 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 279401546 1250 279400296 279400307
    0x10e01030213090f140903090603040f02120d03021e0c0706030506031219030605010e240702060d0c110f070312050708120901180b0c030702120d0501060306060306080d 74
    0x5030010b0021015165151040daa050701c5640581100c166240c6103110b038070160b420040e03034224421100541c504140403000c202e590100820103031a15000b085402c0c19512010100c3d000201c401054a14510142e60003900a4000c0c408841c010720715840401c0d1041c000e03100300c5130ac15028800070710308039140c000110064600186141e070580911180543c0780c2e4001c40183c690f201da400c4001d007100f4140740c00201111040e0b40002d0402060034401c1f40c3d9078480e580e00828000704410510101d1621401e15440f82c03040100003504044006500031030140b142e88200c032a00d01a03030301c0002d4082001d4841340d2740c582c009121101e94102d40c5d42040000c04100e82415052403500303100341442040e84800200303410980d660340344616258100500382c0070038400c1c4203480420b03a100c070b2440300f5284c8506201341c01c020450501842c0c00400300c1c12a0b8020840c080c100c40300c0380101541e41031100d2060002d000d0a21808010a00704280440c11f207010b40246029240c2060060440030305a5000b00c40 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 279402796 1250 279401546 279401557
    0x501030b090423030706060819080d0903230c01050105060a1e120e010b131104030803150901060c0516061d01030605030f0109200a05090a0b09070f0f0905010e010302 73
    0x350070100300d4522103448804c1c0060b022042c060304c40001ca661500c0092410a14200903440f0112100a85000042c2e0f01c6810746460107400400083e406134285025502c0181568100064a200d020050301d80c055a00082000d418080000d01103640d82302c091000c1030203900e1221011a00c954144032030b081c0c2000364000700c9030561400920003c403903400c0c03030300320780c1400c05e001420707511790100c0222420070615031100740b2500c0f2000c01451074007118000e0240a50b000003480f021001000c20071800c020000e404003020000c10a00040d6596a00030341000d1002c041286e240c02581602c04d071107144c0105c0c0c14111040c1f515200114944050743da2141c000342c1c000c880c180f50340c885001c1400d4604004108614034a44000103407190f841c20152040d010401c01c0f002252501019420b9076160032022208070754055031300091640b500006007010b0f10705034140030342260440c002c011030305901c1030905182ca1099250002c5100d000d11040b07604035118052a808251540c1009003607500c41e600610 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 279404046 1250 279402796 279402833
    0xc0f170310080118082512030e0f0f030d0207020a090501080f06010b030601231603030605011107050a09020318030706020301090f0905060609090f120304030e06070b0103021905061902070501030b0904 88
    0x100c01b80303140e890613030b6101080180b030000b07550f4554059206100300031104922007000018592400b1507a00310366203125010320b1321501c80d004100303481151101e42542c00908031418080c0001d40c2c6403007400d6524403289890300043d2103188000200f400440044130f00545040c0e69030f4000750440c00783e604110321140c00e0a02c00709410403460550a190641c011a100c0c440c5d03070040781c2d0500c2c2c20700060203104240311850720794002f848100301da50b03192406c003011202644805070704c81d5259207042081c514a0b181d92400c41c00700042080800c5010750046040c0c1e00311902c100400700d1050108021500415001000b1360700860200d0407a02c4c26107812584000440125003c245a00c490300c0d040411904045091103004002e00040640090035400b00701c00544507030f824500c9984034130b03800160610010703024884001841c1a0040041039110140a000d0811031b515094001340d40d594036003070310648005000341c070000314241d8841c0c041d0740d6160800505007041604d03561642c0302d1014a250859 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 279405296 1250 279404046 279404107
    0x1404051c080a0c05060c0f07060506060903071508010b040302060d1a060d150501080c041401171302120105092107020d03020718020a0c0f17031008011808 68
    0x180c000801c01e0006041d06919641c0d54142c040481c981240b802d240908080c400100c140001c10000740c18030b0a5807000c0350822004249900d901020805a10070980b0356a014003401c0b1003c541401c607241400f000c42002d80c2e9019450ba0b9076018184c50f0701032400002c0d40088100000180300030145c01c8540c9546010140549a4003400006580c03a4030008015941c42c0d103503081c0315010b4001d26200d000802c03007801c1c16282464134032041c0c0c2c12071080f8050803450411030000001c503a4400c503401030b0702c0300402d402029507040c803071a8002410142c9004a100f5103c1040049603140c060091030700030369240009128000ca8003800314600f10204a03031038165082803061102507031303c0c0081800240c0c02900501201c9040100c03d140f03030303503112400c0400e85004000c00500d00b83d01c40254684550045090038030120030b40b5082e40c2002c400d121421210a011060042403004607140303604503041e40c2d0080201c143d0580400c080707105550006815a0424010200200300f80c2d1144640c0462400d00e1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 279406546 1250 279405296 279405349
    0x1080c01030504030f05070c0f1503050603030a0f0f0512070e030d021506010302070204090b0f0405060c090306130227090d020723030a0f060906050906040f08130e010b0c0c01140405 80
    0x104510700d075030b40c482c5010306903610b0003443c074503054428103401010035003f4601d04500000081d1024107021101d401b00201c0400d41002148903406403150620501c1000b112400e059000a00900043c0031040c402d000d01e90308030201d0343c00040c4403404841201c0c40501c0301e80e2883c00550082d0012003059030800d4039000b50400059001c0b0b90b0318410b04c1c05a00142c03240c209070a120349402d80c01441d82c40c00400c00c020b4a00c5541e400100030707038002c0600560b5809600381e0310100c0c0080001100c040c140c04141903850055aa2840c2d0b000d1207154503604450124640300310032030307482429200c1c1910b08092180642c0700454a0071103680d03030110103001c036004a40709071f40303003003e4501c0010181e55981d80e82c0a10703010004580941c0c2d0300486050700411326400c040d1203a4244201c12030b00249005000181418040e6140001e00010111488110299a0b5562400d600b6a00c0b140046c0030b10b000e1072a03080300707542c0100001c004403142d94440906007810101030281030070031401460700f504400c401 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 279407796 1250 279406546 279406559
    0x1e0e01120b0a030f0c0e010b03040b010504021e0a08042f0409030908030703030c03180210030b010201180803010503010621060e0a062405010305070c110a030507060801080c01030504030f05070c 85
    0x55513400a88119151800d0701d207000400d15807002c040c1c100b140e03001410014000460886481c02d41500e00c111001a5620482c3c1ca03270300488103c11003a4074041c48086005802d172900030320928840d9001d0304880301c0300804403000500c0d401c884011070044420b2441e20003030506056000d0f0b943c080c0301c0c0c01c18403625030b1940f29007071464024610031000286c54041c4040816450b014a150f603045034040400d178484140e001445094186406000b0142d4403028884c0d640e2003500320091803500055102d20004050a062055500c24000d0714025030030850002000300780101c1046031607440c0480003a500d642559034402904000384806101e103d50030302c0e440401c084e48030380801d40d90307204000425184400800f540c030f080c8540c450350601d45448104681c454010780c401d5904c0d584034291074007200e298800258907c00c00c0e000901540720303040005c540c02e50400d0b07090303050355007074403c9621043d6450011410348504403401800110410031110034540604050602107204a160030080340c2c4605 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 279409046 1250 279407796 279407813
    0x91e06130e0106030b0103090201141608040b07170c0c09070320070201120509190807080d0207031205040507030201080403030b1302130801060b040b0306011407031e0e01120b0a03 79
    0x20001c4101100110040101d181c052043c142480801c2c20f0500c0036a46603000648944c0780f4016255041c0c40c0000ca5803d0220314410911000742e000800c0d940303d41e00c03403204504517000b00030215006c03204c080040c9130400c8550152101c03505030307c00800801e640c0f2024051500b0015042000b415181c2409580c3d04900e400766402894086241c691941da0b42e0000400070f2a040c18072003001c0d440c050034800c4c80e03800440c0d1840c40301002e9441000f100b500389010040c51081c4600548400000700345c0740307103d02ca207030001d1004030300a0f50b0345000307819900c403401e08642c1c054a0081c603503844141c0400045d40500e880a9212f03000c0d04002074207059a01c08500003240000501002503400070b080b10788001c1c5116210040d00d83c0304000c00c0a0360400207410420700c9180901c0e403071900040001201c1c3da100d01c240703019800018280320742380c0109240140c140910030100320000ca0070145001c80142c4110300c55450180f05940f85021f21000341e104100904ad40007401e600002c6400d00070001c940c0e40b1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 279410296 1250 279409046 279409049
    0x3020f060717070503072c060304061d16050121090c030302060703110306060d090f031d04020724060503120c100c051b0c09090f070605091e0613 64
    0x82d1603041c96141035900910325010024501d1090080500a03c848240c2c40885010802094034803d080103c0c01e443ca140c1d0820b003c07c8a40d4080e400100f00020019290031140750a03074481e032162000d02405d03e070992140074202d4900d07241c1c2c586601c01c009a6224518048001080350b41d06c4100a5902c90800203641804600390b6807000c0c0840c1c10400c2603410000c2c03c0d44406140303810484102245244c10003840040d0440344030b45004182c90003a00466070018291607070114445401c56107a2801a00d51901c61440303100c00c0280944001d40e9043c03a00807035211503405800b103050000945122841100703400303442d0203070b150f55941c0491251010490f000081c401900101d85440d400c1c0740141c50045041462080d0a080c05a0342d90450b4011040d511400851036501c07202e208054030032440c2c4007492203c1e40d0f1021040080c090700c481f000c40d06115106195083e1000207407500010b94140c800d142440780c00100b80282d80002c0d0040b03560040e440c030801010b9510700100031060403103520300d5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 279411546 1250 279410296 279410311
    0x3020904080702100206162f1b040912030504060e060c1b0714060a020102090d12030e2e0f14100e04030504151b030201020903070b040f03060903020f06 67
    0x19282e05500c0c04500c5202c010529200a10f10361800c050100c0248034069607140601001c0e8007002941c840c6030b0010b0b50351140c000300c054907a42c00c0c2d00b062940c545144c1c01c07000120166110700c0036a410140210042e241e0800400218900c495904030700070b0000500940c0c596603a100048280306013032207114002c0c00003007a075a4840e000350300406680c44400604400303941c820078041004842104450301002021511b5640b01c008080b8142c0c0603124421034a548450390311240b00c10048002c90344d043d0510590ba0401c05241010400d503941c1392040e02194000000400808036012080c1c104041c92400090200303811888108100c280c0d100b000310450209554000c105094180c00b07107500007009800102c15031410603803400b038881d206034000d82c2100452800304801c031502492141d283c07410784142c0607140c03002508000f4000e4101ca00301c24840d015146000840c400e402064405540c5403100603c009455a40c4840040524060813001d500880316046400f120600c007880c840c208 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 279412796 1250 279411546 279411563
    0x90b0702010f0b0f030c040203060a03050d08010617060f1009030b0c090909030a17060d0209100f0f030c2306030f16050c06040201140d0e16120807120903020904 71
    0x10385907a003010f40700c41820807401207020051511282d038000540ba089150242d40c01a07803502e942001c15441038094001410310b2058100301030305240c4c00b5040604a5803a55140f80003180c10540f24151040150340301540039564102600a0385404403002100c41c1c450b06002400954030741d21f50340f94060441d41180c000c18082040201802c159086503405100a00610314100305c640015001a1915200c07408550500300000c8054031000d40c02c0341c1d1150020007031a07040c074141d1840503641889004440b04034106a41c00221104880d098909581e484500825814140440118006036048000d269000702c44001940da49a01f40150b011b070303604072480740551601c80c1d42d5851440c0328885010401c031040107002500d41001c00e407030b50007550902c2c00108410402c11040014060070305840d4156142100c10451000c0c0040c4115981c1480340e208130b620707596807011400342d240b1180d0260411008000c4c6000150000e040303401d888080303003400b58429403241c0128003404011a411100042d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 279414046 1250 279412796 279412811
    0x1003021306080105040f0e0709050903042310030b0a051e040507020f07060e09010510020f0303100302010e0d020108010b03100803070c051305090705010f1101021920030a050d090b070201 82
    0xd0034020820b60601610b410301c44e0940c0261290342d40c0380c80380305409c2039650f07510200712a881c041c82110000c1c480603648200c418001c42c55120000c080c00c060743d1092641281e8242d0781c500034002c4a50444009110b40c110b1407410061200382040c0d11a444c4420095101c220038550f10303031003074602030040d03a4010000c04134070002071842c1004903000300c0c05210401000a150f0341d5980307050341c1907440607541b5810f0922448000e034503000c2e0f1514900407a00021040244ca401c140c851781040320f000b41d030340d120f581910905101280d07071710310406400150140014027a0b50f45010040d0b402c440000b811000c5255036051503400c54102070812646420b060b0341c2000705141040385034110b540400410461800c00c3c2c3d8810b5034500c40b0744503180c14000f542c0404880b0600454110f6905150400290341c1c0e5600c150001c1c42c00c0b02c042c0c1d0b40d000424402c14400c040c5804050051810904140045150200360a0141d035140c0010801c250400d44034205280081d407400d4410740282d0641c1c00208040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 279415296 1250 279414046 279414049
    0xf04020901060e030703020112180311070603060b070f0311030403030305010e010e06030a06230a0203011511070e100803070309090e0c1c0611070f0b060913021003021306080105 78
    0x6520681c011020060f89102c00e41c1e40d5138011075041d04036642400d04c074041146040710540039140703070780c21480c1500c1050801010700d07401004089043c100a07054551481d11004141c1c2216828080c48000c0c0d80705000c01c000240000c00c0103c807060080c28410300c0c3c114100c0282c1c2ca0741d80b2941040b0002601c0784010400350240141d100e0140164506208551401002081c0c0e10245d100d4094107254541c03032141c1c564500c0810340c0d4200d0280d812610000c1c5040c0030303008040d500038407894400702d9005201c050180e1003144e03590300c0e94030841d02410f5140e01e401448083d0080c0585821010140048001020301c2c0070402009524820344580c01c80314a000c507214106c480b8a9619507960f00611500c090301c1c0e5840390080f841c0e40f034100c191105901d160820310300520003142800305001002031007009000041c1601c034141c5220b51f00000b0b0390365540c41400200c900c143c411407410031f0400d04410040ca003451605010764090b00e401820058007030000d41d90004190702a0002c60504401440340e03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 279416546 1250 279415296 279415309
    0x20f0f0a1805031f0b06180a060201020703080f040606050d03082502071a090406081515060703050306130203010906030c05060c0606100c050102030f0a0b09010b0901030b01170f0402 80
    0x21070180c5941c100d01c02d01c0c000c0880d4803000c1001c2c0d40f98204a08001498406165501144410402030b000035141e11a02000804250f114070403240b14410780c120026001b0f105008565803e5415544c0e14115211080c5045800d034019104030360442c2c90f41c0c40800c4546483c245102c0980c06a52078100508224115030b1140441500d8880c15040d0003003188007898000480208482d040e051440040d601c040e4021614007402031580d80c46402d0450014010100056035942040e07103640c047c07643d40742c414040086001040f01389800a100784181c00103e4040c901465028070007400303600c840407825005200701d0340f090700490b01041c0d0722003050040c0710083c113000c0f0180409a415620b0311040e0800265a40300c0204524815502c5858000d4a02e00c252607268109038010000c0d07440b41004403080158070401c0300d1014180349401070011142c588820500c0c1240e050356405842d021508004402034014980c10034188060360080203c4246090f11042c030800c10640d112111303041510401c0740 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 279417796 1250 279416546 279416567
    0x60504150b0907110109150e120a14090f0414180f070302090c1b0c0906040207112407120f020609070605070c0e0a05090c1206011206020f0f0a 63
    0x18941603400000d5140c0030107007074220f800350402c00401480080c101d0302514004500602c203820721242040c01c1303006a00b01508001a40d401d03a001d0f03045068080b20107000d0200014001201105488030440d0010000d0003241c1015144001c0341c140e9401003400d0340c0d5540d44032551030325584100700c0d0a1340c000e07405200407810706014003000491500c200d60307140000e00029100c0c80c200008034a0b1400b82d042115100b204100062038040d00707200da05500c1d504044030303140c058500000041e0462900340308440d01c4684c00030752590b850200a0620134203c502101000940700d46200c0d00011106090150003041c1c861007045d001d000600c0700007003035103000f60198015036100009018810710045411000c0d80d08500c0c02c1e5807204907500b094111a18540d220806040940050109829840c2c0040d4460061801103800d10072401041c003506a400c40c04080f22504828014030003112089280d000c2d581c00380d0005418004070015410240e40301e03100c003024505e40017412814464110710b4441 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 279419046 1250 279417796 279417833
    0xd020f03180f0a020d02090c0723012307030b0103020405040f0603050123070c02150d0b03070b030c04090e0c0a180609050709030803100f0f0501080f010f061d030307060504 76
    0x3d101c01507808201c00d4484204001e00c108001c00c000b07640c4080e04010f941c07003150440300b80d010141ca00500b89005034541c9170038000c0d55003040103000045854441006840b00701c0c518040260380d42d003c08a008050440181e4101340c0c08110004041c2d8840c083c07103801502d04480001d220b8518a02a8210307009401c411100c450005200702060b034180101582c88541c500f0909002912840007030444882e183d00c0c41100040031809605500b01076020308100386040c0e08845240c0d85070920780d606400111480c3c200302d00100814810981c40c3d8101139110000c640c1251241c000e081e0014400d111260000544421410309420004141e8040d8800408c0824020442d03402c00c16030003001010030380800f800110001012039407450311502420002c10b0205400e0280d00d8656110040760320b041e00c01c1d58002203003903000c501d4240c00502128100e030041c10340362a40600e80402691003071a22403513040043d440000d003401381d8405200900d092403103103000103003529040c40e004250050001350385 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 279420296 1250 279419046 279419053
    0x50d0b0a0b09010f180b09100206090309120705040603050607140705060a0207020d021906020d170105120a0501110702040c02190803090a0204140402280b0d020f03180f 74
    0x10059556981c0855400d101d0a2030502100c401600d0265951410407122211000616400060010a10001d0708a2400c229510585810582d00c1242c2c0e5039405da420506035081088070030300324940340c480320700b25808001c141d41d00166288006002c8901c0384c1d205075070715000710081000060b0700001c8015084030320000b0398100b1310140c0756140d840328010604080d19900103071000c01d65459400c8880760607802046503054007040014010182030074401c0401511810342c0a1078030341d00035600010081e050605040282e07103070a081050009000c0d00c804038034000d000342c19000c036900780034503034071141c810b1225507030340c00103205020803a072080c440d51003150440c00f601d4a40030b104010710f90a03550041812501c3e52900c4450300d013040d0b00014000c1d03110f0303c2d21040c9c58940e040140030a2099001b102d640181d081c400300c14a21a298041140288405483d014000a080d210143c601640e6211005091180b038400c1d41c10168802c2da0000f00c0391180803480c03c1410340400a0452200c2e148e400b8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 279421546 1250 279420296 279420299
    0x9090b1503150103030f1e030c0206010b18041a06070c030201080105060f0306040c0e19180e120c0304031202031b01020f0a03021612090e0709060507020105031f06050d0b0a 76
    0x12000310401800000e0070456046007003281c4070702c51f0000005816511801c514401807000026004100d5540441c0140c0240c80000482d80414002d941e40c3c0d1600000f0025060145410071004100c5100c0301c148039505642c100c40b0355112a0060100070344680410840141180005816a0016400f551240000704042d1619138102000c0c0c07034002c002034a000c00c1610070800181e5407507038004542034105070a104181002006d5100340811507040080c44000300c0c80700300300300b13007514500305004030140d000340d401184c03020400d8000e00000844809503030a02c0e07221360b1907081001c040b206904c0180d0020810940c2d840c801e11401c03150906100085242459140d01c1c1040743c081c030003510003415808161081101014020201429071010141c1d0506010510241c0120384500442141c01e903040700103050280a0039003401500c1450f1111401c110055004407440d5000410024510744c030050b080130302c0d8246107003040103841300da217445403102c00341e040c200211040084a42c0c81507003909070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 279422796 1250 279421546 279421573
    0x13080d030b03061006030911040f061a040503190807061a030105060a03050c010c060e0105070c120216030f240e1506060403020108040503120a0204030b070e0f091009090b1503 77
    0x11800889801b4203004c0381000003418000840103400507459005403c22070040013003081c40c0d2100302a2201c00c11000030307501d1850200d0b40c160285003c0e007905603006020980744c20034101103908030a482500e10301e203401d80030760b030300401e8a003070022410042042084140c500d05d000c1c01181d920400c1500c40804462031a2070b8030380da600d142c02182d8113010750012100c1c02d121150304043c030700c0903640d8028413241c00d0482e001000c0480c1a8400e030303000d6080000c0e05141d01c0c40420018014404e89035000c0e240303400c5484990070355002c8a0300304d501c0d10800d0340100b154400d140c00004111000400000c02070034042110b41070402100e01c4880c0b40c0015820014182c1e103030810f61742900e8080c030300400300e40c0d80c0b4a0700c1c51442c81030220703039092004044104061524240c009000340c1e849407901441540314010180c1c0d10035640c01d24203034001300081c6004036070300784075900650041028000008050703543c80e464080b118903c80940320b03007401904000b000c82c060064606500d105074014a80c0009800 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 279424046 1250 279422796 279422821
    0x103090f02151308060603060c0c0c01030b010c02031015080c0a03140c09010803031006030501060519140f0304050d05090105030703020a03090b0718080c03100504020613080d030b0306 81
    0x5030300920031010100c50004009558064903c60400480d649112540710702c0c00e01e503a6042180c8044c842c0c49a0780000790658008000e42d000c0d5240d800c001c240750b049140c015400360810405a03810800e1641d1140056a001c001001440d82c03078040000e061244c142118031020403640001d9225440142203d4240d140d1202400803244c1017820215401030101c25181002c650390300c1c03603a002d6084800810300b243c01000542c00b0301c03d01080c1040c1c480c0d0f1180150241e031800d2003800d000c00c0c028084205d120328030031501c10001206151020710b4903800d80e0b01c0d140c6900712558208400d40c001c0208002c0001c1001014181c00d020b0418506010301c00000030250f1100910310000c050300880c840700140c0c0a80c12000b0120f0b0b00401620302072420503c024850f480c1c0c140c1030242c581665100150011010447c610810000f070050000c0300100341a401c054180603000320703081203040000080d001700810001c409841140e028003c87c2c0c010160003802e81e50703030340741441c8260003080c2840708031840c0a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 279425296 1250 279424046 279424073
    0xc0405060901180f08030c010506030a0b0f0601020a1401020a0e090103081b1216030201140c16030207090626071202040b030c04140109200318070801060603020414010309 75
    0x2480d01aa20110750380076004000030551103001101d40130400070401040100203020b00d4072500d4020841960796408051351590342100141440c418480400c0040380100012584210306004441a4135a82d0f514050044404c0d404100d1170f940c003081c81598981c0c0000ca03d800e02d002250103620550441d214032000c0d104010310f14030b5086407404400c2c54410248644120200203d06090705c402c00c01d030f0503491340302d070041d021401540380104020690200c1c40342d0902665403044002c2c01c1080c1142d1701c0300b911660200984c10343c070940d41e002030103003480d001e002e025241c1e240c101007801d03805c242d203942c2500c0d1251030100290401070084c004201400039445090f82c0444020a100e008100401d007080c8044003016001800c2181128070100c0d40d00015040750b481204c10050211104101003d043c420a1b6101c100c040420124081101c042c138510b6200301c02105490350669514802421181c096200201094000c181044001e202c03202e500800304007800c061104012584e143d0903140c482 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 279426546 1250 279425296 279425299
    0x30b1b03270f0609010203010303030b0d03021b120f1615020a15020c010207030305060a0605070b0606130e040c0e010501050a050a0f03151e1e030b06010c06020a0509090c04050609 79
    0x40c0d06045860120800020688140321401e50703d260402c2c40d00c1d0f901035402400164042814402d0076419418030004032040c09806601620583c9010b0306580345801d01000800c0d409066290364400388d81d02804408090b400000050000b1001e00726054000c1045510050050242420003140c003078000c10411005944200060310025851010100030301516048500035840440e14108041c0c040c3d00289c080c142c1142d66802c02651000f045490344200440103142c0c81450000c80c03114144035015150b50740c415800c1d080c0240e1610900ea0304048111401d03101c6002800e01002100c0c41c00749800d0250800386131852601086140161161084052407400c001e16a10502c04191007540116010070401c000d101c01980d40d507050100e1000343c2c46181d9408400c0541c002184078042441d02c451801d41c030b03181402c1c40e00c0c580701d040c1482801001d45042c041d840404900144003840180031061940e00c072142c81c1d41b00c0c030082c020100c5c4000c1285440c004104002d200f180d17185000e40c0e030320100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 279427796 1250 279426546 279426601
    0x2109010b0307032103021201080a20010c11040905030309160f140910050402030901020913020304030c0b0403090308030708070f09081c090f081f0203010e0a020d1401030b1b03 77
    0x4d0380048009209010902894092100011586800110310300d02042d0282c400040d110600740ca02c3c000c80010020214049111140c1c4c00700016240800392406600042000946040f183c9541e810f5a10441d00310069401c00944001d16220100da100082c0007243d60036151a810010b0b0a00c42802c1014002e12582a2100041003411021002d0001d40b070094015034507400c0166940e8041e4111000061103510301150005d5a25000d10079030703100301e81582d1000840006a00c1e60543c00ea009801642004802003000c004182c2850056001d9106641d83c00d250303250100c801003400090364011410410800c90402c10407800088101100c009513003485065401030b8001d032001400c40d44114680e05010900090840c4c0100320150420100489001320307410390ba80f900d0407880b00740912401400382002284900c1d0443d405800d80c010511320008500c1c454841c81504903000f41d01c112400c99034071041182c0110b41117020a1100c1500d0000d42c11810003e02c103c954403a08175211000300c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 279429046 1250 279427796 279427853
    0xa1a04050f040b15031b0c0c0114040e1317070203100c020124090b0d0f030305070311071b0b130e430c02010f142109010b030703 57
    0x1d50b00c2d800b015400c3e400406400d2480f260740040b190980040715850261030300071000a6011440c0b0046030480c4400f60701a1100c0d0f019100156010580c8000b0780c107030790005003c04901007000c10310302c0740100b014220300c4c06903182525105042d0901842e0030f800300c440601200005031800507001d03448e28030b000701c003240c1403007080412070040c968007506141501c1c540c0050720002000c10000301c00d4504200b41408070003020401e00075608500f02006042c80450b100100210303100b64000342d0003101c3c6245c081951720200304101220303000a0001e945140d10013044410b001c200480c0a40101892201c0c90306068105040356143e0000344520184001040000381c00d4644d02c0c07c2c80a94101036035101d5034cc41e01d064074442c01406e0700c402c818812040f0802960421070290880d807268550503074942c0c012080c400401c1f91201e01c0581c0e031008940c800c0c08144055200b050050b1800d00c00e4068024103854039582d900d003500c40200300c00d806030b00840000d00206007082440b102411910b056185100c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 279430296 1250 279429046 279429049
    0xc050d0e0115060e0307080d08070507060b0406260105131e05031603020c010509130e010b130b0406050a15210c030e100c0906030b0303091e0a1a04050f 67
    0x62682c107441040c0124401c001050b000c0c0c101e501c685031210240c0407210036903120050b055a4024003061b0f800032406040004009030701c030750003d25406100d0304000c0b8011910801003800e680261b0010640c80700c9210400ea01d184100307469034017000c2000000c0c4000e0410400020b0300c0f903c03500780900300d020401661740d80840c4c41c018a902d202e9000c8100d036a22540c00c4c103401e9020382c4c920382c210010301600c078041c801d540c401c405072801c44800402062044194010b9070b002080c04001218095403501c10540d11540c074840006013208070940049030640d060000c100c12200075400051182d40e03401420301c40d2a01e11529440d00391405d0900b240c0321250075902d40304102601c0c0c440840e95042034113907610280e050b084003540340494400c40e80d44895102c4140240c40f51098981d00140d04218100071031071194001c40b007509406815079140941420100d0030ba100309504101e0315540d0340001d05a41e09201049800800c0243ca6007041c90403a5110701440d84654800c80340705036170001c1614402d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 279431546 1250 279430296 279430301
    0xf110307020603070804020a06090b030c0a1707020d0f09030c0306050709090e030d05011d04060b060d09050d0206100f03200319021201061a0708040e0906040203100c050d0e01 77
    0x31160000c02c101d440b85030451008200740d0040f1801c038040c90f0001000180b450245140d102038070011000c213404e540e210152810709030402842c10341080b01006900c1c02016000481e076000e0345260340075014401000308060006c581c3d0580e03403030400074413400803c04112030000e81410303250311860218580e06c61810444115101da00040600d61404081c00d074140c800200908003112140310910140e030b6205000500e40d015540c148500b0748502c00040c00140321a80200038444008046070708021090000404403104040f0444040d0b0002c2003014104d60100305403030b484042202004001070500d101061080c09602c002000c1c103c40c281004000703103086400480d02c0c0300c00740464111303600810305070305801300709041a03010b0080b60034040c80c5010107006000954820000c03440000c1807080b40308110791320801055800070424440030a5030450407a40c5030084c4151801000316041600405040c8280800c070460f880d07190001d246007003504202070b00c1c0d4204141000150600c006990b9502 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 279432796 1250 279431546 279431557
    0x3071203021204080706030f05220302010204090c27060507060b010203090d0b0a0c090f050d1109010602060f0622050a06050a0909170c03040b160203160e070e010f1103 74
    0xa500c0400f15000c500c03140e00081c990111000c50340c0170300c0840e40700a0108200d0b10140c45a0041803103038410512014a0310311040311042c401c1c4001450b241d5680400c20445030220320b1080020b9103210500307034130307400e480010001840c43d00414054034540f80001e08903118143d1700034260b9491f03c100d6082070380281b040da2400240030740140d800003694a40b1480c1080101c0e44030080a1402d11040c00742d500c1044203105480719001920300041c14101000005074000d001100d00424540005019032901c0c00110300a01082c0c0050445080240940012540c010145805505005200300a9609007030341100c200c04408000030b5603440d00b41100f4003501c05034010f2900401410400198a0580d51101e039849009060308042074200400011031881082104006540240818041c0010707101c0284541c0304400a10401da108990100342440c0c001d0101076141c10040c0820401c050841c111107501c8000c030b2420b00e103d071103240f00103884180307840081030800011205500401400300304488 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 279434046 1250 279432796 279432823
    0x606030307121718010e0106051c08130e01050a120302030307030903020a06090b07030c09031110050c0d030218012f0a15060501030c1d0d1e0609021e0307120302 71
    0x40c0318a86141c0d56080704d055100c4803c09503207480780309465004184940b0f815035074010319030b00b458810071003896412302e01e94405868481c2d04000642145803c1000d4400801f4000b80304541d070344c07510307081085414140d030250000504800c2c00340c00007035002c030841e03500015030306000402400c2d500f001c03403a00c25a83c0000b8015071610540c0d43c2400111040313039220301c0c41030743c5c103100e041c460541c1250511118840200700900a06d25108607140c8000708102d2925585081c0d8102210500054078200d02008801e02003a4001480cdc41040c51250616502c0f48003030a04481c403d8142604034059000350b180c03d41c01c0080071280c440741c0c080511030f2401440c0c000025165149000e0103d400602c034901c9803501180c41e125009810501810324103040c5030b041e10728003000c4400350060020104e0104005c880c0801504000f0014500d000d0550b040349001c2d060003c0c010303405205101d01e040d9500c2e20781104140074500171804d40c1d80007624000380c41044044040c0000a0320702a45061442d10819 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 279435296 1250 279434046 279434087
    0x403020913060f090203120c12091f0504090b0103061428030308010e0a0905060703110d061d01090e252610050121051002030a0f0608060603030712 65
    0x403403c0d04410b401c9901c00c14022801c0d1500e14015130503190680c82011543c200c1c40e04510030100c1d400d09564090480020301820b090700364043c0d0081707400c1e001c3c241d10b4000b002c64030115003403044a070326110f02e1100300001c3c2004c100782810310000c5100409070400b06481078000400303000701a950f4095540303c01c43c4440c905036070741c2d03200c0c039002d0010322090050005801040f0005030351000316020b684d032540e40000183c2602d840d00320088014080103d06d00c3c0c8a040c082246240034680780c0f1945000300724446120740f80507001044038080000c181d0001c01801d0400490f0010341c040400d01180d0711b50080300480490200b0340d103c40000d0126030000807142d8168400d000e0b012440f8202a0380c2110300c105858001d54080b00802c05c0364001c0c043c010959040c981c0f40d2420451410941126034001c40c01c40d40f2180050700c210099034421199072124a4403002e00c05078040d10340c005c0701d014040e034801510262413340007007a43c90107030500c040e04520450031044610f50260042d0f0410200180c1c40 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 279436546 1250 279435296 279435311
    0x81b0708070f02300f061e2203120c2d11030706060e0901020307210e060901200c06060904141005151c080f0c030d0903030b09010605040302091306 65
    0x1c010001e044c4d4054094580107690a94070300e86408a07403103126031280611101c2d81d645820514030b080c030b0018001940700c0ca20f4560f81c450800301106200c0580d110341e0342d145072200807584001c00d6420850021040c0060a00018030b8800d011407500c152a03480204812803c101000c119075440d104417580c001404005206024000ba0790810f90683d08440520708143d1613202c1e0301c500b00d1008861543c00551110359683e070196200c6c01d561030b00034503010042242414195406c0c109001503407140c60301d0791344504000040040305101071110360602c818034100000100300988400008081c1c500c41c2220100203810000c10304680d0f92120054802c403800712003a00c0801004107825544020070140c462680c0d0030b80c0c07500d400100b48100800c0d00b054108000c0f550345e120340d41c0044039140300042d000c0c0070f002d40428003000504200c140d541c1d0041003944140c10040c0880707051001850080141d6001484002e8000c0c0884044035415148205d00d566400c4c10004203400356940100140d092809 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 279437796 1250 279436546 279436609
    0x6190e0309030a11150f030714130e0406020c1b13060605030c0703110d020303040b0115050702010e0a080111090a060201111602130f050412020c010210090c0503030a081b0708070f02 80
    0x5184a008e17039413511801e00004000141c06030241650082c0312400c00c504c2030103408504011541c01c075208002c05030a1508000d1258100704802c0707174038003069801000303001c1a450800d80d0004e40e030200013800c00106007080d84c020260b220082824600107030014400302014810031808804084c000160b41040304034902c000d4403940305a6041d00e02036030440001c960030320101e0010614400f162251440c00c80c0d5a801551100040791001d0b078480301041c00010324210a01401401c4134007003000e00c0d9112050420801000c1c1c00d90021000c5a24041022800380000c2c0102c3e4010303092103a11119020051002440c1b0501d03040048440d181000c80107111025643c000902851007490503030b00500c03079000d0403039803036851000c1d0500503031119081d4030548000d54401c200503802001d903041b00a448402203890760b8400c144c1100021040e40070004641d800244500b140024031521500c0c080f00d40e1540282c41c0141d81c4042d01a210807400c03581113582e04c141c41c14010190394180c281c048040300 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 279439046 1250 279437796 279437827
    0x30408030c07050312030f0601090305011d1005070917031315030c020c240f0a050307080f091e010e07090b0f04090c0e061206190e0309030a1115 64
    0x216440c1da1480355102c08503040c90f000c0381e600e40098401c40d80900395902c0d90100d40074084080c1070181485411000407000c55401e0144041484618064401c480d0f040303121076141c496203407915986a49000300b0701c6070341e550080900085801c0080103408009040075014158460003003c1044541c1e186000282c060f808000c0c04242001c80d01d082140044000c001d81c0c48402010300705511000030b062180c0440416035403460a040313410016070030500c121306c210f54954800440380010034008410003006640c04029580d100c050940182074904029060380d03034900c00d0301e02c80390340e1071111100000070140c25400105c46030880c00481d000c95540d00780e800b0052400e10355442c05606441300c144098180350140d500042c5d0301022290700e591030309281644c1650082c1c031581d404040525906100c0508000a40c0611010b0701d80c007003c501401c0c5090b04882a0b0521075078950420300c503241443d900800c2c540981074000c1c41c5036840401d1100046c0ca2120303a02200c02140c0c5021030035405c48080350 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 279440296 1250 279439046 279439057
    0x2001050f070503090c060a0216030c0927030302031815010e15010c08090f06030c0c0106050f030a0b0a180b0108070b19030209150d050403301d03040803 67
    0x688040c19214003208484911003120041030991241010321060b0508000400c9980388071b00c1919032442450f50307182c4100d20540e100b40c0e4414183c4406016a18040c031031600c0207860b1485014810480240401120491034005414550b01100182c6a82988214041e850200c00180c8010016440030240c6529081c002c981100e60f0850005081d00080c0d10072211001d416180c0c41034840403951940b140d5804191041e8229901c044034800640380e1001460080724030443c02034859102101d00d03401c6410b2a80800d200350b600240c414140d403404901703000f1745a001409108240e0740c800f4148045d1044401c49055507802c829100240300301042014140c50070001503c4180c0c0d40d4058290280c040e500425030304d00c1000340b42c034022a0080d03004118a480c0038000c0711014200f0008d5441940102d4017040c14241c071101003000301980141e0320003801d8400807001900005900011480c050540c40c3c00c10744643c1c44001500600b03a58540d100708500715000c9a0303445488041c49500d03034109 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 279441546 1250 279440296 279440311
    0x7140f120313020d0203010f020a021b0405060f0d21050a1206080c0d11041a010809010507140703050912070e0c0301030f0312020d0c050406020d11150601200105 71
    0x4064000d005a405201200c0c02442e288490900281440d001c103d4003105610341264190368804c501090104540090040b01c2c2c0550041c04040360b06000c0381c1a440c0344015020301c07c910b4001000050b640c1c80741140030a82041d03980580142d01c5181c01c3c070350045a00c19045003081c1191101443e02d40c42801401070904503950ba06d445608103203210141c4006000b132103503a070440d00702c0c540582072201000190b140240c0c00c0c82c0b241021000814112010394402a52800c0d190b2407603101c0796005940e0a4218198074000c019601e40306c5c2c1d000300308846543d400c510003a00081c5540c11b06100304280c4400c0000107100c20725003110404501e588518030f105002810100c0c13800105652401d4060381c0c100da4001c1c0c0c5c119143e8050340c0e812941703210b802c0789106d5825824460111880c20743d106071500845507031203540d034a50415502034644010f080e080c400704142101c070b00d002280045542c000d0b0003807080128066440c3c110041e20020411020f070900c4444543d07644030281c01c15042207000704807 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 279442796 1250 279441546 279441553
    0xb12010b010e09101e030611030601260408090102070e0a0e06090303040f0609021519030518070b090109031505040b13050a020d050705030703080903010b2e0507140f 73
    0x103442401041e20f4115002081103896840401c04408a001c0c000c80022188041040d203075129919281140c00d4074024000994012040040781c1d6002000010512024448000c02440c46020882402002040104208004030365160310340d000300f00781c02c041e0060354220130840c81c04811480040c0f0309111681010300c02e00e0045002003c001c03049078000c07504144070111751451501c131070019043e890402c0343c102c03074015003e0441800110243c440d01d1802d120150300b1407500d030402021707280045c1a0a520204250140070207240009045084980c0b036004991a90380311030040e50812266800508405620503200310581880d5000030701c164130802c1106025154841010747c22900e00f50300030701e80d5003e603602e02c0143c81c0c11074200b4003a610075402c903440790ba100c102084c10000c0e0b5074401c581c481c00c040780c2000185000c0c002da0310201d1080d1200325000c0102100c41200701c041500644840d0741c601a41041c15110344100c0701056084500004c260401ca801c441d030b26010101440e02601 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 279444046 1250 279442796 279442817
    0x6090f1a1507060e0c0409030c0605090118020909190305070c0f0b030c0304060608030a020703050c06090303030426212a0a02030d1407091508130203010b12010b01 72
    0x14000500041d000c141034003103401e20700d00e0796481001381858000000f503803041e10b401060651b154042c641d820380c0b090703940e41c80c0480c96240130401d848024015003e01d1b4100b81c0304a0100c64165003003840b091301103902d15107948070030860310b081040f80782c001c025040e80c0d640c015046c103800000420782544101c9001e008990341d500e40054034851405014000101040401c1d4041d03242c001558109000700c0e800241241d0351805103180d6031148d5015400b60b04117890400070310000f440107104a03801541d035589000d80d0540040d4880c0300060000380006010301404d0a042d24802c107418a42030486d104554450000c8401996480301c01e528444940c8d0200005900b0f410240c561001403410b0404d400c1941c00c100b40003100d540245040e4000c610040c80065071800302030003200c0d007500e580d40044005080c0945d000309060707129007021941c882e20101c07040301c413940a411280d0201c041500d00789150600d200007805400451900c95021148181c007200f00c0f0019805215100000d1700e8254109 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 279445296 1250 279444046 279444049
    0x12080f07050a1b020301021306030f061d13140d0c1e0c03020402030705070f0c06022a0420031e1509150406180501141f1206090f1a 58
    0x3481003882010000712140e07142c422498042c52070f4882c2074402000503045c0707d0410a0340e48401441d81c0902d0010ba112000314030003080e58401da001034000c125140d96400c000c40d604080620380609840f8401d00d4003442401400320741e0303510310010030410042d1407406000c0c040041070282001c00582c0c0091a01010a10458403002101c130650791000c074810645140d5001c0200940004200c0000e1040c10042d01000a080c6000505690711482203800c80c0350406400a181c0b9110460942c0205181280700d0000204140c5141c681c1500b200e0100e071a904c1540c1030704800810694045240401000b0f00280010b10081034051a501c0311a0045503603411080d50440258000040e4010058038003046400e04145403590080c80c01a00101c0c045996258041122083d508120100b641d9040103105846011130306950450080380e11107041d41c1c0c004000c4081c110b0715107107082480107150000204116580110004102e00c020400c20340404c4c0d01010007504010040081c00f000c000944c2000303 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 279446546 1250 279445296 279445307
    0xe0618031e0d0c0209040b04051e0703110a06140d060506120912131a0c0703050f060a060506120901090c080c1c0b06010f030608060c0702190e0a0b0d12080f07 70
    0x3c2c0c5400500e031250035140c6481d418400000a070050b46c660040ca02c503807560079440000180100c01c144000c0817010f28605106110100c1c1c0c0180310703c54001c40d01c2c10014a135100040f00501c03d03100d00307480c2d512848031410f6001048103522a0f0340102c804a07440000705d4507101c08506c20404042030382c0e00c00a250842011070b03c81c901600c6030706482000148042c0403030341d8026841c903052800c2c1a1500d40406c030030b03503c0c0000c80d60040360650b2100c030745445403d800340040e540120010605200c0c803402c02000840c180548107140d03c007000c560300081e810b14000d4200c1144607401c01200e01d0415102d980068a541c0d0014840340989110712603008030b007451400410495802032800750440d121100112750340130a00450500301a211000400c200d90b0500c02d6600484511044035540c3d00c5610511020046015001102e6aa249410000c50a644943c1e540c40307140b1503000aa074000e090b00003082500c00c002c0140a84030030305500c400503a0042c0100c1e00132800020031450581e1000f404840 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 279447796 1250 279446546 279446567
    0xc0304082b0f0203030a0b0a081203071d0f120c0405090c1206090a0b06030a06050c0a030507031e05070c140703021c03170c2110060309030e0618031e0d 67
    0x44e4402c00024a5142c00c5038022403c01c00010000c66106568090092608070400c00d0061416800000e000d4100e4000c5000780c25491b10740c4102004e4404e000004130b1201c0d061a1084c0140006012569607a00c04d00015000c0c4100400402241c02c1c8440e40d2591541780012180c01035080030510b4595030700005e0690301c5844420018003250100703660302c400459014201c0ca030144118030325400040c01a00625100305030b690622a121602e001d0020199038004c0e100c401032500c1c08600c4d40c054000580c442e1015143d00c100440e090301d54034001c5400c600c42c1c0c54040d00f82c042000303008505a4010a0600c21640215601c025a19011081d080391450140b00200441e00c80c0300d110a600804244075a03205503001c24084c100007856444240020480507a142081c1b07140e400c20100c4105081c1940190845107400c105012469a01426900000d00f429100d080080350b40007003881c0c00d0240c1ca0902c3c402034180c800b1841882184c8801ca0749800c0d2181d00c502481500d0040284505645130 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 279449046 1250 279447796 279447827
    0x7020c0604050f01110a061b0503130303050c16050304091103010f03031d040e0604150c120f0f06030804240504170c0a06020a0605010b040b0f0c0304082b 68
    0x51074149498104107118410042141c1404080c0c480061101010b01a19540500a100204440004c00c02c00304d4554040680b05090242c00e005020b940c3c000142300340c6046600d41000501074940c5030021340780e070080104400310940c851504404002011010f0000c6400189007880300050440300103c16010034002d070203c00359800c60030400303c1d104021041e40f050a80202c421014040700208080c1c40550700d0903d115404802800f0402002c800e164a0b01c1c1c2c1081c0003000707508000000202010011454401c0450722540c1c102c00da12a01d0340544800401e458017040307034565a1600030503c0c2c105114081072175062103a00020094200d408080301800d0780d507810310f01801d117072080080c20540b40c80c0b80e8441c400d0014940042e1512003541003d001650014140644070b849c0c500180d0310160045551100103101c108251039010f4250703441e44032141e0f400c40e15030204010492441c02a640108040d1250640240b411803c410214075181100c075240c110b091249072094442c2001c00080c0c0e07 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 279450296 1250 279449046 279449059
    0x10503010b01140a030b040f0b2106151203030403090509090c01090509070c1407051504081c0c1e030f03020a08010303050c0a08030f07020715050901051308011a0907020c 75
    0x40c11034403005802130410540e5400c0000700020280f003c00c00b2290f85ea04c04050803652102246c0040c0f4100500e2140c2e040c0420410001514a0381500c0c0c0319078024040b00c0102c1c4011510740c0d11036070b461443d2413041008a041b645c03280f17403604004010081c03d2050500464082c004625800008558001c0a400684540d042240340c1811f10600394002081c1404100f03248980100007610741d5444038400701c42c100203190300e5040500304400300c511001c2e41d000d907181c100810040c403080800c41c4400e18410350300180140c000d1910540d00301c4c4031070a00602246d051000c54900401d102d01400300d040c020381d00c00810001d410000e50403442800d0f8640c000c149000010400280f2620080600341010420380c0c0340c00c80300b079880c00d101e40c109941e040020351a04c0c0c1001342031a41000a02d00408800302c604020f11000032014100e4821490030700c1c1002030000f403640480400410340001000050002c202d40d00c000b2000d011140c102d00360052061100700003080515100080d8a02580e9004102 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 279451546 1250 279450296 279450317
    0x9050105040326071e021905030c10020a150501031b0e061003020c01020f12060603190504050132011e0618030210120b10270b0d0c0305010503010b01 66
    0x2807001840510203403103030490f0810582001070540c600f161100a9100d006070080340643c41000000799045560b0f8140f400010401c0106d0382c3d0000750f9080c030210075a07005070034213240c150407801c10000c02405004140300c03403098200072071103030300a5049034000d040128040c09080c04049001802d80f1640a203465600041609840c00302802ca09100380c40c00c0040c501304e913000c032150a98011030312000c6d902d980030840420920894010a030301507402c480703462544c6072500d800001220070b0402c041c0707160781e070700001020002c00750712030022600c18410b1000410140008151002030400515a140020500010b100c030b51007001e1880d8001c05001008410341070001c2200c03154010070b0a56812588400e0000c0561550f8203103805005803680c5030031590f1030030b41c0c1e8881500c03010744909000e80020440c0124856120158224150308000a002a007603815100200d00c00e02d5009075034162000100c0c4445c3c041d040e13000c201c1042e80d58800f03004681c6c0e01e200709401c07a40c01c9092540810706200e1b5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 279452796 1250 279451546 279451583
    0x90105030105010f1707031a0a1a03070315091a0901051e0a150f2012031f0b090a140a090c11030301150e03160504020f090405040503030403090501050403 68
    0x461345202e00c035842d104440301881015100110030940c3c105000c17955480d801c1c080e00d5410050302d5840d08040d10801d0719030340390503055241504480c07480c44d6200340101c0407641c02c91094000c846252007211400c014542c40307047c2103000b0315041c5a44000c0c2001c801d013810360b03401c0091407503040f9100140a00a2000100030201210340ca282013036610000c80540458000302914500314044510b51702c85c800f5001e002400703001984c41030300520815a010b000045080b42c0060b42c003d070150701c00825501c940345e043c01080c541580d400c40349002107246202083c0c05000714090140034400f21007002c0815691102d09031041401d840141c2c100c80c0342d10b402d0210f507055400900b5040034518000d00503002008149003144c000b82c005001001000e802404a80c0e84586880307000030081f03024028810340e84c0d2900d00d44a01604ca1240295000715003054100c031102c06840d2a080c0c0a00280414039044c074160341c90340d000301c4040f4041240080d02241c3c03940f06405490640c0d500c1051401700c0c140866 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 279454046 1250 279452796 279452807
    0x807050a060c151a0307030b06090708011a0f0c030d0504170c15060d140a030314010e060f03011506180605070803040609020a050a03150506060324030109240507030209010503010501 80
    0x3901302111003514041849480c20400c100041d07010300040851130400320308020012002510380707020001da01c80140009004036150139482d03404484219030303400d10b0341c041082c3c500501b42c040c0450700010a1001c450569508468403e038440d460305490000c01a011201e180240790440c002507000031809000c0881240c500e5800800c000d05500000310f00c0e558140001102444802864100f13080e80020141c040c0103103034002c0721070306916001c0e40c10059100048100207051a01c11007213483d8910603900c007988021b01030a200e04101007044d84490001d44502c1c1c4010100217002d003010b1000860520450a6418036030388540940d01d562126114240603028103207050380e124596000c00161359484450b86001184140d803103880300b110b00684c4ca0116580100b003e40074100420400c8842c80e07124883c00f00c405845500485600200c1d40841d0040260000c01000e03a000500d5125880c0540745001341e14001e411310500c2542e03101c1404406900480100c40d0126600b440184810341c00784 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 279455296 1250 279454046 279454061
    0x111010e0d031a03030309030a0e0108010518060103060b131d010621020c07150f020109030e040c02010f0c030212010906030804031103190c050a0e13060b0114040807050a060c15 78
    0x10f882d03d0188009200080c1140e1090300d121106074000076100314015040100d2500c144000d00300b510083d03145c240031511240034403012440c0c200000300042c600b6030080c1d0041c006819101003454842084113407010300c030100ca002d99441000440401100c41180544282c107941e595500c1c00c84288580d52140c0003881801310301c90010b40c091050300f16204080081000400c0d0554500d440741030303520b00149c060602da001160441e41040c8110f0f003c60340200140c10380030700944000031000b0314504103d004013151901c1d9007043d42080e201500c00e0b68190060044000100f450000d82c1e40c0e5400f00c1412100c5511009001d20400d200c2000407814410100d64140400740a486040c2c1c1e000f82c0902110624950443d403441c441d080901c1030741020a07590003c0c00c0c0440c0d1031a000c0c01c20103065508442c010a00801c100e8131070841d031201d6445007803403080e04540c19102d10f4456440c1d241945d00e0b100c05000b1540038540281f40064264403440410700340f01d81141540d1820b103a03e04240d000f6102c035 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 279456546 1250 279455296 279455321
    0x70503040e10050429060a020703171b060708011401031404031d01091d09160303020d021b011d010306051804050c0d0503030a050723090111010e0d03 66
    0x14003000a0105018070601e00c01d400d00d4410b0061a41000200011107075020000c1d0f8210300c19680004108030211056554414220740450300c0d000e41d000200d1030102c0b10f40004281c0b0380c040500380c00c40d1005501030202e40c540803500d4483d00c1c070310092440d6604800c4444400091007240104002c50160a00500742c13030040c50041000802484610f0258030169401c90025000c0e0700035855090221050600c000d00902e0050886032030015074144182400003211058041c4034080703108480100702d2800564200301702924003507684e050207505c6010000c0b0903005070190030031464500303030b8400d010f8907010f805840312038440d120307446011980c0468400302d5060543d1a040800e490785c0c0c0c04000904825944282d441c50300c0c2c1481c005003411000e100050186503030001407000183c010041d2540310345010350004150741c078483c04664403809607525112800c00105040c1031a0b000800504164001380c0326200700c109405505401c1300e20b040d45007246d5400140400c100c0703510903001421b40d40348 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 279457796 1250 279456546 279456553
    0x60414010e0402040c050a09140a030f150f0504031202131a09010908070f031e0b1003061b0504060e030c06190f0305010806010306091a01091d1209060705 68
    0x4416098188420081e040420100300c003a003040300718901802481000c00d41880c10030300384002c20401410000d05405600d03403845e5441e280c1d580684841440f00011500070b290282102c500d420320081054683c52290001800c000d40f920054429003e5180500e506554003031814021880420081d089080c004e02c2543c0d20301c80009a020000007400c800302c865040c1540c1d0303460f24030005080a6038590005005030813400d0200005201c001407001120341004601f1022a00c0c03030f03441f46800c0c85040c40100600140c2c0f00f4030040061820011098a10811041001d492484128548075060300101d600240040006001440c0314440080c4070b43c1c005012100c0001d282d000251058004400002c2c20088140d03424205692009200750742614600f42000030f03505015900340c0390207050101404490721900c43c041000b1001040301c84182040200b42032950b1190040d00240455602021a075941c40000007034500c4045100e50244a1356840e90b840d2281c03910078444c207604042001e560900 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 279459046 1250 279457796 279457811
    0x50d0f140f01090c0201050108070510020f0307081806090f120106120f06060f0305030403031404030618050106082803050903030a030c140c300d0e06070e01090b030604 74
    0x1042682024040c101d054401100ca604104501044881440940c011a81031200401c592080440c1079005e491003550b4256042085090070303071600d012054000b4262000160381c1045c00107060250000000400d229503864861104018180c041d03100f003076501011602581c1160314100001e00c041c42c2414001140f10b96980c249100c8509086070141ca19015040d90502004103d11800000c0c1543c052003250303042c01e60702d541e41e0300c1c002e0380002024000c0d698050740d0000b0b0080d041ea4000c5500c164203012038142c240c2008000710110380112a0b41d0f00f80000401e4802c000318542241848010070403001e4005100e4034005e0503c100070a40030301c04c041283c000c10381c030240000e00c0301c1d40c1641c0f8017180003042800d00502c8407401520780441d240c0103214001d50103201140380f040b0000c5500c84100080d80103404826031900510b80403000030b00c0091800003a020b640c015190005400c01031341e2079607548840030b460350000c01a8060024611600520241c01c208018580114016100041c0d81 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 279460296 1250 279459046 279459071
    0x1a0405151e0a1403060601021519061511060c04180b060f0324010216030b0a0b060a02010f06170a14010b0a030b180f0c011b06050a02120f01030201050d0f 68
    0x19401150040a40300e60f00704150034108070031a00100d00313100801c0c40014a43c209210f00501606080c00c00c0b1f0041c0c541e2455529640103940981940e82c491a000c1049080141c441401a08035001c1c0d40a40e40009842c508230809850880c0c0030548104480d209900c610001015003840103503008806002d1841485c440388065441406074a4214031101651001c0455050703a89508604540c084140e9003003080003803c07500200c07588001a030380305484003201c44024108450400e40c1081000ca100000c0550540100f025901d950004100150311100c8000c401c0b071303a50240e01025407208045400140110a1008070038144800009100c100c0704001410101242d10944000385c91070203014040c401d14007081901940080101000001070b0011600c0d030424000d00360600081c0c0003d0b0f03200c404414103403900d159208000700400d107002e00d1a2030094001e1003c580c902c6080b903001424071600000020b068a805031191810709050701c1d000d402a00d49140e10a008503244e60b19207a0b103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 279461546 1250 279460296 279460309
    0xf0b100f050c010614180c0a0309030c02030d0306060909110403170403080711090601020a150c12050a020d18030212031806070c0203011503021c03050403080d1a0405151e 75
    0x140400c2c0c817840c1c2502066608000c80030786d01880c00519803c14200340300e00840124111103080d50241404203003100c3c54201034032000424000a9007600526003a0360041d541a842001039440a84034150703441d490302c6209084a0440001c09107540e002c00040c03010803030400f1071212010404541518050700c5c2d0340e07171003002c0d00405011600d07960400891101444d0008900358056020301c002e0186086988030401e03011040600300c02e00d1555001049041d42c810868004a003c139580b041c809414006034580080d405504440405440c1c081072000700d400148501754501d4142e802030952900307000100c003c0d80d00240c0000000801c1d200780c1000e0b030105210242c442c00301621041d282505a0042c0340c00d44940c0245e4600340f0b0308005060005a4449185042650070b80100ca03072010b009240c10384052090303400203010000042403070401c4061030341041000d44802004403c4d141708100500050720b0061720414100905407004220f181030032603e206100c40d4803c8002c00c9500701c64080f500 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 279462796 1250 279461546 279461549
    0x3021f1418070f0b090a0e0f0a050a0b19171204170a060c020d02060a050c0d02070215030f04030f030c08060f01030b09070c0303050c03040f02010c08120f0103060f0b100f050c0106 79
    0x600c400c0c017060700324107440c5c103125440091200c182160001d20781031071403c40940c4020681c41030b040c0e5032170106240304000d03842101005409000c500402c03801311078407c040e00943c1f01d41212085a2601411824400300790300b024400c04801090803d810414964000d1003094441095803060010307a00216031280142040380d100d030380103040c03121031541c0e0082c01c008005052004490800302840b64107001501140c40d07140b01c3c16001a2103100343d20004d05a8290103100f020100030100c2805804880141c210340242c1c460f4072600340c00c0d0b4108505034142c4515a0180011074400c000103152400c0100304c01701b49020524000602400d19070016404490940300709002910a02c1c0203005c0503003610900703400c2182e5680150a40c035003a84c1700041d640c2407210090400c92803144040c00c0064800070364003003040d00082c0110915105c8031f001d8804100340710640d0b4683c00c1800d0f240340043e203446140c180440141030040d4a00191409444400b546201d960411104003d24a200d41c400c1c0304060 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 279464046 1250 279462796 279462809
    0x21030c020a2315040501140d0516020d21050c07020d0b0714090d0204020a05040e0103030c0201200c0907020f120702040b010801120609080c0a03021f1418070f 70
    0xc0001e000d00d46042c2c5140a42810500521806005400d52203100d019a400c849003482e002c088840c40c205440f03014040e01804480c8281010144042e112101d4400f0310024610750132a0403200350701204460000f40d01c10155215401c5402c281c08500542e0000ba40c041000c1c0300d041d25017902030b40450181e03803c0c4c20007603030010200000c2c018480c2e80440781c115801254049141882429000610032a242e448002d118950004103000841e00500c141ca00900303c0c1c003e030724038039a0b403801d000d456800000320032030000344900c854184100003070070b0000b6144403802c020445980300c0c030184009401c000c0c0144047d4030412603881c050800400c20007416041103501a80c41d4071700c1c0c3c4144020781d98440c141078103025401d070060000502c0840c0c0c254425402c003002081c0a510b0b0b05020141d40b281860075030701c0c0d00504030100140f58000951006584803451641c040c001c00031900f0085a42000c40040c1e07200c0004049070780d8650740d02c0420f2000b002841a5200580c1d00c100031440c80c0c1c410303488803 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 279465296 1250 279464046 279464069
    0x30e09040317060f090c09030f070f050f0604150804030509060705160801020c030a08040303090c060305150303090303120a15060c050d02060f070309060f0519110421030c020a 77
    0x510001d461610307036401280584139442d00340a5040000c9004600805540c1460307400720320448141d030208011751118600006403010385444042a100050041c02541d0281c01c4200b07400b0a0b50810328211000ca600c904602c1d00038254030b2604541c2008060300550801c401446540602d42d2004024500302c0d104074000c098041d155400745c80b8000840d40f1041c11a48144242030b50f8a4000c4110307000041c044c41d01074610350311854142e009080104025120040c0810040b8000b60141d2280d8018419440d00c4090a10094201076a03480352652454043d0000d100c0103420001c0c00d4241e41d0007640260010440c006549941005d0b051240d0005000442c22066441481300a002b00c01d1500344a1005c0c0000d458203181c1d400d650040549208101503480700c126080c03041c00c3c2d00c44803d440d0000f00500c0a030810b1034100c07100696011031040c945242004c40c4104030300401c1210102c075021004448025034020503101da000d0340c024150140081c80640600603940c01401902078111903024 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 279466546 1250 279465296 279465317
    0xe041a03060a0b030303010e04140102030c18120712020f060a0c29010b220f1d090a0f050313031203050105030109031e090f09020703080601052104030e090403 70
    0x8141c40c0c1000a004482c1840c0b4101d03680b04561004001c69054840f80c1070304e602591540d1400304c20703401200301a21065480807040c03004000c2403800070b00b03288242003000000c00000f00d040248200000b40c001e2403681c0000d2081107002d50090300a20414002460180c03041d0821011524a501040020001406c04501001000081010348a602282a511000c0c881d140c2c6940c102072003041c082d01e491960b022401c01101c52555640918104840221414403640c400040c01c440215004003100300d010140c00c155070840d01c0c07520a10038440c00f001445141a192502004140184020341b0709020802140484000903c82f80e0019841060655400007400c64000e04407201a0400d61203a410228050301280c5d109100a0344002e400340340000b04010301c1400c1e01c502010381d00038254421021400283c1f403500340e0182404034000c0d225280b06076200300044505110b00d03d0f04001081c11440100b00c4140c0c10800968824441e040c10b00c0309540e001c1c0024181c103011681200000c1c0c0c40181c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 279467796 1250 279466546 279466549
    0xa060f060e0f0f011a07020402070308160c20031c050d0b0a05030309012a420e1216050706030507020309280e150f0d02010f0e041a 58
    0x201c0c1a4049100c11960126043c01003804804200600c6125801074010880c903020360010f804551155a0050085680c0c9030070b4074002d444c648040b601c0007121481f9205100c811070003440c42e01a20b95002301d41c14280c10254100d6214010035541c1c4981500c62517183c1103890020005c50110806c40d51140b507250429110000c05403465240a0380c081c4203800c008201e2a2000800e552010701d090801c007075441882c0b071024842c9661103410039a0700440d034100c0c006001e1526142c8603c140780764040300001c02961030340040b43c0829641d121900c100700c12160740d42c818580c0425521080301080d600340610380c408207500d0750411445528a40c0205034800100b1a00f004240300905207401e05000e24039020700041d4407030042d02945409000780d0503441c0c100321076420305440c0f01800c0458132450389443d061415011a0200d8014241d802541060780c120700d04100018480c10004140c80c2200b00150300440716503c1200c513040c01e10200c0c40d20911140e03110301811801081b85020120018041c00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 279469046 1250 279467796 279467819
    0x2011d060f13120b04020433031b080a02060f070b070509010e0301060b04090f0b120609071a0304171e130e040f020603101d01050906091015020a060f06 67
    0x5001032078141d0b0380f00742c200024003800c407071300c3c0d000ba0102c07030002d50340003a1103001e182122406010160840c41c00709001d0300052140181041d42c0c014000e00420142441d5481d600c81113600800c01107a100384071800061804c00018083c500005200e1414440981e40d0b6005018003a20300070301081c004140b160640d640040a442c111034224001c1c003000c0d18210310848944981d0003443c0c0940d0300c810302c4100143c4a5041241c2d014000b800002a00c05600348a030f031105810303500d0380103600900c1400104d01400da22035a8100c810000f0182ca99110781e0b445040010b00c03003010319a015801d020f145a00345500c0e80183e5481c15100c01c180d40d801c07020700d032441800302940098440048800a0001080040248412250303054030310704c1e602d80301c0503c0c0c081507091640c0401144030900f00c000100c2510115041d04880040d1b50801c4a030b02d890301000545002202d02c14002584030008000170f070014241c64601010900640d10f5058564455400340c5039804684c00c03160380c56040c00c000889024 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 279470296 1250 279469046 279469049
    0x152a1c0b090637050604030503090405012c10050907181a0304020616020d06020c1902131d1203150105160602030a0605090405010b13020903070302011d060f13 70
    0x1101e60440e840b03100d100001c962003000c1d224803c010320b03401106000036080c0031450040c10008290719100e41ea64034000b079407903121000d070502030740c1481c0002444110446010070382000c80142200205201c84206402c55001400c1e8905803d42a400161503211800d0a500030303034542d9100a0400703d01d0b842c03624844015402400802080415001000b51120589030020b034120f801a40d500043d8003c1300240480c01d202960141c031004024040080d6a801044e8680c540c000784c41d4604410210308152030b0304140042d4001107001d0000c9010b0145601100c100402c00040c4c00035905452401490804900d244203032998002080c41070820025130f5001c3e1141d0709103440c80c07038881030215964561510347d10040000d9004408181340c1c100c990042030150001600b403058524082c02c1484c040d00050b100180202c82c0d0b4100299000d0050080345c09000d000f8004002c841e02d181e0044a540180704041911190028900600342d940c010041a0080c074280800f512565050820004200709 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 279471546 1250 279470296 279470299
    0xb0c010b011803031b06060f0810060e01180f0c03020c0c090946031701060813061b0f020708070503060f060607150e152a1c0b0906 58
    0x2580c10b405045890000a081600e0780751502c03004003610b44101685030255860010b00303050510102082c00900e620840d070442c0c1c014400c070361014010900c910105c0340540a52034500d01e09400603c00c3c011410f80f04052404240d10002d40d02d0b600300030700c0003100c940c0416040025000202950b0300c2000304018803000004540c407006e241070214040ba45d490703414803240e2241403402c0b271030540a0100e039604040d100820214840110880051913040021403004070701140d041200701c4078418030a00c085069591540f14a5496110341c00e036004240100042203506035181c443d03400440044003140500d0103816190400e81390401d20f0041e04100701d0b41c000301350640c0b0a80040002d0b44e07001500340d800ca4074201c020102515100c0200c3c105105100340035100320702c0307400700000c0c43c40e456111202e40360004d410b50b0740d08408040700816044064072020b00b030a0719842c44441a5035003000e4500d100d0844076007d45400341c60400d00c03985461400c0680e01d81943c40328603030501e080c49507207554030400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 279472796 1250 279471546 279471557
    0x1308010606090b0418090c0f060804060606020102030603060103060b04200d0b030a051207030e0d031d04020a0203121003020910031101080c0d0c0e031f0b2421010b0c010b01 76
    0x1005200c0c00c17904c407078022040d2503076207442015090081d1580d05001400c115005111643c0e00d441c009400d005041c0c5044030458540180002c0140c418425a4010030004024040b203901c0c44d00d60300054001c64a0841c3d1040c0d0300d000c0142d41d907905614040d407650147c0b840c0e54451403d41820f50445000801c101e020390809005003000038000300b181e84134901c0041401c0d803920000d060848005850700c10494104d075a8254480606400500b00030200d00b4003400c0300500d001c0607062000364011030300e0140c0564018081e03612012603144140d07500011000d12219020b0743ca40001c3c0002c0d5003550720511480503c0d40031b03c01c4c0b20110020b00251350082c28010081d0526480046081c0706001300c408540c0d64604440702c0c401d1203020760400e890300003400c0300d52003445007148910300350b200c9240a43c0c0c03074a0320442d2001801c1c455100e040d902e5004900740b04006c5940344c0b01501e94401d0004508004412460000c01c0070514083c0d4080d01c1c6004420b074480c00b1114100b070844002500d403134140301 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 279474046 1250 279472796 279472799
    0x6060c0d18151815090603020d1b020604050d0f050a030f0b03060103081902030a0e0f2412060d240216060e0c0d02060d110c0615030607050f0d090201051308010606090b04 75
    0x91708124048100e411b00e14005a0340d48885100c10010071800c0461082009147d2030215a03a0380042c10a00032070040d41615404c050242c0195007041a41e070038036004c9442400301004d25030203540208401004030401140b80f40d441000242800b200742c2089035804004208040400b5003105401942819030005516008a05030041d100101180700740c1d100c0c0f04030002e9481c03951101c0c4880244603100004003030b16040d00d081d102c040c0760010304060144101c0c0800042003881c204140030035075030708003040c000504402c1034456075841c419050450816004c001109840a0303404410f01c0490103140001000ca8240000c1c41c1440039137900b01d0300c10801520b070100540d445208841c0c10580d40c40380003c60510000c0300300d4071805038203404202806200c04000360b11100104d1150204021400c0e9807841e5034018007910640643e03001c12022440901103140f000d62031350700803041030303005050503400c0004c00c0e03000141d000010f0701f0540840e51118020010640c01480d00030150441009860415 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 279475296 1250 279474046 279474089
    0x80c0403020d0201020f0d0e101713051212010311030a0c0504020d1104030501020d06050d0b010608100315060801050601020a050307080f13060201090b06060c0d181518 74
    0x24069408040c0c85a00c5039101d1104580c02040040b41c9500d980050b030750040100d10014119054180104c0d00448007141c08086840c485d4100004207242c02244012076180c02517840d800c0d90700705104440500c2651800725495a82401400c0202c15041036005150704528140c0340307001c40305807910b0082c3d006200c204002801c60480c02d0a9540680e40162141d0340c0b42c050b417016003030101a461000c48005004801e0080640050800028401d81030004959810a10031181282c060140903d00c1c49801800032a02c00c006a60f00000341036503580c0b2454403900c5000d00303110207107042d4071500d80e40c2800b042205800e00400394401024006004c40001617243d4a03200d2240c001c00a150110028109412218a100b61041c400c000070001e00415203550000c0d000302801802075030083c00c100001a0503103450400c48103450b904002401110100703482c19100444024040c40c2403000408010501c1c22002002403071500107a6074200a03601c945516001c2c0d09881d4103d445e5078581089550b004c2c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 279476546 1250 279475296 279475321
    0x204181101030923030706050f010e0a0e070302060307051b2d01060324050c090607030e0f03012d0608030f0c0a0b04030305250206070e010201060305062508 69
    0x11035080c2004100c528141ca03182c0c1e140000d983c42c415410b107448820075080800000a0030090384103c100300000c0d00c1c2c2d850020001c1d00240700d800046115140020311105040c0c1090080700c0418040b15110303622603001840e0b641048031281c001410124604000014140101c2002401c00700903012005d2740708411a4006103060182c0740c061038550740807010000c250300c0f0f1801581c0040e440f1007110742110100c0001000501030828030b90525000c41e81099050007281c142c1103009002d80c1c645401e90350151074107a0002d0b0440e621105141d0050b406031400e015a20300c1900c4e40002c2d072107c8a80d0804064908a0058100801e81c83c2036000d102d0341100008a94400d00c8401d1001e80f204080c90140e0b2505c1002e1200a0022852109101c01c01d601900100e01801424050800c3c00202809420000d1030076241000147d2001c0003007194a4051009500c1000701072002007120340d20fa0700c0d0b040c41c107601238a0548155001c085030300e90f0121000d00b04401000e641c0f40207801d0b07041c400c000103507 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 279477796 1250 279476546 279476573
    0x70e06030a0c0c0b0a0c0f0207050a0905060f0a0b030618061e0a0801060e01060908032b060e040f0210020f07050907030e010e0a02011d0a0e0405030708070f020418 72
    0x203260351401d04141c40c43c05100c080580c1680012041d20a01c0c20703103541800f46c200070101402280c070440608000a00100c1c002c001d40704040c240034003192601800001624015003200e4108604000e420000d85515403440042d1114100696580c00e058052040c030b28010060000c9e200551018003c182ea102210071400c00d042e048015441c5039a040020001d204545c001013442d0328010000030750016540c025070403a090790300d902803090307030320803a8075200c3c8601702100c640c0e00464900d009060070f041907200b145066481c4005003c9456020110750740400382d8060300c808124080d18021403929040b020081d0340640b0107480300a00d550b640c41d594040780d00505110f90301d142c1c00503400603c650b100d081507040c100d0003484048403802d09603890b20f050140507070000c3c0c042e6804030320780c204152400f80103071406400d0401240c82c20307015010f03440f0081c1c07084807240420000700c1e000c9400000035000e032600680d85e06035540c01e14810403044800581c19504032800462448002c288290440d28 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 279479046 1250 279477796 279477811
    0x3051b010519030e15010905100302210c04091b0b0903060408180402070b0403090509190b060c072d030309170c0a0b0406021b03070b160b010603020c06070e0603 71
    0xa0382d1929200054001d490b06403940c40c01481900f4000d511003102180c0d20741240c1c4191700030065501d8560910b40300d41c82600010350403101d04091601e500c502c0d4030b60039040004110544002d00c60f607400103400d546090f8020340e0390584c0c0300520b00310030207007640c03034001018100b08542c40c0103503040200340c0724030006002030a103007008603a0b18880040d90b2240e60a210004101710b51303a0042c3d03c0c10110240095500350005401040c001c1058100380c5c88550007161440001c2c039001c0002d00042c0301501410084070341090042c8118000c1040801ca1100a0043c0b07640340007211000c01c00d00c0414120b91605ea0250b0031041d0410008030350007001007001e440321015003990454240000300c0c0f41c0481800103a800581c4820009960000d02015000340c0c2c0150307081d5052041503404841868007904e0708039502d0340018004009001c1075900030845040700c05600700140c2c10b0340d200c00b20125400d80c031800110b40c0010b40c901c01120b00303014140d4032403204c0c1000003581a000000c03424a000007060310 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 279480296 1250 279479046 279479077
    0x91406070e0d03090e010f14010305040506240d05071502010b060405012d020706030b03011a0f130e010f1d0a060e1e0d090f06050d0c200703051b0105 66
    0x80a01d4132521000c0040c0001000801c01d5581d189040c0e80021018070038101e81d0340081111504640c800c0c061540683d400c44020300d82a180d2983e81074204100c01d14010042e0301481c0c0c10b140c20346a0001012846000b280071b40000d0746070084035454041c00b01031800c11645415885601d0f55a11004d075010341d103085ca0403524190412207005440c034540740001d03e42007a425101040d10b81d001450400b90380280d070301071154007411400e243c26100c09000d080c0500c0c64607003200c400c40c1400e00314000b9a61000300324801c4a107080d01c0ea0401c81c5c0d100b4100c43c01b17994445003c0ca040007490b018141c40c1d2030782c0d0030180e2030a0302160342d4243c4414145000038102911002840b08102041181100f140c1c20030890701c8a040c480000d6030b40c3c1d00340f4407171541c02261031480001844c3d0441c1da20041200c1c43e039180c1c03d1504001104843c001d1501281410030b221207030039080720399a80c0e000c0c083c5990b50100024401941507060181c94610b03981306100020700b81c60f00c0000300ba40d2000a40321450784c042c081 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 279481546 1250 279480296 279480319
    0x100f020d050f04091a01020c270a14040309060824130204051315090207080703080406140702160e060303091306080303040b0a0501060516120306030b010603091406070e 74
    0x15118184036550203840c81171306010880320f01d40610280e190210300309800701c5840d00703541c03818070885d03c400740d0721110621102640344101c412111a4035034484a894000101d183d0608201d54070100305036800d80005503606028400b0b96044017070541c2000082100303125114221408568440b80d40905a0040c0c800300300080c2182c0990301902e01820009001c804003008592110009141c8000303c0504541ca5600009071040c1500c03c480c4040e4122203142c1c981101ca0310107880044e40a4421641e00c0d64035020b90394041048807180b4040ea220ba4080c21014400406c0e07154070702400d80003203200c80101070a208050307070000100c3d160001c0644241c54842c10340c0c03034503000411940d070104000740130020400040080c608211031007241400c00c104031990300e40f81c1c00c8a542c011450200c200300742402c00e20020807040710411020003050325000c55855140c0d0344070303100d02000383d20504c0400c0c0c80304282020042034120034500243d10303100401301450b160300b00911107010705c0c07012400317107008011 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 279482796 1250 279481546 279481567
    0xc0a1202010905120d0905040b0306160903080d090203010506090106021b030708100b030708070609060c151a031011030408031803070321020a1d0a1211100f020d05 72
    0x2c6200070200204403100c40341000385a5910b903022103045000051006e0008202e61400b446a40b410030b40140003001d90303540d4080b0442c00c581300c1921640a020b0300c0301d40080010161070080c020502c641d0008076a007481c030710505080d15406008544114500d000504c42c0642c0007030b50382460b00014981200d60201c010120f400c10a15400408440c00782d01c190f40e4bc0e00c00680c003c001c1c4031748107508840e12980d540e100107031203861034019500040c0c1226401c02072144200e900c0008c2c00d000d42d503003c0340001d90303071012000c6418a0b261005804501004024540380a100e005014200b0600500041144e00d080f040c140c40b000304000c0c100d01000c80441c0450301c080210020100920f0300700c80e580d0000b41070180000d50207401c9801c00c0d0702c1072001622243e0b024000d40d1003a8100c0e0b1a07004124001c0315402000c05035940060ba0403c007007000001d884422100c1c0320541e2400f0b1010580b082c0030510506c0700318800100c1c20414014010325002005600040368002d1540c2843c1a5483d8030f00c045 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 279484046 1250 279482796 279482807
    0x160b031e0a0209030318210c040c03020d090b0105190b0715090b1e1b07060c020102090a17010b0901050d290403110c090c0a03090f080c0a030305090c0a120201 70
    0x100030301c0c4c0510001c1401c0c04020021028551225411030b81407404001280d901140314613680101d4540341c209408442013400c050300b06c1e4110b40c0706401c000d42003001d8007503041d00b1160784503010b45903c06510010803050070b058001e5000d16107000d110002d11405d20410310014802d989008001c08000003c00d0705a140c140d210304241136024605406506151640c0014280500034044003065140f011500d541d41017032404001070040300c001402c1a40309e031942001810803000c12410343d50200404801641d482c16001c003d4544165440c0b09049001d0003d0f00f1205d10b1003910713018209850050125030baa80641c41c80302580300c0001c618002580d041824030240c0c0541c8010301c404440c06000408d50025220304200341c0f21030480b2101840705c0100012414250303210440c45c0001c11501d28054801d400074903a1500500001004103603d5545a096501c159200720580e0801ba4080003015854020540c11404d04001000d14044660000c0d01043c214422201105034441401c4116400303107 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 279485296 1250 279484046 279484057
    0xc110609032d01060f0501111005090d0e0d080304150e100c120603021c0c08030a020f070f0302090c0a020c300601150e0a0306020c160b031e0a02 64
    0x5010707114151900c295a04000307692a000b180d090107a40066007a00c00144909802c8030300500211400c50724040055a181000038000e0f00079016412000c48800e400d8090359001e01c052100412404150980c01000f040039410000d00c0351142445183c041846c100c1629041a04401042c0b40740343e104103080001c103100d111500b41401080d020300d10b0080c20340d0060141490300d45400300a42e1100c41d14600311841804000e40c080c01c3c0201c001603d00340072821008142c0318141c10300580380c4512845155070051454040103034492009445010b0741403014030300411000c820074000c03504582c001803240780010310090305503070042040301c40c962003003010b8469000d001c2c09106010402600b14017202c80184241030021030f03004944a003002001800b10b04850725540e081d03c0403c40d01c10211b8600034100582640a8a048008008164148000c0144004100040c0380140841c03050311109170340c591050079444400e004014000d5110002d40010070310016030f03880c0790f075181442a40240501c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 279486546 1250 279485296 279485299
    0xc011407050712020103060b031b0c0f07080d0915020703060f2c0609030f27060406020703030801060c050d120f090f0507120c061407060e03030f07020d0c110609 71
    0x1000d400043e0512542e014000c1203001b0fa030107000c1c2c80c0d241c200d00b0820703100030380341d00b00070081e00304298404414103805010403082c018140c50442030800c9405281040d190400100e42d00f1400b40c101c256030300017505400421000102044000d20000065100e8101f0b1201a14903034689080804540f007940c0050038801c1f00c40e01c80000c0745681403002c02100c110307172070308401845410041448003a0000035682c4162050480910b0005441e06200d0001c42202c03418a6441c0301690052040e034440015001900c040d074010f00700c0d0361541c10002e244d001d040c0c4c00f0800740300c4100280b2000c01d20114001d0284800c501301812844280d1007035000520808a000b02c0903850b010300001049001802c0840d1203008030701b1500350700e0f21840310345820038100c0401000d40e1030010042056034000d0342240851641182082e00b01480c03a00c4042c1546c00c008034030711041d0000010041034000c0d103e0159002002c510052903860a24100540341441c00340028140e081091080c925540d00c850072505444070 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 279487796 1250 279486546 279486553
    0x40f020c0a11040b0d020f060702040507050a030c0c020a0909140d02030702040b090601170424050105010f09060207090e01060f0608090d0503060f041107060c020d020c01020303090c01140705 84
    0x903402410340ca41c000a00d0455071000da60416220a150a0061116a400c0140940180070301c075400c005010581d041c115402200920400000d6a103602c90386201d10059125141c1d01e2000c68030040c11652035402d4002403040c250010400340e240e40da85d5000b5207991900000c0e4013507090500b0010840d01608410144c03103040b05040c103281d13020019080e481e100307880501c800c0c008034003000f805040450f0054001150340c20486202c0703005041c0c40b900540201c00040c0751040302c0c4480d4080d004c100d402c4019440d161001040296031010340d030515120307070f440c0000392076090100080d01d5419900c45e914445441305402c80e8506401c0d4005e8009250110b1884841c1da602c0102410b403000c215035080c10b90186050800b412030181c000c42c1c0c4500700c0140340400c5100050204401021101500e52007044e05100d00000500300b0304c60316a141c903d035001080031040b1510028648131505820504540060091001c070003000903600500380000d0074202220a100350301b013003440c0a0103201808510 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 279489046 1250 279487796 279487807
    0x2090a06020c03010c05040e06010c1e0602030f060402031603020c0106050d0605070f022b09031401140a0c020c1c080307030501140a0e070c0201091505040504050703060305070b0306040f02 83
    0x390001566000c050b0150002d00010340c5006040d9400e00461140c0308142c0d000b040015025840340150b101c0280c421805034111407003039054803103011081501103e0095001040c041c0c031500c0303810324950201c030483d002c0d45945064070724910502c1c1d170005107000b0b1580100d1601d06a4200b0340121010f480c0c0581084000721086c1029005031074296030050216101c0b4600144841c80494085c4054400c111883c07509206407500b0050842030718401c50402c040b0b0680400020b01c0d0f040c040415440c80d10003c204109070540350501e581e4080d00000149103401c2d00601c0e440d8011640a02e244021612000d6810800c482d040c54003403440c000074490200001002107040e01503104a0590b4810f040340c1881007444014049101440d00580400c180350500207100c1c0f920450045d480782e4410b01d810040c1c40d80c0e0325104000e1b507070902c0d500804910049028407083c20188200ca5012140d40b50602c801c41c40e6032201074492100e80079035411402c0000029000b80c90f11f40202d81c0340b0400700300856031034 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 279490296 1250 279489046 279489059
    0x5060c0a061d0d08040c05040905030313031e020102182d0d0209130302010507050702090f13020316031106071a04080c0a0b0f090703031b020f0d0305040f0e040308060402070602090a 80
    0x90004170b404131000c459611002c80c2d103003001c0c40380ea00c841c1d038403400551450700d402166a84011030404110104260200c2607480c02a55800c038600d5019a070700056200c0f41e48075000d07540c4200100801d405600c0c1244c0d010324000f1810040c0040900703140c01c4810042013100800c64804011101a41004100040c001c00300c2e4403c1201001c28081e034020070854031500301c1185c03140304425000c0d43c4682c200300030131480d005c40e020042e0030925024035004040c00d40c1d400b29003007900203400004118a144410400d121040f072a840692104540e141c2c542070403036a480a00110b90401c4848040a500c00035041010800c03c0360481c2c03007920110340c904869490403c1c0f0000041700c98104404015000c110804000140001503903403684820940c01140517080300e8150740340301c00f40c2e84103212004400140d04ca09941a075118080d9032026a1541030807820002159103500c030340090f800580c200404a58880301d04e941082c1c00b15005a9078440a080c4030010f07002d401420787d80145d080400094a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 279491546 1250 279490296 279490307
    0x613020c01050f09060106020a020d02090a09020d050102130602070f0b0915070b0411010507030f080903040902070b07260606030a0e0102130e0c0c060621160f05060c0a061d0d 77
    0x2182c84c10201c8003a070b82c888100b00e07101d8040f00002500140c40001d05801868011a41540f10700ca800f000200d0401640004040f50701c080001d81c1c107a5030000b020084c091000c00c00d40d0141c42c0034002002c1c001d00d40400560300300c0e101d10940364110700208000746941e44d034068a0b0103114040c0721981c2c90f03140a0400591018007074030304542406e140381e95001d803540180103480100380c1546414000184106081c3c485190050504460703010801c0081003d03840c40c07000d0071b5020700a0320710750024a8803a030060221404445840c2d0512a880b90030703505882513200440d40808207480c219126122201c10001601400e00151440c0d400807440c132042103550404c0000700d50420b0760300c0b9110380f21208880d9071840341c42004840c0350041000503079581401c4203990314000e600c0715a81500c00203500002e051000516244020141140f002c008500409859101910007210000d16001d01c5501d99a680c0349230000061030241c542a8002882c402600d66002d40e18440d41510a11040c0a074010312 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 279492796 1250 279491546 279491551
    0xc0d1707082104022101060506210705030405100b1311090108060108130201050306060702180f100f051009090c0c140c031f18030801080105070e0303030613020c01050f 74
    0x1902c0c000782044800c1c00e400041024015078028201d50000b0200101c0c9007204c03e800b2510b189150740b40c0400052540342c0100800c0310010b1011154105281104c46002089014061004010040c010300000c11070110744841c44080100c0c00160300b25a020104403008104482001c5403898000316880e0500c1907401044852401d81e100e107201e42e11a0300640b28210b083e90f07800d12546d0700020304001035026400030342c1c0044c2c0003005035041549980c00582d90046001503903c1070f1907480140038814410450b000d4107e500e0121203035405003070180302c2a449142d03101d107a1080492072081801540074801e028040d010710001404441c2454601a0268420442c03c0b601c0d100301e01d600143e40000400d00414064004000d02091a0034803034030b030703020007004d1070030084035668000d85120320340b10307819013640c40b803081d16460303200c2d0304d800009400c4800c01010130061014140e101a195500881281d511038003c8407612550f01c2c0000030384000b40200c00140c0320b191301c0c160500488100c501903551 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 279494046 1250 279492796 279492817
    0x70b0304110d0302030409090204060e090c01090b0315090402060702040f0b1207180c090848240313020a0f1d06060c03030a0c091203020c0d170708 65
    0x41e07101e0200302440410040502c0150058109000c10320a892498101000e0306000400101c6c00580354441c2048011040c0e034440d8641d44aa544000156001000036005040c0490002e085150410045110103011008103105081a9000508641e82c9609507422150090f1040106104a000c840020000341c00319a20814001c0505810300100041000030748613003880403c8849048042c407030140000d00d070882c0501000348008146400204050052102110044862001011401c1411010764103081c01030b50300f6501c070a8100e182032100c07112020000e8614140c07010340c000d0f00103012004001e010a0321000001801800101244400410f60080352003442d15039442500d1000d04100b4480c40d5203403560100d40c6c691140000c5052503014170080c21082c50700440303410144c25580100c0d00d07280300699030400148450384c07003501000a840c201d00e45100442603500c0181d525007015010900c1142c40005070010440c00443c280503402c06601502d4461100f890a040c9c0d0350094804103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 279495296 1250 279494046 279494063
    0x109140609060d050403022d0304031103011b02070e0a020315010809012c1501030c090c14120a060e190f060801090b04050d0504180e070503100212010504110a0c03020f070b0304 78
    0x1580c0e40582d023a9000c6c2d0f169458011071030141f856440c0b41d400b08840c40425419540c0d1070f604250554800014651034000b6030140400740e00300a40400310100241510b00c03202e01c14030420484e11020803401d03551038800d091425540e40e070b1040030b9006d00810701988400c080260512900500454840850750110700e0907100102c4000c014400b81110034030025002804401c03007041940b019600448002c04949001003406082d0581d181da10341c04098010602c40c41c40741000100103951082c08090700103a0300490071801c141201106080391503c0313079055540d98075000c90390b00546601c004024a5620001c0c40f524100c0d050158011070300316400e680742d020303880c01320000e14450800c460698000000058044441c10b417448010549104850030511a40c1000715141d1340400400c640d5090b020307805079640e01c0318810214200410b0740414001c03410302e09075140e800844400e85103440c500c0e02d004802a480c6080c100d2514028031050700550159100106069101c48011440380d401540d01 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 279496402 1106 279495296 279495343
    0x203010c0906020609010c0819020d09051c051303031b05101a03010501080a08031b03040308071b21050d0f0c0e0109140609060d05040302 61
    0x1150100d41e0a0400700320303482c1c1c10000c1d25030105605009024001c0d03503400c00b0740516005020808051000701160300254000e07415500c05d20700d100414040e01c01141000e589500c0100740000509520702e2000c034449009600b21100d603401e9060004030503165072811245c25254100c03042c800402c080b266004210704000314146034220200000c0c24800d803c0c6000c40c031142d4956281d01a9047c400104001480450070b5100c0c42e8000c0541139980d1f8030b00300c88280c03204501c401082040ac02005020525034010301e1148038020948400d01461035444002031014a1208020084962511156804408080c2c0080115143d040082c145400400c2803c1591489040d15480f503503918542580d003580000da5034402e03403082c2044084c482c28a020504181d01010105006581c0000c512425031a008229148184c2d00c0008110606092800a403644100ca00c1581c420604990 = true := by decide +kernel

theorem cover : BRFrame.Cov 279316546 279496402 := by
  have h0 := BRFrame.cov_init 279316546
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279316546 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 279316546 ≤ n) (h2 : n < 279496402) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
