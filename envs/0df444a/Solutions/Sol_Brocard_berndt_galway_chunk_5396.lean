-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5396
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:43:41.28998+00:00
-- url     : https://prove2.me/submissions/541667cd-b52f-40ec-89c8-45a9cd8d41e5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 970323741 ≤ n < 970503597 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 970324991 1250 970323741 970323743
    0x9060708030a060815070809010504020120070e0903071a130209060301090b0a0b28030311030c0d02010603030305061807052a0106150215010504021e0319152301030b0904 75
    0x12031740d002404078158010b0700700c3d079100c0b680600800c02c51400d90002090741d40310131074660507142042a90340394010180a110050100c07010a840300c2d08005031901d80d658044c600a8520940b070080106210ba08040307818028190301300d40c405014407039020000d8901c2c010307150a81c90340d0385502c0b9000083f141256a44180103400e00095110f14000c1440a0b0985c0e10305041980280c102c044088c03c10300000e014252501468000002207482a460740b5510421180303480510580028640e01035054000760241d80c843e681c2803100351a42c0080c400d5018100800055004001000450985c449c002900340f1100110302143c04008585007100140b0721501984001e035100d040030300610761702d094022014080c0c0d200500c201808001030400200041c0282d520480c0c001481140f507407072514086260400c0c112029540b41023014110500c0c4000315007403a0250f0600c030840080784130720a1010100e411000032481038409070b804180c040c84892190605150f510350200340c072501e13040901740c07080b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 970326241 1250 970324991 970325023
    0x14060a090905040605152403090c0a080f013c0b0d110a080a050d08091507030f06060929070c180f0b220603080f0901090b09060708030a0608 62
    0x10b402c01c0c6c6441103004d00041c840d54000c055981c0b81606208160a081c840c0c0300d9425105a02c0b51980c0c103d2a0a000e000c414999020b01d19440110303e200c000b00d070b03980d0309500c80b100070085503d00460300b1130308101107028842c14540130a05480c07101c1008015030704415074003c00044115100e00001c030685544e00066640020080074108a800d003507000d2000740c000704004001b03c042c81e41e5040d076514101e1081d1001c00c0500000708030403030301c200044035036941c030300100c2d804034504042c004000740440340518a1150520900040d26400f9080c0132058030340e4001c0f510400e8805460074405041c04030301c0300070100780420100010454022441c0f002d007140d03c80001c64608900e036a43c1c103803100c1402c5110001d241902c5060030307541d10010449251100c0460b0b20506005011a50042c551940090080d5200041010141e03590340c0040500c090241c03582c6400301d8031404490b2041c01030b021942d0300600200131359404100007001865000c10814404260700e51200395150800110030f0111443d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 970327491 1250 970326241 970326251
    0x10507050405192402031908070f0903320a0f030810050a090e030702030703050105090f0114010501140415030501030221070b2215090f14060a0909050406 68
    0x100c1c0303802c155100f42001c282d55150540c604046441140d0301e18045a0400c0ca1a0389003a800024002e0090782d00c8080168002c64a00b088450007030407001c811204040025150030010411074055029503041d81e4105509086080d0350711201e15100c071f08104003000603441400d00001071001040740004003403180c1c0d968580184603140c050720618000c1e04004006943c000c00b8400c603102c41e01c028040b180464cc010940940440b22070b421031180c0400603401d40503451707011080c050150090b6000c0c1025070111240e52035940c1c051401c803101c5d00740d5260000f078003100400c0070758460041c0304913060f0811034007890705a95181c84003816462200b0800800e443c5c034010000d51030070424240042c00c032a06100c40d280c02100249446507030034000c07551710f8000401c44480205080c2d40250414003581031284d0107e48600400100c3e445140440c1d001540440c0040b504c3c2650340004409c131080c5104c080f030015502d20030810a9089001060100184050b0015150b2101d00030240124024440010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 970328741 1250 970327491 970327499
    0x41a0f0c031f0f0f080307120c1113090b01080c01091502031c0c140906030a050a110c0a060b010905030706080606070b0c07020301060e0903040320103b0d140105070504 74
    0x4035803070085e885501d950704148440000700c1d035030780c4446111068510300075600f4081c2d4901352010141e03036640b540e0400e0450884220440d0181d02c85060340740140d603452042daa840c200b09070b841140918250010b07002c0c0700c00704054502c20100301410102801078a080030030108102c138104c1010741c42c03104131903180c6030840f015980240d40380f00c80c5001c8141603441c20243d0307030206440d0b1101401d400d04860ba00c000180c100f48c555400038050050091aa03541d4000c00903001c2d40c2c0750081c550685501e407601450428541c000c0c00910f0840d00c0c0640079000c2103103010410344038207030014011038010004002c007100190342d03c21024818000c1100c10742d00d03211180189030854507282c03c01c0c010b12040f5002d00800030b00000544040f203602410030500520765844840401551f4089290020942400b00c0e0322107412015051200100007440c40002c6001a9002040e443c24003901e031a0783d500c000a02c803e410240801074007903004654240c01003881140c044d0071928111071880c0001c201240a00c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 970329991 1250 970328741 970328759
    0x7030f0f140d08010b032a07020306010905040f0807050a020604091a090103032c10050a140f0313062a030e010213090b13020a08041a0f0c031f0f 64
    0x1c0d00c00400c0200511a6814086010f0900403060045055035030021000440002c880c0313a4850400d0311103005a15010b1841303000c80742c1a004070f04124428003901c2c9c000704402209110f018452a004208030503c000d05403030701c5003283e01c50130003a1941d000d00a001009a25004003c0004001c582000942c00c065001c10b0703545510405940c03031241d0990300041001c81c1e40010105d142034494404840350905044541d00d41c080003154854000b40000303002c40d4900d422030003500a9400c00d482d01c0c0341782445900c28072034902c559840c031200d003170061000c24544000000307401c001500c100c4001696551007551100c002e1100b03038005811840c1c50356038804465141c090700c0e0342d00e5000341c000d41c24201000c41003d4920f13140d010b2200f00b103688800c401255a10030446203810b07035600a0465541510850081580b04200c4094803180141c1052090200c500850f035032150f506403c40707030b1040e1070340c400b407003c070b607001401021111040f80786542031102c00307035201c800528401401d0311101d851301c4c00130 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 970331241 1250 970329991 970330013
    0x60601120507170601020309090a0506030606030f0703060b12010f0c030e0a0308010b09061b030a03060e15040f0605040c020105090706020d02060714040905010902071103030901050d0e07030f0f 85
    0x841280e051500b0300c0b01e0aa040a01c5501d11504441124a96071303544004134a0b40c0141106160f210000409000e440082c0d80c0c481d9001d20350940076103440e0781d074a01c141699424040808041c95100c0c4004101084039540000c2800c032008149188403080585060709540c8031502d80d1607002d0345c421980e442e09825105400b40061150043c00d04017041b51009040c01405100c0c071a40e451001400110550b11403044409031102c10440c440010040300a1550b690412080ca0340400d01d0203401240d442070301c00c5510300c21a2030705d0444404602c06801c0c0b0003d84282c002003028507480c0e507000b0600b66038a00507004050281c2e80002001d241858800749480940e52005c815900100300c01d00d40e482d03003c219554881158140b03140c2da0407050b841101c2d18800e651080705454504070020643c0304554000704007007802503e0004c0d0441418041684900c0b07450801800f0034420000711240c458550004c195142c503030b809423500150342e40c45801c040c03c1009002c88058903031448010401c400c2c00c9103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 970332491 1250 970331241 970331267
    0x30305250f11040f0e07050919060608040b0903040b220905191a01050f0c03040906060c060f060806160210020304030306031b05100c05340605031306050c1b060601 72
    0x30034040308502c117542c151501c0084c020740303000e82e0040d07000515241404256004d050007041e010045559500402450010300f55403c41c0d0300032020020400b51b9500106490039103000e950310b9031a149011074403508840e401c01c4100081d085050000074494114440c8a10500041540600e4080b041e1344182c00c0791205440b058a1880f4910307002100e036130006c203071004118100340751640c45060161552a601940d480343d10190b08094000c0784030381c2d2140342c0104191291600744400920064454140e41031340c00ba0500b16800400054504403899441078040302c414010703140310f07401c1d078140b010070f0740e1080300d06501091b01d8000800402116890300282038034410f00c40c038003039400c207000124400c074100400410800c5000340030050000912080b0b2101c901442d0012603080c01000c0d908405288842420420441c20b00010340b96004000700c034460301e030011300c1c0505890166a04030013030034042e01050020b00d040c41282c10b00d445800c140c1701c1c5a00e446008210b10b107407000004040da0014a0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 970333741 1250 970332491 970332521
    0x1504050114070c091e060602071404091110110106090c0f08070806040203040c3204060b16030216080c03010609090206090904050c0616021009030305250f1104 70
    0x40b60318003007004103d55000391003507042d0110341035200c00c03843c0424407034004088010500d0f0034000036145800044c1c820450311503003a8400d414041500700030885e0018000600a0f444240c44a00c1601e040c0d0301c04805101203061404441c21744140d104d003150b1241e00304081e4617503695100d0040580005a1480742107046c5000240f40c586024002c00000d40a08803d010301e4003c000b00341000140176001010300f141005d4640340c840c003020440d5815540400101e2410500725410b6810b0500c0c0c003440050302e01c203070701c1c47d8075107240511180500c40341d0301c42c10303411402140305071000606410542402081d0300b000800c6910340724000c03d42180c80382d52100c2151803500c6900300041e11050192281080f080350026069911420201e00702601c1e0100305622200015845461007203003007610071220b000f5079420f020700400d00400e1310440007900000d0301241d01848550a040881c50394400d00b00401610a4042100360f601e209040c1c02c0320200f294600e0581058018904040c4200408000f00038 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 970334991 1250 970333741 970333747
    0x2160314060603010203330d050a03090b090f0f040212040803040c0e070e04020d0b040c091707031110140708040608310615032618010305151504050114 67
    0x240762100b4141c01101d141544030301e6000070445060b0f401d0144040c8547c05050005030401c2c510708281c41d0019110b00f01e02242c0500c0000c42c445041006a50040c80302410403101c4422481c104202102c0312400b40e54015000c108001d205850444000d0090344100102c54503420039203041910300340075030815901800ea070020071400944c4000c0f0300f0001079050310b00695130941c1c3e46040021308180e40405800034100034140440f03581c000d00381021640d100854018062841c1c040300e4035042a84406803110031002c0700c1c000c03d443c191124203071600f9641450241142e49080c0c020840d000b548081c0c07124100450308100180c0c1003c002e9510490070710341d0643c05443c1541400c520004200c0b40c07214025406113441c1000840c3d440349000da8407800c809818156a441d1508561360301c9508aa00c00100e030740100410301e0188251600c2c1c07408407a0805100c039440c0011002454024503000c103c0c0f408510071800750f15601e00d013000140b00c0d031004580d6207091000240c1911400900c04101102c10 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 970336241 1250 970334991 970335001
    0xd0c021009020108060d1a090d020c12070b0c07120b16030e06040b090c13090309060c0f020f0d12020607030b060c06040b060103020f0f03062d0409020102160314060603010203 77
    0x4c403040aa0264040b114000252254241401710402c09409000713210a44000d005504a00103848102d2001c0c036400c0312a440540b009002c940c0f00320780a0500580c3c0028002c2c00800400b030060513189043c0c0d400c079007186075100c2e07810240500340003040d91101e2201061021107040c054180038080720a080500202d03004922460780d8140041020b40700c20a1031b004200884010310441440160041c11001044800000b010003011159011400301d0b504c0400028a1030041913409001034006130000080c0c03010750240009481c2c0343c00c0165001380034448d14400120032004041c00700c0c0c0b0340d43c010461440d005202904032601c0c0001c43c1c0c4140f03407c1c005100a400d002500341d92065108812640f17a85403000140c01a0050807075400c800400420743c2c00d404084500650301c076003001c45207140240b050a9540000600c0079101d403042e07100840c2d0003000360610f50810611588103104544a10301204450480003540d500215000100d516032556000b00c10010304c1e80003203007103000714558141 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 970337491 1250 970336241 970336247
    0x3160302090609070512091006080c121f02160c120203060a110d0216081b071a0904090c0b0d06261e0c060703171609060e0d02060d0c0210090201 64
    0x55800c0494441661b50005402610140301d81040750003e110188007942e16a1403c58545440c1da9a09004040622068141880005078044031851520b0f000300342c0e2603114501d402a503c000e41201480d80114901d900081c081448a40180107006994404840c40d08c1094281200607001d01055030078000c0002401c808507048030130442d070086005030b55a0950400584025200002420324080030910300c4031000d440f43c00415018405042c0c0da50545c460500c03a10030780b0403940322803000c1401e1007048c1c0107080c640c1c4020030040c000c120120782e050780c803c0318101c01d50150001d000483d490b503408100180c42d140c07502003004202002500d05040340c00078140e40e60440d020800d80380c0203e1405848101041c4085040103402803c996520040c50802900611a100b4810030300d640e046c00045120b40d0700b080c0505180c07400c4d5982e840880c1340150460f814030000090f268800544019070b40140e0b240302c0100544008010080348c61a11030070084d0a01000101030300900b418400f04c440180e80c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 970338741 1250 970337491 970337497
    0x715030207140106051c061401150917070b210403090906060201050c0708161509030801241223220b0103080d180b040506091b060c030702031603020906090705 70
    0x8014115064903189508054000c2c3c1600078400031030724408000492460ac804940d140703d00d10300c0d1a0500c0683ea5000f029028085c000462807042d089181d00703020b0f2800c0e00000b0308038078001e40408404100d00c2848810f04040941d011400325a00902c10011095603014000007400c29000820207460a070220809030301c9212001002c81000007441160144c21484864985030880c00c010050400740902400825401d0029030104942900009850703203034243c09401d000c100040c02c2146145500151511004d21144c5504941c031020544043e00d0ba1442c000151400320a840200e800c04100d1559003038410101d030403030845400c00750408907402106030f0341101d1344040200e1f583e04179500618002c00c01040c400c4240c0c02110101007c2c0400d44036070074040d60250090b139156032691403446640707802c80e0364099107010703031030f04c0e1041ca910b030140180c15800341282c1500d144c54896400242000720342e0000c2001c030800c1030000c4c400d5090480e03205600c5a0151307040b4409040191010b00140 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 970339991 1250 970338741 970338769
    0x8160f0602161e0f2c0910050711030a0525020a0e0c07060509030909071b0f080c030c2505130f090506100914040f0311071503020714010605 62
    0x3c000c5020288810002c00c040c903004001071810380300001e4940160f070008800c4910149203041d00f00c5846440c0c104500e0340c0c0390140c43d41000600400b05205040e0016010040000042c400d65507010003e2032418402004981055a201981e95010b450150032040400ca694000a442c0d0100c00006865004040064a1070300e2010403485e40d0b80111080d1074400d02e000100241e05110500402180000c00b500300c1d080f0855041296039a05c000490381c0c0b445000c0f03090000469440a900415103118800000c4c5d8010701c2c03201c0c030f0241001c0135245540d00105400c0b00b203038050040d0f0300d60101e001c0c4a491104524030841c40c1e90358500000100881140d00e02600300310380d5401c28800c14807680c1d2141e100b0325400030548000d443c140d1501403500c1e1140c4180e44513031341400e42c1c980c100702c6508001031185034410500c00c101ea8003038400f10b40d103a070b40300301d500350500c1039080c0810680868110341000b481c0a035800742e6500c03024a000b01c0001040814290749a040003014441a903507154910300c51 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 970341241 1250 970339991 970340009
    0x9022803020910180207050c010c0804050d020d050115031b05030604170904061410050415050c0a06020705010b0f030105070e01050a260a181707060608160f060216 72
    0x5510303903201c980c9101c111603101004a83c6042d0451400c0c0d004c54000d8080240258295494043c5000040d6004001c1000040c5004810001480985042c4250100d40360018101681440d95640c960b8215002e6444100408000c1a0100304010b403000d0070030304660401411011032881c080201c1c1d52400003400050101c0801089003a4200c0450b0507103821000c0100b0910445903100031041201004900ca103000e07410150116039610b0180084900726801032080c004003c4110314100c4440c3c0068807121594010700c2107600110f910342c00944451800fa400005921062030100240c003c8403014070f038003a0341014100724009030400d2030030060510038240f03165505070b101800c44101440b2003440b065500621145404640b0540761148140d512410400515000f025280d46252001800800d0308400319010501d8800034409433211902c5103a000c2500d644a1044038103040e00c030101d8202250074100100720000381400c107000100301c103001600382a241450504030300d90b0740780035a1340b107 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 970342491 1250 970341241 970341259
    0x31b1c0b0103090510090b150a090e070e01030606440715020c04060902070c12020402040e01091407080106020d051c0501080a060b0303180d0f02040f0902280302 71
    0x31079000750026001d040c3e00c2001d88039665000c205d204000c028001041c0d400e00c194a0018445010070031200c85607200041c030380c4405520785103000c40a0161015507a20500a60b030700080d00003190345039207002c1c6109000c0810001d0400300380c09901d100034125200240c1802840c0240400180c0072041102d40c1c1e0012022058030141800f49440c910394402e0000d20045030980440700d070301140c10b4503901c0d0125024041c40c0e5681c141e001c183c3c0503004001d80138012006040190b035080a01c01c0e90b0462014001506140d51407142e4251036109a22040440b46c440503c0e27030b54001201c1189a1185139424020415414550000d5484039120024014090005480c0c03240421107124541c490010850501032580c448180300d444018030001162014100182200380d0300d0040140d80002c50480f107448180c420740020000140501076041c0e948014510300d00004d621203005940103030303400200105040071b030761040c003a8002900d98040c080c040c40c002c80e11801880c0201480071280c0454003001303 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 970343741 1250 970342491 970342511
    0x10050d020102070b130905010f2d08010615020c0406080303280c03063303051911090a05030a0510020708040e040c030b0f07200106050312031b1c 64
    0x403030b025480d00404000c0001240054502c0300c4090170704280c41c0610014080381c1d98802008584c0540c901908442d02c20840c0c090350f003100141046403408103644065103802c1e0f5504012400c41d40d1a800a11000e1703d00e2010000700d40c0c04000303c80200c84280c070201301462808021588030700001c0c1011009900c140a0441043d0f00d80e200012880201e100c1040300d03009100e005030081c1078500c101c2d0328041c82c4a14080e984007002000410180c112442c5802c8400000021801040001c09610480d485080c103000140003510607011302002d0000300341e6582c583c800410401074100d600a034420380c066080792002500c041180404080c00c52000340c1c4541461600c3d01070341c09540c0090b00d075000043e04010038002c101e00204126805411500580d40b101d144000d0044403c40d4550082070f02030000030904015074000d0034012000e81d000281d025102c40000c0e0400c01a2401c1121655010090002014802c6420242d8680500342c243c500114000d508600c02070400fa000c0502d80d03100201c03c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 970344991 1250 970343741 970343743
    0xa0203090415090b030a08120c04090207110102010b0d1106092101020418090f24020c012403020307090506060d0507020319110a15060b040b0c0d030510050d020102 72
    0x180e03880000400a01100d0482110080e01420341e11406601504124010b5090700380800c10410072500a0304583c503000c2c40c003810031050700c0701501010132000c08200004203285680f020b025800c0c420354001d2001001d440009003502c008103445480340585c1001c1e4800501c00315040c01c15070000313a40b0a525001c0c4040010510750082001940b00600361281000c10030b411740c000d00c2079039801c00e08028a5807036040d992081742c17940103000303051189041d843c0021582214550400196a80c07400d091300d414601844140d0300101032200550703444030200800c90ba082407182600c20192800c2c99025459600000e550303081c20320404981540d40c8020406a8490b07070100c4100f101c9095080c480390503c124001c0d46d80d4024148102a00040303010024001d00c12080040d6800040d802131841030000e80741e0350700401c0c07001c1910034440d90724440060102801c0014000900a80005540ba0000e80d01c90b80d0070204180000e0f0105450501001400756000340e40d48107039403007a0f030000c81a000b503200507 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 970346241 1250 970344991 970344997
    0x4180b03030f0c0d090f120f14010b010e060f0307050c0c0d0c032604090f060e04050c130c0813020f0316050f1f081e01081506010519050a0203 63
    0x150303030980000a240003030411468002c00000200b001200e84400300d8200c100c42e00505402600e610102e180410014405548141d05005014039201850b1900c942e5071a0403110424405441994440b18a110b103580c100004001c100c0b0705950340c5140c58100c4070340d00c140b488006c140c8010300601180c41028480304000c80034080001401d01ca10142442c2848030a084140c44100c4034032417004400240401e4940204901400c41007030141402d003003044000243c0300741c0d280f15109580d50320001030900954101d40d40100e000300040d2402900c4a0284262503007444481900742e41010b444d81c00c2c1c154801c4072998403092070a070203518a0241c2c4001000b006919850341d5140c4112401b81d142824814900c0d42105c0b021110704140504800a01240c0c071840204d402c00c4196240c2e01c40d240b0360180d01480e0340003040206003150002003604007070141c0307001e0b0841e0f03c04d5401400e42d07112580c00c06150580000d400d0814a0034403080c20f00b160301c808038580c600000c02c100801c02c81c0c00a4020816 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 970347491 1250 970346241 970346261
    0x11b02091806041505150108060f0607060204090b0909160303050304150203161e02071a090a060210150810110f0403110a060309021e15030a0906050c0903030418 71
    0x40d00c2c07541c01c0c03e00341000e00164401c00c07292443c3c500008500c007018000c0c40c1460509042c2c543c0c45031550340b0400c1001401d10917411b03540040c0b003044108005881440280301030201a940090800c0c01c000c140001004002e2030f0702210341c0300000c02409082c1c018a480e040760f40c0352402da552691240303020501c510040860f58078032400070080c000c0c000a89040c0111420040c0c0e00c441400c0c10a5020361213501c0820810f002503007100b90103222180c6140310403a40349080c00075241c42d100313495010824102c102d602403c01a049410121641110b0b8001d04851811078510300b840079041061164840007046412065260b50707882c401c0c54044450150342211800f007041d00c5d240c42d0f5a06100c100412030a21851107007880c0c940100c4c4260092040581a64018000c44003840e07401c0e07250840d122181c0205036110240340121210003407c403005600ca09544080820951200c0c070380803095900c05407080c18880b00902c210012610000261000c441d046428419000c82440c071201c02001e60300303c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 970348741 1250 970347491 970347493
    0x60a080a050a11070602090f1c030f0801060f0e06070206030c07170901140904060305010c0c0b0a0e0616110601061e0f12200d020301171903080613090c14011b020918 73
    0x4864840314a22003120000ca500138bc944000005600e4802c4540d19024018040410a03031402202d0302c40c4641caa0f2003010b83e016200c1d91501d0010740000e40c05400840c3c440c0f4942c0e100007505810000b044000d50020007141078003034240804000040c02c10704002c541c5042c000d4002c95041455600d6401400045401c10000c010103112400006c15402c1d56072401d41d091500e0f100461041c2c0414420344410003c4140a4000c0b600d90984012a40300b00361600d200300100c290300c107144071000b0300c0f10600808864540b810704070309074610342c541880c0c42041c10051044104000c850182c0202c03030707401e08105242001589101c2c6004d003410a10a080011032400000300b520b203000c811580c02141030710051405454040e040c418000e0b69002154107140608204406100000307000300d0015402580c014a42c41d0403021455880e0116450000d0a644051820000b0130800f80300c8036542c90141420300e400050170072840010300c1c010103c9038009000d800c00d440054031503102000111021030701c6030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 970349991 1250 970348741 970348759
    0x3010e191e020304062d150317070c080105070315060e03070306050603010906020708090a2304090303020f0c010c0e2407031407031d0d050a11030c060a080a050a11070602090f 77
    0x1914641e407841c0388003c0442c1c000d10380307011040c00819031351788001141d27806500060380e100d00c103d2448aa41081f00c00300c45465000714042103016007030140c04d1080d8042d41e4000f404000500310214860250340c0024280844404180a10380300840d0322003e60b600284049165140c8c5d0740800e006045910000e480d0764030100b03841c8104440500140004a0100c99560481382c441c00180600041040707004940e0201c041030610908140d0424072056009003001418103940d0800f200d1617520050040081365035468a1942c0340d40c00c0b041203400d8460545034803001700d80303003190090400c002d95000060314501240d100d08144c4503a14284141021540141e26501d40b440d0103001811113a00010039892111500201d43c289140c1e07400503190414014400710050f074842c488043c20001c0d20a8040c0902d418081d44d03a2205001400d1110380350f03640c100a454808140011908060b000c20b883d94107029654004030010015104429041360005a48250141c000b984028000e45680e40110102d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 970351241 1250 970349991 970350041
    0x13032003030f062d0a1509030303090201051207080603100c0c0602090a0b041806080105070f0e041517010b0420130509040c05040e0c130914010203010e191e02030406 73
    0x20350611051210141ca172141819141c0d10200100e0014980360030005821410800200c0d1007500f10860060041c1880351a18000756120026250f040700d0300000303d041c080611000c0e0500304002900b00c00c41803410020440c00c08001003c0c4e180900002d80301c0707030700411420881d50300e02d03c44400410070810890790b2141e40b481d154803000261500902003510740003001450900c180140c9114030000c2c1d88030346146412080c1526000e440c50320054105550380c4450610800d00c204190283c140a5016055214240174803800e407948422140e009504001120f0010711a880c440405684504c00160705c0c0c00c1504a440300319501a409590f20040c08401c0c03100b4008101905420f0701d605030780600c0300c100c20040c5d1135540c0f503050300c980f0f8100c80c1410081800380115071003501c2661064101c0902d140309203008509980080e041088200d00b4401403120702c8140710421182076680a2003800509001c43c042ca10841002c411422410340001c00101084030940c4101c41c1440f815004018881075 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 970352491 1250 970351241 970351309
    0x10c0c05193c0b0a11030c0a051c1b020d14070906030c050603040b0f06120f0304051f050301031b051e09070509090c2113032003030f06 60
    0x31054008a41107010200d55620203039038024541a00c0011007074a1804541300021101e50410f0325425045010520a04904250900c83d07180054003d500421030441e080e10940b80c000e44140510050140414200d01c003180040c1c0c2c1600d1058040358202e8110703100307082c400314132040c02000788440d0088902c041011034140e400301d010760703020700300194055407602c05000c680d2200382c1d006042c07420641c001a90840640c500940c1c0101c014000b1810b1540c41a0500c1c50701c00c940165409541004c5428007080c140211900c42c545400800c0b40d07150107070118090020b00c010300000d071014200d0a560b054107000c844946c402081c02801140707007008481111459001460000e900c200140340c00f15039418424025030345486070044c510807403030f00c4030b1000000c0307030f4802c040d03242076a12100d4043c2e214048005009100d003010882054000c2d92a150050030b0b014100340d0b04a10421030600c0700b22081d8000140c82e0300060418141b0429110300c800070b40604007071001491804030000340300c1c101c034031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 970353741 1250 970352491 970352549
    0xb0f0c0c120307090e010501020a021201020f0409060509070903030518011e02030a09080610170a0f05060106080c030c16031e021006171504081306030506030c010c0c0519 75
    0xa19540d400282c030385c0720340c420441204203200b90340c0141d010200d00c40151500070b080710010428200014603158603409103500c6c82c4c00c02d5000e14900c0d585c4260070069410890450317580300f0400c2c500340c2c98082c2235940140950285c8861b4401d80b2044141c101082d0b400341001400d1000d0610407440f2802603244029030b0381e48510f000d10000350750700100103040440015698095008a2601c000207410109040321480c941031030500540708020b0100d010901d81c4584c000098080d8010305103560500c40c01901e5040d000d802404502410800c110454510009589112280c510500d015803a41d0500320b546944150b00d40e21603a14868003807014940004051404a411400510043d940c1e00c103a40d00d0000d080d0140c10701c81d0081c4100343d12105108140c250300620490001c6e05000c05812035095042c2c054011502281d502d50900c021850100507900084000b46010300d031040b09980c0d005c84103901803042e240a5600c00b042e07003480c04405103148014008040c0c42082504501c550009251 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 970354991 1250 970353741 970353751
    0x90b210103060f1a09010b0c1c0e0315011412100f06080d08090d030c092d1e0302101416120507030e130b180a0f02070b0f0c0c1203 58
    0x5860600c1690f08580034610135401c00301d004103a548141e10306030507038049a000d401c6660b100d008400c452034000603503000601075a09103544007003040701544145460000c00c541c0d118101315105004010402520400c43e20621043e1a1304103821407100607a40f030a40d1848400038000d0420b041007001d04150343c0110103d80c0a4421995030b5128920150703017443c0242c80301d882035041302028055160094020030401c08a03442c240d240d6503507402d415a9031145000d08800d140000302400d40c1c0f03012401c440200541a131080c059601d68106290042e00c071024480240243c0414010410090040c80f100d50b8005c00b0803070443c0e60381548041300f007151003c1c10f000c5502200021200d1061482802035414041e03243c4c8030340c0c2a030702c0341c07100f0007038050702c140307480c0e44050388800443c02207848205c00031802000d0040031407039505100b03400200f41d505450750140319078070509c18200230907101d0b11500e0700f00030b4401c0140101c1e2107a281d03e004902c2403100340d0040348120310381304c0c41250040e00154071030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 970356241 1250 970354991 970355021
    0x70b0d0209011e080a1b0c0b070215010f0f050604050303070f05070911040515031909170f090102100c0c0206070c0801110a021606201006090204080c030607090b21010306 75
    0x1400d140c440208174406c4000101b00107849101e5290000f5004840d545d00a03510f0300443c0c500d6600c41e010b0340460035090b0410300c42180c0d4503104000c0001c0f80d000c0c000144c0411100740341031600b00000300e81d60340140758002d08843e40d40013081d024008107000c0113001d090100e4040c040d8071005140c140450b40329100f902d0151001780b0499000070400000d0304d00518001c004e0480c280c4040c0e07024000b41c60940805c4d2072041c000b09511400d004018000d186400c81ca41541c2d440d0340e100c5001905013400184003002c202e0500c1300c60344055a00045528260750b04a611603250181d42c1810700d54410142c101e40250f44c40c020200d00e4180b10700d405000795120503801c4500e0300c0040b905140000d8180d00c2848041581069204116800107503044c580c01481000c8400c1c0182d4000400d0603206c1c1d80d803082c2c141690008050010310000e002600d03014500340e00620b514100b000c0c00030040c5407244200440c1032804200300c035503012844813104003840c00095000065840382420801000320700382140071 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 970357491 1250 970356241 970356251
    0x30522050424050406051c03050903010212180606241e2d030a090201052206021603080a0c080403080309160503010509060115030e0712060608070b0d0209011e080a 72
    0x82032506005400c06c1d11009408950035424107140d81503d030808001c101d083c0070080c80403114645091019001c0008940350814141c140425101c5200310442500426900490208202d6440340050420340e91014083c0d40c4094840074034440035801000241144c428110051901c852020b03c041e015810f011540300c2503001001013107692902084500d00302c81c80c0284000b07200400c2e84c1e80008071150060509034034050355421a0082d9801080803016440d001715002d2102642c10054411104800302c44460700074216110900030740103400d521000c0000c50100681000141c50968008640c0100960380320304042107641d132140c05d1000e641c02c4039442d2220000e45407505006550045150310040e1403180d00b404014460501008501360500d07403210034401102c04100140c90090103c0c1c00d1400b0106400e03d4030b041500c0b42a480689582c1c04600240040c10703140044461f014003400b00103a03104010f8006aa10710601209403c144101500c030500581c2c00102d090311071044944100301e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 970358741 1250 970357491 970357499
    0x20c0c0604080c01030f060b1201080613020f150f0304050609061e0406050c0f0c0a020306070c02030d112113091503021207030b01060c1e030522050424 67
    0x1803103000354480c0c220b20740d008200c490300c41e500940c0034591586501101080e0581c681900d000e4540c080e580481c4803485410041005100031b010080e000380b030b00c0e030070802e9154442c0c000400b11320081956500c0389046030036248414000c201100d1800034030b540003d8580c0b506051640e21190308943d500203d01a050008041d41ea402483d05a2402102d0b00c8450360740355a206d0400a140c0282454044c000801012500c5c4440001409074881e0040082416001c41d02c1803608080000d0009014000b1034848100143d42c00306030350b003082501e4544007a114001d0720b0100d00e0101a001c072140e90000140108502c400ca8034010403210144900445015a580c1041000c440c007004501c00101c1d4011424401450301c020b0a8a440400208556000f43c0700d0304d6100100000b03170301190200328448403001c02c024005200d50700081c00c40c4400d50348100035450140c194810b100e00c00c070800c046000c00c08009024130f00000041d24020f0303c100721440848000220260202d2050820144c4c0168009 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 970359991 1250 970358741 970358749
    0x203070506070f0f05091504080705040617330a23010b04060c02060c0f0a0c0b0a0c08070f1a0106022a06071403120a050702010207121b0c09020c0c 65
    0x1000040f036a6201c00c1015035042048a45030000c2060700e0384003544211944078220704a0291001e01001405400002d280200308000c0302c1c0c0f07690000d01c2d8204009022404000003051110204481d40500380c0c0305540109169003000d81c620003043c4492013a070501c40c0261143d80704000c01e0a0443c902402a00041400900803400340701e000d4804408000c10f00004c2d2252454051542c0301920003810001c20301d0302c440c00c1130000761183d2202d500c0303824881c0a104202c0e00076001007010030140c1e07141c080240e0f07004003000c200100240c030448000850074100955500251a059004411131000940c01080c000e0f44000a1003090014031401c04089600c4800d00c561484510018040d0702c01e11a9a5060001d80d412401c4103848100760790801000070542030004000c0c00032105d81d06003162a00c1c42c044d00484601410303803821a8418040140018040c1102100c0c108142c1445040b10329107104a660769022060020251018060001602c0ca07983d0007a15800310a2400c0d0b820300d013140f0040c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 970361241 1250 970359991 970360007
    0xe01020319050432030403210c08030703020715050702060403021006050f12011508211227030a0507050615030a1506050925032f0712020307050607 65
    0x503094502c070014648001a0301509500c13840c030181c070b0100c1c09030040980070781560000e41c400d40303802040c80000041d0b100b02801d01d1091300c14a0a01c50040c01994540b41140e0200400781c400b8168009604400c0c456207449203101801088010302c56850300d0a00291251401d031001c502510544882e48180342c1d860050109640014002c0380840c400301c2c0c100705061701c00000c41d880ba0b540ea1307005040340360000103014014041101c000c0174550440f402000e00300e9080140461480d20510032900c030803040c2078407a070300140c0106100d008503e108451116440350241038481c2480001200254140c1280181000038000d03c1a28103540c3c5200b0208181a01d9004136039054010020940004145989600d800188840300241590319000400c07071017001a100e00f000c601c540e106d10410b086c0511195623402209103030a11009520074a030031a58050420800c0740104440120050030001e48107507000c10382c00083c0700403020002000603440b03520280058a0901465000549480c0100da00d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 970362491 1250 970361241 970361243
    0x2030d0b12031e1306020607140f0301060c02190f0306110a08061915080603060703060b1818040c030c0f080a03030b04140702030d0c0801081507120e010203190504 72
    0x146143c2140000c0c940403184105181c926000303000e200040070b45116030880d00c05403060341c009100c2c42c100040060f00d8091200d1595414a5080203111418002c02d001d40741141d5150420408103001480003449180c40300f07101d07026103038010200046c04a078001040046a0041e80c4c00c000502c054810004c1510400322120049080c0c02d000c103e550030034090740c104101000f5074201d0155140c04c2c202c040764100321014400544076909201c010300e400d1181c4e50301300c02d40b401c0400455280c64039000850142d008a043d1607400c500502c02140c540015940200c01030341124551442c1c2460140c465850901080d0ba0080c20a0400708488890211210507112408014000040d080d0b07411000b800b0100d41040d00513072640c2c2c4400c080103040710411b024900a80103943c50740e010444001c02c481003019075100b00104840100300019001c84c4810304543d02401d40700f0a69145401621015013480a8445080c6041d0440340304410643c050350141c003150301494900350490400c04141c0f00c1c1070718 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 970363741 1250 970362491 970362493
    0x1e0d050408090a170c0108040c0312050a0e103e0f01181a040f020618100905010905040e19060c023304110409030309020a081f02250302030d0b12 64
    0x44140c5e21580184a1160300502c1000d80c85a00c1740c881e0b441c0c414010501c1e1040e004100041805031249802c101c148845000a5480d000014445a0020300715001444910550104c1c074115194188404c000091026400c20030500c1c05910a003000b50b4801c0c8220704140c0307551a109004045c1c0070350707404e135490043e041000e01d02c80050400c0c9500050402a004482224440c2c511100607150140a00701c4280000200403040d6810401e10800c000ca5801d142c0400c81c2a440900840e80c104040005840050350009161280e50540d145041181c8000b074500720711042031141000f1481e0001d0203816519401d81b10f4010b40f40c0e02d100c501013034007807505e031104007000004404031000c10349003584680181d201c492841d20380700108040701c03504001980000d407101244030550411824510017080c2600041200380165010104d02514244840154940000780001d00c9000c4403480c0b480c80380c106a40f00302040385854007039944d034042c01a0070005030420704044a10328010803103010401c5404 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 970364991 1250 970363741 970363753
    0x13030e06070b010e0a06151b02150d0f0b0607060f090f0503130e011511070302060f070501052203080a0e150f18030d09020102100608010207051c051e0d050408090a17 73
    0x613900382c908a803030f4203400303442050748d044040c003603503900301c500184806100b9130682c0c503480c0d00e0300301e41620781070544440f070241010000003054644008480341c0ea03800c5980000c0550200d00000040c01407400c010341102101250384003842404402041f04181c0d40050440d071607580c014030300c2070340300074440e50309801f001050f180a480e002d180f60a0420b0a00815a01c01c141c883c0d000503040d0f04140b42180c009c200c0400c411042003c24800e250704540380c501d4880b8282484103915202110f191402400c00c031906004c10710408103134004201038840e000c15202c0441117000c4020700808200c44141803103e400c00030900340812036800410415800d0060b51802c100181c00c0030103007000c480100d045202d0b86034080213800c800e22410340a00844400036136504414100286400440801071140103078544040300d82a40210131a002c00d1500d40341c1c04408150940200007130300808100c44078040c10f10301000100500c1e0030003465042421220350705115180d4044c8000c002c4040d4165041b42c2c045 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 970366241 1250 970364991 970365029
    0x30f0f060a0b0937050301020f0a0509120f370311100f0209030c0109062102120702070819080720030a0524040b13030e06070b010e0a06 60
    0x42c0d00100380303020018124000440030001040102c48003010740010754500a00114240e510020407a801000d04400950405443c0c00108030f65205200c1110240800050844d545031941c901410080c0508070544241103082c4450315100e000120004000410101c043c1001e40c107544c0005d10114900c43d804080000c540c1e900380c070860708042d441c2c0b80381d03c18114200b40400c150b000700700c9500103810780035890b40b0b01d070010704d0300e4084205000c130b05029200c04288072155002510a0b6002c49401c5d03124120a50008890001c1c46a6030031101583d403c80200601d0702c2d000102001101c40c12022100f11065111940010007003e400c000e208207410444440411009441c1d421080f107900140040a04803200080c6005403140b005c480301d07008408940080c2100d8090003003d10f5600c1c078030f00c1c824174080c0d4410003545c0d4001d0005544602d040300410525114080507905180007034241a51440c99040c02c0c401c50360248103c04480d400c100c00034044030141c1c059a0704654002c03500031010007e03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 970367491 1250 970366241 970366259
    0x20715050705190201240302040c0809031806072f100c0b040204150e1006020a02010504230603010f03020a050d0c0312020c0603180d170c0906130b030f0f060a 70
    0x4518901d0210342d01c1d00d0b486606c100107054941c00100d101410070114910314030622040d18030104081060004c40000c100c1240004821590643c25407182421441d05500000d0301600803500b0140c00c00200c42083c0c0d03214400c0d58144008258414014200c042c4a0020400d5607542c0300d84200004044007201000205410101c5421034401440481d41d002045206071081c0e20a600c0380d40501070481c1400700c0c9072154080b00c409000644083d2542c40036039000a015031045200d41d4a104034105281020206450781d0f8100c0d00000400d0035075a941e5580d0060101d034020300003607200382804a0002198030b890584085200d81c030005070308515255880300c0f94803090208100c0254044e04055000c02c1e1f840720700540c0b043c1001d8055145894200791454542070b01c1c01401003c0c000416041401038402c4007031650700c0141c1c500000d680e10384c03c1012403458016242c101d0074107000403c01082600403500a148508902c0e8100031880d640d80c1401d1a11071010b840345504020300da8000d10400003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 970368741 1250 970367491 970367527
    0x9020702240f0d06032001080a0501030503040312020c12011a0f0a0302101202070309061103120a15080102190807050f0909070c0f1b05010f02030301090f1e020715050705 75
    0x5440380060013640d00d80314424200601030381a020282202c0c124030300c643c0c0000016800c0402c02d4000c200b2503045640343c81d40c900c40c600001d40390681320b414051f14244200400420f2000161258000c0f40c080d11a050280c11011040b04090410021005080c240307010240c4a400e002000c5041040c99902401320408540201d401003080180001354101003900042042c0b9110f50f48440c451490140014200c1000413801c070310b01c3d00704221841c5000c400b03074402504008000c6001941e403015810580c12020704d50702603517030f0354004615540c01d40c2c88103481c003034494002d072074484041e0784034a01140c180c49100a503081c0c06d0000c0c4003002c0d590520020080d403015203810000200300d01d039240d54030707101c3c542203003121200d000b83c451220b2507102c000c22a004010a00f0300000700d540c0010b000c2d4690205001c0d103049955a1540c01c492003505801c1420000c91581445080019101441000c3d5100650035107005401503140ba5141003d4450b680c1b09092079a1580d080130324190300624124 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 970369991 1250 970368741 970368757
    0xc0f070302030105150a0909080705190b01050a060c060c091502030c0601050a0b04030303020c0a060905030a0215090c0d080f0304050d0905030304150807090f0f050f030a02090f04060906050109020702240f 90
    0x2490038400a0004bc004104403070b880740340c500b28034044402a140840032420140c02042c0203d034416010407100fa013010b80103c070140d0040021414142c81d02c0111640e4069600480c1c47d80440081c2214064001c0001c1ca030b8040d142090310741981c0c0750803d00045d004540f203800b050010070030003000403a20981c05004d00586140c243c0740c8050b901d0303e0785401d4420142090350305030000107000d85482c1c0c040007c01c0c0300503501c170340c1036034a46003082c5600d448408410945001c1c880e0b5124040404c038444044038108101d8040d015100e0900d400d149581e07000c02c01d86c28000c14031111000c645454000b01351011100744007440d540420031240100c810b5903001e010b03034044c8410841d011881c41d115005e0140501030f1591444060fa280400700044800e00403004c0780250014107601d409a21120590740d4003180002e00003605031550b1a0917001440140c0d0068901460600081000d00c06900104003ca00071940d0409001460702d6080120820103103102030b009003004148070403112600600300007 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 970371241 1250 970369991 970370003
    0xd0f080430170c120d0f050a060f14010201020702061207090608130305091f030209030106050613090903020f0a050a0b0a0203070e101101060e1e0412140c0f070302030105150a0909 79
    0x9202c030484508803d40000480c0c03211983c0b200e5034a8145601482403e6114244a43c2405032032b2425220304c41c3e60300540600101c0402c16034560714564005d404413a07403e0740c0503046950301c0b5032069114080c402d041c0c4100f0001018800c0c00181180b01d0940103000d812419040b001601d001d69080d62150302411000d5040b0399120300d2102c0c0f1603042c2e07510301041081030702c01603502c1604008040c00c55040390442c0d80719200601031154001c840c01c011000b59080b0480001e00c0c20b4460070141d01e000f420000b01ca00d02c0c45001c1041c41040000b003460095188034040d401c080e91101c200300030580c041100c89030001424902001101d184c446980036540d080781c1003040c4e415044203440c50a59945420084640c103541092007191001c125104d6200305901101c00704a080695a448072503d101038600100718016240010035802141241c149070300d400205c48400503038941c03503030b2242203500c001c1e4425481c02000805280e0b8030b9110221000e030091044e1a0b490a103a416001054100b405a80c5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 970372491 1250 970371241 970371253
    0x2106070f03111201081c02070b1806191b0503090108070e03010e0609070602190609080d14041a06030d2316120509010804020d0f080430170c 62
    0x1481000c2c20040c10b100c84245040003407581400d200e00d140c070360140d0703c0614140b4240c085182160740400c40800b41c41e607245110b65500008100390070302d103d010401b17652201d400178111001c1e03600c6804601005450703840e01600048056114040e000081601525540007040305148a42c030030500e00b640021503003080c0300c2050f40340c40400d0031280306c0e01503003d041d84100705110791090104102001132801c1d2008255458050035410880f0300310705002014152505031038400c01c8112001d0f100c4944c462102000a0312000392007101d400c00c19141075452000030a51a030940128801c41441640082d00506601d002520300721000f030700d11078200d49010b2028400d11802c0340b02c0001000c140300c00821003022140607007010b680d445400c801c0d400a004080000e408030347d070440706460b44990100c0e860403180109042c000918014004c3c0242900400200811700340010886d0801d000c0e440e83c4110f901c82203601e41a61814440d8501a10304480300d6006070140c0d0151004046107480c01090302e403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 970373741 1250 970372491 970372511
    0x50f010c0f03090b0315030c0906010221221d0103081e0714010b090a060303020705091305060403030c110111040506090d0b01060804020108240f010507080f092106070f03 75
    0x50517041078502e0710f20010352140a09451a0812602c50070240850300040319041400000c0d5451106c1c000503000070310550000c402c00b44158054442241da1014a01d84e0452140014581d0a9640c000c000c1d8940d88010151050202882000e041e03039801040c243c40e1040d402d0012020880e080301104036107030104a081c00056016404034000c20901001182ca98280d10404c00c841d80010b002c034010380d1a060b82003020030f07400542c40b021504142e0b100405600c80402079610200c0da00b8006d02280700c1c10f0140004c050f41a03000100449159503958200c080d4100401c0c240d9100c1010403000701421b100034030481c5055402059a403500408038040d5101641d151035006000340e0145020481c50b004010035940c0200070030ba4881034521207240c0100b494040240200c41118400380100581103850030183d020b001250300309a00502c0721900c034801c14008403045c0d4001c90762640038150712031900d106070000b0b0403807081a54145020300003554452004943d03075400e942a010425481f103229070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 970374991 1250 970373741 970373759
    0x7030504050a021e1305060f06030903031b0405061201080f010c020303011806080a0302010b040f0e0604030c020a0f09020904110405010c06051b0d0e061803040e091606110601050f010c0f0309 84
    0x2641c0740030750720010946141c10f100708001e00d00c4203c238003070090400b0001c01559039408422694003800041d10040450072074405241140a50b401c155007106000905990b061808249241252030707510850345410040c2940c94207a031014110704015072b0081c0014000722000c0000500104844180040c615544d515500d180119008081e00940d655260f1501c050034070b40945452050481c10a0007140f0440d8900c0c0c3e0f031440c004101400304940c8400c030b00219910030106d030004080c03c05c0b030700511079100c050f020004e60240302d0661080b4546840c1c1c3e01894070b010281c070101c80c1c3c16144d492000e10640ca596015040040c03c1c00045c0e000020301404482c1c1d05005004250100c60700001c04c100940d0100d07141141c050015031201c150075440401c44117000040782d00b9684c3c2140d00c010300b0344841c1e84044c5040c2c4101d0440c0c031440340d900c1000c105198029148462200c41508031500360742c0e03507010300180c0c00b10311290324002225059840045408000e55414292080c500f00354541e607034590030307 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 970376241 1250 970374991 970375009
    0x2301021e030603010b0a0f21080a0f08060901050d02010804212a0308160c0203010204062c150c0a0b04030824011d13050705041d010b030609040f0c06080a0507030504050a021e 77
    0x40c2b40480e0310b04d4200350440d54045ca035164080003d44050441d94100000102c03441401c40000303040090260014003000a44100800303004600c46035000c2c0c00040c0c03403010748901034035a950101c42807544103e50340320102c0c9141c010302c9030301900d81c0100d03902c50b890310020f4540e50107401800e0140c4200174200607207003480284010000396a0701c112103110000c07104040f8018a44c0300d10b140b503880900780030543c2c0b8141603040000350042d41c55030b04c00020f822541481c280320b0b00602440080703000c00c801e1540142c900391007403100740c101901242400028840c010801250740d80006c04030041424200040a0441213402c0000c280c1e400b0420145a0b450988204030f807045e0020310089000c00411420300003407103070391040180c200035641c10041040e08501004140511403480341c00400e0a0010103500101c01d01d8100050049854480d403000d00044000c0d01c0c80007a80b8544000540b41912034480c85004541c410b0103481c0224440e000c015038a01c0e44840302c070300c00c16070450008099444c0984 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 970377491 1250 970376241 970376257
    0x10225050322062007050f1804080714061005090703021b3012060409150b1903080702010c08131205010c0306032301021e030603010b0a0f2108 63
    0x41d12845040c0301004001404e075034400303d00e003407544000011150010851400f0307540d040d6400403140300c003080001c0c1000150000040c1c3e00c01c0c003200344014400808014004607004180e40e00c03a44c2c0d400d885051b60780c0c0080350300c559580e944020074072442c5410100c0c203800c5178052a02500305112803a80141b4506480188501130303004e00940c05a02d0b00c4103041700621640050300c9503000381c0d0300e11280d010b489800c41e070901528880c40018215961b0740d00a00ca42a000403c0320f42c3e65290305486002841410102442010700644400c00346601d0010740d1709603030784a21040e08100c2036500560f52009614811680c00109210004515040d40d442400400d800700d80703620301003024107115003155003a1000c0400c260900c003040c00421180c1c4811003035800c4c20011701040c502d40003c040e0090144a408204401021801140400016000d940180c0045000700004241c0404009000c03480f0b00c2800e43e102c4081c07034204500710020348001244d940751800d44154821590b6407007004ea000d00e074 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 970378741 1250 970377491 970377547
    0x3120204151205090c04110d230f060d061d0115030309090b0105070311210403060507022d070305060405010e0706020c0109180b120c030c01020102250503 68
    0x1039030411a500240c00c01e034400c070703941c4100454100b4400b01030300c8102840740790b80681d44940081031f08401580807103c0c25900c0880c104829406100c14130401e4000c9000740641a50660100d081c824030f4410305802048010002000000580c0d80c6070302a108800083c616602d1207020740603042001c1c01610744d0810660307140d816007801c0d4640a0010082d035008807003e2807038a0700c1050b00743d03003100403070360816094240400700ca812400b04614041c3c5045100d0040007000c000716120300d07481800f40069900c039130000d00a650700d42d102242d442a103402444107000d080c88010259460000c0400101c900a400741d543e280d450751145d5150034010348003101c0681d03464480d07124124040c0305600142c00588041c20150240c440020080c64150161f12010440428041d00c5c0704600d03805000d242e00003420481000d100c5e4110f0a8403024020b4441e4024000c7e05602e100d590303c1882241c440b00d07050a0509555540f50901035000305083c40d04640b14801041403c045d18142e1601ca520507100305 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 970379991 1250 970378741 970378769
    0x604020d0c02031e1206090606070c0603090311010509070501030e0f0a050a02032107020603071b031707090605160c1a18010801050127120b240603070c03120204 71
    0x1d10034150103210f0440fa0240040c08105102141580d4064200c0c101f11104142c580740d403000142d00b84500e803c024507248452000094040d0550800002d4a0003a214480210200c100690a861048690b009541c1004000b4070540d80a41e01c400125500081266242081c10601c10315243d10303039000359820381c4401e058004600d010005c01d1800541e45840c580501e00b02d00706840c0713600411000038131500c0c0c00300005407014425100b24004050308040e04000c4900d40c05e0180c03610915006008104504400042c00f00e405200c0c0201142d540e0340c0c81da8586204501051001c100f481c00440341818010720000c1c3c102440091640c0e080c07030016810790345940420b900e0640e00d1036042d446050000f6000100480d81c1c100704800020810740e404136a5507100b035100c460031020990800703204804940c0d503ca06000c9031856062080c0240406566031049d007d8102110000607010241d1040c420000070b50060700c1861042d4035903210741406811400d05c1c94011051342c2094001e0200c1300c00300 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 970381241 1250 970379991 970380007
    0x201180501050105150c0303042a03080a0306140a1205010e03121e06101d130207110402160f0c050409062a1d011e0e09090304060210050604020d0c0203 67
    0x88545c0300102d40c07110307802c0b9190664816580392203000051000e00502543d02110040d9100344003d041403051594881c0e54241e140d142c104521342004103074400081c039280c4080385042c01d0b003108051402008104c44801d0703183c00f8000742d0300c401e00f100850742e40d520307580a102d0001d81000540140000c5207120466403800529040001a174866945a5025030009100c15601c80748072000c5000c0c2d0b11310b00206c0c0b03010342140c01500070120400e0350303401c22001c0481000841c0e41c1e6019001c40380c4035040380380003035941d401040140c0c058208000845014500f940c00080c1003843c100354228841c8103c042110b07171701c2e00004e0889200c0d000c00c0d21810303100d176032003548041584000c0e06040c00718000ba44130f440c400e05004140380300901242c000714090402c003040d140c2c0549403c0b002145040c0c204c0030305a1600100821071091040214000c804480100c0e400b4a4044141c8064030b08540c01455180900c0c040c003800f400d809040f06820a0303003041720006030000ba0050b54001c000d260019a540c03415 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 970382491 1250 970381241 970381249
    0x902120a1722150201060f0e0711190c030b06041e0b0a1a0a091a1801030b190503100608030405041d0a050c030c2e0201180501050105 59
    0x41154080681000500000080301d10307154603030315446019140d4480c2074600301c500d4512040c0b8032461010700d244070001000c0c1499a1845800d0030503a00910015641d504001c48004003401046410520031000490542c41495801c04000f10300003100e403410303050612000000a6040159018605110144140120040d0054210500ba41c00308031502850064600c071400e4002c2400c5459207426852050303541e55480b88018140c590251101000420030300c00d11a030040301c000001c00c100007000540e00c1c0e2080340c0b4000402d100042a40781050003a00d460b0f0f150164034256042c540e540c2c4401043d0b88900411300a8203210051b505050346c100401c041c80c00b16441404140c0d24180718003400f24407408020355003200c005903408a018124480c0d1100361000030b111034881c61103041d4410061110004c3d0300c4040020aa09540005903524240010301d808404426813007000d180200a05000e1004100000301451000141a240c14600ea10641260800507601691104018401468 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 970383741 1250 970382491 970382509
    0xf1202190804241d220204030501110c0303150a0f0303020f070806010803070b100b0f03101401080f04020d06020409202517030705030405060a0e190201050409020c010902 75
    0x450400d2100c0038443c0078500402000d1045440c441d108040c02c01d1002944414070340340c003400c180119000098803403890b064000d4025200555656080a00b1641c0c1c403402c14049031700852031080510325503510b44d94004006500d5001480d0852220200002c5207100307080124081c510035400b40062111500d505131404050340c103d00c0654004400402903400004200c51189900c54160307169a0388446100c06130441d10341c09085d07c101700058170281103007113a004500c070b000300e81c840c41c1e04a0b403100d500a45251004000e40e0100d581b00b00440d100107281ca250070740c005d10052040001c1c041c0b9a440000b079030815031010001e29141c5a5184140554801d917000d40303103104c4103440c20040d0f002d2600b6074100c4c40001c00501064064088010300001e1311142c0c00944240080554074106101d000300170f0b40c812035055a080c016040031031600d4205004e0001c642105034000c14151000851981c070407410a076040341801010040042c0034281c500240141c07100440001901100038014401401 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 970384991 1250 970383741 970383779
    0x506040515040e07050c2506030c0e03062701050402130207081e0c0106320a08010204062c0a05040e0a05010e0105090609060705030a020a0e0402121b070f1202190804 73
    0x40290412a203000500481f500200d400360b10700810a050390800603140103025003130329900360103094200a601d6070501ca80b100c0d05803421a14101071014a58031034201c80050350700070350000c803070010007448080507009002018062211180380510031f40b24509440c22003403010b4200980415161200c4500f80715560007069241440d200c0503c0c03104541e0a904601c0d440d0714010340514030290303420340700e04070072001030304404008561712a03c2d210301500c014011072100c00414840050920050244d003080b10000c800940344051042c103200030400a450010342da80c2203480f8140009010800900034008130808410000505040030044941080e0006040368138582c00141805110365000041329403200c105180145c50302107010080714440001800207900c14000b00300007008504402400703009010702044c42d000d250780c14030640c84034000d851b0054503020350714131500041010010b100001c1030030b51050748d81a6420f049002401a00d9260030b403001c040100b818441c0041c176500d0040e000e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 970386241 1250 970384991 970385023
    0x1606050a06060e06160f1b05041e3b0d0201090201051204030509041b200a060b0609120d030b0402030103020a170a05010c0e130203010506040515040e07050c 69
    0x6030806801505044001c890940100c0340091000f100c405c03125040c0d03041c0d40d403020001e042000076060070541e124440c00d90340c1c0c000c0340090300001c0381c1c5094071402004c1c0300c05c041400d14440441c40b0010082c00c01035810140d204810000c0c0c0301c070132121001c18480a403d00d18408a440c0301000940c503085601c900c24080d07a01d407040d0040940e0b0080c00f80c9a11800c8043c607011b03c0d030b40302e01c0c0c02c035554055500c4483d0014141010325041144804941044071425516a00301012142100c0420003400c102d55010b80c004424607030100d01d05400848400101034041880c16840d07002065120f0320b60001400c0f0b68000b82c009560480d032600800403054000c035030a50440d4150380024001000c1d61040ca4200840c4020b540101031041c4500b86016030008001c201d00c450158001d44076600c001c21151148441052440341802c0c6882070341d042e0b030005042c140c105810704050040c02d80c1300c500c41c5c0ca0142e00510002071180320f042005031060506030741d12070302c50707044a40075072078401c9890b015890 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 970387491 1250 970386241 970386251
    0x90512300c030414190b010311010c0b0c1e0a02031e09130c02010e06160e0405011a090112020d02070b0a0207020306060114040f080f210403110a05061606050a 70
    0x442004042a2030700241c1181034210484c40042c2c56515181007541d0b82081c4000704030040e01403184200140e0b04890041f401d40004101c001c00450344201c1c1f00500901d418105400b1a1410241201070600703162603040c3c0100c0c146038640c103039800e5000307842100300583c070006404641100c420b120264024000b08803509004109000031a0306120020f0344803165902c02c1c0d400c0d2424800d41005121b10400801c0d41c02604105000640150030501190089143e060b804840c608062143d81e0484040641001c10a00701040f0029140d100c040114104554209040040034451004020b072401000700140d0fa10110714150314441c0c0028220759596205100c808007503240824500e030700000902e003114141003404040ca2040c01150003803110b0b82113031840802d02c00c0c0700003924803000012801300c03070483c1860084e03030040c400780c0d41030401604018441040041c034103102c4000f200303030300414045240d034440000c50301c00c0e00000c80c5209a8074400c4041018088a4030840d50001c0c0c0702101404 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 970388741 1250 970387491 970387501
    0xc0d0801140405060103091b08010b1504030b0402031608011e1a1306180f050604020a1e140a05070606080c011b1703090f10051003030309051230 64
    0x1c412001d441e44580100d4071100018100d030701c40d03440700c000c4030340c400030111401080041c150010581d601500e14558640703d440c40c0280780003080c82c1806003614901625140c03c0d070741d41c44a00200984100d07018800c020b9403020000c842c4d46042c0180c5503600002901211508103e498401d6107030130b10b8046407074103c900c400d8040840e034100c0141000e86034100300949022540c0014607856000301549000300044600406050700110a8446002810311550300d41c181000102e1194158030404540c8400e0010070f130701c080080b902d85002c05420700c04081842a01d141c84154060f000c4400020350020310070003041180d104a1001e4200b000050040d2140324001800c1500c80b4407259004c0e481458022040020801d04d03055598158002c05407a8140301080d1a0f4075100b11411748078501031204206c004904174483d0a124a102101c610b468a244d900c094005011403030040d07030b0601400c1003c03a0801d1500004140c03002e003480d02109051244030200c2000a09140f90281003003600301801 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 970389991 1250 970388741 970388759
    0x409050d03110a0f18050307090b0f04020306180c0903101e090503040b0d0b03071415270d0f11010f020106050a031b27110304050a150e120c0d0801 65
    0x2c4244e0094140780030034220b0b5450603c04510590700107a07152003601c0300400e001d200380e000421240021b0718024144102c5004120070b9000c00c5800642090704d8090303045844c0490a1a0380e0000640e12841d032a1000d00000309061441644100001c1e41d2250504082440c0480c0010407055580c0400c11800c41d565892903180c0c0710300e11400c0c2d01201e020409007507005507640712008001004007120304203039070740f002803000c190990f03191885121410082041829901c0859100c81e494025190121a2485410100c03809502c0c405800c150740e00e0b8204001404000410000340c05541041d280520780b8000510424600a5000442e41403540401c00d031385844043d01d09403984110180728404014608040720065580403051810003045110081c0c5020007280743d2010325034005010201034a000035589110a6400410551110490300040380340d11a481042e518100f5002c0b41c4190725540f070600c0c114110244d030891103030000e030010319140d08000c1d0108800150a0100c195031500c06a2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 970391241 1250 970389991 970390007
    0x92609012714060903030705060f1f05060f0403050604030e040e071a0304052a190501020c010e0a090c0201140117060403031a090106030e12090d1502090409050d03110a 74
    0xd48440c1d00c640361488003d681c0c2d101501e1001c08081d0841340c60b8a143d0500e43d603905800c0e0b03121181c520111000c210600090340800521413109015078180c01c0c80d00052124a0f80a5141c080c008401840088006281880105e01031402a51180c07410742640f0b0420084400303526500c06558000f0f6010003203a02e608840c5552210306048403500c1e59a9420b1590400a41c25040a024404031030111303520800810a04c640da0019601c40141742d8105c002010014440d02400e07025038014403130091158031500140406200151000e007045d540c6206100a503903000841c00090b0f5111008001407141e4482c000d401808581c0c624602d44440c01c3e4076a44a41c4090300181c101915125080c1000c103a80c002400054409010f9a6296950f41c1e00180208423078401c452081c003644a110266054003819241c10400c003e0140311841001d0b95280000080b00e040401c00781c0d001d0011160b26038a51048080581c01000640401e580d0301a004007103070115000e131426500c0500c8040303001d50740503000d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 970392491 1250 970391241 970391249
    0x51c050a060e161b0b0f04120903080f030a061806051305100e040609051603050f0c150c0f0304060e1009080309060306180408130b0702030d030926090127 68
    0x42410480c420f9400c00300a051101c00b4244400b001705000541502d2103d4600c240d0148520208044109504a0b5500914440646000018820200c0b036080c058001d5400010020703000031015600c40080d241d128400c0c0440400c19a00c0c070080040782844087da102800d15104200001c2c03901c100c44080988040c040c808600384a04005070801440354442042c083e00300040703480d92820074290741103200041c081140d041c004e00041c2d0407640000200c5001038a0010408507946007481ea06c004c5d80c4d000365000c05014402e000e12090350420502c0208003828155448031010104041800101344800401808100103e0000c20148101005481f20843c00712040c0344d40b0f883e0440010f18507102c0e000d00c8014891043c00b40000c00a100008101c203030f82c00c0c61081c0501e40e9981c184c0b002d0340035024000c1e415803c1112a0341c011071080d0310502d20f4621445051000001c0f0045409064492000512614900203060292917030031024003502c03440100280d5000384511088000d8020181c81 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 970393741 1250 970392491 970392497
    0xc0c0c06030c050d0218011b02030c09060a03080301290c19170c010b0a060309081c021201080f07091112060105091c020901080a120f051c050a060e16 66
    0x5485040c0d441402220644c101410003075440d88508040300e2208550009494081000341440380311a00e020000000c0749500140900702010101e001d101c840d01c4010195a4400b0b624040400082c10b00009140070306404007036014249542c034201c0c090700c044958641c0b01e04109100d40020070782c0009400c0392070304405d00c41840b2038100f450700050400c0480703c0b00d0100040800d0001800d03074154407801806600704d46642101ea603401c4140c085900e070503c0640394400800c0708a84000890381c0c51403021250312001803900c001d043c02d80d4074800c802c1e0441412900403030111480480c0411400001d070690342010000508666030201c0a4810080c8003030f5900404800180e03580c0c00340c810b0700c40111014100061102c400400c0c0d031711b0b0710920402244901d050000206852100003054140c155200400c00039401ca40340e400d8507510b90500c204410404100495500c86000d0403681d05c2c4046010f1000c129814100c0d200d405a6015400640403c9050400c12030045005200d41c03c005820781 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 970394991 1250 970393741 970393751
    0x10b040e1632030a020a0303030b09010e070c030302090d0501060803040f0b1611130c0905041404050c011812030306061e050a03180807050d08150105030f07020c030a03050c010c0c0c0603 82
    0x1181c20051400c801170b52005421b0000800e16030160032050040600322400406681c861507a1802441d068802000142d0101224000207002e0b500400070004d004240fa859442d0340e61342e050075201181c0151030346410105042210340389a1118601500e1112101803c008680b009018243e0026002a100e40c410742c101030004d03100d0388585540c0040c0c08000b440a02d044801c090104d40140c4500d03401140b0b082188424504006c500038043c0f94040c0c09040c0c0c00d03454100459042050000e14900e0040007100062914017800b02c00c00c4403031007601c0200d07010b890640d01400a207203100794666180c500c0c0b40e000d07034900e6005d411030710b4001d690b0034002800e00e02001c000000901c0324000030300780b030300008440c020300c040024903101d00290740d030314007070030381c0e5120103441c0174000440403d40864024004500c000480500c03603a8008924812650001d04400c00a498100c403800c1c184d010800005080155500c00e00500c044140d281c200400d0301c1d0519a43d0311807280f0b113440783c0c104240e13840b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 970396241 1250 970394991 970395089
    0x504030c0816060f2301050a0303030e0709020d0911010e09040204020f0409020f090a0f06120207022b0303061a030a0b040e070e0108060609091b03010b040e16 70
    0x340002c0b00381d1030304540c080120350440314051008000701d2200b48412a44103c43d004900e40e02c2d152181625030180948100701e00d15030f400d4010348141e1107a01e81d103006d00500031400790000c0c400b0741604070300d070040880e040503113040c580c807041201c1c9141c0b8100040604a10b25030340b9181255600182c0c16a4016590b00302030380c44e000d090040743c0000207528000103001c02c40300000790180450b20303811a030729055155100040018000c0300c2c4160000705140d140003001000c003d6003d05003050004e019001d078403251030803607540a0285041c48a0700740b954900b1405055052040901034034090b02c10308504040030681c22824000100040440d0b600c0303006107803c1c0d4450342c01c44140701c0c0c2c125040301d90381a12a074820500d40e80900400c4468410030002443c1c61070504001030103054044003400c00103160403190210341c80305010083c1c0541d03e4404c090341a880324843e0205445d0340d44040c00000a001c504505550095444039807020300000c80340140800b000d000744c1701e41c014464690390368a08 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 970397491 1250 970396241 970396267
    0x815030c0f0a050a0308040801050c09090a1119050d1b141303080a0206070e041e09062c1b0f010c03120908030a05240618060f1902010504030c08 64
    0x241d0f400c45034009002010000030010030350090030039075404400901a555441ca1442e106008041e6401d0740200228042100701c002980008501c08042090a280c101040a04880311041c607403000d00044001500c99200c84152141240d810709883d140900d1840141004014504152018415007800a81446601c4820034030500031584401c5807619404884d402940351a01140c00f00d01141400c00302c65458a05845520382a07000121181c00c81507003014524020b01040ba03080702d02c542d4808540d14100241c1a00da03039102d001452210132501015200350078203c3c12160062010281c1519090399900c0e103091001c0c692003071800740001c06c50350400b211542280d07699000518540050301090020b414000d511a5030200401e01260f214080c0c0d9100740b12202203502c082c0f031a40300b8a05030074642140180000000e4041040c451841030001920a40c0003415092170385c400000c070300f400c0350a80c41c0174656004050008200c2454207031009080480f1210000b41501400a800405a54 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 970398741 1250 970397491 970397509
    0xb0c0d020a05031b1006080c090108070e0a1d070f060e0303070f08030402210102040501080c160b0702073c0308090d3e031b09060607081303030815030c0f 68
    0x174010100f88416a0380c0d4102d07075102c02ca06480a070280007908008102400000780c440115505814402095520391407076000404030754803c0c1c8100039170001c2c0b021074140e0400914003c1c0801c0c4c3c5a030240c0750f2504230082d00c8403043e800018069001030011c0e0300070034031101790411529002884c8a540342d4843c40020030b211149400308600040c07071510245400d0056011300103031003080e02c0d60b180b10389400b00944000d00a20340745540c580c8032a0941341c0080d000c41022038000016004645400313403240c00344144196038607440c85041c911049003003488400e10800d00480a102c0c69031113100341c15500c82d14818851801814061444003901c8000c0124003540c101c90100100d49002640745031420344c0c1b120002c3c01c1741c00100a4007c00d81c4507024600400c1e02818003c00c2c0e50401d0f0305900308814070000c6000200740030703417140c028000d84003c21417003001404000318035800da88030b8500b1890082c00822010f4503c40105000079101400394400244412000c80e003201d1206007040810300003100b100c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 970399991 1250 970398741 970398763
    0x10c1416080301090203100e0105300f010915020301060c0b040c031a06030606120a1b0e07050d050c0f070b0a1e0e150f0c0a02030409060b0c0d020a05031b 68
    0x11000000005520701c41e45d018500440008240e12410b59a45041c1c0c8071218003070048a07405450440b0469031071070800316100caa5034400802c0007154007000310a41c1002510040d07582c00341d454000302000c0084442e2900340c096919803045040d5410014020103010304036030020801c0c0e010901090610105000100040d54851000c4000030800c03003900c0d2490070305a0744c107402407040c1000718801c0d1500500c408201e156480c0105800b48607078031410007101808041714901c540c0502e0100b030390807a01030030300e1140103030780c82c0d40f40d0700c1d00c0030400b840840d4002055010020018002600b0821404048600321500221075403a1034403102c2c0c50314014000c180406668205a00300240b01a100d6041803102c5002c3c201604c7c0d5040b048c44001c1441c4030103c0d10303004400c00400c0020100c101d41c00c0a48100281881140c0c117082c0c0300c5034248107c42460b0003290000001040d10b144540c004c005c01c1c42c1030481751029207650801603981596a001c0d0420b400d598540b10003510300780110803c8428811 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 970401241 1250 970399991 970400003
    0xc0207030b070210020a050403110a0501050d0f06050d03080907060c050319020102131707090e060408070510020304050a020f040e072303062e060504180b210609010c1416 75
    0x3c0c401c00c406c0541541d20a201c1191b0300c61400d000b45e00c02d407a000d144002241d034180c4075149455854604040205500300100b00410b640e02008620398880f80400a04284251500b1501d810007004081c0f800d649079008008001c488902e01001400110554284280c140044031003200c0c580d034140c3c06801440c1000220b204640c0000541c3c41d50082c03280007000d05c0c01c0a5601842d1105440310594040400b400c01550004010030001191407000340002d03400340c801e40d21000c0d00440200c0070790344162010b5500341c1c444e6a801c4190300e80f0403c8548038003c121020001c0c40330840282e0748914080c0b0418003034401c0100b1007036290304844414000908020140c910381d142c0400d10f80d50340c030101004180041d4900700702c8850128054002d8050380c9264039951300f4030b0314101060416030390040310347d0249900c074001da809540300c80b21005094030400944050072a003c90400d49000c80c000c1242600341e0404440ca01042c1d00a80141c2800300920001965024040309178050ba4001c50001005 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 970402491 1250 970401241 970401247
    0x2f0d0e0607030501211707080f0301080c010314040b06040b19090515030a0b160302090409050f060a020a0e0d050321090f01090206090f031c0509130c0207030b07021002 74
    0x346581540094140c80c822201861412403031031503004d1107070f52408000c2200d00c0e06d10240a5040450020b0098240705054840c5400041102010706410030382c0220b07001e51125095040640c1c26006d080d9000d650007551580ca46813684840c0483c60003d094640103680d11b41d013556003030300c41a241488203140d00c980300f158103980e031100e40006c0c00200e6005181d5060840300301c5192602140d0507d2064015498105030f4582e001d100c47c60300c60aa01950502d07a082020030020740300c3c0d000700070780c50b0302031806010000c03510031900b410120001c10030f240c414410440302c1c0750075420001e04005c1e5981950041d440c0c0e40146402840c5100d0b032880300c08180540400d00b00085007000007a44140f0040b01680c0781040d105071a9400d031804210002d50140c3d003031060200310708050f0001c07040540002c045801c800300300c030020801402121002d00c001030000031010031600345070030070f8001695426810049406c0c2244029143c0391180802002d5400820225031024030030095034100b2450080c00b159 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 970403741 1250 970402491 970402501
    0x30c0309080a022d0915190e0721090b0106080a090506011203110106120c08060705090d021c061d06010e0a020901020304083003100303050903070e010e01092f0d0e06 73
    0x141c14a8070842031040090700d10700d01075119000307c450222800e0b099200003c1e21108002e42d414044a20806040b40c214407e0340c07074048040c0110000d29006da040308201d54140b4800602450004119240660a12060780002000090704e103044640028680e140400c441c80c080b6008040c403a6218015800d1080108080598901d48080c49106854696001c0d643c1c2c08500c1d112201100c0e0310010900a00410610b030030081810000c461004004081c542d000c54082140341c01040003d03101e650307480700c50300b052032090205440300341d440340c0082807150300d000781103582607000070b1250000940200e00c83d100c0c0d034000c000b0386000c0c100c0d004c10b5503410042d0202000b401e00d6200c810382c1c006184e503150902a0151007003143d000303d004c151420001411900d080e01d0a5000400041e05449990000101000c103001035502904c2c040060290030351401100310305132407200c48000302c1107880000c0481c9100d181803400b6900310000c000241c69040d0f47c1c10300001448011000c021300d0140604003c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 970404991 1250 970403741 970403761
    0x606081f0e0912181c0804060806060c2a0d0503180f0a0e0901050c0304050604171b0102190206060a0e0a0603120e010816090909080405030a030c0309080a022d09 71
    0x80c840384103640305c25000f066084000480c625006014011403010007081c0003c910540d41650b00500c0649424075080d0322a803045e16002d205c4040384600351000c0da048501c1c482c10818a0f945034401c4584001c80079a6071980d68480c80340542c0b4048580d011403a41216860350f8082c5400014010400042c0c9540d980005040c20811900301e481e55103801f0009404040b140282ca000d660410300402c800d980d280e0758034460842400c0034068100c0181b01e00c1420340000000100e05204210000d030b01c4000400350114071600000401e8150f4001508000c0107460740f9000d40304645200c0507a5034140c80701c10380300d0010022508090421540702c40001581604400304502c107000c01c0e40c03440100c0e030b10344981d900e1400c1703107042010000c2e04c500c40c2005400a1034010740f01031405880603d02d17299a840000b444d054100c0c03012408501c4040076041450f0f000f2040c4030003498118040d1180000550001e14205081c00e4800140d207240201c030710000032411401d1520407000b500a9000b818100040 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 970406241 1250 970404991 970405027
    0x5190e120a0311010f090b040816051e06161704031e08061207140f0418050d11070608061c0606030c15170a091a0106030606081f0e0912 60
    0x600965800d0030580041c5e12020b100701602642c114038443e80c1a100ea0f920080e440c2d110405104070b000520b044140491014840342c0042c2100c49500c4030041c0d40c41314003c0c01c00000511418402400c04050200703030350405400031b164080e900c1c1c00800c60382c8618055590103410380c2104418903100c03000045540c0c006220300d0103240202c601c040180302026149990346c0b0680201605c0c18a250000c3d049818840c0c04511286401032010461111103900c800c180c051a0303005982a030300562000308041c0d0049200e11042c3d0b007980240c03440d41d06009010384250400b600c2c2c240580111074030920000c08541e150341c6883d921032418001503030f4074107001d00401c241e0f010325040405072289502c2028044e500118441400044e0354400c2c6d99580003080090514501c262561080154004c1d1155100385116000c3c000c0d549000451a0408030b00510b1300400801181c0d207007020b2140e1051081c0d00c01c410780c0440e101050088000d90303031000c1d4942030401e005410985a500803402c000014074076485 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 970407491 1250 970406241 970406267
    0x60903020c15070203070612140c030115020706020a111216051003020a020606060702041509020c06070c21020f010905150915130201091505090a0605190e120a03 71
    0x50392070703440b00b4450b0051544a0980d00039030640c014101005241c1c011000c004600d42c0410001842ca15103880c4011011000c40e155517003c00000010302240e2090054012795641910003440c05a04000001c0c1d60b6000c01540640140e1000181240b556911140c0f01480070060060700d0f40d8914240841d0340d100078a0141911070725000c9000f9031401c0c404c2c800d071040440395900404450721001c041c0a81644000c00c281d8025407550041540b06007800d039404020b1150500040c4d4484050007203609156001d015802004190219800401d00e0809107500d602c101f01c08154140c04034a0f0168580903000244407603c0d401c0924600500402003135040c0c413a4691144c0c2003260340e4054802c2c0e140c0c1c10005d04400800b0841010805822180b061800c8003403060611821036900c9100d51041c0c50318404140002410002c1c482c030490800d000c0c04002054a42131560600450000d10b220003000e03844908200164104c0364112076a81c1102100300c02c10710010342e8150b0140d800c0080c02c501114030303 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 970408741 1250 970407491 970407499
    0x40524040e062b300e0303040f0e010f050607030c120324030b010905010605071e0b0117100911011121120c090105090f19080c10081012030c060903020c 67
    0x111514070b03e40b0507451600001c001c201c5807098020f04c00741901e169410026064141c80144004100301b544070041c00c010302100c070350300b4031305600d0b1004080c02d0481641010f40180d0042c803078000003136008034000c5444d03540504020740c0303100f541104400034119a60704d25818164486003013000d03088000400281d81c0590580d100d00d0780c1310011201650020300c42c0d0b1000032401c0040a0103c1c1c0f0941c8100340304481801c1002c0001010340f184d102090007a01b04061080b0301c200c41480108040001501a841858042c40700d0806500d551441c51540144203040c85094407480342c0c40322060040785200c030b06c5080c1129040408030380b195410780103100e4500c7d00080c040003084c4140f2024081e00c00c1140165150b510748107400040c007460148020713009803c10441013202e14080c5001e81c20f50041c0c8045001054124951000c01c100c4243c5a0f001340240301240d4140100391201410000c10703503000145201c81000b65190441c0c9131400c0f483d002c1e01040c034200c003100806a0200745954822403c803 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 970409991 1250 970408741 970408763
    0x905030414040e1f2307051612030f06140120030c01090f1101080c16110913020f0d0b04060902031e0703031706011e1e05040524040e062b 61
    0xd241040305c0031001104400c444140018620b14824001020110440302e107500620200f580e40c2002000f401107144003080d02c401151000300703054450013000b0207603800c000d40c2c00e10118001800308070a5200041030b001d641095a0f044060810843d92101c82c158020418040507042509107050111001c80d80700c9504403894080c0d6220f5540704e8018144182d41c0d600d854141510121a1654032700110b0380c0130062840c41c0e98507914104003500c18030542d0f211041c40c5a0610400024210b8085598419440303000d47e4004512a000d449501c00c1e8407410000349207139a80002843d0880c0c602e0001400c1216401c60004000003040c0c801c21644a0740300c143d88074440b480844000312003145c1490016018200ba2482c1d0302400e4841c40380301d0180d0a2161002c030081500b61420300072140540003003100010304100c4d5080010814280c0b00c0011514510180c1c40742180781903100b14071031100e1910300000820305542d607158040440035142c41040300303817426400d418000e401e0b8000c0207460000281d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 970411241 1250 970409991 970410011
    0x180b0303120c090103060302040e0c120f120c01090506010f0f090501060c1211030d09110406060e101202030a06060320030604110904050a020301180905030414040e1f 73
    0x141c0300812050620100e49603100040640c050700400c4000d8100b544844000000d40c40300d114418501d800600500255820341062001d41d4490f4103006110380d100c004004106c0c2000300f00141c4141c2c001d511199203088005000b07000d00201c0f20042d20f03901403007000068482450007c0c40468249080c0074054595995695003150824892040070a03041e00d2904002008420542c5118519061070100880c5090500d49590000c03a00010313583e507200c83c030006021040241c80300c4000c3c1107900b4400941055801400c900140610602134a40141c1c48030075140078601c00c040301c46122030115203919010368010003406c0c0c54810080030038508a00087d0303e110300745400e000140d40b9802540b441d241c07042800001c200050809030500d5061000c01d01550345ca015007409180081c3c2d0158881d414000b1807090306070100c00b4140c1702860b0880c1800041d1000c03081ea01103814400540007058200e4010074003408030030100010502550044030040703540384206032042d0080d4481007218000b1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 970412491 1250 970411241 970411243
    0x5041815030f0206131413060302061b030d1a09070201020909010b0c071815171b0402040909061b0e06070b04170307081f0b090d1b180b03 61
    0x354400c0c4020400860300900101c0d841e4140a4441840640103034a0104c120609070189401c42d0001403090003140d07a83c1c00e05241000d8041ca0301d841040741000003625550000300f4a1140c0150032100c00c81d0032065994103a4144141c50500a511006022010320014024003100621440d20300c02c1040101207454240f0520030780d580c02070041c01001e621790803e0302c50076a60700400340c11000b5110f510000320b0100c26826410800c0d060b40309000c580c0c1c00e403c442103100030550740c0094902c950118000c4400c94030008070714a400f070000310003060548090010501a00c555001a508141462034010800415a0003001540031040d90035103e00100c643c12038101d00d40212803a481401401004041200c0000341a0441c0c0304120380005480c11014103011038000300c0e0780b0004100a8402c01c62030700c1e5403880300317003074400c503040b6003030030b9604140310422603004151480780185004184042009907e003002c513180c03c41003004e00c130070036510800ba08040c802c0804040030a41440001c07099814 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 970413741 1250 970412491 970412501
    0x3170703140a0b060910111e0d0c210c170c0c01140d0501120c05010309030c0311071701021e07020f13110d020c0c090f060d0204020415050418 63
    0x31244001001d5803240718855015100031565558440000c00040750956910000e2401c102641c3d12110f8068042c6606c0508025014401e03026600400b940618024004605000c4040081c100b000d602c4040f800c000d5800f445d01c0c000c00642c00464a60140c005030000c01106080b1b100e05050810010921142d04035400307018116a55580403210f4a40698020000d203001645405a40d9080c40d218680020541d1b0080e405002c202c0c400c124150140042803103920050003080c00c0c03d0000b80281d0f58000d00510f070348240902003040e9104800c2134844180034500007080c0590399405510760780a0802e000b5442940d001d046400600380722b181c0c030031034141a100d04c03d800030809503036200f5a0013070041028003214501a155a540000c1c0315112814020b44068012044010b803924107606010303140c078408068251055546104002c488030254090652008060700d40b60f0b14004540f000c94007038003407900007251a040814000c2c0b040c3d940007001c0c0048a11908402105503141200042258 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 970414991 1250 970413741 970413761
    0x1b031605010807110f0304150906140712050912010b1908060711190503032220010e09040f1218050114070602120f010801020a05090910080a03170703 66
    0x3459142c00286501c0c05418602c0c010070b10a02139a030002c8400300042c1c195409074200c419030124000065140a40c0898041c0103004103080c46504609643c1030500a4000c80b00c3c010510038a0400c400c0700c251040051301c0003c0c2000c2c0a80e40e040142841d840d010f080d03059540c0340650358610f038060100b0341e82107035a03084a880f44007800d002d4031054000c9410001485140c040c074332a14511214042e03a0b280030740d40103170140c000303543c0781d084c40313099071580180040302c1c0c425041d0890001c001180c260140c003d000206603c14002504032140140c4451034180c041680c010103040411003444109104404854400c4680c483c10280000d030649562442c0d07542000702d480d009000344019405071714224030080081801d681001c0302981c0754001d985c0708005c0c440040801400307010f00741c1e40c0c0c40f1145000d4480f440c029402e000380401c0040c074a0041d081d405101c0c25204e4040f41d80440d010200001500c542402d81d560b0449608001d800001c0310030380e02c004200500d0002d45850710130321400800e1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 970416241 1250 970414991 970414997
    0x15030f0705011205070903020a0807080c0a0602030919170a060c050705070614043c05030d03050a11030702070e0604090c030807020a0906060e0301150f18020c1b03160501 75
    0x3c4841070518038010a0010280e03c144280c19030040056500e0091050060040800900310b5034149440c00d800c000c0002d4290340100d5040005022554022042d54140c00341a10184602c49900302d080941600310f500c90070344102102002428680080b50034090180141d00601c604090840304603103600ca4181c0c05003007600110410b1040be0702c180317035104580044294637420507451300e10074400020030007090700708541c0c0080c00c2c1440c0004030310042da800b101081088071083c5803402003512900a1000302e01050f942c1c5c0d000801c41106a80012581c44403107008640380d00d800040a0741d00c8c241d500401b03c04440d1440011101e107483e015410125038041c200000c03a80c40c40c0d8800700c0d01c0d00440c1080740d014041010100700e003405846081c009040c0c640e9248941c0356180185400c542648580011044a010060065550340b00c030140c210741c500020000c0e01c103404001e0600900074011071201a000b00e81143c1c65074001840c4444007038008a0585103000542214101004075030301c50a804 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 970417491 1250 970416241 970416257
    0x60c0f07051c021314100302010e09040503041a070c0603151410030203040f02121e03070809010e2b0201110a02031509030409050c0a0207060206090a02220515030f070501 75
    0x60820a41c0c84e4410702c5065000b24640c03204240b180c1c3c80c3c01c0704494103020444001420825907a00c110300c7c61500f0800c0d10030030101d051545a05807a0303c1a8050085c21880c0c1c0c0f0101c07c0c42200010843d03076615000168111020344134234004026240c1400c11280c500404400468040d0345200003814198000f403210300d10802400050b006500020026240254101041005a00c480a00a1440416a004c2c0003048020140c40002440054078103600364018013544c00055181012078aa48409003131a8400c0b401010020b00200328044000349040780c400a40b11445d07a1301a01100c5842c404d0700c40f501110b0500d140c0d0380c0d607281c1c00140071754164080035040600a031481e08030313501320600d030090700d240a444050320070985e030b002d0741c42c6a2100d4002038090030f141c1c2c0c18001c0001800003840a007900c3d00703003401c50503500c07803400b00083c0c8990f07400d14142100179000f9008281c2054103403402d115501d4541010f40001d007181000c10301a002c0d1181007005042e0208008068501c142c4900403 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 970418741 1250 970417491 970417493
    0x901171c09060305131a09010608010b012c13050f0c0a080415180c1508010501170901090b130c090b130e0307052d06040c180605060c0f07051c 63
    0x181c10b02410051710003885200701307004125141c9146158262060f02c824141c10a00740c4142102d020f80e000f040540d1506501c1040c2e682e0044240c18815404005080b40c44600220f4554040e1810345955101d00301c0a071051800100790803070341c403c00d0803114074002641c0343c0445280a11494000340d0000d0403040001e40007070300381340d203411020b440e640b00064181c0304450001451149500250787d21090020104040d9921007030340c40244036140361100095151100181c402c510b000d202c540724103608400904403c400350301400303c0c02e0b08450122945c2c1010340509000540c1ca80302a0b6404440500c0810a0032050007540b802d03c401078003901c00041b41c0456500200890f030360004140c0800c11005000c07c2081080500c41c6840c66100d09a00341d0a10541c81c10803041400101c01c2d4101604100226281e110071608444004c3d650240c54802d07203a20785c005149641256a11a2003c6030b014521794000407042c0d00c0c0d2900408880b03030241c0711420001c0000c2802484156100d042031550 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 970419991 1250 970418741 970418747
    0x919030f050c010f020d060905060604152a1101020f0105070203030604020a090312020d2003030604020702180c032706011a0f0a05032203120513020901171c0906 71
    0xc640842d001000141c031180040e000303401d03030388010007481d003c0b503e50381c041c8582d104d1442180d030482d0045440c2458540390402c03025003440408414410302140c00796080d55103250b101071002c141075220103205100303041e2803d03491000c0f200c0485070040c4107803210400280014400c103800303416685c00460030342d662a410000039600c4401e44c18100300d001040000002c4002c41007000001658000e03102c10001154010400300e083c800b012000c000069a0501e9080080112904504155000740c0e03074080300d00100d2980c24070014039000f070940c2007003007241c41320584029500070480c3c92120480581d610b00d406140c105000710115441c0c11131001000301801c005940780401030031103409c0d400c1001040340d50b0929040341320410301140e000810000d42c8080350701444040c42464040c101140c0294500420101c240610314181c19990004160311520035240b58058690050413a85203684a84407849001c10b40001c540c00c0744140483c1401113240e502421004d60b80d641d8486000c0c5103007200c11 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 970421241 1250 970419991 970419997
    0x909120509030a021e18071b0b0402040510051309050607020313150207180b010201060504110733090204050702120307140405061b060108011e0b040e010e060919030f05 74
    0x1001c03100501300202191600c8035044948180c0040da501306603440e16000c06044060394110350981340c9070107a06e01000032784455110340c0082e015200019107586a04144005c106503410060b4003a80c000180031106e211a0040801c0a00c110f003603c01c0d54403902d001703036903d015214501c03400003602ca000b03114150b41c4605020032209903104031200c5030360300e86a40c00a5807600900e900983e4031030380385d1142035809008001c02070005407020095020a26514495030082140092444030200390084040500c1000e001c860f902041508105441010310b0500070a0140030490161f4103007030001e0341d11800403c01c1840b0b1000c43d26094a19550014215255512108142c0f5044402e010210703041e21030030060034076525510000125040700c1d807002813030140c0580c0600d040e030703041034020012020900b940755034075801c0550100d0224808000100544103001a0750f0603503281c030101345403403d8000b80c094010b90700001035488104908100211a1105aa003e000b05100165045266201d0402 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 970422491 1250 970421241 970421269
    0x70e09120c030904050117210d0b01030902040608160801140c070c030512030414120405190302130b180601050a0c110d2105090d020d020303070c0909120509030a02 72
    0x2e0b2850000310030000340c00c40e10281c1000302c1d0310740f10011030000c454042040446400c0400c0540821207120b0b0043e01c154418440303030a407050348540c843c60b8181d020b40c0001000c1c40d40100140007031a100e0f0a581d503100c6016070140c0c8030380341400d00054078500c107110306014060904002c0403165200c0101e407400342d0003100101d5180400120003c04a0b40911140f109034481051055803070505043c80030070000500c0d043c6000380c100004114000c080c5a01300e40448205031041d80c4104e943c0f810744100b202403540302035000001c605c6010108100c542c4012080c400c11a02402048002200d854106008882c0e8a01213001000f415040a000740f40000119210b25031030b0039060b00e00e0010881c0440c60744004c94030614240c980120342040340750205010045440c0c614288140303040080c0184850030310181c026040c40b28100b0239924140200d0f06d1035504100060322056550750300c2030003011100d4080e94180c40c0c407001d001103984240211016048024020b003c02c0350541c01300701400c102c2d66a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 970423741 1250 970422491 970422493
    0x51005090105130920130611120310030611040b0306010c21020a02010906020a0b010e04110d0311060f0f0609100909060902100504030305071b031e0302070e09120c 72
    0x400c6400c0300c1c41c10081c010180200300c90200d00400c0306005d55004100b0188094640c0e00248251855040e07480754040c1107681a10300180000e5644241d50b003480321a64043d181240b0000401564000020f02030040b40c0c030491003003040301c0c0035038440d030294081d6010340c441d000307420004648150320608000b4142c0e80500d40c00046050380e502d100c0340c625440c010f4070025810090908065681118022000b48558005843c05000317994500030312400501407424000ca42801090a02c080342100d00c8404c0342c040d001503003c585c141005000158032864440c2c0368807a28002030458849002024014190f0510000f11074407080b04020b42820001c010400c210142d0b140012903044c80c1c010f82d000d041c014100090126030700d005000071f800d104001c5006015080008000082d0701000315501030340c2000c0c21aa42c1038105109071641b01c00d9500142000005040d00c50312900814000d06040740b1940856480c80da481250343c0c3c0d4004100d80031109500320042103038a40b5004401403c203203404030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 970424991 1250 970423741 970423747
    0x2030d0c0212070614010e01180f0f060b070c060207150f031b09031511030408160c060302180f0310150b1201080f060907091a031c0905010504051005090105 69
    0x141042000f030700103010950303542e07407036201d1607561402001c0142d002d8500340010f0f4002e981401460342407141d288110034151555408a503000040c5079101500043c22400184151983c0703420585280d040401c0664104500c9000001c0c0c2d5400000d1001c11511140074602e030344090300805848804c1c40c1200c00b000d05444e0b0020501c541009501d4119800042d20740c0f8621070709504100541c80761400124910610b40400c1c5036400c0c06202c1904c0d48140d01c00c680f1035807108401c0d1401e00e03814488000403c080a003180100b446505600030300303031707a00304102c014401031749043c10442085240c0784000d40681160f0090054071074550401440c14104c01000303039080766904034141e002d600000d0380c00039000600006100c1c2100a000d024a1040100000e1000b814694043c40e11824075208044555581c1c1c4000300005103101010701040038000c4c26107440007480756108505204000002000850301500440d5a43c003400903603040d1800580403900440c6003207403c2e145940302400082c1408414 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 970426241 1250 970424991 970425013
    0x80d0e07080d09080a0f0609020319060f1b08070807020f0a0503131a0f07060b1008040201112a0411070c030c050a1d0c09030d2d02030d0c02 62
    0x40044000410074080100103802c0a00c0c40140700d1003068020b01c0c1c213a0007003524840030603280003844803207a8000c44000340c4010648000703072074810460580c1401110800c5904180b214075400f000784422007490900c510b485400d10150940342c20302e1410302040d00980814086441400d10720f03032080c924011280083d2800c64040d291041da428201c0341035000082c03490407840d04482c08001001a0242c44080c1c00c5520445005030080c48406400e02d54081200c4003406180e40041b0030401c3d01801c01108240b000310000c4c13103080201c909030f0208030440500101c0710800159004003e451502ea1022443c41d18100f41c01c40c002008556070143d203444904070322614945c000c05000780700303c2c0d560b181c40e031441c40c040344050003541c09544141203802d001c2100c04880f0740380103056521200a03030340e143d235507090305200c034003528840725054030400c1300c1183d400e50461106450101d00d000d060411030400d5050141e43c41680c0f14001c0140c000340140b800c041c400340c0104003108294010f45030020b40f2 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 970427491 1250 970426241 970426243
    0x3060b150a0c03022a0a0b1c0e0712030804051c0c060e0120030f130f06023103060e01052e1a040608060d03021b1c03020c1516080d0e 59
    0x2c5020403244903801040c0b028200d15081b4020300040000c1d0aa0508181244013140d031001514209000510788070014840b030003405001300740c007401896540303059084007170400400254045a003103e03548594080b00000b01030f42800c0c0b100380001c0755680074002540780c1c0e81c1005032119200c0010300e5034031114104412000b210480c04040b01c51500c1648915100d1001c503071000740a02010b8031000094030203c0440c2005040500060f009000565145800e611614214604003803081141240c8880304018203100d10211048030301800c424042401040070781400c98505035000c0042d90900015407428a8208200110307200d0766802c07545105907124005000b40c0c911605049030ba0200140901c511078102e01d00c190004801d94000100d1200c581c0c01a640b00001003122003018540c44001240ba503480c01040b400381c041c400e504882003218a006036a039442828401d1042d112890150b9605040000f610320010000b055824914203613140d441c0c1650000c2581d2540da9280d800310f00907400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 970428741 1250 970427491 970427533
    0x10909050f010608030a021005070c0311030d05040606320d1a0901020417061314030c03072009040803062b0f0b010609060206010e090a140703060b150a0c0302 70
    0x40840e020315170301c14024000905140c020052110a640751004ac17001041d07000b41d0f407911841d4541840c1c0041500c61102901d03500505943e031081d2400c1038100001c10210b50025404c07110410b911031142121070740e00c04031000345881609907403610b906100381c3d107291980b00c104c01a400f40710402ca00340301e003100e800ba248100300e03059007003a134000408120302b20144150311504034110303020f4455070600c101070686c44006454098440001628507401548080c030468400b1100d20089a03980c1405161008908010364152110b040d10901c000d64541004a081403166a000c0d2145d85183e8403481040221034180c40505003015000c041030381501025440107001c1805689d0400d4a100b1500d80101c190354141c111008010301c4580810503503400094650540f41d00d07603c1c140e100e41d030300103405107408208580940182c20f940f2503107510303c2d0045640d10580f40281c0d001d000e040031a40500103142c0c40740b4258034511100700014190544034a000c1da010f2407280c410741d043c1100c4685180702d460 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 970429991 1250 970428741 970428749
    0xa021c08070605011401050403080a0e19031a0609041703040303020f041d0601030b0a05011d030304030317011d04020f010c050f0c1207080a0209042609040b0a030803010909050f0106 80
    0x10f07588100521206500c10600d8072000803d103400c034a01411513481d0050745c0100c070a403406010802000600a54482020035815507011410064050344c0c0e0810841040840d84405d4103840507202040399030414140403803085070092021480d07596a071f04040c0d259070004105404041d42840400c1e51508030342c0050004100001c549031003041b00c235a202851101c0513000505052401c5400000c2da00c0d1203caa400b220000d081c080404180756840b0300854481410031549800000f501004164124001c5602c00034112805a21a030322106070482d001080f20300080c080004000090061400448620391101c040c0341c40e1545044580d0380610b0140c044603120810b8000603202945828041c0c0c2c805801001200184501882c19182035241e00c02c105010340108001000901801042c00c602425070085090104402c3c0600d00d11402580104004900c6103042060002440c500700c8062070130350780c2088540e17145034a841000030041c0501c0c5011200360082c0541c80a400381c0c20710072070000b0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 970431241 1250 970429991 970430003
    0x1413210519032d05060117060f060c011b020607020304030203070b090316092004030b010909080c030c07170619020c0c0a0f1406130e06011b03110d09080a021c0807 72
    0x2112083c2c3c441c00c1500c0e401008141003003010800c001c101100d90076030641001058407088204140380010403298419090403074040d40c02c10394121043d00c6035070309150031400d55a00360340040c1c90f2004104d03201c0c8035a10029525901212050110103e200004d01c0c030a403006040350a14030130b04d1840740c41828568403561301c00e0b54801c512001c14207000300007039448144010f03ca291904550310050410018050440c070169140000d504100a010031a1100d00c080d0080382d8031640705404088e0f54070418001d80d11000d6803d41810743e68200040e020b801045400e10702c0c0744441c800c51080000b9081101a081180300c2c02c1400952600c44195500190502d0b0006184083c200f120781c0c1035030045603c5860045a0400c88110b00d042c4060200003503031945211f89405850300001280c1010300c00b02c80700076001240130040c0030181c01100d0031400c8000e0f00d0603113010340d64548058996202030310541e01590842d024100051501c403404440f4042c0011031091283d2132a280d000c22500803080407114 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 970432491 1250 970431241 970431311
    0x30b100305090c04060f0b0c0304120f0c090c050d110f0c060105090603030a020601060e0a0317030f10050109053607030b0f0a0b030a141321051903 65
    0x240b0406000b40d0500311000e5500b0310445181520b000c80c00443d034821300f40103a4000c6444000101c050003210000d0020081a0305030402c58180581c1c0e0755105a401ca030a50100030000841910354040c030917a0075402e484050a02e050110560041c020350000030383c0300c28041110711400e05006001d41000c144100080c0081d40c1408240410b106000e0003207803195006000c0b13002910303400204a415580c0f24680001c41098205c0843d0b00240c803500001e0422034411a01401e5160f03510245204450841c0d00070340310f4861503514038a03807030316004003800211000c03070034800ca00300b034201e02440010605078903410410352352103424050b81c0c180903d0174035440340d01405076a86d81400350340380b4203d007100c0c4d91100c40ca2034000122610030b5407213070003a1584080000f90340f41000e80c0c01f180c0b155241c1040c05040386003100c8074600b00750021204441c0007601400103030700c002d080300007600d403140340d5200c940c9401c40d40200740601c00c8248035413608250300d40c40c01e50716010407190403042d0440c5518407a10 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 970433741 1250 970432491 970432501
    0x301050a090308090a080324040219020c01030b032d0f0a02010906110304060323070822054801090605030f04030509030c0603011805060102151501030b100305 70
    0x41280d5000e001148a540708100080200303051008803900030401e4200c0943d080d1400301c000c009204948152a4000c0c030100c0c581803007007002f0813190010b003456400d5590314243c0704015021221000c42c07080d0141c0c80f01009071101e2864000c3c90742d00c04a1580709080344212034400e18a8a660399030076060a4015200030021942c00c084810080d100030b0402c12041c0130311711005c556a0280d8030600c000c058036031180e0b1001151140948110007000c02d003802041c6042000502070203c143d41c00c07000c20440510500b00d10a4112060501da50b000c800740900300c0c40c002c40c0b00d8274512202c0c80d1820b02c1e0309411035083c1c1000454020703102400d031819041081818140054159900c07030780325800b80101041004110400b101445502c103505007400c0e5181c013120700110345800c0c58000c1d03840e0841c2c000400402c10100c1c800301120581607440381400190349180049840d10061800c28124498040108902c00e0001c0c407000c40701356040c03400007501061240081d40707160b080381000300802e41e51805d003c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 970434991 1250 970433741 970433747
    0x306010210061707150c1106040e0a062c0103060203040c0503190611041203140c120403120f0f080a110304031808010510030303021c091419031704050a020301050a0903 74
    0x40020203d07484840c1d2a17907a66030300074211000b45900200340300d1510b2481251a03407584192000341003810720086030b901e03151b154140240780a0044da40d0f440d60044c0c025146941d6042d4a11007100c5459050583c1e0b441d55483d60084e400240048618041542001c0f4568030104890740840086111071111140c050400100715074090019104a00c4100030502c0180300a2004284155151916150b01d90744801d41d400b01780a00310003001c03d40901c004440d12244050301a009490146048008100400100f5100207210f0340605011802c2034000f0503070b25008111a591000c042c050211b0250f000841951003a81304480c100c2c08a6002c0c6000904100340b00a07001c0038045110007040340381880210899441c4091000404054002581c6400012191b9810502c1c903840c000500c50300c4100d2811540b0081d43c140d1688080c41219a0000044909202c3c02c5203070740c040d20340c6988a403c01c181e40040f1180100261042e200706d51010005032024030030184281402071001036480030920b401 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 970436241 1250 970434991 970435003
    0xf09040e2a03010b030d0c1b1a0307110601060f12020c0705100207050612012c0c210103120f020c130e0c090a274103030114010201150b03060102100617 67
    0x104401c03108040701404101e2180c61f0740209c4121490b0102e0322030340c4801044a0701c5400079039002c51402580c0000882507000b29800f04540b420341c0780c132440b80c108600c03032070b0481c01070500f17800180c0c1c40b00104000600305413820350110102441038131119070711440801c129a1080240c0007090f000d4900400081c00d88070104600c0013a07640d1180391600c2000000f070080040035180406208001403001c0d10700f0b0516404141100c101180000e26683d40e050503846450305c0c0703842c440815801401a41501e102040070111180000c04038120340610003030220041c100c8218015041c031400d01e507005036136203000070b4910810000b2808204196030203a4940c03101c04211f5420015000200c0b145d0005852a07030070340e014207481c40441c03640d296445100c042e078650001d0700e034503407003415041c004866070106c01907069030721a01011a5203103503c0012800c030b0741600e250070560941301d00140100e00d400801103801c020305104849001800280c0c40045404551200d444490b080002445213039050100c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 970437491 1250 970436241 970436273
    0x40c1e17010602150f130204060b0406110303010f14040207200a09020f0702040f1404081314060703030921020304030209060405010303080c070303020f0f09040e2a03010b030d0c 78
    0x9004642d1400c40c031195118070145ca000d010302c20b4900007802c1059000c0c1749a50300b54004209020141e40c480c181e00807035210740110000074000003006265032038008100e03070482e00c00c00321507846240340000c1701d0032000c0c0c030b6260194410340030000300c004a07000b05850740035204a44c03940c00d205190704081103020541a0b014a0201d07005102441008410109850b50f0a40540380400c00e445017141352030041a0508a0405030b46041c1c0a1100f4440d900010340b200e08603048106803020b44699001102c203081c00a441d034021010840b00780060b201e0b4022a00c0c141c4520590060314030360101200b80024a0740103071005070300125040055141c1604010340081d016602041103504589008251340c0b8000d00d07a82a0365030024010040500c2981200c420b200040380858903080c003588050a280e0001248a200d5810aa400300c66000c0100305005d5007960352980013000b81850180710301c4040c641d140e40d9859517032240c203c2503c4c0c030188500d900381c0c00c071380d0f641e16114003440c5002540e03000f181130 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 970438741 1250 970437491 970437493
    0x70b0f060333040f0b010b040314120a1101060509360a020d170d1b0e010f0e04060f080102070302070f03150f0b151b0c06030402040c1e17010602 64
    0x200c4520740300c908241c841d0900300b01080c030561580d00d42c20440f441c070728506001404982c081c000000c013000c075180500b0a403403003040303c01c0882c01d00450f425581d50403601c0781ea0611034200403c2070000e0190f4403880c50103c04c10b001103186655500000c006038821a580321880c440c5448041000550280d40c0440c0e8000d220300c0004100c0183c140c540d2201200b1009004103140b040741e17000e11501200c007850391210700b070405554052a4426401400a48a503d51010051a980c1001d0740c007810314250b205078180e40d85035042d0032048080316035540000c003d64000d0707076071240030070b0345040000c0350006048410005039a40b5001d240080c075122480c4e025200318401ca1070f0500000d01620240d0592411845000c00c030380c041d501d08000108800700c0b0281d884030003010040b100b1100c40300900340d0b84c101c070340c60b02c585800c040d400320791200c4120b040399900c900304100050041c80d15508c03030802403000340380000c40080c0101c1e07078441c40000302d0020710100d8070711408001002040759466001d401644 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 970439991 1250 970438741 970438783
    0x20606130e1e070b1603110d020c13020702060301080102090f1206060607060f051501090f050f0405040f0b040503070b15030a060e0321010905131a040206070b0f0603 73
    0x44196840e5080340c182101e5900004000034003984081080c2d201500a000742d841c0e80c3c440c4d03040c00240303000c501170044010400007018191507541c04248000c1c5a48036401500440c48540104004182010b40e01c0340d0465081c03110340d02503200c24000e94068080e0f01c0006a4964101c8104044140c83e251414403034503101c0d03041c01010401041d9660030a005848080d110500e924059002d0f000e00f46000c0d00b41d40c03615082202200040001030900102030721200c042d15143e0b10441d072a42e0303283c041d454000c003003594060050704055012a0b1300600840d45100c05e0010b030342e50001010016101501c00d0f500c04900c0806214100000c182c001480c0b2051100320f00005000c65240c9001c007001402c8180c0e40d1080f801c1c554024021039205c3c1c41c040c3c80c0c5602c0d58401241c4080894401e000ba00f0001d440c260000d0070155610700a202c1003600208a00c0031000003928403000010001c1089030401e109121540001e1540003405004038980c0003000d81034641801490b144c5a01d8a031186070304116a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 970441241 1250 970439991 970440011
    0x150f0c0507110f18040c0e0702190f05070e150f090c0903010b1504031b060203090603071718251502160303170a0209011409130c02060613 61
    0x10200d445455200310104031100502c000510001404805143c1000d0200041e00580040d031107258440d074440c203940d9821035240c83d00c403400d01c5000c88410001da88101c1030700007400001901020010320800035000340e6020381c0d072001d00306055503000c400108040014072251084048096aa1580c00c0e541d0300102595040013a1a040f005002e00da644400003401e2003064800307402000640501904019000101507401d44840d4464442940c0328500114105022508090700030201e0321a64000c5052102c0241000300e5a80094140d0703061001d0050148100122004654803130942103c098484c04001d880541c245078a00c00c450555540074444101000300200412080d100300c0d0a20300485043d490041e0700d086150781c11081c0c05559880700104056000c40600c113541081241c128850315103c08201c1a8081c2d82c00960101b80711107204480c109415014208100e00205101c03039001418820303000716041c940c800740050b0042000c110460801500320400540c0700b0004001038841 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 970442491 1250 970441241 970441247
    0x230a0f290f030721090b060a120c051504080105090c01030c0807091e1d0720030307140403120e04050105061c0509120c06221e05100603150f0c 63
    0x10f090b901413000b800c281140300c510342c00000c09901d212050421801d81c190174111220802221080d01c00d1480303603400309040303865080c241091907019074181e400904000400c032003d00c0d90b00c214030300314100348000240c1ca05c0034015180500e005101030b003000c404036000101a640060011800e0102d100280065141c1c091840f0044400c0204030501a065005c8082410f50b19075014908007542c0f0201caa512280306d12240d8014101900c45c20040d40305820501d14a82110b401001e5030342045c40001c0e00c2038000c3d40d41c5151203283d4010940340c00c0d22596800c07000d0030394054400000d14440c0c002209410584210341c0908001c882d01c50418032204004104600c2041760f181050b03031500081281404100320700e850145002c00003584500350980165928441142c100e2840d8070307103020035841000c02400700c0918a402022026400301c0d0b0000080b004103c4880c01c131254401c5014415440416129410155100b401c4443d00d0042554064050310800c415116010740b0301a41c241e100c1c0c0e0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 970443741 1250 970442491 970442497
    0x50303030a09150f1b020d080c0c01110f07060606030204120213020f07050a120e010801090e0f0d0215012c07091e0509090601230a0f290f 61
    0x24040070034102000c1c41d28043c0e14441da10402032003400c10520201244158000c1d00d0828490701c11070040100300c00003265103071800c900a4001c41e4030013011803502c000800c01820000300c4440049048036a207950ba20a0354010311140f2001c0d00040b0346a4200b100a000d2040184038600e800d50401d404c5c000e1540a148142d000248201000f054408508a280d01691104240c43e03074611303121080b034109161591000803084510b03681c002098850b8600411840e00c001506035143e607800c0e800c0000000040400780e070208a644201d2900c482221420084421054091340c080e02503020686001035507881c068004000f0608090122840b034104201403010401c10507032800e045440d070010540b980512900301c2005184084004480340011441200443e4005d5440d030485607100707080306884001c02c5c068000a2044c240f011078150070390740f5420101c40b900400c1e2104d00c99565091035440b84095125100c1c2c1e24040740400a801c6103455040d1064004031080e618040085c060144948 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 970444991 1250 970443741 970443751
    0xb090103111e091602011d0106060207120804090507020309131b020a0f0303050c1b060f07050309061803090a1e051e010f03111303110d080301031101020c0a030c0e070905030303 78
    0x2459200304c0882c401e10035000380d02c0b100c108400103030202945080d003e0191010f80110310140c400d80e900050202e036162090003d154120782828182410101c1000152901130003c108501c800c3c0080d5401d50f55404003881012110b2000080380030b0203200510050303410000c25410343d084060071a0103d0380001715000704551614001906a0f91811801418080c5096415503e80da026104040076400602c03035000708070211001d6003da640f21803c0b40c1a00c0308403610102c40c1c0281c004a854807107000e180142e8080490103481c1000c00100218900050a42c8103208070765860a0420400c0c0c04a600040034060580c0e8181c1c1224020400d8a0209007416100c0d04210006100c2403c41d4441d43c0649a40811080704958511107051421040c409500054400500c4059288540d15001070300e9006035038801c90403406d503071842e01c3d120503210700d10f51041c1c1075014000d1940c800da90f0305480340010b580310300855545a41000c0898100703010040c11142800042c02c0c00703101c0c2e0f5034004296030340a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 970446241 1250 970444991 970445011
    0x207020a0e0a140108033412020601062d08060a180203060f01110715090521100b0d030503130b01150e06030402091503070b030a20090f130b090103111e09 68
    0x907a40704450741f1050090100c0c0900020f0114003082040c581c0802d2183c100ca503e41d031050600c84030708003100e80c2031101d0040c1c089802c04501000d002d00e400b800c0c2256000800a004400655441c4094a5200304540010400b2a8000200f00c010310b881800c9502c00340080c0b80149003c002d505c400781c2e07a01014066145500d100b02e0300000303010312600c5140041c04002d400010000d00c40c0580a5100f80442d81c100400d002d01000d50030200001c0c403903030038584e44c01400d0000c0079030285c40a4445500c0034194641a00e081d030084000b048643d410070b8028031070fa110864020140361001841e501c100120540306d14810402d00000da5642041139403c0107281915014050303541e00000d1501035103602039914603102004116440e1030a51180c0c1d00c00d6510b2009101a00368a05041c2d404c0c840c545490f03503c980030141201035400c0c014071301c03140641d402c080081c1c2d0f0042040068a901070036030003100c90b440d0206c2900000d0500c9084220300880d62050800c80010703160004000000042c04000c1d6 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 970447491 1250 970446241 970446307
    0x50c070906050120010902031203040b0610020714120a0b0906150916030f0c030c0905030303091002030601090b0706051801050907061404030b10030320100207020a0e0a14010803 78
    0xf01340d43c00c0d0300421026900800300c9a85c61140040b5180d181c0084909032610540c410005504d400c043c0c03402036140b80300d40c0c0600060744c1802c1d0004520269803404a40009900104540f803120070403c01c1c103294040c4044440346d15008a0301480c021000f02038424403000c001a01d40d458456111940c0c004103407902004038030300c40302e004800070070010b913060711000d081c000c0c040200c6800d43e010000d6280360780d440d2411552a041416580c0c403003951030b40d400394006076031940c81d0a840c0d8080c580240d0305141401c43d040d543c4060451580200780142e55150355007040c044010301c2d20b0780b840c025440c6d4200902882c034210b060603460340c2c0d1030f210f100140725121a40040703007007440b0200e41c0619880210007141341410300510a03485242d00045001c62400c407801d01102c02a40b204420703022543d07005041c00302021a00c01b029401010f8100d070880d200300c03004504110032000355482003005000006500459280e2520111300682c84001c00d50810000558900b00321410340c20952049030624075 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 970448741 1250 970447491 970447547
    0xb010b190f051c05061017150d0209150a092307050c0304080106080622080919090507020c01030203060609091b0703020307030207060e0108010e0a0609020a050c0709060501 76
    0x2e05114018180c12401044400e145090341940e02c4280944015600d5070184504070600f035030b148881441c034901201860001030340408602c10f02000c4250040c000d4404041c0c654040f412005c8140d0309940702c80c3c000300040d03044c0c0c2410714080c401816558001d020b40b80c886035144c0d43c1a0103111400c015542c2da18001025076014108688807540309008403a90b0f01d45da25400b500914003030107480264007560f0b011840a59416403150a00101d6401207141c1220541d11444260f00c240c0b11103402c8002070001c070380c0c1d120840c2ca0748401401c0004001c282441d04000090926060000d000d060520600c14806107441d05805c0e80c90140c01a00c22565940710081c0d0170920104078410304c10380d0309001840c60109640800070740400342c480d8080303840554070390002b611003c1405c128940003d180c4001085401d20800c2c0d6a90071000614001981a803101102d44c26640000a1a0045400000c0c1c2c3c01c2000b10401c101c030010410404104103d0b410400020314000b2560386045844125011001c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 970449991 1250 970448741 970448747
    0x11a0105030f180f0a0204180b071b0b0a050f09150106030902060c01230108010b100e0d02040c0203041503020f16050312040c0f080109170a030e06130b010b190f 71
    0x203034020303040089800030118190421380c0c031742000d01d0803401581001c440c07108900d40b55042010070760b84407180f002155180d0b42c0c22551005076001601200d902c0c0400c24020510785034040e8082c4000e018042500d180a6070440824180030b2b0160050340c0c058126551001c0c0b1002c0c01905481141c40e02107444540390000903524003500001304101c2d41391100c00072503e00400c518803210700700c1700007245142e80d8500c645403c039000500882c1d000320342c0700182c091052141c003280d000c1c1a0700508109550b500d42c4c020808032000981858003503800003405100a40428640c554010000d180030741c586400041c1c103100301c1c060706440d4510354924405040c104041801943c0344103041045d8031000d03140c0750406030b5807550a4410490a0988030001040703900042c06403901054100040c4019800c00000308881075101d40d4651040580e0b500202102000074820180613480415041080004034145034150f9070b0182c1c80044e00ba581040900c3c071145292510810030038540c01e107014510140b507020303 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 970451241 1250 970449991 970450021
    0xc0f021c05030f22080a1b0909060b030610030201021b030f030a030c0f08071b0507050a0314070f030b04060f0b040903020a030201140705041806050d0302030c011a0105030f 76
    0x1e10074080803031400c40c40081d100241250050302c0c01c0e002400c2d801031503000078030141401245080d07045080301c0d2000c150851003580c102001c0c010341c0d80321180d550385054200c80d4411012946242c60321102040c902c0c0407c806900b03c2c02591400c0c201e186590300207952802031a15804a050307000a520303507190343c10b00c0f520ba0498494426665113404115000300101a60300182d00071442020a1074043c3d8856407281c0c1c4503030030036190481143c00f811a18006207407203c10441d020b10400d070f80410580c40d1403c06200440c4952070381c00c40902c4035010503040007640e800c88400c01090078410070108014140315904960000700000f159400f50390020003800300030040580160170500c02200b0550300141c0d0100541c0642c0c000c00c9201403c620408542d4016074a039400904148000d104d100a240c03c625403087c04000d0000b0070740d0361840410034201c1d5003041035002d600046640042c01e40c081c080d51340180e15500642d03140e02000c00010340280030240890485c3d81012001030250003100e1a0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 970452491 1250 970451241 970451243
    0x160302072313090219150306031a1008010c02100b090907050909161511150c0a0318080408061312030518060c030106020d050309070608040519080d06060c0f021c 71
    0x1011105c00c0340134804405c444203501c0b914018000b13080c0300c109420320034480c074429281c1c07000750400100100e0007a081510005000040d511402440004500e8000d00c07820324241c2c9590050005841000102e60444a202400d40c2c010309100d8204880040042000f4041d10821101d156281e1603410a0340c0ca132001c0c510440a0001c489080850704601c0e032500091481d449544603903084451003100c50300d0314200000c60b00710b0b81900c4007041c01000c0f0070014120484042c5400600c0000300c600080c441000f0b03003800d0700d40c100002014005071900380903050380300c4c4c00b030000090005040e69483c2c81030801c81c50b1200401d582c540202d02a142c1d9901140c280511000454006003028440d4160b81e134002c0c0b007118050310490744401ca01c0390060050704e1180300d03070b1070142240e0380c070f8a1700c00e0301d0000005008540d80d010740e854041c0e02c1021329039000d00381409105c1e410b4445040704009001c072590303030b0040000d000a0b81202e000007102e404c07040440d140d0581d0364000a000600080c4001da44c7d4a00c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 970453741 1250 970452491 970452499
    0x302130e0411120a0f1202011e0204150503040b040305281e0905010804260d09020406060905060913110a0c02090f131403040b1603020723130902 64
    0x3040c8018000c2c100b00441000900b207400458445001e1411075860b510031034010050712818011030046031031490056100c14260002041c0440c260b210408486480551010f515030b001c00d0030310000710010031200c01c201090902c28030713505081c2ca4017242c1c540001d01c001c04001d00010f43e0702c480c00304800f02c40080400c0e07415880420340c201d080074000c4800803018146501030a0741141c0400c0c49540c2460840380103854504540c0c441740c540c8a58881d0b84500f804014070341310a080010007104006111000c000c44001030882ea1520411080d1103081e070100c002c00c0b0328420140055659030781111482c4d0b10844d180040f42502907118230103811110855801d010000c10240500b41d00500c0080c0014402c99000042e60380d5160f54100300e0400307661500c0c07802d1005007250001442c03180e01c65080c0c030740402181e0900382c2d103110b80802640404110007500800070513003010141c0400400c80580310115203030411a0a040c0d010616041515005210ba040801035603000d441a5011303c0d0081c1e0050 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 970454991 1250 970453741 970453769
    0x4081e03070e040c17130b0708190b0105030705070203070b3007050703050703021903030617060601020d0507030c20030f06063105040b0105010e030f0d030213 70
    0x10810289608200d419402040791094207402510301440340581400e40c40e1180c400e60642002a0a0018401401b040004004842640c045007014841500c42c0c8503550341c103001d920300400343d142008c415180e801034031410198802d02983e0000c0a8070b520014a140483d22400d203400000d20f444815417095403600340016190402c405030b8441030714043c0b555802c50303000010709503203582c4d0101d0407129580011400d00c07421000a21031002010864002d03c1100c60b08161410b91010702d045000b8114046039a9034001c21030f40c0c0c40c1d51003640040c01840050032451405900107034803910708070042c2c0b041143c00903030881014028000c624203503402002100344500050f6070b00030503070669404c40c1c1c07003071086850695061100140c8244903100290089501e00340d19100d240d00000e080c89074070100d03003000c1e46ca03840c4004940320302c52140d40111001c94055242400241503d03203010105c0d0b0007a00180b01000e08004000742040c0740d00042d1400580d1000c02c030701000054545c5410529001d0220 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 970456241 1250 970454991 970455037
    0x80a031e06090b0f0a03300807030b030d21020c060a0204080c0307061409120f01050403030b0312040b0c01091e020f06030103050c09070224011809080f030408 70
    0x15400001038507007102d82040b0804010003004441c1c90400103032a40070420b02d40c1880003c072450020032101c620b01c0307880503849045c441d1003051038840300d5245000030050b10810480e80c0d0f141c0141582524150301404036206813110040441c0070341d0100c0605042c0400307604e0740016081d03040700d06c036510050a440150030400318040196002d8800d8049a108a21402a5515001c240c039011202c0716218010000601d0110700202e400040e080350784003401c5c2400030000142030111038610a14070000103054a0b207460f002e000c8801113190140680c6c400c001252441254000b2101511990a17240f500d589403000040d005d4280d28600030585101e00314080d01251030100324103000380c820bd42c1156041d026100307000860009100207005540016038040e175908018100380d401000e01c1c81076910204134508112500c0060500030002103042100400050019460380d06c01c05408800c1448255525110300295002d43c05001c1c4620200001080400c100e040072103079080240700d41c0d9001d01000c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 970457491 1250 970456241 970456301
    0x1709030708070315050705041a0706020406050d110f0720180109050601021902190515042c0609100e0a0b101106072f010903120e0a080a03 61
    0x10f484115804241c1490b0b070072081c2d00c83e00034240b01e00c0440d59150b04280c40c0000c440c0128814220000f182203042000d000810b84500007000540030030f84601d070b600d0580010200071a6040d00da24030b03200c14180041400b44000b48101d80c81a07400410701485025803241c00c1200a003d0049180c0c4140e604070694160300c0300601ca9412a40d01c0401084a95074140059031520f2002c1e20420f1500150340b04040140782034042c80646080707800707044000e83d86070304c08035002c00e009001c402d99060020500700001c0c40c2044d800000b0200520000c4185220b1500803070300c290000e02070602c998541000210942c0c1c0c10340582c0c00908031a560000a4100070f144030000b40080945140158071286e01c0b040094003030f000072000c0d2801381c0001d014594414400301c8820112081c0d0801459506040aa0b2461100c24000400c0c41080000039076205500d805012180c4111031007a0480c20500c00d45444c0c04003042208410340c00c0f803803807656844e0b00c007811070041103900b0501240d0003c107550b421548030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 970458741 1250 970457491 970457503
    0x3021c0f0c0206070f050307030221240d08033103080103021c030207180204030206040b0d1410091a0301090614100f0b09041506020d1403040308041709030708 70
    0x5081d020381e1070710741300d08408071401e013800c40c09030010070820401319844503ca0780c01002e40062403050040c864440b0b80c3d000b1103043e8103542c00c907200400030112b202440000004500e045d0781c200c915041c0501e665991100d039010040c01e04441d000e414408401003038007020192405403011078001c03100e40e414034019204a900307010a038056000f6850100f841c4001303c42442c2030359050340040052074542821005889104154500c007c0d40911001006848000240026005001c10141c0b80c0c0240c000500072a10f100b0840c050700301c00d400c28008145088a041416030b0b244100100d804996420650a108404413000f6015880c0404240a000d03103a0712040006030314444144071900d8584480c1e105d01018069a10216601e61041003000600402088030410252000ca800801e0740070030f6074075500303540c020f40c05a00280c0c0c0e80b181065103d21a0f0442034600c0c14041d040d0306090301c00800480000f8002481020034030700e101a9040c00d003081e100740d1040103044030040f903210001c3d0b940b644 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 970459991 1250 970458741 970458761
    0x109360816110a2718030804060e030910050706201305060a050a0e150f0a08060a060c0f06290910140d030903061a01120608070603021c0f 61
    0x509a035011091904102490441d448191604c907041c1d0310180c3c09202100d8543c5607030300d1590328101c1c0d950490700740ca030015105000783c9903001c0919142c01d0020640f0703c80003000c500d503002004048166900c0820803440c0c280a0f2400030b807500300c01d02e000401413074810250760017620b001d404480130425001c000c0c0303081e0310441044000507a5503424444507005800204000c290113100c07107500244202e100c100300020060040007003c940070b02480c408e82c070010b5802100b0900040b0080001c0d000011a900058182d803610049817404400620000e100e07072004005083c034144140502030780ba008005c55041a41188403c4015440c00380214a02c0c50300032401002a6400201000681c0c40450102d0300401c1c44485407800d0300042180c0b10019590840034820618400300100d01d180c801d440110100600c4011003020300305c0017404423000c01c140e083c0c3c494140b9400b8403084034045180011124181005612a240f0344100601e0344a80d039002c803611881c041664071034101d0341e0442c2c02c0c80 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 970461241 1250 970459991 970460003
    0x902030d0509030714220e0627060609010909030c08070602031b0a051b03130609080d0804020f04021b0303240409051b030c04140f0105060c0a0b0402011e02060105090109360816 78
    0x241d071265403c0d45540e01242c1c03cbc2da00400c0c1c07900401c0880d0550b00110849032103403400f0341c000700c2e150b0389400307103a00f1024095408036404000c01203044420000d0b42c2c2001010707500301e41450322803100184103104040500c0c2580c0c04a140401c0141400c1007510101d0210b40712140426031643c1004040e50114410101c10388940d40b440c1c940d0600614059025031340240c004482c05180380c0c184006540300e00d1131941008201c0802c40000c4000744003550181710346040c10542c02c0b042c162059542c0907131425107413042e417a01240f000010400030310035480001c0714a0700040241018000380c101007000c0322490300103086c00c22501140e00d10105680c40b401480b04000816600c5d0003c2c0041030284803e441d801c1c1e800100e011001c1002603030002d41c404d00c140f42400d17451211614034404102860100310140c0d025800601440c03512000e200e01501b1130840400c010041c41d1403041400c805120180305080c04a81c050480212024500142540010324140c0d240b40324180c6942c1c9980700075041d150 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 970462491 1250 970461241 970461301
    0x20a081905160303020c0409030e0d0605060301050a0b0102063601020d050c040302220f06410d05030c011d0106050a060e01050d0902030d0509030714220e06 69
    0x49505240010f581d056402042d03200448001d000c01400c944205500b402401000d281d400d99402050a018070b04c603000200e203908100b400c1c14291074015024004940c14500500580d0360f000500c50307808014002050402c0b18070307080400801c0c040201190784035916688002c98004150000e1040b03c3d603074801040150303101031349690240280d020095124801346c8108a41043c1081010a095844580054518200440300040700c1c51940002200501c4480c1c1d140715a20340c14000c046446482c2c1c1844108242d41c0f151000904c249490030720550040c5004000d020703040041d282c15604d210020881c070b1480c5650811209000082400c01d50b082401c042a68180003031140200c1c0c81c191a0220010754000041d00e0036040750104000c616a12000440960380401c4042001c800549501e944c0f0780c141c0c418136082c0f17482078100c0c400d902000b20f42c130030076619468843d1801c3c0840000760a2058590100540a05514070b100000b42c4549001c1c00f00c0c00c0001410003840c11000807601d19 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 970463741 1250 970462491 970462513
    0x50609030a170610140f0a1d0f0a06050d090212010b090a0912050901180f050f03030408030d0c02030d060e07170601090b090103150e100806010e070c020a081905 71
    0x200d0078812900581c2005400081d6280c140c050701c1360381d518580c40702a5a00b8410a02d5412907187c10607102c1d1000940ca0240300380a4040c10400400300f490250382101100b50280c003c14280d001510a46d8204903000a88a4036005207600154100d0313401403160210000da200404d004e8024900c0f49846040e501e404600080004d00c42c0310701e40c66118a48451008500c0c200780c8403500318040443c180901600391050207140722034403d0241400e00c01c01e607140b070700f0711050055071110342c074240d8000d40c4100020300a0000000940e120003d240002260012030004100e086004010607010564104800440e000ca0140640d502c11820b40ea00c01050007144480051340d01c4007990041d0200d00c036050300b4011046600000c210004060502140302808420540500380580c0d12590707203c881e40c0700703100031898510250b000400c0b9260052585504020301c60755000c0d0050420428024050b21010464454038180001421602d0903100039100340b128024020f803a1480882e624095055010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 970464991 1250 970463741 970463777
    0x5070c0c030326070216060c0f020d171801030b0a030b0612240a0609061a0705100908030f010e16031a0a060f020d0801060c0b13050609030a 62
    0x206080d40010010100601c0c5440644040d10004070044804648003801501c910808000c41d00985490740180060304042e02c242c22040541d420050400c145c00300507801141000c5c010558540e01111030901c0e0801c40d16081c1e4900015406060200001140000c48020304103c0000945401e8a05010f00310b002000c01c00001c0003400014641c80f94078000c00c00905016a4100d122181c280840d0250300e03a0a055900c1d20980070400c9050102c001c0411440624601480b40182070f000e40074005103042004070101c1c0002d010f18203d54107004200740c010300070b08103c150840c1c1d010101c1000642c4245c1010481984201c4002a00030150b4000061122404c41d004d44100b90340d82005c0c4201494001c21006001d10b65956000002c0c140402842a507039034020350024284c6842d40704002100c000041e04081000c6000824801800c004001a0380c00c0085072458503840403d908150340c980d0010419a00e131200d001c1c0c01c0f8821002041b4004100200070050901d040e1035580000d40469620703 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 970466241 1250 970464991 970465007
    0x6070813020a0303030c030905100b0307090501031109040c05090a0f0b0a0f06120204032a0f050108062e180905040206090409020312030910050f1501110a140d030507 73
    0x350031002c07204080020038400d81c060a4001824a000300e00442d003a22664900607088922500f032507603c442c40659032800f040928000c181001080c4010362460b1a00c006041080c0680fa0080032100c2c00641008100d0b070203100641002051800341e8200504100e00420742e5070b034001c6080b480d00024140324500501d80c58200c0360705000c0f400c9401d0603c90100c48048103001c0401c2060380030300000c000500c4035200c4c01414511541c0c01301c0200521a500c02d00d11485d50f101898140444c1001c0c0711031b9030b111059580c0113001b600c0c6000e00c0702e64403400624032006202c403149400344051450150540c0700d6030120f8101560042d1001440e12010b400080314020361b0020340c0007208001c1d00c81c1a04141c0c100c4580d06000030181c03601901a100141c400b41e0044580380001e800440086442d540c0c140701c1e864001c0ca80c0e1400550a1802c01c1740c001e20340680300d1029040c4440e102c441010040c041120020403070780300313000038101e0000c0305c5841e5581001d19803200104e8246400200b1a52086110b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 970467491 1250 970466241 970466243
    0x24080d03060501021f0c09091107050c010c05060f1305060702071a090d06050402040603140f1c02060a0e030903330403121a0409030215100503070b09030c0d030206070813 75
    0x5500050005d1089074005150201d04802400601c0c2c4000940020314843c504800d00c2c500245e030303502c5a1629101c0e0402100100340e905006079070f45a80085000002e2030340e84a9030b1a10180c8094a60350340c0c0c441c0c0c10001500c010f0207449240104a4508d6010580c601110581103003c0021741c400e04100e4100d000c0c10302c03041c2e003221a080880300468802d400107900b0a0000d000050301075140c0d1103101141c0280f40c01d00c441c40d40088a1441034500400980146070782d20a4408503001a03200000d40f0f4020141084c0d529903260515082c10120034400c03611180d1b4001c041302d001c04001c00b840b00280c05682c0c2c0b06400784e0301d5080d940642d1054892480d01c21941341d030300c0405075020a0117880007440e492001d038080711290b4603083e10360346542c8640a0003500980084c08603c212207118810000c0080991580d040000010466030b1000a542c0090300c5014404584500c00c02c004a494a01d5402107140d11070a05e2030800c0074113401045060080381c0503a20301d6102d58801c04030100500031428 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 970468741 1250 970467491 970467523
    0xc08160e19050604060b0c061e01232e0305010f0b0304020d03030f0c050306031b0609130b060a0c0b0a0903051605100f020d06062124080d0306050102 66
    0x2050a107141503804a0341c004001031002680607111001000950410150170140b40c3c040d9060144070303501043c0d00c406043c0c680c201c107003403036044c804142100440d011036070411094200c180c2030503a4071281c2c07003282d000308215207100b001e0401154825210fa19028000442d02d0100085041c4201100000030340d00c119000310700d0358441e40e080c0700c64030104000076002c2550303a0714040b01e105110f01030400d0b203503030540d207a50300c0f81802401c00d4240340e03040050341b0000003c0f59282c00d05898400070348003201000c84151001c2d4001040000c0a08003400000c0e40c409030000c0d000c01c005800c03101c0b00640b28080c800702181a5540050001140c030380341c034042d001c1041400041250171001d0b0034908594859002d5039940c03002d40f40100c0c2641c4000c4543c4a2154002c038514071000300c1807081074001d115918204e04c1d01a41c010216808980c150142c4029a031074401c5c0b035580c000c1c51243c0500d9400c04070390f14041e490380c90080a807614019814800000d0030450006101d45c0b00165030004401088 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 970469991 1250 970468741 970468771
    0x50403020d020603091e100b040212010b0c19050f0705010c0803010302090c12040c060e060f09040f06150908120910081b0c0102090901090627090c08160e 68
    0x1400f008215040103240ea10030344200000304203135144280d00c0360403081c1c200004124074401081400203032a0042000da001d6803040c402117035a0495a4801030448500d41d91696980070b0280c4d0044c1040c0f01140d51025010817014002c040000008209541403030b00300030749800588a41c01195415040341d0040d009960520060002d450008002500401031001e1145050f2400c5414000c0e064200d0b000d40b030070f20542c0000c101c074a0f00046c03014520442141d011740b0300480141d10225500405207001d00940e6551001058006140d021001800c440c240311610002c028400500e5513026014807200340c091251006c07540c8030460107130307003140900406104461003030490844035044024045a40002d4950849580c010100c0080c0f0f042c486000016a0302c290780028407014141c10b81c0002c4403c5d1a1070810000b2100d5031400c460030442c0705070a07808950b8a0312048014120003800600303c421495000a41d5600010b601c07001280318941040c2d04075a81c654182c65804100c803942d0340c4e002c0031 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 970471241 1250 970469991 970469993
    0xa0b04020a0203040b0f0417060403021b0109030f02030703051218030601051c02030a1b03030801080c0303040b220e0106081e150105040909080310090209060d020d020c0d03050610050403020d 84
    0x2407011340099251b100c50513042596802d811046a4223002952070070760800d2090205140d0305010f40c1c055000d4440200c0c005030b001400007030041e9054407015054103002c41d402d000310341c3d00f40800b40040d0f030403038100c0714185082003085d00326600c40c3e849441c07401412145c0d4992070801154041c103c4070000c04029031200b28900103040d03e2803401c000c0741c0c107000b4001807100140110038101c86401240ca040d032407040c250f15004c1c0c40500103801881070b591000e2288c42142c0c0d0000100d40c25594814802c40d100c80c071040c08081d02011902c115112003580200100380361540030200307030481c2c415036980121922840d0800803920055840e410038500910300080440035891030b01c214000042c0350152600d550381041c0009ca0b00381308800c031802071000040c00b0b1949160300c1444041c10303401394114601003000000071054400c000d8096035450b0082500c60b050b80b2260b0603034504650000c2030b945000c4040380000e00405c0f007111003510031008642c0e45408180f00f1003e417020760740d003c2c000d904c4034a45 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 970472491 1250 970471241 970471259
    0xa0603090809010e06130303080a0c0305090a0212070905010308120109090f0b1009050a05070807170103110d021306060f2f0c0303130302150a1e1b0b0a0b04020a020304 74
    0x40c440e1140d80145007046006d0075201742d03940d1000114007942e1106c03440e00b08000340300d003912042140003003050700740014444c0e142c0010469011503941141d9a80d009802c204038541000120b07031140060310b02e0080000203008101000f4142d41103030240c0c0a09a83c0c903054913400700d81c0c5058019100c030224080d403000041417503038880e0704440c4800b040e03089995129660f000fa58411200c00c1c44094540c2c091200c41e0b504064541e0b00001c42d0f003081c0d848584420701c031800e61a01440080e010b00300c4c2003a07540d1345486a86480e0301554010341280e038041102508007000d40302d68440c080003d0744a075410b08215118070030740ca08040142029072901080840341c482c0300c0d103400d0001c41c4540100302d1801e03581d503800c10060010002440004000c6071440c010801c00c0e50448061401480c010041d03800700c99131003410100c031594a070184204491039150211001c0c19800640138215410b1842082841061000c0d41e1085550900034098107000c0c8080c00103a020b5411058050b92080c4070a01207650 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 970473741 1250 970472491 970472507
    0x203090d24020c010c0c020112020d091a24150306060d0e0a0501050604090b070309050c0a0815060a05061611060703030c0f0c021f02120a020c0a060309080901 70
    0xc0540c8001003440100501e5200300765121041501e055400541200149820301030985504020304054454003101d800180c030120314011414a1668001080d406c2a141c41c2c0c0494505608404500b441c40003803100c070305840304192904036411207011603070b2500c002c003c02c0c034940c03200c40501069025851012400c0050300058a001e510000505c05070303401103000d1140b44444078070030006290891182c20100e0846002a11403030203036040107084408600d080540c0c41c0c002c0b04078940000e40341214203242c1e040c2045003040a0b400b28040500080030b00300000c0750b219280210100425940300c6008004c040c0819210703c1380c00c075000784180350a00305083c40e20b1552034060f04c504070507513104000042450740018400c40220703503500d815050b01c9504c00701c01644c3c2a51401c0001080803e500010071411004841011010744100c030510a00e10a00209408441d404c29081c1c55101103000079442e00d00c01071420b40215410640050814407034000c042c03c0b11313000301e0708a02d4940c00400440d1458 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 970474991 1250 970473741 970473743
    0x5100504170706022814040f120614070503090c0a121e05120315090f240303030a0b01112109040603080706050f0a020a05040b03070e15030105010207090c0203090d 72
    0x9901740005031101040c0856804183c219980d8400066120b00d4045d0181c54061501d41040030180014001c280f14424032209460b03518103c0780103541d40346403c10180c0921105007441c4404442803040c2c2c60381000165000f06000300540d1104101c86061008031803107881400c0356402c103a0340c5007010840340c0c1403918440c882d0748104842011640c84403443c00180704041c4010034000420050b010440c00040390b1004d8085800a0080c00d01140780d01c44d41901410300311016640449281403084088401258840e0141c244ca481c7d180290b0080000c1401207032007804150380780100405003002003031050076030042c00c40c40925000c00e804e40032110313000f55164a410642d0707040c000c0003042d0200090f10000b40304040101d02481e107020300440d8001301400003080c00340140b14200c21146c1000580c0e041d501d08200042e1640d0b9420001c840700d1006201081d0010401800c444080c0e4000d0002c43c16540280c003201d513610759904075081220a40c012200043e041400f4004640c544490160000c07 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 970476241 1250 970474991 970475003
    0x612010e160e0a0e1c0203040906030b0402030d030213061404050909030307030c022a1f0f0e0a060e06070221010207020102070e07080601080a0e0d050304051005041707 74
    0x1400100035224a002a800e000442200040100700626600c91054039800b08010784240300c1407100c441415900da40072145490000380c40c24821529500c200162001030142d20401d0101a13682e0608030303c2c1070415501a4028081e8aa00705852030083c0201c9481d0500c8a66a418680c504001101e9000b07915004880c0d403a400c001c0041d6039035640c103909000e0010b11014641d40e00304080701a04031910180183d09541100320481419015910b0030040d25051081d0014030f68180f0000608550100240080458191098078180c0780c1c084170b03000d180000c6850790440d0103041c4003040000711191280400180c0c1a001130080b034144940079101c83ca1001c1c0c0340c1c0c4005520b154840441c1d0140fa1460030880e0350110340b50095690410000d0f00600f170a0450b0304050414400c01045408024407443c140551003000c111020101d1b071010000161120a40700008500c601c02071483d40151800d807498400e203580e05039084c0303a5202c0c1500450344000c03403c800d4413a21141603902e40101170280c41c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 970477491 1250 970476241 970476251
    0xa030f060e0d03020a020f0d0909020d02090a1d0c0310050f060909010618090917070f050d0c060608030310090b0a03020307170f0f0d032703030902030c0103020c06061201 75
    0x420300d401c011291000010b5203004d84c80d20b244000092904c40030702500d09181e40081c45002c0c0342500f115001084d02c126400150341c030b880704080c1c6006841000100f03a0007400314400003a651001c4c1400d0011181181c5804000c0d40303a12044000c070380416120880c3d040d61492040003146003141c0c00e500c14146c0a06164103101143d000504400d030268000000300d1404202003850105803090310300034282405080080b10b4150303c030b00000072082140c0b00404000080c40d1014414809804101241c1c08000c81c0e03986a090b01004059960340c22044902500704400802d084c20301200740c0340308540f444540c6030403a117070003400000307000c0295145801c0980c10340b011001d6202406144040d01900340d5071407034092030b02c5140e40361150f4014100f07003581100202290b0000085000490001d031440e0108955082d83c40b013000d99120f000501000700c00540d46030080541540007440068001c4095a54405492005400740e01c5151a040c56680248000504514005003107204c1c4c082c0d10f02c00025 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 970478741 1250 970477491 970477511
    0x6052110050913020f060703080426031005010305013003031b050c0d0507030801180623031612321b0102010b060406050a1812060e0102090a030f06 65
    0x142c50000c0e60030780350b81a180c003007800540c10410079061131200240c43d01c0303183c0303070320b40d28000d152010103000203242401400306000c400b03038100803100d0b0b4031100f03004250b40ca040c545020003600d04a4410240480d0420b000000d1405803114017240900c4a1a000045028101ca80300c080e200c00e09021000d240d910201c5a2248a40080004008905480d0b8542e0340c42d00c081e4032464014031091590402008001600009a10000207411940220b422a00c0040c588085801400036600607413100903206840d0803141000c07030701c0304c130294078107a05482c88525241c81d5000b00152500500b00b205c065050381500103045103000c2d81c1038030b000c40c000c084000d5050045078a102c201c0144003405034005100b2044900c14944040d070040b409000070840421101d0100342c2c240a1403041106020010800d10203880c01910500c100036a002c024401540e25000200008011031300282d440601d04481d46502020500c02c59000d504003d104480440c5960f4071580526040e850071644280c50b0a0a90 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 970479991 1250 970478741 970478749
    0xf030613060906030b0a0b060f03090a0506040609211409040213030605040c0f120b040f02030604031110050f27060705180402072406051908070605211005 68
    0x1030140c9044100410404d1440c00c0c1900941c1d00508554002464a40c10030700b1940c407002100c20030605490302c562a40e40d400e01c00350602010850160050050404000410100303a01001001d4030845c1c40034425000f03145900302150510b81c0007400701f90703819010020300b08181c02130680390700001e0015150100e0300000c4e15032070380311783d0007140c03491348135000c1c04208181c2420000250800e003441e401140d152500b070300400402a40040d01e40e0070404045018003030000c4440381240c0e0050104e901c1d07420585030040000041e0f0803500303414000c08500511209031400b6132800b4902c07481d01c20b04203482e944580c00303041c401340a41d80c2c103004021048840c2d005c800c5c00305038416140d544805850380b07002400c0b108440000e05015200c0e42c81044031200080b040c11445500050310175454011884624050005000340d41006a001034a1070440c8a03040050100c07405a880d24026244440da4600b802d81e0b40d40640b5090512507501394400d640405028a44175070303c0f066a540c52907040f40e8440210b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 970481241 1250 970479991 970480001
    0x111e1809190c08250e0402150711040f0603020114030709080d09050f06040e070e030f030c030304111507060507021609021206011b08030c09040c0c1103030703050f030613 75
    0x2c07644026504020840d81030203210580c44d048030a500d04024010300350b025401030784a802001112010f69000c2015501c0d002620368950801c6010599a4003550038000846c034060f0303c001d40325900b0260300d10344840c03584c024034080f41d506841e003c90860950050701034030340005040d88200902c03604002443d04040203614800030154071200350340b60a200c18884220744207000603000744400c000402c8032410380d200b95a441001881d00815012001e40000e04101c108040745405100200c1c15855240010000b103014034412448a20b000a2800901019160781009011800c0e414031214000c144d40b030b001130783c0c01601032041d1030074422880048141080690490202a41d01041450341d60304090719691b009842420a40300c40c84042056483c960b880b00c00c02840c2400200101d013011504600391042100020000d00c01448610b10060000e007107410f043c0d810401c0b8190201d81410003204403100703140c1560b1514544214507108840399031004c1c20142e040486000010442c584a01c10 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 970482491 1250 970481241 970481243
    0x13110d021804021b1504030e100e09011d060306070e060a0504050d08070210031a010f12050a05100b0406021b010c021002010c0f0504141207030807111e180919 70
    0x10b15135903150000c140751401d58820740082d0f682424030140004039800c0a0001c80c0e0010444040008500008044554000d0046255000040c83c00003150640a42250294140c6410600c1d911592040101542c0b50340030b0701d461000c00c44000800e4824140080200b00110007414002d141c00e6a40f400309200a001c00000d0b2100305000c1882001c61500500c1c5400560a92405000c840841e84181c1e00303201881c0200c078107000d00750b80705800050040580d080c020101e54400c00480c07400e00034120152000302d4031f01540041420020961481000031b580594103e80c0c024100054007901440e10b0985030354009040c40010703604400107940740740302000000c4195001142c2d000031118050701024000030f0b4a01804018081441411300301280104068000c40b80004408200b824190528015810152036490000f585d102401129000078019074002e071500c0b01d1030b0842495002003101c0aa0003d079000d02810a40070a0000e00c1d0303801030b00b02c00641e059030400050302104076444040004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 970483741 1250 970482491 970482517
    0x170a0809060f1306080f1621140f010807081b040f0e01020a030911010c1e08040f170d090e041b050d060501090c020c0901170111040902030613110d02180402 69
    0x308070400d0564000c05801c2a42150348500702140f040e4060030350460002e180e0340a10311079482108d540300c141c0000040007403c645600c810b08003810034500fa1402401104807520a041c400540e1040000780200455140d210540310007898401f000041c050400450032400c0c1c5800030702d480d24400f0f10082c5662030303040c0c40003e4600c84606d0144041c0a4500000e8144140b002c0350701c0100f0b484204003807183c0a101e002840303088191801c100d01e800b45801c08407115040349000b050184408007481445042e13402201d01e03130074125108445403209809203002c1c43c044c420200c0e000500480030000c142d041c084071503450940f120003080b8108000a410744c2c0150b2a50010072121200d40300f4030040b403409102601c014031150010810b0000d0611800d166a841c05441400d814029032080c0107441000501c1c40d81c45544d210000081d4009655080c4203254114400c103504405101d988074151250031741c08d0404030140004c60081d0006040c822400c2e00c420760116060359148001c0c11a008400303 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 970484991 1250 970483741 970483757
    0x11030a0903090503030406090e0405030c07030c0602010f02030c040506070609020402032d13080304031b0606030614250e040603050f06010b072102030702120601170a0809060f1306 79
    0xc20010041c50b4564469406500104024000c080d4013404180a6038003c040c001141e8445182a80c91442882c2d04800c441c000c0c18070100070010020752000480f44164000c1c0f12146041001008a02c001e075480c07000b20700100020849820302c84054202a0300401e800250f01020750081070a0b41e00c200c4040c51405280c0f039130100e1031000c0c81404010701e001c01c03006500900d4800c400c1911320310b4920014007001c80200000701094810404403a042044c05d07021b1166414034500403002d0030090004603442c0c1c0c01d0203c483c455403d0100081d10070407445505604c62119a120102034181041e01039080011894802d5080d45450260b0401140f09030001e2110741810300c030840c01e040c8107800aca100c0010820040010030f03210144484608420390119080303480c04071007a032941c4035111009404c41c0e10381c1c1da80102d465011402a040f201030001c44c1442c0c50300a41c42ca921042000340003040c10b501841071954030304183c0301070b00c6526115400d5900e00b54200480102400040d441100020089 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 970486241 1250 970484991 970484993
    0xf0708031b0a050309090402062701110105040b240a170606100e040b0406030f0f4808100504030e0607082b0903030614010504080d08070311030a09 65
    0x11000712070312062800140020301c2d080e54400d6100c0c80350f000610b00c04e80f0100041415581c4d81411103505001c0108500b000e0a070711000904045244442e07180031070a0662842404041030140310301c140e80c8030308910b4056440072010914052500e108145510344042101210303103690400074082d000640c0007561140942c120700d8a003a03401410180142ca03101501181d29401c0b12500c23490350000c03100807c4034985034000c500200040e030f0020303101c940400503040500c1400c12800007564056030850031844000034256002e4104021030345c1507181703a403041010030303d503091881d403011928030308800c0c50998924a003850525680071161200e41d1f50410311080541213400a060300c001034503c0350500b0015110304489020307103d03070703408c04181c400e441c821a205140b055034044c00398103604100c01400c03402e000b0002c00751401101c507203c010f40d00c90b904540c01882030703a04840c0d1890003481801e61420b012203568401401090505480740100ac03200b181c004051f610a4002c00e80000e4500f42e1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 970487491 1250 970486241 970486267
    0x9060e0603210d0c0e040507080f0c0301060512100f03120906210e120c0706021b0a052206171006061407110a080f1b0a0501110f070803 60
    0x40a81121402c0414080da1003462000005031400d2000c0e103400010741c0002d840055034001c100281c5198454580401c1103031040d04841842c1c0a4102d41c103004107280d480a008e4221032200703004241c0402c105014000b0384042ca03e0120f41d1101d048492204815030316036512114488070780041b592464215902d80000d40d109141e0070041140780b0f0544d044418040842c00b42006042c028589192550b041c0c030051081000585807100c031910b4002d0307aa080b16441151544094004e5400502035141d448190000403aa02c42c45107500403c4103000c2440c00d020440441d440d0744481c400015000c03502c0c0c0c1090f442d4032402004055501c041881c08080c0410b0904006460302014015440c1c103009120707141c1c5c001e14202d001c115460f0401d69802c01414074092504000a03c5030b8003440407000855229004500c98840c2030340d010460700b00c0c05031080d0b0390802c1d280a1102c1500041040410081c1d584144200c42d4514005800d540461141034105401c02003a03400802c010751000869502481d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 970488741 1250 970487491 970487503
    0x9150e16120501050a06050a050910021c03111801170f06010806030a0b0708060d0503040b130b030114061b010203040f030f020d020606090a140109091b06050307120609060e0603 78
    0x107203103801000558180000a410103d00740030340820004c01007501d0150034080c0c0200c400c40d4138018442d074841c0101e508000c0d030702c2e1228030840208440d440c81103172245019000e50b450b14a03000c10100e007011816101540b001c0210810740e410401040401403500103003000d2036000b42900c40605115180075400035100c540c010380700c2d40c081c0d40300d00c0c14900071070149034100d904100c40380740a10694a4000000d40310440c00300015000b8040044d0000740036000d032000b00902c0c1445985644150b0342c030b4075404001d001c244a9108002ea81c0d06407100036181c210003c000c80c5004241c00107862800e2258076007240c100f100c2c04ca81040c00c00c09403005050300106200440d050300c2c40207080340d11526900039100e9a02034202e034010009800131030312607503194210150700010140508415079440d040840074180e48070040d074001da01c020031741040d40d20f62485401036a0309a100c445c9141c039048421649030100b0000d2051840d59004046442c40321030003144001c18840314042c03014240740c130815003008 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 970489991 1250 970488741 970488767
    0xd0803010801320403260a0f0902011e0c0b090c0102070e0606120414030a08190603020609060304300e040501060801050d031412150d05030409150e16 66
    0x203040b00a4000c00a0301c494408401420f41e00c400590342c0d225490144d8842c545600b4050301c00200c480390500694080824610072070b0004801d000803078558032013030101e070001d0002a0000c0d40c840e0880000c8040e04008011451543c40d0058031843c858440e9910104250f0711020181c1140c541662550307410001c20300a001c040a01d040c060a2220002e58284030700c0105106440403040000c090112035852006004a55000c0d41da4881c0700d024010407640d002c943c0513810007121413040004011510403030081d80e46c0030781300030301d02444070040114075080240101c0d07840c825a680e034101080388508a48401c1055803034000c40410700100548000006c1a0050240f031a010040041d01c1d44031404504480e0140c60030707000081c01e030504071020040c9054260700c040002640c0d0041c056584070161190740803142212100e6556020807075069804880a015544180028070103111558080380a840e003005a0085040e0f035540711140d0854122001d18120f18030b10542c2c400c09402801c1c2040803 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 970491241 1250 970489991 970490021
    0x100503060610081b0c1501031a0709030b06030a0f0b010914040f0b190203251e030c0216030602030403090806043815040f1104140f0d0803010801 64
    0xd468071440081c08000000c0c95541080030300c40003103e01810007030417103a0140c41c1e2010344004401ca81010010170034207200445151b044070702d0903c07210011503900d901174220b55544d8200e82c0d01d1510707940f0100f10080e140340c0c0e0601410140c000041d41454469802a01c0b81802e4100d40d072500d400c0c581100e2595000ea4107400a1104000005da450031100809580c03021030041242c0795114550440e07644518138002c0c00e84004180240d40040642100803440000c11400c150030411000303e504000800741c403082c01c4102c05c01840a80d020f500036480c0d0b118103104480307961070149143d040420940e44103880403903000040c0014554407519003c06000300400411440c04c281d507551f11984400e8202d0550440e490b400160107030700300100b060341e0011800e80c1480d241070a0621060140342d520440f40700340d241c0202c4c114525114020385092210300a0f0260a085ca05102491458001c51040c0d034800d0074090160001d940362030700018454080c0d41100d450390305082500e400c48144c00441c21903 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 970492491 1250 970491241 970491259
    0x10e180f013609020d060b030601050607080315030309062a01180602180901030614250c2a030302010b09010f05130605041e06050f150a1101051005030606 68
    0x1641141803440420829580030342c1440140c4062003002045a54002980b0160300d203100e105110a58100d203018800480c10342c0c90031f985e2031082010f14032074540c00820440342440040e00d0000c60290240002c14003070300b940c1ca08046040000c0ca51b0788510711101a00221020b0700c101d02300c00050700d660440e8140b000708001c0550400c1207180103540030004003a140c0005194071561200b070040380b80f654029040700c0680d6140d00d4440042e2400c43c1000003c05140000589210403500380031480d001842c0103441c3d140c00009086601c0405610150340c02d00c3c0c540e1010a081c0c54072100040100c030300b003080320b84131421858000d003541c4080c240c142c0704400e244010f001000e0150b010308212802220901c0c02c030841c0321004400385c02076901c4170317900c1890010200c00700c03480400011980075030404100078564848040100320400f488580f5006120720840000c0c10340306c2001081500040d05100401e0114003e4082c203503081203800e0b080c0d01110501c01c2006040422030280c06c1a422511005 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 970493741 1250 970492491 970492529
    0x31b0c0d0503120a0b0a091407030603020f10020c06160b07090e01050609041805010204050a0e011503111303080a090b0c0d120b030313030b06150a0e010e180f01 71
    0x90b0b00d02400180c001114501d10100d0600c80e59a40611400c20018021202c00b503603032154400142800319840e02d1400d01000003500c0035111748200000d032903008020240c000c088200f401003042003044100301358880d164001e056a590103015003800500348665800b220894074004401d45009004201880140b90007030045240a4024a043d244181d80a0f134541102c10f00050180c8058003000c085039882c4441074040c88410740081c02503403825100c11006990710400c24403810024403904041c1003003e41034000c0076110750001c0200c0c841d80a0b0312405c141d08000552000c0b90250300440d405040082e0900e90640c204018800808942c540c86040681c6400c0c00c945601c020100c5a04010b0010030440401e0819840308032112405003c0700d0701c440c000c2c09912080420723400284d0700d031710311500000d100d0714200120024099840701054103102a481c002c0c0d8008000a210505000016150079450f1b00d50000400d02400d07200303441c00d05410000d184615481042c1c025428032800500700076 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 970494991 1250 970493741 970493743
    0x1704030c120513121419061e14092a0d081c0606021009330c0302040915050d0623070e0a090c230c06090312071701090507090305031b0c0d05 62
    0x2c1d40480c1c0104d008680e40e23610310b50024050032041c0c07181c11a1440d207115940303024860044644100c1804c0d003262642d03015407240c00030300340e8201c44403624010b60b01c0307441001e4100030703000c040d6062056400070706004108406030302c00d8100300040c00c031140e558a01040003aa0401c5580c48115000c0030400522041d9168203100758900c0c100224602006401c458a0340e001a1440f416901000710130091010144001400380d4080c3c85000d031054100306600b500c1303809081103c021039100504441112840f41e80c1c450107800000080d41901009050070405103440703a04042c400c4900303607201c9000c10072020411009502d15080014124500310a0340c00c07041e000050010148071101e041d20111444008030541403041502d03c1c1154000c00c4c041c031200c1c440000140000f20f501140c0c00f007403566034602c00c070b510300354803001075803e120040010005041c0e154002500003400b403514400d2a074a07610b8291940d40b1800d180b800d01e00076403400801c0703080f040c05608000201201c3c400d0059485464003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 970496241 1250 970494991 970495033
    0x10b130302060c0a0804090603210203040519080307030c03080f06060d091e0503040602150c340b180102090609040507110604060c1704030c1205131214 67
    0x9008020010b24020107201c10090301c002d0540c8020511ba0f16500c0315424000340c0824401190704070100100c021140081c0d001c01810700140d6801503040614040030050300ca0702141c6020b1025040100c00b24001c07030184010300000d8000d484040d0b00102500d0000c1040000524411200a600084c002240d59200072246011038140012554005c9410494241c0c1071a513200380c81d030003040d82aa0200300c0003001420841e00f1540980d015a11003c0030301c2d51004040b02d0406916008006c00039188000040d41ea020300ca122030580c1c1e80595070031800740c100100380e0701540c44003010001c011000c10720f542c000c40c20041140080d4203043c044c10101d07899004140c089032245403600300258010b4406e0302180c0401070200121a264145820850000d00121000741b00082d1030808a8291800700102c0034022981980c8808c0c1c9858941c60b0882d00d01c80c8116181c04012003040100350407030041c40c0038030182c0004111a0701c1d40d89030785050703141800d0b900c208502c3c58116a0003114042814491 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 970497491 1250 970496241 970496243
    0x10120908250210080a0e030c06010e0609070e1507060c09170309030312040218010303120b040c020a2d0c0f050d170c120307120e071206020d091e0605010b1303 70
    0x1c101e03040e40321405c640b00900320280ca0800ca0b4400815029800840024924100c400b0701100940340c1d00c43d05c0074802815422a41d000200390003c000d00d4981c00c2080d51402070b180885000c90800009556600c15209150f04090000c0c241010500030491603d0164509e200b0541c000c5291813640004a51640180c04990019001e4400041d055413600000c01c06c1801d0968922815580c5a180242142100040405000f85040f1040600342080d1081032614899500100034075829645c45a0340418031140480800d0490355841c0822600c11580c0104c0300d10881410701c1e894100000d41e50001960fa000610403003081c1c1440021407546011450a42d5440c1419591009000c0f115440e040c4c91030741c10444090000b0810401c03d612401200d514600c8482c1400120702030166250348584900498080074000003103030380007440690051400c002421804151b008143d2114203400070781500717080f4002036200c10320081100501c82c1601601070a00742c00d003007040260041d44103042d5400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 970498741 1250 970497491 970497497
    0x90e1002070c050d0c030b0105030601180c23041a03070f050f090a060302030103050606040c2c03060c0717030c07081c050a0621050c10120908250210 66
    0xc040d4144560519040064a000f60041155107024600820400303158030090700c5035500c007c0045950310300480c0c1c06040342c0d10800b40140c0c20500404240c000e010b452a040c003801a00c0504500b0b86202d03c5100390b03c02d001c00e1003035458900e014505220344100c0032664642c0a0104208902d00341c0001000440458a103406525140040b43c6045a44150710105610603050240060015455001541a2880784080c1e41c0c007500c459003440140d0715074000e4032010804846106926a813754000d900691125105070a81071000010078107000d01991003d041500014196050102030f0007540121079003805c00710314510b42103010114901404000614000000a05c2080000040c081030901800c6082c03c006900f081030f0b100c030003803150b482010443c1051219599070301110800304004280c0141c0540307501080c203002c110494681c0c140c45418044600300c407041c6003500f0300c00c0c018118410100300c0d82d90180c105010b110300d4800d074400d0f00c02c1c214806500b03006071070b907024958031030400741 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 970499991 1250 970498741 970498747
    0x100807020f0303131101020a0b0c0d1d01020a0905011d01140904020a031d15010e0709031e05010614100305070201020f071a0a0e19050a080a08060a090e1002 69
    0x104040342000007180c98049244004014042c00c003031a018540c4d0040e21600d0307500310a48500006984880000001801814140000074440030b01503000389428520507a0005a40c0d02a410060141d00e8503030a00182c3c1c0c1d03000c81c1c0c40351040c2c1c0101e698009003400f402d1550b080005002501c0e03030179882d158064100450001c152038286032500c01c2c1c541985004009549908800d84002c006101101d1461020354060a44500c50103000c503110160381580304c14034801d44c1c00c28040b0542440c01400503000c20180060006c0401c00110109028101c4080d5018110788642086030030f44450b40c001c0c0b4048100007800300482d5880300403035281d005207400c0101d581e9945a034140c2c02405400d81c50a0280000103194080001c0040508024544840c072039486840d45900c000c11140c0c1c402607900d0a80c0010010301c17128281e02d42c075031740c80c1e4481d800300c81c1c120b400340c2d880c1049034211907502008240d0540034003401d8541401c009000c0c00c08040308002c1030000d00e15040d510405908500f51044d400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 970501241 1250 970499991 970500001
    0xa080411121e011d03070b0f160c080c06040f1b06050307030f09020a1806291e0f0a03050f040209060409020a031b15050a080f132f0108061008 63
    0x29040142039403c6058442040d00744d0401e03c50716a40000401c403146418480000c0f0b048440070405030290700360b10312610011a5001d07081d2240d00c109401902d2031002070001c002c00000410030944202e200c1e54111801c07800502d8401c80f00d0580105072441d8030b40c500c1e0103014069000041d40c0d0710544503d80800c00c01c4660000304c0050451050294010001900c007085408400491121135900386400b000900e540d4101541c940b41d1074502c455a00aa0009200a0108140142542403102201c0c0d4040040d95501d485e003030351103040400004080401d40005041e014800c195000e414092402e0a504d001e2b0b00227804800003c1445100e0380c1c1d1044030600751744a41d078204000e160f0182d05040b1b40451080c028901c00040d101c0c50780f414006820301270280348900c05488a402c6640ca074107856031610101980c18600042007820080d1a90740210081074050756400c10710385a00b8100e500340b440d040300010961400743c44280c14000384100b0302c03d42e030729501602b418011903407070614819120 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 970502491 1250 970501241 970501243
    0x12010b0d081b0703061e11040302010320040312090803360913020306100308070b0a091b0510111504032d0e1e04050a060b0a080411121e 60
    0x2d0806850782c41020f4010040103a6648404034111100720030080381c442c0302e05120113484140d25409100e40c014402000154040c1d00305007414241060800c884100120300404190400c1c3d100ba20143d500381c603800340e640e8220071140c2c00f0f0106180598503000d4180308480f072625403a030030b0b446954000c2c0014035102542d80c010303024102d0f00078440b910900785681c10b07800420000405030710070f00a41d404282c075420907142c40d104503507000321900d0800189840b00c070310b0f4007402000d007043c0540342c41c0603500007000420902c000704086018132010906042c244010b01e00d901a140050203001c640020310410001207030702c82c1400c019105040ca907524a011500e2103083d801074500031407082980c0b180203030340181034071968440d0350394540d0780d203a180e0812403039511080d02f941501c2203440000065003040e80245921424840001c40e880355604154007059004000e5440042c41020a100c00c010503801c843e643c0100840d01d5550305c01d52a6401d03030321141000e4040140750f502c184130800e07401e4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 970503597 1106 970502491 970502527
    0x901080d030903020c12010f0f0204080c0d02030a0206030c04060f0e0603220506090705031902090f07030605060a0906032a0c05071e0512010b0d08 65
    0xc9206a000303003040c080079000c6001c1d06400890300e031128415007001410101c00003d80c0c0544c9907218045030040450701a035640108004c200b100e00008011882d01d008a42d00c2c04003000510000e40340403001c0030001d41000c80441040241d6050401410843e0210748a5044507080c1c844210f0f403100800c10166488038084c0041354400e0b10200983d4102c403903064000d0030790202a240c83d0f02c0d020301201c1d180e07900c0c3d010390740600007802c2c03d0103420500f200304540d20020710403a41c005400044010000000d01400300300143c00360f442600108020500600781680c1c030742400200804144680c003400c000b090030038941255072540c9440000d000960000078411041603960111609080c0300016581c40c420b058012035401c01c1c01840c2c0d80080d000280040e113036464901072003d6080c0505044100c2d900d441361a1280c3d41701c90120420350795000c0c04070340d5200c00c03008600041c04 = true := by decide +kernel

theorem cover : BRFrame.Cov 970323741 970503597 := by
  have h0 := BRFrame.cov_init 970323741
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970323741 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 970323741 ≤ n) (h2 : n < 970503597) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
