-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2753
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:38:20.10282+00:00
-- url     : https://prove2.me/submissions/b5fd28a3-bd8d-4da1-91fd-86f7078a1818

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 494964028 ≤ n < 495143884 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 494965278 1250 494964028 494964049
    0x503070b0a0e0a170d0807090803070f050f030a03061d04030206060103050a0b0d05011e0605030d032c0a03030e0c13180b071701060e01050706020706090b011d09010501060e 76
    0x264002c000c4000003403031062441e202c078a07004410005d0200400c5040010703217041000742c240b00400c0181102000182c03004410348a0941e030015a418118a60b41405460101d610103918854000018429080e0f034160380420111001c5200d800c050742280207490b4442c0c0000c890203030140e0000d01c00251a0b41c8260322899200001c1036001500c01c48290110720303d540c004208803051b0b035559041d0b02001080029060744003001c0001405131034240000b0a440c0d140d180c09610602d038607842d4a100380916070307203025030343d02c1900d4000390918101800325503241880d40b800e4020a02e081c1040b07241c1440407600038546140600b025903d511083c120301d000340044000280403960100e00440001e410040590207840240d9805c0503030f44084103589500746c01070b803000c02800300004503c2400d98124050301c104603004007006880e21903e00340003000d0404500014074501d10f803000442e545c5403000646004804a204540050f0340304c0004a00320f801c203010720700200301d40400c08052440d1810906 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 494966528 1250 494965278 494965307
    0x80106090f0e01030209131514060438031b1c0305040b0f091e0102061e0106120b030d03050901060b03060901050418050109121421070306080a05160503070b0a 70
    0x1f245015601c3e01e41c00d01c545c1d105046440c415440f01c07000150721050040e04c0c1d4010004440810004142400c100003480c01c4071031304165815206103044007070414960365201d0749000f6080c0c4400224001c03584a00201111f0707402c0c0304800c0d0300c1821a44207401030394035403d01d0f41f40e2540c602d880e061685a0502d41c1103210142d200b40d000300f14404107510f80c600c03604000405103021100c1d265144001a04043d00203010f611124044c01a94005111a100c09411118141000360314454640f50f0b04000d841d074042e102c0e81600c11550140d4995505520030340c480e082c05802042041c0e200d012506103032200795003142d4450344000040c41030b842d007035000d40020304580c4440240122542d41300c03403c1d83c524071020f4030502d040112071401c0540050a01088a240c082c41518050310100424807440350f090715240c2c2020107c0014041074069400440a0300111080380c100513180d107009951540719082000d44100c0f03002c0d0009007400c000507208203440c0840343c6a1b04040d003d601c1102c5909100500 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 494967778 1250 494966528 494966551
    0xb0402070f0b0402040e1c08070e031e01060f030c0302060a1b05070f09020a050d1e090b0603012d05060109030f0803060414011a0c01110a080106090f0e01030209 71
    0x400d0001d0018203501a15501c500700ea2505407409004220440c0c804081c5130381c1d282c101c644040c41e0b140091442090300e0015041081140d101d4010450300818070014841d0117121301100320700210322511034003090301790090080c424542c984415030004135192000600c81007903108144010701d04100640145d00301445c151130380440e02807401840b07000e00303041502c0b1504100b1051166654019108000d0080814103501d41088008024a82d2043ea0307045124241d840292031104007055012002c0303c50344990a100d540c0e424100405851425604188250b1810420602c50b50000c030851203480040981a11801c0e1085034800c05418010801070400003d803c3c007000140146078110b201501030f1452584915081c002d010803146442037204c00d03244440700401507407000c003900b0918510f0000480751034580c005501800b4203881218003100403808168203680503409000e1904131801692400c0b0041d82da2000543e28801074000d400d4200d41000051001d0309042031007c1d0028862400c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 494969028 1250 494967778 494967787
    0x7080903060705070302060c031302040e01140c0d0501140306160201020c0d08010e0708150f151902060106080906070c03050913020d0b090c04120203070e040318091a01030b0402 78
    0x3070428a044540002081d000f1074150141581040030940c041740d00210340b880c6042050b8071680075000302c60000d2086072141403841c00040c00707400c5143c40040c0e0103c000c01d2414404589a26a00060314203905546800c000180095004d00710701c000c200054082c106c00c2c2c0780c0414024054181000400540d03400b00440c5288010404c01d9174a14040b03542e545241e5410031400410003400603104208000141c014840c0380e0301c1c685944951500210f0340940d21116100205808400c0060401841d09000c2149204200c0803482d22110340455802d880d200d0381c031200c043e1405603080d02c015146901510000700301c940202e503614001402170800604000e070b80c0000035030f50700c01c045500ba031554010500c070001c0c1d101401180d03240d5030200c584d00d469141a2a04650074001d034847c2c0c0c00710310102e510600c1951030038015000980003800d8401e02501c0c3c9420081c2281d1004400843c0c1140291400142141341c2d1240100f0201e40b455202e01c01c5d0700d01130044001d80026858254016030800 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 494970278 1250 494969028 494969047
    0xa021e1014030439090e1c0e01090b030109020a080702061302091005030d0924080f130804031a0c07050c19080f010e0d0305011a1303080c0102031005040b06040b0708 73
    0x1400185100c4061380ca46030341501706009602940c206c5c000c40ca00b2984480c0590389520360811218261842c1031034200901d1180c1303001256a0400e40d40003803050600080040303401d504a0b001400100450340f2400429101d10808a9907030004841007525206250341100040c40d10081c4140c0154541d01600720080c0c43e600084d0402c0522036411012500e1400200300d4600e80b55200d60b0021080c0c00400070000151710003070b08454004211100d40100900054484184200030303141464000207050749440e16860084840050001444c10300c0c1d00060014804408520480340001c0d07102c0c0107003015004540610407102406075104200f1900d052001c00c00100820010700e2552074600081800c4880344803c03810032221404010401d8186401400041030180005800d0340c082c0b0001d40e0344030505211038154a100790401486e50f00000b80d001c0c0710802c150041c5000742c0d00d0761821f842c60b0741d9540400048039484c8070001c0e046070041c442081b03800b140c08060801e050240108034940328248 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 494971528 1250 494970278 494970353
    0x3011a071703070c0501050c0307050a1413030f20060904020a11010e0a0c05100906050703051306050306040506030d080c0706090501090803011518170a021e10140304 73
    0x121000c400080d1080304134002e01a09014407030300440f140c200d20780fa604060074000e0142c40394040340c0d4203021240c01900b0803c4102821124a88040c40b05c042ca00b54580c501101c0c040039a020a44250031300c040500c10b40415070420b180c89c0720009080300d00e4003c0307100502006c0d412141c107002c2444060440c0501c0a9828002c40351214800005008280300c07601e45078003640034542009018103c440e10701d0002d280c01c04039140955200e0704021341c44120f6880e089038503224509148501d2a980c11000404540180141d03005401c216400e1005540b041309141d900c80f03a9002d000300091042010503810b444003801004031900801c0040f480608a031640d0342500c450910495480350000010001e200c0c0c0b521b00c08201d20110700e040d60140810707a1340f503446650140200b140813809104240b030800f1040194030b40c05580946428003030200400314003006490307054218020100095010241c501c10800d600c1240200d000190850311a0340b911984480844040042c003e0303011110741d10008c50317 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 494972778 1250 494971528 494971531
    0x1b08190620042d0509130c03110a05010509090601051803150402040e0d0f12380319150e03030901021305010305061f140a120e0303011a071703 63
    0xd041034941e66614002102540e0302425441000801103208104000e1085803c4a404c07248100c810240544620200a00304020598000c0c28182c0d450800000c004964541c21a880022640d07103440751f0703403100107441511030740003c207620180d8100016000e6001c0d502510702003061251510310b074202040482c0c41c0c0020f000944981071000300404c421840d2501420b120f07281028090b1111004041e00070f440c08586110301780620401060701882d07001d00e58070102e085645000f11580340e65000403d5050609402d00c0c44000f070302e1300b44d03c1c00d030a0700b000038000741060220290070440741c0454440e10008000200c2c2040229102d24541ea011581080035500070700c0c035a000140e684880143c50103c0f02d01c60307400301e0b050504101c100000f903a5210085600600308902900080b60b9446003101c0000400c40034442c5002c000c589540c4640c0d00441049941a491000b0050300382c964104582c0c80c0030034402c0e04c40c484641c110920309800d844000d480c1c0d0038821205900682e4000300500c203f42c00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 494974028 1250 494972778 494972831
    0x80d110c0d05090f0d12030b04090602030f040b10140103020309010216050618010603021810230a091503080a1202181f08060607020a1505071b081906 66
    0x2c0802d4003d650b01e4403042d111031014080b034800b50703440d00b00d0340e40c0d210300c00110400701e06256803014224066102c03a00f24a10305640004115942d20740b0f82c140c80c40e511400d6034151112a10400003650044802074002e0555a151042d0001c030078202c001100070b544020300c0c8050030354080c030410001041c4d40110b84801d62290003e85500d00d0210006440000e00006c3d07075039180e040810410140e2144500070004c03030b801c80240601e0f59200d0500d0b08036001181d0040c030b074880b4070b8028010045603044419401d68822181c2000d00c50b81c99480500707582ea48840020b041100c2001080011007040c0208044580c909015144120110070340c0c04036001403140d0300c0350324680392600300c0b245488600720b098540c0c030b40c0074043c0e00c825015009260441c002c040798041c5071300240c41740030342d590244024006c103a0000c12900d0f01050480081258001c1081101d410702c01d103280365907454070343c0203200c103541000d0002c08400f400e0a2107088003d00306842502c25a584842c12400c440788234018052682 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 494975278 1250 494974028 494974037
    0xc14030f06180f0615100e1e0117070320130e04020d051615030c0207050603060a08100f0623130e0303040609020909010902090f060114070b07031107080d110c0d 71
    0x5c00c00074001c0c0c1c03400c018800020403071084101425551140036026084640d50b200c0c843e803904290040c7d0b01c074070301c4004c4140c2d0702400d241001541d55060708107645403054240016000c802844071034031240500b06042240c800700c00b0040c00907410800b45668098001003440990030f189444003400c001c1d981c00c404012413040d1000703002c03150003400a1180080c0501d000c0085d1814020000d407603113158080c05200b00d1002000c40c03030540d50b100403c40545003200941c0ea4405040760000000e00c050310340074001038104140041c1c0c50200e004441c0001070810401c80501c41d21004004050b43c00041c01c1c0c01060307072510b800d0250a020000340d442148141400516141c0038010000c41000c01032961102d6030400340d1520060315600d1605402c2415503485031003d0b01c4250050f200d951070340d8641d003283c00020500300c080c01b940320040380c06070040340c5042000b0504407035485075034807840b0700180c50301e14104202e804460031680003101c4156001819418141e0940f4500d0500d20186c0c10040003a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 494976528 1250 494975278 494975311
    0x182102120d0b0907110c0918011802120619020307030204030b0c0a020f0106080c01050c01110715062918060a03090b1510080a0b0405040c14030f06180f06 68
    0x5007407000440d80c004c80d1504000800d001c19500265176185000c280600401000307020400c008242d42c20000d01d504248024011000d031241916030300804001d0907032007803158500000c030ba4030300400c665000d00c0348060307011102d84500e103015020398005001802010303400c00c00000422205101e840c000d40442e859070b40c2d02c0300c82c80b030f0092a0080c07030451601203034905201085145000a80e150380708000307090140d11007058800d51401011004c07041001c0c2540041d10004008803114400c16400c02d45004001c00740d218048076100001ca085407842c65404071200c0900d050b80c000141100c5d11450701c035074081400a001141d140d4104001038804a511115501c041000ca4070344503038018056090280c1066007000082d1040e841d28010805104603100450000001d17074002c0c21007120050414000c0d4181403038010352000c0148110f00500310038a1a004040c9030101d02001e0740300e61100180aa41ca41c0954180b07940d45100303500700280310700e003040c40c00e62000b84a054441c54140052200f03c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 494977778 1250 494976528 494976551
    0x50403030f02280302070e090a02010210020403020603060105070807060f0f0605030a0f1202030d0c02071d04020109170f010509031201050118031e150609182102120d 73
    0x1211601c0510000c0d504081c8194080800f035140700a000b5850f4103181030507400301d0406904004054100e00e03d0700703031a0f604001d5500f400184a4110710f00c00c4c0d0031a1200c1e80b006047d07904a00483c040258442002c10208025600c920098581d030790050704c255240110640d1680308503195030565100fa07940f24614000401d1252040ca801080c069001c1c1c0301030b06081d9141901509882d00c010701550150481c03100300ba20030000c1c0c1d00e00549c00841080100501303580695100010b02c140f144410ad0040003141c0d100b5550001800740764117845040001d400d100703912480c180540c1c1c1c68003091043c0c00b00360342c60759000d0203080d00420b12800034555a2040c8850102e4241c0160003450500440341a01c4031950550038410045070b4201c981519003054494a60400884c080070240c0034210954113101e550f0516031144080702c5102e4400c20640c1c1400c8003060085e01c01c80e0001e0301c103200c00c1008103490441d03419000f001c42e40da88180e9180c80c005180120380703904031203404020207039503074469603c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 494979028 1250 494977778 494977787
    0x60609060f0e0a020c0d0905092811090a0906050f01020309010f0f18170105010503010c020d080c0f07230303040b1503101a01090b090901060f0c060c05040303 70
    0x1a10604005214190600d00c1d04440d1110038850030252031842c00c001103c4407415810f0f034400b04070714400e981900350200c10007072402c405030150512803c0e10801040c241030207800319409541000494800d007030206034030704001b440b140c0700164100038104400c004903910f1002400180c500342200140301030900060010300481d510b6158159441003040307524a80c1c2091a800012420f460109011900c00800311070640d00007031102904540c2c2d60000c80c1c8001c8a40422141c02400c00080201d6a0f0314002c050996280617880c0001d40c00032880504445c1c1708031091648030b104400c4a9141a0301c0262110f129440081c050780c0e00d0420030b0364900d60445c0018a104a01042d42c019402d6041c1034488912200025003002240f00e441c120003a200d4a0a0082c2000008607040401c0a054004d004c0b41d0a40001e041c10750006205501c0491205845000d03164150006041d041540e0f013840c8090354020144081403090144412031040080c803d03004000301102c00d60380b0345495501d149400741 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 494980278 1250 494979028 494979041
    0x108071701050108030924030403080610094502070c060e010923120c040b0102150c1b010204030c0303170603060c1605030c06090f031306180503030309070306 70
    0x10180d051000422004c0000020354441c140201d4040b40c0e8550000d02c4c1481007880f68a42d846800c00c04420081416000b2180360310466040d2042003500c031000c02c040b1044035450158030740707107000041030291001c5404028000801c00300381c1c041d1404001500d1b401c01182c401d440c040b810383c0010b80d030003c104c66200100c00600b4a810126102540f01e40041c10400c618000e4042c0214044035240c0412445002d00031000005001c0071015010026034944442060052a0050f420301841c0c4d1629440091003031590440a060b0b0940c1d034540604485040d8442000001c0c1d500c640c1d614200701040c01c0c4010070040d4803600d04840740d10326500d40940201400d000c24030310071046404020346a100451390960090058000c01e0703030b604c0c01a0403101c4080d00c1c224098134601c008035200c0c0d140e070000030340306000da0f466004803008020300c030f04180c0d903922906030390384025054203c0801504d1b0054140702240601d484a0146580c3c540c00840d2a540084442c2e00241d4003070b407410070274004903100d4031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 494981528 1250 494980278 494980319
    0x10209031c111507050d09150b040b030a030e041a1206090c060703020a060b041d030c060c0c3007081c0606091a0c0a2004051e0601020a0803010807 65
    0x1000c03e01c0c0e10114103140b0140040001c400e1180c0020b00b02036640303240c1d0001c16810f42c88101c8045051020180c000244504610540100d09c0c00c1d80d42d86403450001085c600140d0705590340041038190400340800761001c0d0342c00a140941d10300d54400b1a1b95940342e4800c0c0c481d0604010402860030416451420b180003261030700401d4100802404242d0209400c0059900070901003880f96000c1e01285c02040c10000f0321007800030305c1100711a064408801008070101501c01c0301e6064481800c5030641d440b8004c0c81280c07a5000c6946c81840042400c0505580142c96180380c2003007c0100071250568025442203900c0f43c00043d00140141c1030b0001e60b81c0e04102220100441c41c240000a4045105801112402c0c01c51b099451507545c5ca5000716202e00700c0d00740580711444051329240b1400c070401408603038095441800c4000b1810188910f03841054002990f00110794400d49150700040040e00003411800f841000001107085070008500900c50720006060b100e203040000020040c0b0040705 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 494982778 1250 494981528 494981533
    0x706080f1012020904051c0906020709022802010906150905070905011d120d0207081902060f07021801060e03210f0310080a05060f010e040506070e03010209031c11 72
    0x41c858420750390340001007640d0541c4c0900380c43e01d803030804070b24120314016812419401d40780c002001d2548544804c0840d0440d030201c804282d12b0720b034040d05034040e880b40060b008080c58402e01c14041e9000040759603c45c28000040c1401c0c40da2a19001e8401ca40d0725120203a03d900c4082010000354480d0581c800ba0606e0448601828000003c00d070340032020402c461650010b0f441103480d90707442000480c41e950310003118540c04401802a40ba501301c0d12071030015014410b209000083c501450302000d5070b008000902c1c1541b400807050441d008443c042e40c109040c0c040400107040101d004a020f442580c0b20b0800613111202017514064024203c04040e60a0520b0b800b00100641c1c1920f00c0280c0700a04152241d40703d4441100500c0310358001c2201342b01d0882400140000032a1050107800315401c0702c082d0340e0b00e61050000701d9900740c8008000b9408040080c5100c0d110b20280c00080d9801000035181111500000b0300d0700d030481b942022080b0442c04003402180e00b103c00214400c006002 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 494984028 1250 494982778 494982811
    0x1205030f010b0a0c02011101110c10060608370207060504050c100c0b070e060301030c06020c0f1309060e01150510020d0212030403142701090503030a030e030403050706080f 76
    0xf0024442da00d01240217051001c07404400600315402e41242081900d05d4554507241c000302d01c4401da07551750f000303078428001c3e113440c5004c83c05600c9011445c4c030400040c01e003c07040c21890b40400d000e040c2200d00022b0030f444032190a00500e800ca00040117454024080800d6a051a052050a1104e000c580a01c2034840f006600211a0845540e1021075041203800003903940d001402e8840000d02d048140c1d0140c0000b0001c410000840204401d0310425401c48030641c0908080c041100f600f200000d500101121628090540030380145d0744580c40740070041104015404170609407100d144070944910701d540d2050006040a5080720300210312480200219803440401940b1506104e0360b082d038018000000405050040d485a0103d2012075680c03981c4518043d480c030030503060204c120400c180074030040c0e4042e601c101203c0c015140300901075490004a840154001d001860007a00381d40003c2c040007011840038003950000388069202e00d119490504442e80d60080c0007045140c1041c0b5004 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 494985278 1250 494984028 494984047
    0x506090109180e060c0309071a030f060a0302030d0c0614010b0a080c070f030c0b0f010f05040221010e0601090803130306180b010611070e0c0a050f071205030f010b 72
    0x100c440455481181c003880108140c050b42c8090100221101001d00c20070007403010400e00c90303004511600c0707100c0a54500c9511105018a580c20060300030020080034404a0b6081441c0603006d03402c841c0040c040d00c034456880d80440e04041c0d0410300d030404187c80c2a500c00a012480c0500038441c60302a101580960602e8201c0c05940623110000080224800002d05078074406400c0318582604104812444581854000c103401c540c100f04880700d14401e4003003060392080c9800c1505884200c480484018180003e03c0001d42000c494801421400114900d06c035910301c00d614080c01c415183c2c1d205500d08100050711404481e071090310258000c000c1114181911208801520b034032100200d418150352410546588207030302c3c045e10380c100386400029401c0c3c20107007012407a01c4040c160b8443c1d50350390300f00e003190850855440d650b8002c02c2104942c0305106030010a9024021003119042c00c6094031540d403400d0030f6408540214500100b8000c0a0344a01000c5004240039641c0916058000703 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 494986528 1250 494985278 494985287
    0x22b0c0f0801050112110121020417010b0a09050603030702060c01060509061509040903030f0f0f0f0e0a080d0e1e10050403200705031207020405100302060a050d1b0507050705060901 80
    0x5190240c40800c0386800303580248e1007448101d4407454500d5640c414070204410040003540a40302c3c0f41036100300c1806003800e484040c002c8034800030f40248000003041c41c01c010300f006860300900c5143c1c503000800c24200141e440d0800780c14401c0c20301000048050500342409400ca41c00b5000610501c440b92031803030254100001c88100b08010340c1d02141c141c20b1454250701a20103521010f006a00b0103041206100040d0320030f24040070000d109201d01d16849100c03000301c2d8034103030000402da0440420b40c400314502c0c100514444452441c001103246480c62108d06010309440c0280c1c10322003440704c00d00341550800c009050817070960350800c030700e0400795400341801441d541c060203481034800e100211550240400c0707005060280a56106000b04080106540d010745000c9100764580000700307200300c1083c2500000d80c0e6014200c18a842c0070350005603243d41064039000c1c2203e4840c420613a400c0c2c640f103195420207260341c94943d00c42c0c0d03103072424605225007034000e1707402003105005046031070313911 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 494987778 1250 494986528 494986559
    0xb0a05010e0607080d06050a27060503070b03060310020a170702151303120c020d1404050a0e0a06080a12031a010203040b0706020d0504030c0b090a050a022b0c0f08010501 75
    0x301045d51784640740850320143c00240e00072a4041c0b110980021540800c95000307640d090a10316900080140704a22003c484660085c241c15511080d82072010520b842e00541c0c01c00700040481d00c9201440c081003003640e2040c0c00440c0016510450880304004820083d074110541d13002400504124201c1303161424401072600c0711022020441209050190754180384003204a80244410b00c50140301941d11075881d4400c000040d511901e00780c440d00381c0c400b0340c1c0c161030f0300400d211b820620340900c10382d00c007402400c403c1000c2d50b10390300000c00300d404024129140d48104107000381002c0e1504041d044039045050007641030400300c00000c00741e9010084038196034250f40c42c141c40d400181842030090151200600e140780c0303000d00f804141500100003030380d0300c1d02c0303250900300b01d0ba15100400d441d5400e180000340f460784514048401840d1004003140501a8244541e10444205031601d40303142502d002034400301c2e6111810701004107a0f80c09103024014480c000d00c280d5140c48400300c0603804 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 494989028 1250 494987778 494987783
    0x90a05150411030601080c0a06020f0703060903110d1d0301090c030206032a0c0d11030702010302030402130c080f100b09190512030406030501050a0e06130608100b0a05010e0607 78
    0x251000060400901e4003440070b0008010381100c0c055030316000215681c61020050764840c051000700041e0300c920000b024160301d00d280c00a0f001d554555030304c003006801e1100c0e089040c00f440c0322411510074410030625408030b4050b0346807081540320000104562034145002d9002c0d1f4101081c410105810410364021294141c812990700c2d03580788c1c0300701243d249240c6421071055110f4a4426648a01d401500c1251041030550b0410403003104c06507281400c102d1070220702c0c4c10a00004c00036600aa0285a0050019201804d1080550a032008942070049020041107541c0140651000030008090307002200c11444075081c0d00303000840f41c0c03600a075150544100d03000c1c0c07401e0380c107286a404131400400380500342c200b880030b2580ea21034494100e03000c1d0f000080d20b480c0c0001018502146100b04840c1d2034103850b941d68a8240c01e01c0700012100b2a020200d90301c50600055440c0200590081043d05c0360000a02496a03020010640469031005040082c94801615142c0d0380c1c40c1101c4186a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 494990278 1250 494989028 494989063
    0x250201090e01031a0603030c03070b1b03190e1005240915040510030b09100f020301150e0109030b15030106080f060c16020a03060903110a12030e10051806090a05 71
    0x40d2034000091543c461048c1802d02ea00010030031700b003000004c1c20102c0c040c3e0f44452400030380b004103440b100c0e454002100d0707420080c8240c41160010601940c0b085103910716060941d06030309244070000b01a20810342c0d031080031000f03034000320800120703141040740c02240c22a4550340c14101400405401c54000205070703c03c41d590b4001c515520b01020000c001954480610383c80c619082600720b445080142004e80c1c1d8500304242c01c240d000f403e100b00d07411f0381c5940f05844280504200102d502d05a0400c010303050000c0c041c1c000c00454240f12400e80b0501c012040396040b45003103400d050030345038140e20290142e8000a0741482d403210101f0031136402a4102c080340c6d01c5000704c0c080890389a10b6510060340040c0b0711a03020090124a80110589900946440307641152212080e40d5450103140060058240441d42800c1980320341c00c4004d120f0244811545d0110f1810724140844006560444141d4204101112042e405020965002010801803c0c140e1101c3d1500c94407550380900540440 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 494991528 1250 494990278 494990281
    0x2c070803040902160507060302070b1317031305070803030108120c030d150306020a0503160e01020606011101151503060e040312050712140a0b030304030c0b0f250201090e01031a 78
    0x21403050300001e8134190000c08880c0101d030303124805002903220040c00e071207213841e800001e2200d0001307011481c1d0441d880300d403040010600340c052414907040135000011000c0380306404404039000b00020005000c17034102955482d40b401c00440e10b0120360381000d00300c414003400b048002103004810745042080c0c041d00440e400c805841006480304407500010301281c80424404019070303000000e1071040f200307801001240c0d005248151085606c0c0031506006a00c0302c4001817003540308400244d400700700580003050311222458402e074402007907046007001d152921060007210394940280c0008041d100030900140c03d040e10010046911780c1d00d9a10010b499402040c11113204008000344244174601c100f000c8141c0343c800c000c5091003950a404400d0400c80745440700d1a01004071400c5030346c8055656243c600c0c017018071001c0c4d04551360403080301e01c0c24000610034180c07001d0145000e2417400d0110a07000b02da07100140008245401140c680c8200d04010b000007440451000340400c041000c40c5041d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 494992778 1250 494991528 494991547
    0x1406030a03200a0803040b0103060513080a0f110a0302030904051509010303110a150509070509060f130917030103060509060709050607020a0f0f210201020d140405042c070803040902 80
    0x1c010700f0f1500208041d000004003c180103041074540d05a81c03103028240300359140c000204003005440000502540c9007080001015405805400c14803081e504015854030450304149081c44110351058001d6000012601c20034905445007581c482c9080161000e81d6403a80d010503144130781408000e05100c4868500700ca4403a0401415071791a0340149980e990341030050703451020300019103101c06280701d90a00403505180c00980c580c454013010784041d9000b0b82d43c10410a1001c00118140e41e15a40c440c24003002c69454408140d185020300c0b09140d89500d18a00f0404490008001046a802000500078000d80c0b010144044036001c840c0140c66040170b0000903100c079565406450080c4404034009403010002420a00b16045410600d0200054035054210307607500107402801608060048000c0c280590030b801030b80c100e9910010b0900740c41d403021400310b0b802d41098138200031200350100d8080c2da4910120518804d1680504001890420115503c2c043e5029200c0e000c1d4012032200c10 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 494994028 1250 494992778 494992783
    0x9040e2805012910030908090d080f03040b070801080a030504090f0e0708010f0e0313092c15060102210309101d070f081207020f0904061406030a0320 66
    0x2c2c02460312030f420380041e2612190342040340d000c0706203500a091401400c001e0358000e200f0714900c0c40e0002d105c20324000038901002040d00309031104035100da00900c491410700c1604005580b103107200c0d0400b5400c900300880094185071059201d0041d40c0d00a4450000003a880703c250740448040360404608002400f03c1c1902030070310354006040503c1100f40004400c00150400000f24000a00401c010842d41040e00d48030704c226640004c0154000e44108071054990707101d03448030106a0541e0309644042e080d0310400da4101d030340308119a40b1642c0300c01c03000e494002d8065000b0200b40000d2100d00d001442c40040000c004d12580820140400040c010a1007031101c90341503840c0e1102040402564610000c1145c40c100e80140184948100407600c800401e0140040c6c0314070200410000a004d82c180080c0d601000d000c90300003081c02042802901e84d1080750b4000c0e40b0451000c108001c4d00c1081c403580880c000c0609110f548000505408640c0041041c0c001e41c44c2d0804001d40c0e07100380d43c03440c3c0c03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 494995278 1250 494994028 494994041
    0xe1e0c0408030d090c09090f1b0b0711031920040603150509071d1609050d080304051009210305060d030e0f030303010621090206180f03010e0309040e280501 69
    0x4405042c84007c008000903039400fa04a64840c00c0403100308002d602800500320900d0107810307508501000107401040d43c210140c04d00f400014126014a40003400c0110000001c0d40c04850703041031201e2140b6800c100152582d40e00800b905c00300800c501e1a201c51070b5a85e40c1001c0480c3c0e250381c62012481e440c5081c442030001e0407484d0b109103207504000c0180c5080e90000c98600e0307601254000c602070214401c080e105c041f42c07002040d42000404a03213504c0740342d50015104485070701c11a8460b4424440c14040c90315041d0003922a00c5102c21040501c0e25621034807000c40041526100400949603107410301c800081d0b400d8507014031a001d018000c00d02e8665604500c5500d03200210001400741e61100100c600c15240c49903500282c80c903500410240c5081c00c1c1e001b035202a00340f00c149000c00d03915120f24207001004101d034880e1044440440d0848110090240c90740c0c00016401c102070070540514005409003038010803075403217a02c04036904240400c842103050804060b0500070711209400c8503 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 494996528 1250 494995278 494995289
    0x130302032401050f09010b18090a0204150e061b12070b0402121606050307120f050a1113050f060d1415040e0d05130e1e0c0408030d090c 60
    0xd5141581c0340d08000103070412a442114150001c00000c40d003414180d4a0310100303400030f00002066402c03c142c2462580003925035a0010344e103544441001ea40c1c1c3d1249a004144600c0d0040e640c1f420080c13045807460412000c0d4042c4284099901c0c041c0c2c4139130040307840d014544003070405120702c01e541c51403c01e000490415210700d03000c00c00e00c050040d2000c00c07500992085a06540a80245520360f803605206109100d400100300c004102c075500410007550f0206040c80d21103090440e00003500c00301e0710b261440400741903403a0200b000e84a1b892041002c4032641c180094280703008500340c5100541d003801030310700824034420107452a80302c040a4658001400c3d4003032211400d002e07040b1a80010443d0001c407480204580c071016030070300f803080d90b40b900d81c59400750840703401c4214152039961008002000481d818040010091302e50300c05680104004003607114600100c0b408070414140180a00b01460800c0008000c840030000480300e980800c0c03000410007101c40c2c20440030040195020 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 494997778 1250 494996528 494996533
    0x50f091f0b040f051f0806060d030908061e01170c0d0804050904050115050105030c070f05070f090e07060201020901020a03120b130c11010e1509100c0f030f0b090a0213030203 77
    0x900e030702a00358210601c035a01d105c2c10394046034940c00700c5410000c036500c18070003940c010b13102107050303800c2402d98069800d000b4282035001d160ba070748003180f800100311003c05070070384400e0007449030850000a0b18011705082e0680c00003000d01f0100310340c8500000d60130b00e205103010b0322240c04200c503010542d030090500400d003042c949428281f00d0b0180420f060804c0000c0e04401c80410030398000d10035203000700c91908400c0e040c03421554640d815100190404e03159445000c2c40001c40d4481c41c001000a004160f2000c503415010100080c07414605400000c10369005000d07140300e59071f00048580946403d4905004255811002c0900800a4800007600308000b400148040065500b281c607920340b060340d40d10401070f4000501803c941c0220031180150b00302602444107100d211110300c0c0c0010981084d2211980004990b01c00ca03140050308101040c442030350101015090712800802c10a01c9009009000f01000095014000141b01e546c3c02c59001c240c89009071100c440d08400355902408 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 494999028 1250 494997778 494997791
    0x30c1a15120c12030706180b0109050a060b0c030a0813081903020408010f06061701080c0d0303020c03070609050d0906080a02031e0108030306041508030711011701060507020103050f091f0b04 84
    0x814a803203a20551040e51414201f0b485e01d91582c1c11031000c0d817203c0780c1101010000340d0a1040c110090a4090102044252501e40208808104c1c10080000c442803000941e9188180c0070050b00100005011207503000f000d044000c0480ca1030b408036004005548a03241913644540d41c00e81c0240900d4019403980d6280c82d07281c00d6003103415031100050b581d9544a0181884010b00400ca40c14424044d11249400031400d00700750381898051041054840d0401505100304280503d145030440c807400d98000da242c900074010f020301400141c824110030b02e01422120b040c010081c4c060348002d8100008240d0001c0007508080702510842a040496455461603595581c01d195403904191031701407040e490212132004c5040750b10f085100b201c00c03102c06581002c07281d448124116100400041c1480120700100b080350304801d840b64007801a50b110103072503070f84500006080380c1000b01000c0c4c58004040900524140004082c2140c82c0d404100034640078800c1d41103006081c2e141074041c0c10030300b0180c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 495000278 1250 494999028 494999059
    0x9010c05061e22031b021c061b0207050108181501080606030c0f09100f03060615050304020f0d020301020c010e0a17041203141303030c1a15120c 64
    0x500440340c0c50400241c00b81070789502e0442449044030b81080090f82c040582e1101c0000e0080401070b440211800400c0d01c0011a9008a101c420090005000d10348010804104010340340c032603040c141a590750342d101918001800659100250b020b0715040c003010750001020f441e41030b20807140c0700c41d215042c6c92090700c0c2000c84d100c2e0b0072020b0084088902070040080c09a060005203003403d594000c20240313851001205111070000040c0174194204048a00400c50309040e11004004512900c00001c910f4a40004000b09081c80d1000004000040080c000940c2d254601e0f40c4e07a089017140c0b2402030000500c0040c0c024031407500c2d4144e05500b040351040542d5004900801c0260060402480a100079001c102052042d03000c1c881c00105000120030201c0c0c450503246c2c13014070300d110041c0d24081d90000410b00814195204078006044144118200300040d07010340c0300000c00b40c031b901107182400039660f019805011070072406124844c0352143c4280040180c3c904148014014240c0c2140f0003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 495001528 1250 495000278 495000301
    0x60b0f0307080105100221090406032d02060306100309060515090c1e070c030506011206140402011e0c06050906040c0b030702031c02071a0105040b01030908090609010c0506 76
    0x840d80302022810b000000625030a04103410719100e800c56000d00200d0350502c211411f451000b00000000c21410b000404a603100d6210b040041c40c014544d4902007080000b001060000c4002c440c010380007003460744d400680350582581e0700840c0c210751261a500c46601c0031802000c100c640981454140002e00c084000081c817080d5140005550004541d50b520409074810300c90b004a82808004810180c20792070a44c1010340161840380d90884a0980c0e80d81720107143c81030a80102d494035a0003100c0d8010021304d8071504512020098516000b444c003900043e00c0400c024140091703002204040c145002d10858230411150391103d4100403900304440e58a6980c40111411540d810140e18080355141003801030320301c24581a4011490322143c0002c0c1042c0ca1100030407080032907001e0000340c0c0043d0b10351512403012200b511000c002d030b40c03502d010403041e00d03d0402050706040c40c00c00c501c4081182401141c0b6020426240c2507034031004c040040301c20321a0014041c100d805071005101104851 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 495002778 1250 495001528 495001531
    0x80405030d03090b0f040c0f08060708090f120315040203010b0901020f0f0607050f1902010525020307060b030c030303250e0f1012020c030903010509070302180a060b0f03 75
    0x1502140c01c0d01003090000c0e030807960054001340c4a000c0d141c1c00254805105c1d40c1d950380c0a84030300401400180d4443c0080c0310002d8030f4101c0070b4260030601c20804816441207200358071076000c20003000c444c804441010749502c2401c1491111017400000200b551590401d00030510f00040d100315600d41c0d440c17401a8050304841ca41c60b00500601008040d0084009198041203548501038001174940e2030058540d03a0048084c851580418404070700c45401c20b218111002034580c0000c141480d042c140e610b15013030840016510300802164082c60544c0c008240c0304800d0f403040c40001d1031426580040c3c6449040e0b840c16905210020402032001c40250a45600301c0f1300d0028503d850400410981c0c641241c0301c400e6070010b4220034800c190346031213400207182928604000000c1c1803c406070341c0699102603c8002d00341d000040200503828244101c0b90f10030b0110014001d40360440c0e0000d28494024140203681204150109800000d250300400c01010102c1102e941c9020007070034404590070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 495004028 1250 495002778 495002789
    0x607061109061206030c012f01090f0302010902030f0f07062a05100b0f060703080406090c0f2d0b0f040801020d090629120f060a1e0b0607060b06070606030804 70
    0x341d800b8102142d4003a007144010140d45c13072030104a4580703c15510f110309208d081c0c460880d64890140e8801300f21030f580000b405a00035400801c05441b81c0c01850f25000d2400e07030302c1400303030f00001e09034a009102042c90f5003a90028a0301203102c400982e07030001e9414171a03d070320490402018100b030412400084085860009010501c41e84000404101e80e2242e200c4005401a200700966000240b0502c1010f5019105150004400c80b2548942a0702c0660743c0200500800c100014422600c0790003501d0403404e920010202c16601c2500124002c4000380b0690040b02c0021400c511551901c074150b5001d1300d000070086403075124203c40507000c2d044a101c03d4231074920300310540301a420100102d4126620a0281c0407489c130003c424040c0e0303034101c507640717a0850050a0520301c1441040c040c0303a0203051200d0011030f100300001600174034004520003802ca0039180400c11800b6850341000d4820803500301800003150361414010400c80e02c00c0c0c08000740000d1130000044104545c5201500036590b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 495005278 1250 495004028 495004033
    0x80f0303060913020f0d06091a150402070c03291003021002061e090f03070f0318140d0c18061802180d03050405090a0207031d060706110906120603 65
    0x12a2a4080c030300c4039483c0700f4042d421a038612038800305405c0c882c4508a14a1040100040c4c0c4c401584554441c0b40c000140496a14518418002d00c070f200141c40030702c0e12908440444c42e265a60750740d080c0c1410039120013000d41507040c0a00160380741a0001040012502e0032988091070b1011700b212420105000032407107280400c40140d1a180b000480520403103180d600b2081c4029100342840301960014078900c140e11461f03a040c0c04181c000c5c00540442480381c2420345480340a0f250260046216204806086400c05400c004003160305101d1a151802130f10441e04e0a43c0500f0a00c07000c0c030342908080040390007440d20a551313030305ca5408002210451903049001c030803102d10311780980c1701e01c51a610300158806281a0350b49031510088020394400e06042e403a0070f903074801083e0001d01c21100482000d03804194501419009012642c0701c1c1e82d40d60400111000350000140c041c050000c0142500d6942c1021400c0c08503a181283c1d1804802060981c48241b03481a540502404454103802070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 495006528 1250 495005278 495005281
    0x10e09190e100b03060f220503090a0603151508181911040e031305040b03010212010303090f06030c12200316090e04020120010b040207080405040b0f1018080f03030609 74
    0x110400c803480c0903180303420281c0c6414500ca000e50b6003040ca100c0052355140010041034000356a0103902d0f100500040d10042180c44081c0402c0c03d103003a1590041030351641d1401c021203140c0d80110308903481800c4120620405260b40c400780e10b0140c3d8080300b020342c10111061001881416031750380e0700d00c650441c8c050100614010103192240120f0405204c0051003080c2030040c4e16107900000b02c541c10207000182445c40c2034000d032024032801e038000e80110356020401d0240e10b8100116501030f10a604043c48841001031b0003c00d40440c0300b003424412aa50600900b0405203480003624021402e0342244d2a8184600b0300e10148564001d8a00494088000000e210294901c40c2d840303a50161a0b101180b81ea50350110840f461700342c00300c2415545d0354180b0590307540e40d1000d49015070152007400e03291410207060104903601d80c200a4854070b10f0b0003801c1c8003a601d502d4200c0e500c104503d0610301480c1c0a403030622a0f100590840c031214090018903910300480000610300c82c0b442154080b0300f9 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 495007778 1250 495006528 495006541
    0x7050403050c0a0f0501110a0501021206100503010e04030e040b130c0e0117040602070302030f0c0d0e01020606090a18240c0c05030f0a050d0c0806090105010e09190e100b0306 77
    0x40a480d0301c21310080305aa0a800c001a60107020060010030803d000d40d0500041e6580d11400c980c80303030207481900d090b694144051400d145009460002050a0161455050501c054842c02e0001d10080420050106ca02078586442c0c105500030720700030b04005034600c807400d031350700c007a090204a00d0001003180160000d030350700c18528104c04420740f0840e1400c036100d40e202c4d1400b9602400e0b040d01980b10400080e04588800c400800306a107445029000c2481070040081004d0020081c10307045620800c184001c1d5a614041203820002e92000020100c1001910065095915401a00300503130101c2c0850103416029061041e66121403013040808020001601d0200071400040d26a50060007444065020f0800034500c10030a8200181400c0403156030100f0317581c01c043c82c200040c450905000103414110701040c0500710034203042c0e42005080c004502034120052040d400c0034001c80028102d4005c0c0c0d400800204041801d03500035880c00782c0d210010308030340240203000780f1558002a04 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 495009028 1250 495007778 495007789
    0x60a0b090a020f04030b0405012c010f05060306130204150b120108030c03070b0406060e041202010b030106150c0c1a03040c0e0708060d0203100614040f0212060114040e07050403050c 80
    0x4100f12944505080c116201d50582c1400244211425940e40e007241c00145000340041503200c0c4c03404001003030070340c0e001c05050940341980440800c040c1018140000c0b0b07035002c5082a8030030200303205280706250500014001c0d1484c0303000c0e00d2168490b8100032510304c0403040101800319201961668a0340e0b101d41880c1d40748113564076110343d0b81041c003183d00000c1e500f04215400134021000070540a48890b270721503450a040d83d0845000340072522a045807138080c007500d034148008400801c181071a00d110300040c0700300801400c0810803000b00d118100026940c103600034000304040e11200c0804100c9051055005960903110401c05180c0040d4840c416486244100c3d4141e503008917688030304042c0000c050000c60200c0e8540035407160827512a4031841100d0060191095140608801c9000e110854a040302e901036294010400e0550300040c480156400c0310083c40d180c03d609d000030240d40d08600541d0860050319490200b40a25107510034050000c3c1d0703001d40300307840000400340708100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 495010278 1250 495009028 495009037
    0x30c0b0601210605010314040201091a090319030e09040b010b221e210b070c05010911040c02030403020603011a0f0d02030a050a0e0c041e0501080a031107180902060c060a0b090a02 79
    0x340090008bc1d0148142e6200710340c4091003c030440c0c06075042c8251080081d060034002c00843c00e200d0802340c2c0d10824140d0007200400030307003c1500c502d202424542c0b5081c43e400700500920004400004072350344100c56030603d0140320ba903580d14990519071101c064003000c0e00481180c03141491558404550001200071070202610004004007002d0100e40d1000ca111a004048501f4003031500c11840200780203004228026100340f4006020500100820046401d2422580c0442d0310a000038001078032050210fa056900d80a091900880d078101c034003070742d0b2003210400ba0440030f0114040c11002c000e600030350b0003440505024052130b035400c0001401c0381c0d1030021001d40c81d40240722031a143d040942c00316505100c1ca00c607114202c0e03500c0030b000069500a91262031141c0c0300b10658014564000440e2441c000050090505540381400100d0080004a0340318981a40d9002000071551084101d0b071001d9080002e40d0311514004580b1801400c100c4035580c01504400002400020b4520071034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 495011528 1250 495010278 495010283
    0x9030a050d030e1606031505101101060b040305100b03250603111830030d06090c02030d0b010207030c0e070801060e1e1315080c0a03030c0b060121060501031404 71
    0x301300071441c15000320080c1600030065074001071582d0300401c660b03d1340c01c140c800d0382c580354442040ca036035455095400c6460380c1d4840b040c809010300091001480c0814441c0d16582c0f5084003046a285000019080110714000541d420b07c1c0f01410081e204060000481290f402c2d4500700503d040c2000d820442d4030442e2211010140030200e00d420501d041901980c4001c40103810107146846200d415040c0c0c801e0700d101346103c0e41f022411a00d0b944c10382c05001c010b400c0c0ba800502c1000c038031b544041d54a005802003000443d0721214418041d901c03c000080042d80c1258440d84000e84d2542640044030054802d0000180b840d03001042d00ca0250f1840d503d004005000200422040c0c054550301d50403088180394400700804850040b182d4038000c1c100d075481a00c00130083d49241c498203034640500b9444140c0a41c0c0f04000c10030121760080140713682c0680180450340c09031385090040307d0f40c1c90714103404910780207c501013100300c00c07007030340250240c41080e00d0030000c544405620018580d42102e00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 495012778 1250 495011528 495011563
    0xb04020d05041208070f050409200c010207061b090b07050f0303040819090f0b16020a06030507170c03040206070809130501060e09010f300503030a0b040504020f060a0509030a050d030e 81
    0x41240c031048ae4011810342000240c001050843d040710341029034020040b07550329a4000c030f40c000c1408810f2140c031003818981001c0f40750242c2900c101602021061155a0811002050722004c2c0709041c001195000c49076800d0b02d690f890580350080203038011070000002c9190240b400d200312030243e003c3c1001e50700340905900c032107881d001c00081154043c02d1078a03116400c807000440146c84688504010b403e02e0745002c501460200c100034030b03280c03003032940c0c8041c02c030000c0030b000741c1c4812a01100d40068041c0c403440ea90790007504000c01d051080040b1190819523429907001117144aa11003410b0310b000740d50b020603160a02040000030b403403e0043c5021104600020030401090805c41c203801400114480300e442d03450800404202104802618590000020841c1038605486403002c041c50889003000f060800f5004202c6200c1442c42c0107000f064000b8071904503038001e10070b45040000c0181160012a10b61030311a071242d003003c00c6080440c0c1071100c0014020000300c1c003240341c940f90700c00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 495014028 1250 495012778 495012787
    0xe0a06090c021c1b0c0602010b0303071104051e0f040201030e1212060d08040b0309100603030e0d0318080c090603010612031803150209010e061305040b04020d05041208070f05 77
    0x35a00c0d14a2070204a4002c0c0000c0c5015041d02c00700106143d08045c3c0616085508a498038501a085d1082c6001c014800e4008007d0b810024003032000c5000c80c0d480c1501d00281560721081c684021049071036034041c400c7d401c0010492226202d034070300743c403c6200380d07800d00407803010b1000300342c0c0c40b03060310746041043d4018010301d4200302004000301c1d44100d00410782c405420050321103240a5001e9003001600d80c00c0001000701ea0a0100030381003c07009240001c01c1220f2464400409504007880d50511990840c5c3d03088003418803402d5000807011041e413008042642da009200c0e910003101c51030034020121000095160301c0d06200c0c0c14100c0713001d03545c0c0d012001d1140d50300f1184c81c1d05030105103180491000010004c86e400c90310521881003440d0006035038070100300001d80095071070202c19101c2e02d41008443c10180540300d80e0401c6480517500460780180b83c5c00014060b01401160641e0146014100001c2c000c0d0401400700c10300307182e2a610b240340c6074404100d514085640d03020f80480c07010030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 495015278 1250 495014028 495014053
    0x5041b02070f1202040b060f030c0a17061f020703120302120c070209130f080a09080c12031c02040503010c05120c040602060705030411100f031406030a080702190e0a06090c02 77
    0x8000c1410f58000400d40d910b0010b030040340d23010942058503030300405a40072401040c0d0513002001e0010000981500038124034210b80002c1034410b044082c00e140c003440c012504075035402045984040c41c1c0c4042941d0b8100f440880080c002c2d0005640140381c10b11102c0071031075022414044485c0b858010b4554066642d441d07246003030000d01860100c40690508000c0d001140410026220804050759a01b000a1030511868a442c0b59082803900ca24085001c20307080c9c06c00001110010503031120040c06096001026200a000b40d50100d5099400c1c04414805658840001d1420041c0004080101d031039050a052450095010b40f6002d0703403126011903403580c060005540c0c014030441c80d80303001e02e1b50940484c407295080d00740440801c001e02d4400202d00d4142c010300b40c603a800e01c80c402a4915100700042d644a01c980005007620000140440c299100c1c3c40c8211640100c0800c0d203940c3c00e80d02c42c1d2088030f101c4100c0e015040c0764500000031039011258020703c0748401140d80140480e0443e603 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 495016528 1250 495015278 495015281
    0x40612080a090e10051e09010e10080106090b091b031302220b091602061f0312080a0b0108010302030c0f0f040c030f0e01060803120703020405041b02070f120204 71
    0x8a55007010301440d1800000c14000c3c18007142d00c2110607003002d8058a1500d0244241507261000d1420140c40942a000068407031214250444030710f8980c10825071201804403024031400d400620381542441c601044900e0303160001d04418034142d4601c440e90ba29002c0840c0000005840803156060030400f04042e4581c141d490940030340000e184440305042114150401000081c199072929260582c1d012a4600054110b50250f441c103087c1060a6001c00003d447d40390041151100d00d150780d0043c110810396095200255610014008601d5032480c0041e1595034101d40004855081c1035048048d54810306465040701c0d4083c1c001c0c4040003100d42041413021a140744281c1040c03071038a1341030640c2d5540c041c5611104d8952400100044600b8051041d5180044407001503810103408002c02500081114000045040d9804d055207944800300d000e889168400c55205042551a00e00f04c2c0f824403003020707801c0c0f8039000c07520815a17840348070300c61500922858140584840351070002d81401d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 495017778 1250 495016528 495016537
    0x60b01120f0506031204120b0415090f050c0105071e02030c0a1d0906040c060f020106050406060f020d02060702030313020604050409030c140106080a2916090504061208 74
    0x5040c903032109014518000c040720301d019803100700e46482c1e00501ca41401c080c051240c051441c1a0401d140500b41030490130341d0886103078002c100c070080c0d2001400b4062240580e140d0220141c0c0d0600008441d414107115600304404159024059680000320035801001210441c40e40041040103440300f00042200d030703450300e00f026038142c00740c1030f950200c99680e4038018000d030480c00c42492880c0c1007100c020848440040c440d520396400142408041640f006041c401c890f0903250244c1189400c0b44120301506a6034422504141890004945142c2003c0c555180070000d5084445c900c0e4680401c036030781c50f03040c0c5080025800810110342c1d084c28140d10312102d140040c1c0309516056480000c00c08542d04004141c0c009440d0356243c808001034414101d400c1410345000344101402d02d0500d40e1030b0611044014561045100d2094500c2600c3c0d0302c2988101c1d1707506008c401450301021000c801450398080c0d01c0000c120b0b2002181d40e160602c0391800f03031550100c80c00240e8540f03980e1200c02d07074030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 495019028 1250 495017778 495017801
    0x120207080912010c390506070905010518040506010504080f0d270302060c010e0f01020301150206150d1a04062c191109010f090f020306130c200109020909060906010306 74
    0xd003103442030b00b0080117040043c0c4040c0f040d001040b6510780424018001c92994000c1410883c0801103408507205904100c5d040e50400c94000844d525031b540140c46600c140e500201e40c170301414030030b20f083c6200400e603400d0071600c036144c01c1e01910800c0848a20852591003801c0019040c4500340b000d8180b030005440150400000041c000c0140f6482900d412901d4010320f009a40010040c0480810f5450311491081c1c2400142014140340040004400303008440354004e910200d060801c1c4444440d002c8092000040300b4038845c00d280c10044040c040d400c40030b40086550302100f01d605013541012407010061040a45580c000300d503580c0e03c80001e081c10030340c0c2181907084c05410580d2070101d114020322500c108140010f14110440c030503140b2044800321041e01c10b00130400d258594480800078440f40100000e014080c070700003681d640c00e480d40601c005403403401003800300d6403056020710500e600031110800580e43c4c007441c4980e0b800301211000515045500108009111a080714400c0c40 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 495020278 1250 495019028 495019097
    0xf060c030e061b2502030c12120a090e0a140615270909060405070b130311150a030e060c04120b180a060903031b020c10120207080912010c 61
    0x100301c540b000410000c440b840c54408100e055010451408024807807c020003030f01c030b81080042c14481507498400000200e43c1c0c8600024901c00c005114000b02409042d800c107441b07000c0e00307114102d500144859200c81c20020102c1c07001c20802e281002c982d0710643c04410240e4503003c03020184207208521221510312030013061310301d008681d0b18104503610891140c00248035624103030925078070340705680c1e012090750001000682000480e00206c40244d0342c004c640341701d50303080c03040202d550100302c81c10441c070009021803404101c40c0e06402c407800c0714106100711545521030001c82415071080e40301c0d104180c2040503c400000700c0109041382d11030403003140c085040c241d482c4024100712f00c43d54100c4e44a40e5646c0b4038820190588500320003141000c150302c407000c0c1c8036031000e965860006589841510702c2c00c42903009500c02c450080d90140841c10079522020b0a20340300c1c085411619845125405030004410920f00520a00d920710505039a843e1301451800711048048110a4503180040e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 495021528 1250 495020278 495020287
    0x2408030a03090c050a090506270126010c03021306020c0a1202030304090603060209120609060402061b0717060609070507110103020705011a090705040612020c0c0d0f060c030e061b 79
    0x241d03105e4021500500d982c0c00d0100e0185018000c100c4240d00b04c10901520f914146032203c001c000d0310f0351150544801d07201154035081d200801071381c1c240000282d500f141d800c0281030343d1206d43c16005064191414641ca06415403503200507a114000c0c04070054001941460801091440d250304000c41800035060328507041d103480e0540c081d20601c2d0416110150001404511802e00c1c1e2a200500109440600158206000055110007001e04040c2c400c0402158445003003600d1019911a40c00c80001c0340c020a039030300f00124118000c101c00380e229000701000145c0d00c1c01c01c820391500c500110b588162a0040566846081403034042205040541c240800310005509100d480440d508a64a003465020342e5010405030303944c004d00090400c43d05000c1002819004030745181d94401080c00940c40e0068140954035002100b0301e1142d1120b00d00c803071102400105c0c9041c0c58014090701040c05031550340e0b08140d041d245200c0031800d19600c4000011180d061200d945d130354070042052402d00d003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 495022778 1250 495021528 495021539
    0x11010f081906150e1801031104090309080708070e0a0b1c050c060f13061e030207170a050309060c04051c05071e0e0f13021509090a2408030a03090c 65
    0x6030700350b007011400420a4024290280c2c1360001170010340018643e400304140d81140e460440b411b1042001c2c0d4010740e1500b902c4010907010300c2108014002c498122600140c0d140840d0b6031b512000d20034034440c000b110000c500105080d004569400e01c010307103800c489184013012031082ca184e01800b40d88a0080d0760350726540765540030092103840d403004855615051601c0426500160950200301030000c116032010f44003d01c1000400407060314100142c0783c0c00103040965501c1030400c403850780c001f00000c224040540003c003950203003d02d001140c0a070b40d15201c0189a91143c2d0007019400401102410b05202440082c2e004651141c000d03504c1d516030b00c07811244000c1f500004198500340c441f1080c01382419400200c0d60103105600c0e400b01c02d007009500c1c480e0103c0e4100001c0d01902800c0540c0700410000000c4420b40c40c0044c000a08900d00004284000c00507000c1500d01d42c11b1180c44404e880c1041c42080c01541d50143c00356103005001d917016001400c4098040301d040040d0040000c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 495024028 1250 495022778 495022799
    0x130317040819030203040204141005060d061502030c0610050a1a16140c0a0506040306020702030f0d020a1e200a050301060923250c02030d030911010f081906 69
    0x86a00990710f0158503801c00784100815a002c2801001c00820450200b0070b11846c010000b00c112101503850550380c0e036a18030460040d01c0c85030007000e024403800c5401942141c0c000010005c03210404103482c0c0170340b21701c040b00421802c02d106159001d02030704414046050000350017062100d01c02e001074a4403040702c0e4240c80400d50340c5030990b406216031842d2000503605018060448070216400c03039940e41801d001858a0045010140865901040c8001151800c000840c3c44040300800c032050241c207544029031b00c13214200102c1c3d1104034031000355210040c0c0c4400c1102554001840d0181101d50322040203054803100103d540052500310024894400380b040c00041e052000d0040756098581d1501079503c24042c1e101c0c28480e41c8841005045401d41c103c05a11240b104001a280740d040441250a40b841101c00395150044280582030345406a018411280c8201d58481c074014407400107540c54a5410018804101c14100141e60340c0542e0f412501440c290800c00078040d0f48400c20b00c1c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 495025278 1250 495024028 495024067
    0x3050c0603062d1203040b04092004090b10050306060d0f24150e0303040608040303020f0d0510080606030d080c0705030a0203030109050a06030c090b0f04020f09091303170408 77
    0x16800d0300140d0140e01c1d0030001811098888150000d614192034510041c5451089115461030582d8070f403a44403860318a00c501358403001032404000c0e25642c88cc0d00110061000904141c801c0c80b50481c000c05041c0070b001130b039209500c028100c50810711100044030140c010b0341c0500503910703992941d004500e540900c041100902817014000e45d40d04202c041c95800585c00803240030321082c181482040c0d40c0010444054403034070700d0040000e03162440c00f603002e8041d007540501c441e600030403405141e00700c0d54841352090740800920384016a49240c001e0319000142c40d22034064015101a81260f805104a15041282c01000510740751003a2201350031070f0000c8900d100181c100100421040c01d080c0600c917000300c141a42000482d10319039408045040358401c015110f6111a882040ca5456802b02c0d02c12580141042d9912458080d1504890340700c4000749111b26000d10216412590520111851070fa06440390b0140c0800a214001c034100010400c8411070000c010070082e5007201424607 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 495026528 1250 495025278 495025339
    0xf0a0e030a11070503070e1303090806160f0e091b0712020a0c080309031c03020915030601090b1606110f0a031407020d020c2205040b010608060a03050c060306 70
    0x10001105800c0165040ca620f5034006072095001502c180300790a543c0d00540d406c0301103000d0034404c2110300e15003a10800340785d40c0000080d006030030800140c06c09415524000a56958600640c0d9120303000c1070700d0340080e51000640050f500c000203015540c22074030321600701c10042c1c840b50400a9070b41e100c0c5400192480c4550041e088818450204000f0754800005410808051070409c5420401320740e0300c40b2a049403c495600b00543c411203180298121404410007816010080f01554074038102540190348550014180c0040028240c840105030b5400e0b020303203540300b9a8200c1c10344880b000340a000e4942d95031001c0802118821815031070061455aa0f991000f04100401c4400d10400b204c0040a440543d00003940c0e141640c1c0e80401c440d4a40501103a1000501e9080104414070382050302d8040e40b580c0c43c080501c410701445600c447c0c121034081e6142c68060707a0314020300c1700400c0c942c40014015030080070411420300c1c180003e50303440031000e0175203409050400000030070710b280304001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 495027778 1250 495026528 495026537
    0x10180f020f0409140412080622141803040b0d110d0903140c030702010819060306051005030f1b041404061e0b0328080406120e070605030f0a0e030a 65
    0x108110b0943c0c0c0108042500414024030342458140c03036140301e050000030440704012040d0002041583c8a0101d000d4044d5050301c0800c120540003034100c0105401c031016004040001d000031590746255140492080285020323504080c6019840c5c105034210352801c1b03111584401c5200c0300425074101400100000711404113187d011420003070403a00340d03d0170302c2905600c00c1107680415880001126240e80c4d0a00c1e0580095441c010425116505014990155800c294001043c03080c0f80c1c0103a40501004201421201c0d610400c141da03d5210f921411942d81140d148160540544080e4086840f400780c0085083c2c0300e0481c60696a000440b000c6444e9952844080e032404110802c0c1010070451417401c03ca070720181c20000307545004c1c00b0386120740310b070924000183d010007808071800ca4a80c00307111582c5441c2c0307440c0064005412050310720790302c904d080108800e104001a201c1d033100c001c0d440c2d10349581c0703440c0e00b5401c03a40c0c00100451419038890400d40d400920810040050340250fa48 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 495029028 1250 495027778 495027787
    0xc050f0322060201060f12050c06030903130815071d03030d0c120527030c241f05060a0203091305060f0a05030c04050405190309090509030310180f020f 67
    0x559900001c00c1d0014402c581c900002444121084c002180507642200b500000290a0386040740c030b440130b507000060304200088203020700c80c64000064018401e110354036900e410f440310f0341103a4030385121030341e0b445202d2042c0100e03144a010780f581d0030f0302801c0740e04030030240024400840e10350341c1b029042440b0703181e8030540c1e5601550b00c10520b0b41100034404080c000790401e14400d01032140f428402c4a10040940b00c107001054042040b50002d6203000c040d108141183c09036410b0022014102c411100840e0000440384a85200720a60b010420810b4140460900703060080b140c0082c100030701944405c120225190f41c0b500d41e08180c44d05140e40c045520329054090010281d40d000c032190285c807906000307020350382e808100c1c0c1d12880415070b00000c01d540c90b810550f103040d522040c04003007900d4a2101100303042d400300c0610299105400c0c03e04c040e403514000b0984c0c80c4001c480b04000b26082800a10150500c070015447c4803584080c045031950705050080201da0003440c558020020006 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 495030278 1250 495029028 495029077
    0x150d1b031a0906091c170a2f180105091f110102210a060302060a0c0605130209150a0801020c01050a0c0f05040611031b01050a050f1302010c050f03 65
    0x229050b8081c0500c0d018007014100042d0082e510070400b001c0c94540740c41c8858800f0b0440c4610011550b4981e100c0350300020381450f228560090038842003500c00802c00d91190b1040d030903180540c004c0c01d500b1400e0b0529080107418030ba42c58020030900e680c1089003c2020b4100b59991018100d080d50000c10407d0f9004200c6038050a0417900046100c45a4018401c5203640c000b50102640b101e14102d000c4c0d102940e134044120001c00980c0c000945c445004681009442e5002044c403ca00340302c1c05c800c200c1910f4422024041d0800050000e5014002c400018514035000790721030311000e4050010002261035140c080e00303907080b11456180076952502080300c040781901414000c9203060810031154081254010124480c0b400b0741400d000305072007842002c0320100103ea440c0146d0321005415868071a4400e4064182038038400851410702d0f000c02c40b42c00c188503005004040007034510b0b810400d5680191220000d50400350f0301c500071070f01041640030b4140002c000199290501c03000c20180781 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 495031528 1250 495030278 495030323
    0x20307140c03280b18010c09060201361b080109150c050405061602130207030e0a08251d01030302100e030d180c0902091008150d1b03 59
    0x2c1c0002c0c00816030200f5403c24420642d002e40440d0700001045250303602d01c80f442108401106100020f503207000202400585d210000100341c5642d507000384440c0b040742c250440e06d0300c3c0f20b80401648800031100031004001c040540c402d418400c0c5010800c3c900320340c92003a0407280176030002540340d44800348481040b1703d9039041d02c1402c03201402000b01c0da0000d90003c003036002c2c50050a010388800154003c94200c80d040206400e5401840384201100050218003e07402130350782200031600000c0c884815251041202d415220610003c04081e444052441c598090400061f171584210883c0841e072a140454010010800c1010583d015455450003d2405048195611aa5103000003c41001ca0040b04a5000207580340d00411807032490f04800b00a0740051100a10f0b4003030740c080029041c80c603600506985481106c00f0400358120107415644404c0c111484800ba8140041c2900e092030102038400d0924050003260386014000c084001800d9040e400a83e0700408403400d00c10207840c01c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 495032778 1250 495031528 495031543
    0xf09060501050c030d0507120c030218031912030b09040c051203120412050f0a080105120a02060f030408120f0a06091b0f110109030c0605010b0703120b01020307140c03 74
    0x2c0c40c000b071900340343c032039050784900402136191402c0d42c6403004079021074443c0b1000f00c15507115890070000f1000d0300d14090000d510202490800d0340480c50600c11510340804e000036154441010130317550302204d40e00e400244002c4a58081031543d00c420110003a2201c009262250341b08020740e4124508110401040c8079140c0310110007035204101c8410307550f1005640c2501325521120200903209140c01c243e90340e0140d03500b5081882c5000c43d03035000c0d2540c025003441c1221001e50307140c6500e81c0c0d4100401d4603142c1104000c0d401c0002000100400b100c03600046034031900520382c40b800d11206540c400042c1005903001050b1800e404284515900c0c5407103410001c1898030400c00c003050410041c0c1180d003411a000500f4001000c14000c45d4500400300d003442c21a00b080200006103a600d009010b4051140d01503131082d1900340013141000703440c02100c8500b43c00d80c82c0c0d8a000c8040750200809001070448040c1140824045e03040001c642d101c1c00071a2854820150104010200078076240448 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 495034028 1250 495032778 495032789
    0xa060e1f0605042f0c01020d02070302061009050c04120212010203010e04031404030b010b071103060c1c0b0121020405030a0b040b0f010e0703020a1106090303041b150309060b09010f0906 82
    0x3024002c2020403802c1328410007440030140e41601d03074001c031661600900503280c40741fa50070700000e200c90405900bc07a18030310400d5098082e10700a07840f4010790f8201c682c201d41c00302d81180100301c14040c51780401d4003405142e200a00740540c03030005a00427826600282e2240300300524480620041580002c200007544440001030303030409155403a00c0528034018407554440d03000c00600b010030f100b04214400318004e40901100c40c43e0034001c04900d019032101a002602e03158009190100801a0060103284801650303403504103503692003511003040340f6107480720405608020004040e2410302800640c1802313246040754518080c1012142c580004085507442d129050047c005044003260590f04100249401a01d92652400658050856103c2c60704a84244020060200e00010041d44154030a01428510201540081d581c400850241424403001512102c528a1182e440807141c7da0080300041111031340040850924402a007001c10340d682d02d240240a06c2002e801000010403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 495035278 1250 495034028 495034061
    0x303050a1b1203020703180f06120209090609070207090f0510090c08040303181403210c1225030b041b080c0f1c020405011d01020a060e1f060504 64
    0x10003660b0b620000402a100a9041c56804202c143c14180b1403544a000c0400c855000b4031440d8485901e1440c4020a02c12040056110190350440317403468000e541117000050302c4103026132103003010403100c102d0041c280411841a48000500701209016000c3c2c01d101528000403a4205002c0200135081b45401070712801d070612986a42140d03000002540c003a8141c80c00042c04500c100c400c0803260034003000500003036004d40c50041e5800e804001803070780c0e440b180000c0c01103850000782108400d2089400c4201070100b4002408054051f1910b41c1d13111001c24506c11100c0c4030009030300d425680040104001070740d154223415a40c14184603001c498a4088040c1155a2503400020000c04e001002407880390b0020612459148100007a01c00c24904a10046004604200800000d40003072080c00d000403c01034100040d03042d054520f88441c0010307400307410401d42c161900750181141c103800310464801c500c0c14804541c00b00b007007a00c40341c400c0c1c1c41c04200e40b46000200b1003510160120b5900d5903 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 495036528 1250 495035278 495035327
    0x2120a091703160c080912150f09030322120e090109050903070201110709110706110a1b0311062409060612070c06060923090d23040303050a 62
    0xc3e0b4000710040640303c1c481c030b452001c1201c01c1c076140145000b000c40d003540084043c41d5000449102081c200138015001c2d000600c1565401114481d02900303450340342407500200042000b040400040a00c00c461020220180c01c5840e42c1c0d44101e00c00c101071040020780c21111a13807081c5005d40c02240100754803d01800a0f00b04407680c3e0362607206070701c03009040c00043c50210354104000d0141400408001008114441107403d420035554050041190800d00d080c8010403001c1c00c840644605410b90740d202c00007078400e02036001d500f0403ca08140c0c248111004032030002c1780204400380c41110401c4142d00c14199600b00c00d4480001d400f213040c4100c404004021098032070f18140d515280c0505d94890041d01d07915410780b05040c8030080509400c0c00c00a020803001c0d9150003407400300018002030307440f03640e0000d407001d5032110039a500c0c1001c0d0043c0300203040f06841401c4010380b01103449446187c0e410100c80c51030b5164440d502c22004510046104280c00313411000b00d24036142e4800214a20 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 495037778 1250 495036528 495036541
    0x3061806060d0c0f0e060315010303020d050304080c060c0a02100b03060c13120f03080c120c090f041517030c071a0405060a02100c0323060402120a091703 68
    0x162600142040d0082c02004442d4060003c044020360040c200030340d08018041c3c40740704680d07000b9000c41d03450303000e880352540622144102c000c40300e048a8141c0d000d000601a002002c90340b69201030000d490785c14003800b9540f0428018000680502d50001d0a19655180e81c500681040182070100c442c481c0350002c64802a103000c6905540704840883c01555041204240c1030b01c220183c05c165024900c60348500200401414404400390003510b44000aa0b0360005107032103440307060f14400d24100020041a140b8031100007520b0300800c010524800c846003c00800c0440702713102880940300c02c4a060030005d2409602003081c000c003602001d503290100b022551984c4603143d01c10744608034a03407080c80c5100c8141c0070aaa0180c03500414159491103000360080d55000e480300d0101006140c146490351440c041e00c2401003259851601d034004510070703621485040402425036070402d800300900c0089502c14004980704401d02000010076801901f00310055912901c0456030007042003003071024 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 495039028 1250 495037778 495037783
    0x1101060501050f0c0f1e0115061e02010e0a030507140c061902010b0a09050f0106081b03060613031a0708060a030f0f080c010e0609030f09130e030a0e030618 69
    0x6184450800040e90b5880426603d40352000d4075a03d45d015004440000042d182c56000101746a80c01030000d204407001c480101032603480501c01da2001c1030081d071007201010000e00c03c03010030581c10300000510f1b242e2400400d0401c0c160328411000103400040d6042000789054507000d07074601c0640113180213007111020480500c156070440110300c00c1d10080d0064140300b50480664440003900302d089107562058014040c12041d1607919642101c180003040c181d209101c00c0e88521104040e4040602a845201e1803640c005048207401c01300400142d9600f00916201c040250721a48400e2601d00f0044013034441c100c80034014004100407082407001564031810440e080e02d070015242e16540c8410314150f0150f48440b0001026108082000303107004c5410340c0107409440b034000542d81d0507550214101e803a1700c990b0b402101500340501c01c1d0a000d0804044540000003000c40001c0c0d008003032007086140d5082280755600041407003071144c0c00e0b410103000742900701c4070300f085040003401560359164 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 495040278 1250 495039028 495039037
    0x411090d031d040204090c030b01110c121c02030c07060302120f06030109051605120303010f09051306020d09022b06180b0f160f0203030601030b0d0b0a0606110106050105 75
    0x18100030200620a6014004000c80380b09010020411551140d50350000406000d07400c16041c00b081c94800244a554000c01000c0c02e04428040a0320b240da104a0800909825001e10310320f5910980212110f80301085000001561003500150b0300d4801001d0a140340030201d4101204160043c40042c11102d51850603681010301712807229455030b5101d011a00503d1a400f000c2c0032841800c4030200e0300806030a400341030320010784d501d10003004100503482ea0f9100a200d0801001e0f074124080105c00e549a1040c0c2d00010741c098041840f01c0e8549540040c0d80000340303403210032642e4404a07011440e204084004c404c8000c200c5410348101440c407041c03891130540340509074030b468040c0c1c00324040d50210010807165000d03807a000c3d242042c41003119641d0b403c41d0101c40d0350400103000c1556900032194108010102e50095245a0b1820011009070651601440e040803100281d10006550b81a6030b5104065088000461510f07004000700031001c0d002400d242d43e4980101413110340d074004c0894 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 495041528 1250 495040278 495040283
    0x100602070803030a1d0109060b09010f06080a0c1b081206091311011b1103060928020a1a0c0601150e041e0606020304090b0118210804060504050411090d 67
    0x2629003294a104111074034105d400d08101d520f040300800130400103500042003018103a402d001d0303980e00d03450001e280f40e22030301424005c80ca109000440c807041070b80000e0381c0c01c3c541e803410917114001d0300300308041404082c80c100c5801c48003081c0650308401c180000c0b07510402c12104035400381043c01804915034841d00c0e014250b5103080952203134076405601d14410300a0300d010f080c0c445a49508203020711002a192451180c040d00b0041096404000303007030040e0741020b40c8540c815240e4851075000d032100c051412a0051404200010102c803190340d5408468403002200340d0301e9980000390350030040160042207101b41c0e211102d05c103a03640013001001c0148180d03400510300030102243c05035100550741041c030150910300041a400c0d4003002910450f482035105011024080005481c0703001d240c05250080d202201c0300304011802402000008150502049648441600c4003181640035401c80e81c08500300282c03c100c036003030602c121050624950041c3c0d04100c510310000d111401c511501 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 495042778 1250 495041528 495041531
    0x1510090501080702011b210204142e08010501020606030a0312020901050f04030c05032404060207030e0a03050105060112050f0109020c07081501051f021f0f060806100602070803030a 80
    0x20f11840d00035400180e00308014409000700b401b00d9a0000e0403503058035031800417251201c519115240340f9009a038140c03820400c5070810110203400307008140c952098440303801810b04d0300c401b400c4070140300c0a007141c1240d030b680e01d8841e6040c01d001a00c0c105001e0242d502030340c0050b247c040429440b44103a0064800c1710f00140c0c3e2002540700403640c9004400201010101c001400010000d03041000001c49030283e042d6000c282c22049104000c400110401e10024601170000b80050300a03030003482c425102c2e00b401c03040c1002103000320300488070325001190240c0d550f00c1030100c20340e0481404041400203203024809881c0c03000300382003e800c041c45982c0d0100d4000c105550340760720501240c1e000e46082022a0124444031843c588001070038032500c0d00035021101c404803460840b5002000ca0714584c0c005003800304031034a00001a02c01d41c0b046d110f20300d98030f00b08100c21000a000b804000c0c00307040b008245600784003005c91103d41d07580d070100d01035500068040040d04404000d50781d121000010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 495044028 1250 495042778 495042781
    0x241e0503150c16020918060c0414060921010515101215050303030f0a0f06031e02221d060f0408071b12110307060912050114070206151009050108 64
    0x281c0c212001243e10000303610800311001c0020240c0000f1040000426210031100252144e161140c0c2c14400c074081c1d43e03e500742d82c500076602814440010708000f030001e0210001c4466440014042921800141500b40d44800078412031200e07030300003140749030000ca8400b15100c40703201010f00080b03078060700f0103034442d215641019080c80741c024440040c100a410340c1e90320301d061003c00900d00c42c12501c514910b8602400310141c00340c14404c600503070368052001c46c180301c640801c240200c0044607040b680310039441160415081240d10721610012507c2012070b000740094000b4204821440c2c040c01654072140030800c041c3e14030814103400540041c082a40e03102035042400072558240708403001a6945000000c1180c40024220704050007900f9142d0540c0301c074420591075601c140718400c00550308800a0000030140000c0c40a072500c118000217112030031044001a8410448101c0d0268203c101000100101252148540102260f03424410303d24250041c043c2c2100d8010703941001000703030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 495045278 1250 495044028 495044047
    0x2160e0606071703100f030c0b090409080a050909150603010302130e0307141921020c03010c090501140a02060103031d0909060601031518241e0503150c 67
    0x4101c50650740c000495141030800f03d907064460b40e000b519149013450f4100e2000030390302807040c402ca0030f4945c0041d599014500c1c3c1020034070240c20101c141c5500540e0380d02c88000184070040180141d2161b81c9907180c41d01c514400304100014010409400e050b2a004180e83c01d6499000716819203a04803400e1b41d1501070108110b00824041815400c175100000340307402131144100c0c800c001081a28202c035035200c1c0c5201c4206143c40e03107140042c08840c139220000e4816a0b1a01c01c640050030a10446004001000003c2e00703480f646030401c400708880745024021940d22540460f20010710202986c90680580c800070359504051001400700203890080c0303000c0005181c0d40c003c80c40002000080c007818001c403100d0700c404007501d11034082032a0500c9000710230241c220b440210340028030b45851104203460b40d41d021b004500112004114604543e61140d82d0b9012440c1c003400300720108112402840204200e240b00ca03802c03242c465800341c0c000b08405181402425402150700303090035107404007070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 495046528 1250 495045278 495045289
    0x6140d06020c34060e0d021c05060f0a110a0f0c08040905041103190b04110414090303010603060b090f0112020c010204030614070f14030c09040f0e0d02160e06 70
    0x241075503140c0483d58000b040c003102d03001210f0140701c480190200042c40c2d03601c00c00d81d00a1018040250803510071880900907142c0541c25038080d50616108981400f015600c3c43d0400b50b048500f040d10281100502901da002e601c5072941441c0fa80d814103140004019001c0c001c1e5a4201c81c00c42008101405842001381000c182d074010402188140103500309894205c52044500f10303901e02912031004c100644403800c807170781010369420900545c42c0351610349070200c3c5130400c88400d940158448050311001243c07598a24460150040503645030b50420400501307031100366101070300c650400d00070716500c1e0342c982c0d1a0b25952042400c04c181d1400070540d01102a020b50000f544155102103400002c1c071400d0b402ca0407000d5901c00d88040182e441b10300586011200079070304030000d141c01184200c00c0d02904025030300040b02010301420311040c00001000da40c550806201c1c1281c407000591071058082040380380b00092030015120045410012152030b03040c51181d054083c0d034100200c2d0310758551 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 495047778 1250 495046528 495046543
    0xb07081e09040f1b030506151608041706090303041e0309030611071a0f06010c0c0e0106200706120f180b04020a0b090306040f1e1506140d06020c 64
    0x41c20a020211900001c0b000801031000103074900040303621107070003d510a104c1c40784541e2000703000360480e02242010601c00e030030481e000b071095549c0c01542d0002c41c40b5500580700816102014024011007a83c20034142900681091410b078024410300000030000c105880451405078241c4a2140c6182021120f030713103242d40080c3c6468503120801c6452905080281030780b600030200405c0b142d86190300182403050845044845000c028049025988114030180300d007402010302c4415a0380300c0464090b81802a03000c00b020400400c241030803010f1a01b2079000c22407030100501601c3d861b02102500305010240d815600340c2e62401700405003005a44a400516514200040180803900d81250540c40030354080e40308291180c0b000618072940011900c2c40d4102501820071612075940c1d14040151119003104e07581301500740e54021141c500c0710581e555002d4048459403032800d0480d04100e904507040415010b285004210681d00c3e0301a903907044035401200180e40700468948103040401 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 495049028 1250 495047778 495047797
    0x71706180106030e0c010c08030f271506011803031b0b0109020405010e0d032f0a030315060e0607080c0705120304060f030605090f040323030a05010b07081e 69
    0x2440e500109190341d05a220040e480e00e0301d800c40742080c0480c001507581c41c010a40c0103010081c100300103a00506401c1190350418081840301c1d0400c40c480d00c1003010383c0701421001641d0741c0501540010105106440c641007030342802c01190801420040d44620071a6001c0035041c018810301c820440052a210713080c01a0300300041c2001541c49140c51710195000303108090005401c1e1400404074502412403e16042d4140c995240c07a00c0061000c41784008800f401d490301c0b40308100c40c1c14841d04244400e1020501c2541d000500200c0421141c040c40515004803040004025510140780c076000c00f00c456150700700d042c103030301d8043e401200e601d40803094002c1c9030058018510085000b00020203001981c2c840e0f228800110f03843e880842c1190346500c074099000180c40c0110308003d880703080d41d6420078024a411001401d6a8008554414000c04840c4030b0440000400070491414030034103024101203090145000059200c19929005e00701e4404061603082c0c0c484103090710b510742181c44590303 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 495050278 1250 495049028 495049069
    0x140721020c031e0601050a0e16140a18080c0f0d1407060c050106090b0f040c0908031309110702090f090f0610090b0f061602030703060612030215071706 67
    0x126002c1980c2c90a42d425084000c4c0c1304550000c00d540c0380c90480c10b025124a9020030312a596040249900940c4894416003070003101c000a41e80c03204070100a001c482c040b900e8024a400e400440e92041c0f07a2160702154041d0048104450340e035441403900000300004803074924203002c040c180b50241c0c040200951049103e42100000d03220341240c00d40420307501502c020000c00303549540c20300940355000000c0d07a1202400041854928207580400940c4045c2d2406050351a1601070080c51603000343c8603603401181301401001030030b09501030fa14001c0d10f02046036042580b9a404582c400c0d0000d04103100084d0b8090000c0c100c00c604205c050072001c42d450132103485092900c014446100640135800c2d41070300f846071a065a087c0000748903000280508824a041d40000d1644030920842c0c0b0100da250059000c0040032030011300030303000942480c0140b00e080d40e80c0c9140103480d00d0343e020101000080b4080130003030043e8000c03801c03500300c020406d48404a41d903690002054840007001031007500 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 495051528 1250 495050278 495050293
    0x3180501090209090705091306140702011d0a0512160c35060402220504060c0e0a0b030402040207231e030403020307031104020f0a02030a140721020c03 67
    0x6415000840c0541c0242ca1005080d1203020f07135280c80744c2d40c41c0200d42e00a03c48034041402c2d80424507401c0259402990b0018003041e0320707541009003001c10f440010060391641380c0c0140300d44140e05000b40000144009080840b060790300e8940364445001003096442012800170280c0b9150740c143d000d02903002c0005102c050311200d0307284811000403541c0703903902007a8001c03140c3c80300002000144e280804004084564079a03080080c0104255804480031018003000c05038104c0c580550b60246100b000d0105601c095940002d21100030300400c2c074803a00303800030300300002816101181d41113901505c01507079803542424102002030710381d00340c00c00b80c080d044541060110080350840c824074500c044520074500050a207952400303540400b95040d04100070810004160804108c101280540058140240000700c0319194110381402c1015800020b82c800314039920020050f48070507102011400c003001515001c0810150085442242503907016080216008010107420304a0040483c2c500 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 495052778 1250 495051528 495051533
    0x6030118050106030618050c15190503040213050708040602160804060e0301050709180f060f08030c070504090f0308070e061c05010909030f21150e13050309060a0318 73
    0x20003d901c07080d540c5ca450002c0d041051804d007440e281c44180c01000038040d070450b25040101e00310340daa03003207601c0e140f04020b82007020201400a44040d1802e80b00c054503031500780140685c00003441038094072140303003070104004941c00035100e5800542240300142c81d80020100340c0050410b0000145c40190040b800042c000d0380720540c490155000d5000b841075840340c1c0000d690b81c04540c002c406505440c0076154003000c06a43c450b07540b0300d0310f000f0080780301582c030350200010071442d40182900350000500c80e00e440c0001c200d80d070700404c400d0b40d041000314000d485080c0104142e102c000d0070001083d0100c3ea00e103124800307071001d00c0f0000380710b42d50320010b103800004080141860b00b81c03032038200340002070403413124840c140c10590182c40781d01c0144803000040342e2144050401d90f41000c6005050422100756205007046001c0c20301d007200800d401c20a4100c400c10000b0020b07012010305400a400003500801620320522080da1015119601300205801600c0b901801c00c464081804c242d806 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 495054028 1250 495052778 495052781
    0x30c03060310050f01051201061a2a0601030803150918010c020615150d02030c093c041d0a020a0b18100c1401060f2309060301180501 59
    0xc10045084030120004508000103643d01220542c1c100b041c01001009607060071104854210400d200000e0100c2d103c1c1428004415a02106c1000683c08200307690542115194880740901001a5a1201d465910241e654510500000b40050004030110700c94200100c91451182c01c01402c1c011140781071100d00003900e40190032202598200604c014001d4004245140254660340600380c080c040c00c2c05015586419000c52080800c1c10442d0340e41495052014600998411040c02d41d10b0009000300410b0f0521840d580d001d240c4055451500089640d091020055103008128408a4401c000900038110300c2508628803c4440307025481250200740e10b000c80344226142588551982c1c02c20071107000d0345504001c450303880b40455005140541000d110341a903031508d03802102c0240d07542c0c0106138520500090744e1b9110302c0107104410148035854060005908a50104a1b841d10310762041e40d080001c1034095020900811000d840c29081401e4088684401d074040c0c2c0645c2c5030950 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 495055278 1250 495054028 495054031
    0xf0323030f09010c021017071407021c0b13050709060501020303041b0503030d0222030201020d030e1006080c0103112d16050601170a0f1e02040c030914060402010807080714030c03 79
    0x2100b6074001c40010a060b01403278100449151441702942045000e50900c82000081c07c03001049681e5009017800040028059600c0303500c400c081140c40a04900d002c903c0c0c4100b94114504a50034407101f84038590b800003d807a84507401800d208500c4109000b202d04051403500166010f000001b62201c0d0a00290014901c110142107904c112041c040c0105006d45460f000080c0160801419045054440c0c3c01c1140c2e0810b40c00d0a07120440c00650503c02210100e038440c0c60070350841014020290b03014030940c0704911100c69540c2c504003e02c070500350004500c01c00008000045904546014100003d03200450203102c4000c0940110b4107021703540385c0e800d1052040813920808010b5034404c02040101d6aa1f82c0110145c070407070700c80e0b5038640f1800010f2044414941c9203c4c40400540d07034a0085a40340d0140f603c00141e076180f41d041403035030761304c2d62808500740340e20203018840142d92181c1181d60280152401c0c24841d1038104040300c03d039031002800d240102d0080180902054268000c5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 495056528 1250 495055278 495055307
    0x3070c030f0c1a0a093c12110c10030e0c031204170c03060f09160303120f091a060a06090f03030e0102100c03051006030903170703090501060f0323030f09010c0210 72
    0x200d0288020086d94503114420b80d80104200d00300802405c1c03003809400810540f1200740195000c1c04079400219100c2e00d4988600c2c00020744450034220001400d2101d515078003004d5010341080c012003220300149205178070450101000c2101210004141442544810800103013034804030300b044c0da04120141783c2500c03480020b005017498110100e210300c540c00101c0b50b1540f01c1010518001081c0c0c0c0062012460818035142c4a60024000a2418440214030003d5429000071380c10824180451000c281d0400000c2c0541c050b0b061014440901004040300e515180010130b4284040040b0b040401c0c000114078814107100398503105e0740c3c00d42c00803403040c1d01c900880700e9140d5888008030286e03010300740082c4c003140070f80b126219599482452240e001c005410040384840c042d6032020f084078225885021509042a4203104129130450507140011a500d00090343d00114080036459110b070b500d8404041c01c001034020340700d901071503200c0107030f64000f09012030455607082c000d40310402403482e4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 495057778 1250 495056528 495056603
    0x1180c081b090a060810060315060f0306050604090b010305030913020a0f0810050d110a060309170706180303021b01060f05010c050304080303070c030f0c1a0a09 71
    0x8a4505800a18140d03a0500641116a8014020188003184201500c0f4500b2107440e200e000c5110b12003041502c0e0040c0c4208000100c3c5072560800c00701e9280517942c4041c0b09030400104020050001c5440002e598001d280002d442c3c450900040040a480500a24815840000009005010002d000c00100030380e03440c004990b0a244560403031080204c3c56010030030200d0100481440340c0c00803588400d482c00d0340c0800c0d50b2582c0000347d050850040845280900c4611420141440b05a6400030324660400b441240659a1078150141000030815036001002c00c54000744412500410001d0004410303841099581d814010040d5001c154404085401e090450030a0b07801446040c08035024541448441c90410004440121030040162401d100038071012815903403e000039402440607071120001246107140c09041010381205010602900c000b444000c100d1101c0c00b040130345407482c403424241d5142c40440c6c0050000c0712004d0100070000f10050000d41c5840404082c40801c40700b03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 495059028 1250 495057778 495057803
    0x40804080d030203010b040311010e030102220b040807060f1202160516140f130c02010b030f06040b0c0c2e111c050c07061a0a1502120a050c0118 64
    0x307098003039100a1154103035611080000b080800c0b041c1c030500989060516040c260419404000303801c3e41c0000000c0b0b038081030314a801100d2101081c480200601941404c281020b141411143d100c0009110746411710106202c1c1d41c808a118030803010901002400031500ca42c4544d40340b240130655070400702d82d944030f15003c02d98005250394103901164107622522106001400500200c80c40b142d05240e00440a5001c8400c02095405045654006a400000d4403081c24041501c0c0c20202320008210341c01117018003001c1010020850ba01001d3340140c00c0e6039800038100186441407004010481c3c044814040c0840e1030070f218801c0080741d01d220240180c101070641c0700c25520942d100b48910700d10600701c1d481c85000e9508220360017100d001c60242000203585440381900c1c1c825104003030340407000040000600d4940151805401c981221000070424180080d68070940703107805105244001c00e6400740c481c4141c4c2141c035401c10a02c0203112403464410000184640100101c956140c1da56 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 495060278 1250 495059028 495059053
    0x23070f05091005040c0203090a120507120f0605100b1908100803030f130203070905040b0703090201020d0e042415050906041806030b0c0c0705010206010b04030204050c1204080408 79
    0x144240a40d0a0388022248946810704000041616801c200150300023807141c0d6840d6600c179160303c00100700043c03030340000500d07038688070b42480d8868100101d6091141034000100350340004a61140d0351140d80094140c4502c1d600915466a9134480c1c03800690014062041000350304c10350015280c2500c0d40783c040d403203000079102c03901b2240c000c00307649500c2800065800b40c0091178143d00500301c01e41c1017500c3d20058000c41d0400946401414034580c0395001d00c010032841400196011030240703001c10000c0b10941c0003d4031560040500e2040141e8100c3c03240745031796544d2010882c21483c04110700340c1244c01d8403840720890a40708103940c0a299050000700203000d0002ca41100c80300510781858a81069036080d010038031403501d03200c1c1958403180800041c02d62440117000b00142d044040c1c5484407594000d150090641145045400000040001001100039242640d504a0707000c65143d80e80000701c1071070300078000c0b0034030984411018401072040900041c000e85000c0c41c2a0351072200d20b032 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 495061528 1250 495060278 495060289
    0x703090608012d0b120103110604150807030e0d0e090a05100611010212070309200604121a07110d0509060307300b0a0909050a030c23070f05 62
    0x340709003640c4140310808030b001e0808403020301240350983e0b480c3c02802a261111541103070840100504d086451070014014407000c40c001032034104084594615260070b040070051101104200641404041400704006500a800074401000d21108403140b4514076131005052010710000380303005001303170b101252a4400c94015a48543c0b2560140030f221450480200c40c01c0100001c41d1040703550a1001808044c0f42d80880d034002c6000f03660218030f109403814810742000da40b0307100e035400c500451a6548142c80b0601503c0464402034100080c0060900f04940d101c050347c045520030321060300070440016007100390701c0481d00c815401c8428400030b00c0000d542c070b4801c11a003564814010700000d11214800d0000c81c4144030b8041501c5091342100071030b40c4d002c0f1511025580d0302d903240d45c1070040c41e0803d420264020704104105100c0107000b84ca070581c64101e100f0015040046a08196080c820102d074101149540380b1150700701c0d86031404411b500d44e242c6000700c40d104001098001030a2510 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 495062778 1250 495061528 495061531
    0x6070906080f0402010c0201050409060303122f0d420e0606070317070f02101103150a030b01060201050604180201200c0406030c0306060902070f080f04090906020703090608 76
    0x414182040c2c40e1115001900d030b030440890102d0400001704808500074941d0b0007020300070340c803d8484400708903c81217440162a60702c2d10b04450128010742c9403241e4a802a0000007040d51154440d6880004030aa6005030544441e410003440382140014071100c0c580020001d03484107001d0030a1840081000c602d200e141520400009c192000c2c0807541701d190110042c09a1381c40b07414a07031030300c0140003d00c480c2a41e08540c002d0120f102007543d0180d042d01070051030384140850804000c0156866120350690101810400d05154140d20b0202a9140d50368400040c5402071070b0751100c2d6070341e032070024082d1500300e50381400b807420419008070b110f8401032020400343e030585511512a103200314a414841c1c50340840e09083c0700300038a040c507580b40c500c1124051400341100d481441d041d401d11600381c0d0071560003644800e20411505e004145140348246403e544985810f0350f49417848880d0140d070050b038004015040c030f0800001e04002c4c050380208030b5103110703482c0c44c483e00740e0315035064651010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 495064028 1250 495062778 495062791
    0x80d0905150901050d0509011b0206011d0a0207050a0507031e0c030602091f0f020f07080a1b03020307170d0903020f04090512160507140f0402091804050607090608 72
    0x250610221100c40c0040103480b5204041c5020380c00d03e4280051581925010b070340259480e5500d110b100e00c5002488500310003c100e600051556516046030080440c6406080c2c80010741d400700400c40c40c280e5601250041500081158071004181c204181c0b07a03401480203c2d503d41e000e81c034084098050740411810b181c2c018000a083c107142d0384071680070354011000c1035072000e041c405000845207501d03031140040c111651003120030300030441c01070700d041c0c41c10712049059031012000700141e00c0c00041c15218544d010300c16000c519001c5100c600d1442150300000c1d0b040c000d038040814040507248100c0d581802900c1224000d00c2800c0c1c007640c0302e400307a000203500429039452100190400d604030401d91840f0342e04590078804003414500854102400c100c41c414092500c000600c42c007001950050190004a0703e8160000d2000401c0035002100042c0581d17008103042c215039a50404c044132042c804010104c00d03150515040e41c031444122103080108980901c0071415070700c50881c142c070039107 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 495065278 1250 495064028 495064039
    0xf020d050909040303090b01080102210103110d031206060216050105070b04020f0a030501020d090521120403031118090702150f090106180504050606010503041a2d01080d0905 77
    0xc081e8050007110340d00284180c0902d034075075a1540015440e80c60380da008003d400b00060307c4103c000707481401d085064181180b6440c80307000500114803c150100007043e070850700341d0f081c0c1c4c0041c5815039035a090044000181458180c0000301c0640100d0300c86109669070b11120445520307030700159054019501c0c080d00780c1d00b100c0c0c0002e00504050f00342c107500c60380041010f803400790380b40d03a070600703990000401001044c1c4030700c00001040420803507140ba81c4003400185a04080c0f0301c4041c0342600800c4555820b281d4008003050505000740d205101000a00c050681d8070f01070107105202c02c1d60602040da00902d4803000180d0302d035202050306140c00a90a080c1c1041d91600f0301c42c43c80394900075200700c0309550fa03040d00240c1c0c000b14800300185514400004912490681071850910b04014000d5040c0102041041300158000c07a1242462682c0c899015840d01c812003a1030301e02a28102050005484400072408032000006c114100c070007480c120345e0500390710768040b02e0300344903031040c2c0b078215 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 495066528 1250 495065278 495065287
    0x50108061518030102040f03030203120618070e04090605010e16050c030a140903010c0908190210051803030406030213082404032109060e0c060a031a031c0f020d05 72
    0x10b42c05900100d40c80e40d0018005030130103454026480400070300c1e520440243c0e2001801e50713000b2107000b04081e0300250888603400e006c4130390031840c0815400142004e040010030340c01050720759925070241c4001a00040c0c20485982c440021410001007a60a403414182c6070502109180c4a10102c036650904007001d10304114910b41e05491440020f05c11400482090022140d603441c2480741c40f465032a19030716001040e160552480c100301c00095805110050780e0f0461000d612000403d40074540d007403400a54810792841e010070030701c50b0b0304038895041c0000103000400940c5500a0035410700a150f084040983d41c003c1075550f0440541041c00c09910809100707200c800e03c81540394024060300700150046201d08103c8591800d50000490703180d520011701090041c0303071044280c64a0440007c210b00d407441c2c400034007240918040142055294040101c040f00340080c0b001e81510007070212444202c1d80c002c28901c0000150100000a20184d0005040c5200184041c0201029210103241 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 495067778 1250 495066528 495066547
    0xc031505071413150e1813170c100c020c030601120222020304060603031b020d02061312060207170a050301090218120a0204050a0e07050909160f0501080615 69
    0x581d0840114030341800e150580000b070a60b42852101c96130085941c3e000310700c0c10717007004005542d0709950300310400c0a4000308000072418050480210301d6008012036081c8003441010a45600c00c0b600c42c0c00160003440c1d03504201c01041d801c0a4004141030b02034500000602082c1075403841309200d00551b406044035000054108000c3d06601107070510f000844000d100021941660300603102100c140d0380d109001c01c1810b900142204109001c440300c1d90205185800040d010000d003400a80704001c00a503030802041d148685000502c0d80000c080c900003e2414108000d40000c6d00c1a03505c800000551071540c4291400c0380c4030b200e440d440c0c00b41542d0034110800c00030b40000e204045800940042800140d4440c100d89007040c407130600420511580384144000da071000342090200740d00f001c0d0003004980001c40c207201503a509440586080d511081020300d0003409100700c1c100c0c0e80d5031a5000c54000c90300c10710300c4140c3d0400e0322000410b03214603046c030050410f55030b07070b8840ca1041849156403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 495069028 1250 495067778 495067817
    0x4020a0302070b0106090501020706080105090712271703010b07290108060a06151710030f05060708011406041202031e010b03070906122d0c03150507 66
    0xa802a1032034018100441a910602c140c2402e030890000b151342e4000810a41d80d04120520140c00c0c2e500d003074401945810b001c0f80c0343c1107000e400d0030240402280e02440d540307402e03805072248104046020542c0e42020045034140c118520055660030503041d108060f100715a41264102d4400c2d0b10a94034161503501c810580803404090151215404503818565003075001340c4501800707100c0007400541c1001078090049400310b80c4000500c140840860702d140d0f401075a0031114142558044400d039a80070440c40c5500034642004014003501d000540920000040d0584521801e880f412400e0762a50070603006101c10600c1c6070b82c060700c10802170042c0ca00040804904030702c0038040b00e0004019a60403170488140c10108042d84c0c0d0758480340c02c0c00349001c10484000705002502040f0365410b001d0303484003a4480c1c0a028100c585c10f81c0b0700d442c00c509000070084062402000d403450980c59803601d05443c1c2400c2c0b0042e5009032280c80c107107aa1004501c42c142c00380485484211000380301911003c2c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 495070278 1250 495069028 495069037
    0x3020a03110307080d1416021c11102304020d06090311100e19080304031b12050a091706010e18010e010c0f18050d0807050a0b150f09060402 62
    0x456a00040c00002c00050401d00034100e1000e080d1404102c1208040c86004171b400001c0c102d4040d40c0c070440c0d0010000c0e801041c0d601c9119000b10b4421041d0881547c00c1d100c4c411140c0c0e01c0505407261180307a00b100f45055002e0b00b04442416510001206117040d01044820b050b10003135408448900c5c003500240d0396170700c800001ca210b42011002407002030205414285a1858244400c0d01e8100c8440f0385081407081d0313004030001064001542d1159160994540002000101402000702c0000001440601c41c0140789604c21401c449c03d00c1702030002005604074020b940040b402120f004140e038225200d1130920420448010240c5a10b48003540c04103441c090b0006100d2103001c489501018001c0c01601d103944009030021034452402880104000c4050003c2c0b0104a18645113040300b04d280c030303d5942110012900844c0c007503100d0914020611581800034100e00c1592410402c00c281300c4605403051100009a20449800d5030a0248131820345a0103940014000c000840500c0c156010300b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 495071528 1250 495070278 495070307
    0x12100510080706031d0d03050603300c1203010f0608181009020a0902120615031306090201120207050c040b040b0607024b0d170703020f070b0c010e010903020a03 71
    0x20302405c801800902c0c2014044a51600000d45030b00401c041420100240803050500050309004560345a07503040041d100c0c41ea10700440400096020784a040401003480c03405048201ea60b642c1d40c2d1a8511111200b680c0300303d101013460240001d1035003d000e101920940254000b410700480d007032801200a01664000700c1c0e0151155402050507061031014003054401d844586580e400c0200402184a440740f4810b81422000c008000442403407010130801558800340104550726144010390f640f100c01000d14108502c04034081c42445800600c21002c06000c0e81e041188074150b00600081c0e4100c00c2500d900100704002c2900103080c9000400010b00c24000025201c400740c6054151803031040d07004c94401200068107450010004210402089044509c400c50070050b588a0390f1500c80c10710100c620040c0031401c041414001d000080070b401c4001c081d540302e5511100118190f8001c0384150041d50300c1c02e00f2507400400140726100c403054050b0002c0003c160903550441e01500c114589 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 495072778 1250 495071528 495071561
    0x30703181a0d110301080109020307050405060105090d03020f06040309061706031c05040b0f030f0a050f0610020a1a16030e1b010c14100b030a11100c021210051008070603 75
    0x41a5184480703c042c50203080040004180301044e80105407070031002c0e0b0030140c81240750505001c110303078000c012a90801c50503600914254601e0a050781408682c2d11244054001d0004100c05c0540c001c00c1c0c54140c2d01c10740c0305e600801c00d8403031642241000441e541e03501548480880c0c580340071801d01c510807215052030414034150329114280242c2d0040e070054504a5408414011902c1c40c640ca09580410507400070415407400310546002c000010700314900602d1180d90a40e2424428000304601d29044801024500000d00501542c002c0441c0c4407010500c00d18421050035119003d40e020b0113a41718001c0405200186110009441c20861181407190032804100000e01100c00c01645101000c05444110b620100b4070090b10380882c9018820303040f20b00c20303400050001800f10000201a1804040d014560105980111010501a51010001c641c051512100046440c0180c108101c2842540c50305180c1000080480c0109811600814028403489220740d00641590104824 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 495074028 1250 495072778 495072791
    0x715020a12271406061002100207022824080f06010c140c1c0f03030b0406080a050a020310060f060e06041d1b03100b031e09030703181a0d 61
    0x4452039110070045048038001106444088043c000b44000d59010070f0036160215211a1108004d4890342521000f000d8280c1c0030035000107540700d400919200301d4003860900340d034044a40403469411070b0792140241a00520110620344198020441034007000c5031035034005521404000c0d90343c102e0052516040054000c1d103040420780c0034001c1e003070211a035000b40c5683c1c5004403c0c001c071420300d080c00081d0803210442c00300c00070b81201d4030400144c0e00342c540011442071000020b00601400c1d40000d40920a80e5600c109210001c2000c2d0316a0f84210201c2d00070b01d100c0c1a82c0c5054074050312800c010761440a608102190165a005804c01030080c4074501c0e207601d529010100301404106802802e8010080041926110040d101003501a2200303a00b5460501d001c0044101c00d4050a841070b000800800c40541d51911001000f0b0940b0080781c402e890448121640c80d0000030f81600000c0c001200398a0308040800c04d4420703241c3c0e81c88641241880180c40410a0b8040580070760060340da0701 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 495075278 1250 495074028 495074081
    0xd14180f030604030c05010b0604050a0303030c021c09082503030c060b06120405210417070801090302060f011211060a0e030a0308071d0922080706020715020a12 71
    0x300c502e10070f51094403402240321300741c1440c90031a0ba20504507030190000b040244030b40e55440d03d142017103e6051502040140e04018100d0030400660808004440b2a100c81c00ca142d800652550998807440c0c112034408480d072582801e40c0804034090000c00c241070701d003440401d00c00d40070713155824062600860241d00d600042295135001ca01c20f00110b8202c00c05210400c076080c4510300040041c05900c00c0c40001156002c0c0b0503118034421000007516503450b45000c204c06010000003404940001c00c076551180c14042d45540d0100d40b0001c6041050001240380c102c9038682c00c03103403900b0648803500740b41d00c03406104542e809514508184a80440b0101d8156004c2140b400224400c1e9100c0c912401d090801400c02c0c2e02c0c50501ca43c041c0d0174050180d4403600c5514840d580071580c260802c0b0408042d10110480000081000d001800d0005007c0e06100c00b6070000d091880c402c107468850021114884402c9004140742d181c00111101030f010300349540b40d00b1107202d1940d400e10140c0301e580d401 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 495076528 1250 495075278 495075283
    0x5091e01030501141305072c10060e061c05150306090d020c01020706080c0306182818030c06150617060906010903060c020102040e0403020f0d14180f03 67
    0x241d1040300c07140e4458000501c0811094902a044500e01c105092295120303941c46480340a40e014981d25080c86071803815003110048000312100100c4600083d031410300003829400c20020740500d00c007140d0805403116036030810508641074840c1c0307004081c1585802a0204c006030101030145080e0781d441c10000032481d45c00340b01c003901a03510ba02c0100010b1405e20070280c200051300074800d06542102c901049604e42004509502c10782005201c2d5899440c6400903130505100d03500380c04103040400c02c02403e00414403040311400700300300c00e071558a030100c0b181c20191045107081403204407409800c800040d0003200b803421003600c504030105000b0110a8982d481021907030299001801207071402e280300f400682d80c00e8122000303458140c5146071080018203101050312008101c52392302c0c80350410143c801e5061b034000e8407207a0440c0300507050900b40203664483c00703040d4a605000b00d145410a182c051a400800d403140044d0441c107140840d960440329020b402d4109800c00741118460741c041c1d806 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 495077778 1250 495076528 495076531
    0x803070e1f02100f020c07091e0c020a140303070e120a06151a09030334030f08150f1002031603170c0403022214010314010e0a080405091e 61
    0xc1d6000f09820384590100d0004d40d1900c0f000c080c0c10900c1084041c440900c081703440d409071a82142c0204140c0c2d51f00c00c241441c001c0c0500c5c2c141140d49000b50f00210507070702055004a40e4043c0d486c2d03484205000c0c1392381d41c0f24801580d210340441d403c0c078441d0300d59003810035410311344c45019000e5948036581c90b105c1c0000e80f500c11500c011010701c045000e1003420710503030110180c184010003060514064101199813071107a4110a48661303107043c40e694007003442c0c90400007155003024920520b4081c915025081072803081200e004100c403840001c0f0780303c50840524800c044024041190350704104281b02c1207055410341c1204500080100701c504007160440d03249402c0c429500c815141a1792091040d035204090f0070807111601c200301c1000560b0741d00b000d03282c83c02c216400340401d9071119500c0b04010170f00d4032141010703030030038100004c28410106501c400d00082000280009044040341c4c40c0c9a40143e6001455818144400c1c001070510b403506a0f44100360302d805200d04280d000142985840 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 495079028 1250 495077778 495077839
    0x60403051b0f07061b06020f0403060b0405090a1b03051e010605010809060a0b0604120b0a15050310051e0a0f060e13060519020c010204080f03070803070e 68
    0x280001e900349460000e240c0415001126005400550000700700d03035031600040d01c181010031102080031144041c2c108121030040d94004070842d502d1400c40854112500305100a1319210700e031056101c4107003024092030b4807441c0140060034100c03a05030b1390001e070440034040100280150040101c0019010041450044d014204052045c081c030080182034800e40d810490421072402d0038018480300c006005604040d11480c0401c00030044008034885000f25403029035081007841c040814405001032540c01070b0141d02041c4680141958404400400c40c4129601a4010380b07a4445980003503004640002410200025080c050b40040309003a43c00d07a801c040c000e07505d0b018490070030039034810352000344012140c60f03140f464000c0f03c2a13015420b0540150a60751148001903410002c92072071558141c400c1d40440d00e9503420100741c2c1c003e401501038000540304280e40c503a005040002034880c0c0c00c0c0d00a01c11072440c1d44107001207504c0750300a84060b40101c46003030f401401e2840700617280c41040 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 495080278 1250 495079028 495079037
    0xf0209030a061a0607060e0d11120702011205011412010501080307080904020403060507050409061d06060a02070503031c0506030601030f08160203060f04060b0906031e030702060c1c210e0f060403 86
    0x1501f0740075580c00d091200600d8428400c0c00325040046000104000e00c4040752080f42d03e840b1001400141c408413061603072418042d1a040c008541440d05400403a0061016035205d2004c9070340c64640c5080740d0083c082c0c0c00040d40280030000000700070000030310000c2e07009032016007042e03540c1e80c416094410070703560380011032404282800911403900c81e040082c902d00340007907103540d440c98540d4102d50014043d1809800000784a00c2454001c2090000618014007102e40c2d6594407011030120341d140300201414641894042a141d00e0001001c5050b02d400500004683d8001d035a00e04480d400400841c0000081e06050800342c0d0741848441d1080b40d032241c00341d20500c0c00d0300d0725508407164034015078032031030031300d001e02c0040c0c0c0380021000061807602101000c90b4070104a65072460040d144000d42c019000164101401000f00c1e81d28540b604080421b9151640900c040d125034803610082100740c0c072400c8241c245010385400c131034841141d000964040c40401c0d00520308003001140c4c141c0109 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 495081528 1250 495080278 495080291
    0x1020a080601020f0a0b130f150e1011030c07020d0507030b1806070807050c0709020f0702031908030c0f0403050604060c0908070e04200d0b06040f0209030a061a060706 74
    0x1d50f01480042a604c0e06034018010340034044e9128100c03c68003506035464203040040c41400c0180080401d501d1039004880c9815600d01900404081c043d009440e190701c1c0600340b40c80507215058022229000c2c08110801c0c01c581d80c1040b5410240c2050750140d80c84610642d054001c15001d12140000d103024403e541c0c1c1a1500c04010b0804030310031303014002c00341d029108000c401c513400b021054100c1c5180c5002940c035860340c5072080c03808200c1d4103c5403000d440040c0f6520503c8529004019082c401e40a4a59826600c0031056184003001006488484100700050004020704001c0003509040c040c40360a09071280c0701c0c0e031f19020040f10100c2c0c10655511a078252550800c19620050181d42d000706403d90510000d03001802300503000901da0030342000740000000e000540c2884201024118200c659098100004a9001540c00a008a1034001d4184092015000304c03001070300c018004203508c401d5981c80800901c40822400f504884030b001458040e0707102c0c0c0060030f0301c40c050040820301 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 495082778 1250 495081528 495081541
    0xc060a0203030a0614010503070c02032406030601080105010e1303020a080406031d0609101805030a17010506090117043206090d0e19050d03120b0f01120906020c01020a08 75
    0x215241d60300662035100165905011726030b03005017202d0b404030b200e140013048400640b0200c0d1811075960b0806c4011f0305407904030460503203002e80d0703544203203011021150103913a280d03030381801c0311400e00850614240316400190844060134010251078442d10407a10075071001d4583c19080c0e0019000480001e8807800e006007002190405ca04582c041203010380ac141c10f122041581d030b40104040e107800c9588800751480079000480540074040e4000301aa0795402008100400c100c4c200140070784007158103800030616003011015500c100c881030310707045100c14485a800c0108000203004441402d00800300c02403c00b06039184081035070b80a1240c000c414000c803402400d04100522040c1340354098100340c100558008907540c0f1076141034880a1400e0300341c4603070000c09e00050700241e4200706100e8001040582c00401c24502c1184103c00300921200001005482d001682c1e07058001500a4110b030200c00b210f90007100000c0c49200014030384031840f01d599003a47c2010250348080b90310340c0704004c0c4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 495084028 1250 495082778 495082781
    0x606061b06101508010528030605090c03060108070803030f042123030c090603060109030b100501030c0806150f0c070b130501110d0c030311181320070201020c060a0203030a 76
    0x180340d03d50800b00503a43c101400f258003843c110440300800000443d081200c6482010400e0145800071010301c0949400d9060541c2c4003689880305018ac8101000050740c02d8022411600390382d802ca020350f00c0d43e100d00c0d14403444401c0280c0f080c1d4040309800030180c0c0c00540909004030b0b0100f15110211484e50302d5050000c115603400e90600540800c004020300c00007150122250300342d045400945a4a1b240c0040302c3d03030704442d0002020f1488501c107002c4d500195824150849030240d801348003c0c0d000742000c07249008251141c0d40c00504030b100c0e000071000000c0c086c0502240e5002103900300894502003502c1c000c5140d01ca0010305070005061016458503144c04400740c40e0a0a003034191a5164504594662002c02080300700711207200d0b001c0415100ba0048054100d48072010b40d144d42220f10041c034661000c407900d80c8100d109000300c0300c004509001d1051003150400d2030403604645228542882e80c085c940072811801811640304071661303010080c00801031240c0c010341e100d241c103c200300b0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 495085278 1250 495084028 495084059
    0x15010302040c0509010e1c0b0a020706050105040b2d060f0c0708060c160c030204050a020a021c0e010309150606050d0b0609090606131502030a021005090606061b0610 73
    0x141084820808107816903040308081021060940e1f00302c9a00c685844070034030008800a00a00101005c8188102c01000703801402e441400b60408100da6681c8204110413206040c003580d4001056400580880400f040c40c2c801d40350001e4054800380c00d1070745c0003a10a61251200b54940180801c10031f001d04001c103c00e0010384030200c0100303010305042e520300009000340c4032507490466051150f0020880000700d440000c40c0d026206000b10705010501d40040d41210080c900180300f04c2601d04103d450b6a1030800c40c0400c192122850b4200482c011409040c0740402590f024900b80e0018222004500c140307401440503030798407a01d0f00e141c1c00180082d141038110891003200309000303905040d607034140c0d13441c0c2100703048603910794500e00030580300c00400d0b0b581d0024000b014824502d54041ea0084000c02c0118250b901355080c0110809070181142c0b41503c40132900d5000c1000258241420700051206207002c01113040d40000c1c0d00a030707500c0c0c22011200d036044034507011020000b1680014152 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 495086528 1250 495085278 495085301
    0xa0809010b01080c0715020a3501050d03051603030902090702060c040e090a05071424071202031605210715110705100902180403020a08070201030204081501030204 72
    0x34480c40000c140000c0c03d0000203031001c0c8030f08400188001c00c011000900780d5554550070810b6483d08800c41015180507800320030751101c0c0d910b203500c400e0701c0074080c0501d1081300c85400c42504c150742013070207200030000c598108405005041041507100f45072640c04d001503171301c40d55010030050028414851890b8002e030076a815075100c0c0061001030000e5500351000d0301c458441c00a0507a4070301c4041403420000d03581c05071450250010106006d0806500a0720310300b003e441044090700340c8000c80f602d415030b003001003c00c8481030240c0740005401d400c8032403801096204a034140458951480035080022104175100d42c07110401110404814601c100c54190454003941064256120014105041176103142403954408164062503c000280e50742c1503004002c449842d0075401d0360600500294609030322650140021100c18114015070714892641507018243d0b079001581c940226410501c012810316400380f0001c10840c50800a001000314903080003082545140180011180d0250f150f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 495087778 1250 495086528 495086531
    0x240902090a0503061303081015090e010f03150203060a0e09070503100203070c030f111510050f031504030302041a0315120d0c0f1a071403130f0c08120a080901 70
    0x400256100f42000011000e03014201202c1030390324003000235028070203078111a140400860300f5a1420380e00c00c49503010385a1001000e4000d90300d1703101240300c0d2005840000d2140b00741c207401300442510f0740c0155030000c0019000351f50703803034650f803900f00041001c071403c16842d48903600400c4070f498200700070dd17442c659100c02103142d8140008014244905003901406010342210344509a80c415180100000c08410036204100410301004171a04e4007920303810307140040c100b4003282074a06003080d0703082514000e0042403401b0300c00304030420080d001801601415400d0000081981c0c052607141c440600040603107039646002e6503241c0e0400075116000340160a05901200e0100001600b080280e0315030501c0c0c02440d0f40c43c60840070101100c64000c140c2030001001d14070078004050ba40e8050340c1c040c0c803194241c42d440710319103ea9010403105400c000c60b8803521440400c007640c91104a4a004030400c101140e29500c10728600400f281c800c981c11071340080c2070010254003802c16a007020b01b0800 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 495089028 1250 495087778 495087781
    0x170c19261006030818030c090901060e010e0f0708090a05120705060f010b0327070602010903080109021c050705090a08030d0b060405090a02090a030605071206060e01020d03240902090a050306 84
    0x440e4040e90241c1d103c0e0317204041300d2150001131554108107030001c0ca0f200a1403031105107407000d041d901a000c2c42c4564860700c5640c80005c160f50321103c0f2202e1140b407901c44085c0b010ba0341c140e070441d02078a019001c44d210340102c1c5014004200f0604c41001a00e01a0700419a00c010340d14103076150101c01080010080024401840407007003180c200c9401035440020b0b0030105030710318444007205104200641082c403829500150540d010b400c000105070203a04c0b440341d01d07a03079680820160310800141714410540c8950a00c00d01040c0e520094012000c1e240080c20f0184c500301161000100c0d8000f07600781d52011402c01d504004500a25100b80e0080d14a035052918108c04107081910103828a814180c021660b108961030740214440215048402440325081c10100034050455810a840c110760178400007045150040031585034181c81a402000c41400350842100200403010308000d48903c100340c50b48903c40003002e800090203203001e0040e5203c01c0c03517080100708a980e620084c001e402800 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 495090278 1250 495089028 495089033
    0x904180c030516051e01030c050d2306010c0f06090317090709060807080304050d0326160503160807210b040f0605010906030225050606040501170c1926100603 70
    0x241911701031360082c20003040381001038005640602800503442c40341342c070301720f4072400002c00c8030040711010039511100801500c0d03100c0111201e90702d0320009068110484003480c00944180d2150b83c1041c000e290108009004541502d4481416281c0c41402da000d400280514410383c840e11000b003009c2801030148901e0028440c1e1031340210b1081030b01c01e0113050056014180140041c0110300010903d050703092002c110000f0310480d040d07800002c14021002c002c0025030003030007184e00440c0b288c1c403008012800400103c9042400610807401c011501a84040b2884005020111890001c40c007240c070110300c006100c115040045070181e00381c206042007240380d800c0500e035001d8038094900541d850f00381b00c5040c10382910002001e081c55121b0b518074818440007044142c080c42d0221400d02c201e076038850b00d544280c1d00c2244010815040020103508500d4614015a0211100e054903290301d9640c1401213a15401d0314000401e9001803034030002e07140b400b88000c40850703d410380100003c50554 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 495091528 1250 495090278 495090319
    0x504060f0b010f090905060d05030a0207060807090b030a090501090209070201060e060a0f0611012405130506060f0a020106051e13021e0f070f290103080904180c03051605 75
    0x24414405c41c196281e011031107949408c0020600581c01104a9039503d64900303000b0b58403072051184030006219200405c0505200388860001c8941c0c4040d11415034035134031410b90003031541031402c49082d075035402c0241c010b860b40ea02252080a990b000058590319001c0480d0b0720400042c007561240c074500c01d0a004405040007540e0a60340b4500d0300c0003515001d14a00381c010100f8142e025945a4140729191003e41e0701200c4800796017080c0c43d00d80021aa1180540c00d0700e40c10344215601402c140200e65141003180c020b4403940c06980300226810391354401042d011100c11148603440c0100e0504030b0781d03a080c511414444621881c07000c503e050f44540442c125818014105143c1e4200060310180c0040c8400940d16890780000c5642a842c400e031415142116411851598140390900c0d2254017040942c007444c1204d4102ca0224a804d004504000050025280d034503021100b0991010100d101e01428101541c4194003c081404d070b40342a45552403150340c459881800c0d00d5580f0b0f000c02d500d1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 495092778 1250 495091528 495091547
    0x1a0102030309030d05100801020f0d0f090c05010305061903060501090b010801030b1611060f04060f090b060d02030109140a050705040c05091002030904090c0e07081b03060406090504060f0b010f 85
    0x30707080000e032506c403100000542205030f4060b113040d600104204621241d51401040c024800134410003d191402015006a0f0f006003c086c205803440c0d241045154001d4000383c2d4400c0004007901d0103400c001002040d250303043d80095504c0daa0352001803005483e24814000c03021800d0802191540c50342e582c19681120040c0702880d25404d441c081c0b150340d402081192146009481918420703e050030b40820325006c12601611041d0601125042c00426440b8691407079402681c0b00341c3c2952900305100d44150700070720813a00747d03580d04801e4011074000c10510724070f41030034805030240041604115281003900e820092049150400d80c003040c68005084540c401403c6c0d45042c09491030700c1040c1d081d401001d010507000303802d02c1e00c508200802c40c039204056515007641100b240d29130141c00c42e030240b030442d0702c440525006d5014400d1a00c03510040c59100000402c0030423a076498400724025518103a50440f0865110607011030005a54025000700345420301e01002e540390f680400516a440 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 495094028 1250 495092778 495092797
    0x303011514030708040510020c100b0f030a050714090f2206050c070309090501050607032a0b2d06060d140c0c070b19111f1a010203030903 61
    0x900d0016022903000e0303008680307084076104140d5180e00d480100076000510459080322203010b1040d040481c00c0b01361003900d003c180b42900a0030008440b05030440106010b800380d0742c0c0070100e070035045d04644d401c000284210344204094810b251901d808100100207a41c0301500c0b4800a00400046004c4109103d80c0700c404140c030a9012078262001c3c201c0c13030000000c00340000d8200006c0090010001004112082c8603075101c61601c0e40d120f4010040310000e0043c00c4d4040300404c8070f500480d100b0410341c8040171154910394070000c14890207101da50b041c100125807407196481042200346054001760300102d91801803c4002e8941c0035541c045032001003100348960700100740c1c0c81c00c1c005964401c4640b441c03409942c000506000c0340c10411a0083d40340094503119014010883c00358a400f910303070102415440085107403008100f03507274480c0b400310600300d01e01c00c000c10400c10000d8070410820901b00e18900180c1c402d40444214100c043c00030740c16055502c1001071115a60000040b1016280e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 495095278 1250 495094028 495094049
    0xc04140f190902030106020f071d191812020d17180105151c0c03080a030e0607210c1b210509010f3204121b060c0203030301 55
    0xd24000115941d855003004a50394180356004111900d2503401035041e29169003c40b015501c1c005140c035520601c40c01507950f981009903182120110860740316801c912000d03e4500041d0220716100110b40360a03001050b82115026410140b008078000728200e002140301924070b10080f103d01500010109291504440303201c800107158a41c10226454035600100081c022400e001f81c001c5400e69840080512850484c582800c240841d11540001f40d03a01c030017151005850740e02c90364025002424604249074481101000c0c039001030205078403502442e02c0e00b40c480c9951018a01c10205c1c00d4030810900e600d440400190640c00c50f042c1d8404a40494031607010f4140c0e840c0c50101d5070420500003961610854011820030f40240190500307502c281e0350340d00400c044020446000100c0c6681c100041c8000341134000b0401380c1c8100343c135451103c1442034a05a55400010114141e0480c25104400345841c840c2c81d403003400d0788010003030007240361101d88112560006a01d920040c8240d15145 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 495096528 1250 495095278 495095299
    0x10806130201030b030d030f1a010f05300f0c0c0a0602130b0301061116060c021201091b03030207080a24150b09180403230c0a050d02060c0414 63
    0x168441c0d080f04c6518030028060700d00f64841d8032000303400740140d454068a4a030901e40075070041d51880c03002030300b9280140d4960b106144810b07025519681700115641ca5040041d041e50760800b00502d0422450642d00c0441c0d01034a891908800b845001814040c0d0404082110b01005400003078409040c9070403041c0140d03280340c1803c403401c0c1c030034590b80808a004404800040c03840d40080e922001c0c1da42c2038040d01c40e88103e45100c2102e40d10f00e4000c0d0f00220315a9446100982014511082c1174155000001a54078031a11800380905480a5010b14118544424810981d051165a00610000c8000d00400003c0d6650000c40c2000d44221030084484941060300b6a031103401a10034190b500d0241c281a54403000c0d00c0c503095001c039040707030b00800079801d4148501100d501c480380f0668159544100c6000100f0340c400d07410120102b00010a20140003030700c3d070601d09014841401c0c1c0b240b40180361520a400019080000c000d0600610740414041004881030701404071603140c0e4126640241c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 495097778 1250 495096528 495096533
    0xd0201021c2304051206070219140601080c01120b03100203190f020702280b0903010e10020307032004140616030306050a0b04030507050f060906070f0b0a0501080613 73
    0xb40700c4140c1c0480c8512031600320304008414480c0050041d03030801e5030001800d121310200b0aa42d0a829100040141e10038203202e0f072455606606208c28510400328144d030b090900450600c0c0081c20b030898070301c5800c000011200ea40e049140d051001c40605400e01000d0f81c1d0703500190701c030150440e03d0f40d034942e0000000344080494050310074191b150b44030204000486107111400039017100701c04a000b069501280520707400c11034141e03007010071042480ca1409040030742440e20394000d50000d542541d03c810040302081c50074088038194281007400140c40785019413008040c2c40782c0f500358000c22010303141c51603140c5000404540aa940710b00300c6010321300040000c0355043c4291105210091041443e0100f09076040e0000c508407a82180c203120343c10f4940702640e83d9880386100081865000c80c00170801d50404c00c3d01105000b2000f0031150509800b07030301156085e40306100442e5a100e001110304e0800104991180c3c03c030000790f208010b2503041900c6550364403809000c500d010b041c200307503031401c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 495099028 1250 495097778 495097787
    0x31612050c0d0804081b0d2d0b0901050705041206200a02030c10050601050403020f030703022e030c080105040e0a06061403010f021306051c050c0c010b0d0201021c 72
    0x2007110181912482000038142103a20350014011030245005000848100640c00066008501001400309030205d2240e40c031415014103643c10b0700340310080302180305c100300d0080f001019020301480b0614810b2400c220710300c3c00c41ea401089a41070010031b02050150b4140211500d01c40c1c1d80c454000030703a00c8401c158024203c0d4240f2912210503d000608151499003c40a4195000b404040315144c101400009d4241c4400300c4407140081c17030a00c4108007601d01030f400001005009025a5081601ca40100f90394014850701c55080000c0b402203260705200b962082c0c10144114a410021120704040c02048050f041c82103900c616110b0700b802130381c0b8405202c0c44100d107070b10000400c00f560703580c2000c1313009552400141e40300c0d510344400e004012510b40210340d4004d8105a0034111780c0d0401c0801c0d41c03075030402070a0121484804440c6800c0032002d10032940916400794042d80c54400c1d0200350ba095807440e03198140900b901c14038a80040c2d80000c0c081a03680300555409120410f002c8040703d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 495100278 1250 495099028 495099043
    0x30611071208180d031d0105010819030504210302151902090301140f060f1f110f150a11070203070501030b040b04140417040b0301060503190e0601060e03161205 71
    0x11031a0013110030a522030364040c2c0c040304503104a2400800805207010119088030424458001c0d40d401258520500340c0b66240c000d05264403900740705040944824800742803580c808803401030b01c0704981e52502416010000c0d5040c090b488041400c480c40c4c000b09a5240f5514180c6503c202a0042500b6803c2d540c20340001001c1c1e0f6180c5529505407500844d041d1a800c405c2d00c1e01401741c56403615220150400105480554550491501c0031144d000c070102c0b20300504441040c41c0303000fa002d242e071035172009026002d0b400e0390340344e40400c40e03040c0495030904880e10b050040040e818108120401610302290310000c446007400c00049007000d40000c240541100b04585600c140b41c2098207015183c0e00f04241d00488c0146403d13030b550001c0044196a504ca14083d4002060007400108501c80c81440110350191344080c020041c45038001802c000c0da800b210302da65490700410014044070798401d08540e0015030480c002d181d03002c041e15091510b16240d000d011400c03007220360580c003400000c20203035 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 495101528 1250 495100278 495100321
    0x7142b020f040b1003050a0e070605030c0a0311040b180406062705120f01060501050a0507110114074209110316030302060601020c1c150c0306030611071208 69
    0x160300541003120700800401c01102c11003107d915020681494210000e074a9040d030b00c241c8c40b11480c41c2c072128101c00194203d4426081099100c00c0b0700c40c00300e94040f02400c02060b504010680329005030710444201d0350146803907409685403110030454558049401d03504500240c42c0c032403000f002c1c0c0c13001034510821904075a07042540182c54201d5008002038100c5281222402046641d445400445003407227200f24000c00107030140203c001190640610007a00401410210820580395203082e1080c0c010a40680f10f03041d407035140c1485110364a240c0d03076003109038246041001901d110045180940d103c0601030315503451f049141008607000407603102030f2008088843d104291a442e0343c1001417808104c005004d0750010900c69400000c440e8441c0100628110240707803152410005e00c02c5402c019101202c03001500c0c10941e04e2403181c131082112030354020910034214140101a00c11501c0c60b002c10315002c00041000c82c01e8503003500c20812a40c90300740100d449510710051400c9012150 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 495102778 1250 495101528 495101539
    0x10905060a121505090a020304030e101112030711070501200717010516110a030807021c030c0e03070b030a0506030304030b010b040f120b1f0807142b020f040b 70
    0xf50010b00c0240094007084803011103104445130303504100003081c6c1c001500d0003404a4a50000404070385002800f0180b07128007403515a11001a5403980d500d0595004100c00d0140e0700007040c0040a0351040c001c1000c0c51888004100c01c1d4500340000700038203083c0d0281c003440990070142d80500003083c44880011700190b4078038070084000310b030214020b1074150380d504034030010200018641e134007981e2003804507126240644181c40700d9890a460000004210344210702600340c000b4110701520150540c003803d2a038000070011500e030005800e00c3c0c0d220060b240b003a400b100c020030086100d40122030303110b007070400b010410340c40d5940464a54011a00f00030f03c00c0726120004240109440c003d401240e02e0740c647c64141035991211021003c21444001e811100c0c8400042d00070700110000280c0240c896113442082d07035607900081e06044031500300c01307414001c0700131007091880c0120b600192444061462030070b80d030303803a1402030103e41d000400030302070415000010f003281d0b03440d4080342ca8454060403 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 495104028 1250 495102778 495102791
    0xd0b0a0b1504090c08010b09040f060b03091e150112030c0209041b060309030c0330050103060b09070215091c05030a1b140f0706020703020f0c030c010905060a12 71
    0xc1da141c0030303001405500580380c5411801d400840c40340e1282070480d40307040c0c17101e4906044007082c0805821904480840903403580300000c0c0f001e24203801180310307048240240841040d640c14840b1402544100344a503584041410b03003865100c40341180c1190311040580c41180c0c418902034480448000b4003a610581d014100001e114420000400c0c40b0b10110303000b0718154035034400368100c0300113020240004000128840c0000d018070f6401403141c0c0f0300b420782601e144041d04880440c40c503070110b8800c0f4179260710042041100c0c40c0181c55401c4011500c4400c1454102402503594148200680324a80c2c4d01d00403034000e95042c07280240c2001c2d4140d212920707280c1e14901601641c001c1d00d40b281032901c0c1c443c00345100c0300d5074441185405559604c003913501c007040038403030720641100041003010305040240e400003c149200130300e400c0c1e21035000b23800c0202c10074010031304142c0c0c9450003902940001480032500da07840f035850f109454003243c049491b0100c01c20300300c421661512001e0b105500c1e240 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 495105278 1250 495104028 495104059
    0x2030a080c0d090617010e1005040f14060607020d080d0207020301020403060e0f07030c1a0408030301031a09060105010828050f0a0f0b030307020d0f080406080f06040b0d0b0a0b 78
    0x140d10714218002d403905403503d6500c032011950900480c000d24040d48075a001032042d54201803003e0f42000c400b0b81c0e00c1c000144c4840006049446501c010b114441d0790b6248a11188145215250f219104032286810700d00c2540118a0b040c9809100a09079440001c1d6000d0301041c941c1946c0c030701500038000710340703681c0c9a00d0407a00401820042040c0c44c8581c40040c420710f2800280c080a4940c88656402c0c0c0c03921b0944004150014883c0440a1150600c07000c110382000700003444c000c60084044403c194410300741560451005443c0c20403a81181005101e0f80e6007000138190001c014443e203481800c01c40c82d40745102d003002030040c075401d409e103014002d02c03001d103e031050300541042008100c01e01c1348900b2201200c070412205901600240000300c003516246c280100514000c580c03808000100359036586a0380e205810000200354100309003c90311600040303490b0300080545040100b656080c002850030710400c40c0091081031107800007800180d09070408140340c28050700f070440302c489a0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 495106528 1250 495105278 495105283
    0x2031e1006090506011e020304030213050708090304140613081b030f0102042303150a0c0201112a0106090905031b011509050a150330090b0702030a080c 67
    0x155514102414040d0102d500d0348688210b9004400503103c0d44d03020803c40e000074100c41030050045080d400140b00000268542d41c0740041c200400040c00a0f80d480c0c00e800240c58000060200e2045030300c10700040c04010215007100c00c3c0c03810101c5181d07031681f81000803807807800d01a40090086006800b440340489420b4500c94038542d0341181550b18065051b50b10f5130807801940b0540d0300703400407032030b40703107029021034805c43c1040c540074050310180c4840d00000d050300c0030207484542d07145540348028110f2903820700c641100303103600a410a15080001030705481943c01409050b81c5000d0107410303070404403001d45c00200185a2080d042c085070215040241d1290082e000080c0e11504480e00321584440c107110741840341c441c180f844000e880c10448040028640101015000c0e42d0341c44400245001102980000b14030895180c0341015a080c1941c000c2c00844c0e4031454201e042056081321190088064800d4075680314041c1e40b43e1a140c00001d103040030070310b005004010001103e02071000003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 495107778 1250 495106528 495106543
    0x609150703030f1b0c05030904020a0c0b0a0615050c070503010c0c030311040e010e07022418120d021c020409020c1507020c090403110d09060207140a050103050402031e 74
    0x940b01048001d540c1d40a240c1642d40042008503102034104206055600440003c0d07a520f001d542264280318405021030b089038000014040445c0e288807141d41001001d20105a1064400b202440070b02d207801c210507841c4c08a02c402c0814003002203182c1c0d812460412000c0f0042c100140240803821903d0f0380070b81403030001c01c01900020700b441480400e00c6094402c40e41129032500356401c842c1c0c41d040900480e04806004117045010309242588a070343c40d60301000024406080f10f0302541452072003040480f00c007a40c0502c498001004507007240700ca9400b60341c04600d408a001d680e5148071003011082139400050303c91070a00c082004074503400b443c3d000d0041041848110f900d514804880e503004184120b88110042c0c1c410388085115003444a40c0d035800901ca4109130002640141303000b0306046402c0c40030300c0000c142c7c0702d042040f10b504116001c02856003d040c035202485070750104200c889a4090b250505845d00042000c41d10300700100d0f520411810b141004200c111110315072150113 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 495109028 1250 495107778 495107783
    0xc1005070b151c020a03030302031003210807031a061c0f09050f060f01090f02090301090b040606062607050c0601060c060606140d11040518040b0112120e06091507 72
    0x7840407011144115514443c803019400406080c0c000b07185a804502941c001000c00421440c452000800581c00840030520b5030440c1090f5003401c005094010520710004046808050600724039142e0401e220452400c2075105580c096641d0340c2d008001c4810600391450b034009507103402035041c410a00e5500c00a0035910030b07420340b44d1030841c0e10240c2d03542c2c0d031042d9000b5186005e102d00412160b900c91b0b002d1607205104280c054180400c0900180c21039804102c182d4682c13010320300700010030220748180c1015110724103120080142c250030304078070b080b000551004503501c0a0049000c85010394166000e44400c2401c659586d0707100c1c070004100340e40c0d01d4812a00c182c14640d002c141d040c09401070454240b21a142c1505016409064030042c004031085159450420000450181c450381502200c140404110301d86904242c901002c4601050340040e03250603846012100280304582c03080c4101c9914078040c040c15074060006801c501c601101d0a5014100002402d0140340c480041c15a190 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 495110278 1250 495109028 495109039
    0xd30080f010e0714090f040f0b010305160f0e120f070f0e070c030c03090f12230604031211040e070206090d0915020106030b010806040c0602010e0c1005070b15 70
    0x2666030071500440c2c2d2081d600203000c11240703202100c014100c82c01030540168001c1c415004800c178078003c103003140c800702c0d0f44a103070507204ea500aa1355609405203d0300818400745121261055001c01810340c184008188100030400c00c1c02078032560f4114020101300c903d8402e44032070384a50300d00c8039681d80ac5880361980d010030080001684606070f10020f48a24550703103a0403c072144c00d40e4102c941c0e0011070002c4080c0034a41c80f000c220b20140301c0924000e0440c6134010f81818035282003c1800d0011080222001c00c40c4c091003c04000000c686540c2040e41400e1203403c200b00001c0c3d503030240c544003403803c80071600400e00203550a00c0700012409013030107070207507050717510b49003079068860000c00c0c09540070526a1000700590700e01c694130319014007964400050f44a03103d03650f03e40c1514083c0c1c13040503240e0014080c041442240f103c41c0c070042925000801144981000b0152500c400e1005a4400d406050146401314020f00880d90020b900000c1010140340c0340c0d88800c0030b04401a242400b90 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 495111528 1250 495110278 495110281
    0x3280515100f020a02060c010f0501080d02100e030703030504050f06070513290a03060902030c180a0f030b070c020d0605040c0506070309170a0f081213020d30080f 72
    0x22401a0140c03410740802e54040e0000f41541d80a00c0b54540c041340800e044d80d96140780c044409203d034400da5002e0b02000c0c000d06100e4010400091421b1414602c805165181962908580d00e000041380c14081e8981804506503030785081243c02d142c1c1800e0b2034184c40c060034040080040c0e01c00c00409290f20785400c40c101e00760300c5030704907240c2d0000781e0500080a40305007085002503d054018000c240d100b4500840c5050325901880140e170070a5038000000780b400700310520725800412944078040c03419207041e8025032418441c0d8040156900c0b000d0b10b0000180302040d0305a101c0d04034903906940203000b90141c621545054001490100c0d420344840c1807504011403540b4145044840054055980c0d550362400c0030b400481c071544207011942644121101c075000100078100c800311080c059032446440f1f4003880040e544550004010800c4075080008000069640c40c0c0105000c1da0003850000e42c010154001220074402c440003c520780c3d001000d0300b0405070340245440d114019400c02c94034030303 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 495112778 1250 495111528 495111559
    0x61c0c0905040b13020306060f0418080705070905060604410405100b071b0806090a0b0a0501230a030803090c0f0d080a0c05120708030106110a050303280515 69
    0x18804c0b160b00a5050b000700020440341c2c505103005c0f03040414002c1c00081c41110100300f075075841e0800841100d8140c0c001c254082400424000705006010611060245141120014001c3e1189000d0101d28020700c010721240c980000c040007500052030503801e4a00444000d0020f20a1555035107140314604000c0011b0020040302072210440d42c0c0f8041e00c6003040d10551b6800740f44084800000d00e100c0c0c18202c00a00700c0b4080081c1c5000310b502c03030b010700161606814000e074030541c014a0900d0350f80c1401c0c01000070b0201800d9210000684010010010400400044410b90303181c2c40503040c61030200078040d080d080810800304c089070880c0d6030316900c580c8100703100d1003411900303002d0820681400a0400035018030000c500f000c4c4607030156105008107000c3c80041c1c0e0441c1405131100800400180300340c58001c034421003902c090b8401440300c1451076039025a2407100400500009903600fa01c084045001c1c0c03020384007041c0c460000e00180c50200280c01410551182c180d10074640703041d10441 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 495114028 1250 495112778 495112801
    0x3022116090f090207050309041107140c0f041d070807050a09180204182a0b16200a0e060f12030a2a03020606031006060503061c0c0905040b 62
    0x1c4504002d41d42d04201c1c43e080403840290402841078541e03010422030070090759254031808540151030301e4590b485401d541441c1e40c810382d03c03010201139a80046a00300065503001007200c003540b802c980c0800c142401c0e00c8207041036041300246004a05c6590008a82c0190116130b01c400d5600581e0540b6040355504044002d540241d413656002d10034011074500035041c01d4020b0407a5903260188280220210341d030b1a20b410a445920450400c42080d1100040d104c8010200003014806945410504040c450003c0240440c030000c00c0c40d400900d20703051402580b0508100450010300c0240718030f0b591815071070500f50480752284560080d544400d00d600e04440360240000100e401541414181e840c15608070340c3e203821148246480910842c4404881030031191280d00c04d501501c3c49040c10f00a0524101e904424000751078200b00040c02070075070203801d8076031142c021280181c2005540030311403100411800040c001e10030720200420000b480360004c90040c0d1007102411450340c0d50009005 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 495115278 1250 495114028 495114047
    0xd030209151e0f03040b011d06041d070611070501141b0a020402030c0706050f090d03050c07050a031107080706080f040311070810050f0601021c03022116 68
    0x40d808000e01c0e07803000d01d1071104005003180c001da01e9100d003420541d40c400340707500380c0102c0c07041c0c9207201002040108201425440f140100b24642410a0303001000340e8042036200010481d034002d6580d211a10380705482c20344000d0108000340196520b40d038680000411103484001540410310a0540000e455445240c1082c2c0c28145111801d00f4030116882d107035168000d03062204064890441220056a1148000c1d401070001042c034650310042454040c041d00d000400880e09200c440c0c00300000300d000170a141400e555103203000926907079441d8600c00c0f940186000075140e03129541c1c11404054000c130b110700d0b400980070200d8a0645d91a02c80c984d440c0464000c1c180014084004550505c0c20140b0943c0c006200341010b41140215184891811840b588208d5aa070b0004030f05483c403024a21820f50400721194180c0ea0a161540c0042e507103000004c160214113084080305098a03100f54140e0b02d40c2c4039803400207202c3c4880c44495407500b186c1501c034a01001601c18a09142d07a01a21100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 495116528 1250 495115278 495115297
    0x30605030c062d0301060e011d0a0909030c0f08030f0c0903030703030b01120e0d030623090912030112031b0302060c1602031009140d1713020909070501020d0302 71
    0x3071500f00740403d6a61085a082e2241d49181100b000841e8041c1c100c0000e0760291201e43d441690003024040010b0501401e0002c507100c4403828a05402241c480d0038802e0140e5a00c5070005c110001c840c60101c82c0515205000b81c01d810941c040442001a07840040d0301403041da03020410540c40700b01003445a841001c5450394154000c22000c000640650008809040c0504180d4041c00758101c003141602d800140a090310340246450300b580d90380601c075050103031441d07004500c801d1000712001000d49038a2050180f003429441e0004074030180c20045030790544503484031a5102d595607a01030404112014013140072640129400d480001420f01c08030007907416074001c040c1526041d84c0c00c07150b81c0c80340441030a102c1c041e00071400507031002c0042c2c00d056003c0010014488110303062107880d03000410003820f070680201c010180d1681d844072101e0b2205244414003085521502110b009244c0c015100a41218403002000000800410207008458080c0c0030382d00201e8110404908a11400008 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 495117778 1250 495116528 495116539
    0x80c071215110a2f030307030504050d0507031d04060f0e04050105070c02100309080903030414090105030307080a0509040b0a0b0d0f0c0903080c03070506090f0f010501121410110901030605030c 85
    0x54030242107680c11201d40203011000d5139444e280c140041d1804d41d4030444156001ca03071150244410040100011f0400b8400e078540305042c482c080c2c0c2e00034195454083c080c030030078210340802ca03895595580140c000b8610f1205a440c0d0a5440c403c82c81440c4040b00c0680e42c0c0d518220003d189180101100046a40d00510094600c995a10250014815110180c0b99044180114012030310104010006854640200c0c00c402c44580e08100c2c1047d0142c100c0c0340a90414070040300020309401c01e03100da1114605080d900c9080c2c2030040b90040c1050501c0726030080381c100340007030425030032002404481500c00c02840580c1403a240b080949192038035000015652070410404903410b800a82900c2d600b4405591400145480743c500c4c1c603505075001e411903006600782003140740041003514689003c0708003c0c03069615061000d42c490000040103010990b084554498101041c00002e1007500400d1007002060000342c2e40c2a07550304001e03005030110b8900500861103241c00141e01c903104000600 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 495119028 1250 495117778 495117797
    0xf070605130521030a021006080c01080705030a0e0a11100314070509130e0d0206070309261c060f0b0403050d030209190b0a0305010b1303080c071215110a 68
    0xd001803107440b0f02921165074140082d405882c030f0184014034142c9071507401050780300c50340b03403925003110015440107140c1c0d4010031210807241d82051501d540a00d86040c180c1c0c0325079569034480c020306040440803c5602600030356008010661300380c10b40303000b002c5d1003410043d580554141e04a90031441078802020340f06001a0b8400d01c42c40003000b08041c0138007100c21503c0c0280d01001583e80101d200e43c400e4001e094691103030b070b07410000c596216503070340785c1031107010010b84405104c4400000c001d000c03800415400c0d0f50800c421070444400641c079200c03482d44a082c1c071480100a0105005454201842c0b0400154194001c401e450989400c81c004c0c01418807000415002036000d05e403440d80080c0c4142c02c08202a99844000f0300424041201642d1007102c080f0040403500d050300140001c1d2018002c03606442d0b4507003000030640e94481d0140740d07909006103506251880aa20003e00d00030009408020008001d642507003038041c041061110501c2c200b203040485c0241003807500042d80038003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 495120278 1250 495119028 495119039
    0xb09060a031b0302060301030501020306010219151107081201081b03030f030a110307031e05090a0f0201030e0106090b0406080a08070b0604110c06090c030d02120d0605040507020f07060513 83
    0x180c030701000245002c180c829580d40ca41c0030501d9a0000d9005840d2654013108120305560144282d022440c650010b8495600303003a9a02480007904211170300c42207980d80b604108120f11034080300e150f41d8025100c692176404082d05030600c0c035800d0188401d180160088801400081d5500c0b02c05120010007840c1040700586048a10ba040200300303e400b240c850900b1010030724000005e500900b169980440c400a2100000000004600d0800003030781c503000400000352030201d40107000b03640c004001c01c41d83c101800120007502c9003c070030810035460014002a100c90507403160940c101d042e1418446140e903041c1c1203403150701c1c0480241000307000704507080020b044011000c1d8072000050001030425070105822a098210745030440c0300b6400403050101142c1708100c40002520308800800601c08585002034035182d03036240550081e072022900002000803500704501828029104029a00d4140c1000b0354803090340d45e410007030340130703410300030803c10300ca00100c803c410780140c03140181c1131405 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 495121528 1250 495120278 495120293
    0x6080309030709270b07020d080402090408070501110316023c10110a08100609062001050403051c05010b03070e0d021e030111120406090320060a0b09060a03 69
    0x303094244e070078294001913078510751031141ca0040c0a402592501da280c608120060315108103580c400e0f084c400305004201c0107036215081194402d50000c045a1100c002d46480c90141465100309001000e02008202507001c0c04c0070440c0c00c00c4140d034200e5500000603203440d24200c500e005007003203510b04440402a012415008d01c5000300d4800105c031f100041341c140d00d4045820002e01c0c04040c1c41c1c00122405401e80c440800c07030700b100c2000c0450344640c3c5071100c0078040007490312841c400c0c041654030101f00310501ca0304444640a080d0000c3c000380c549460010690781c40007941c880d040b0303c0e502c0410403c103d640714545c1a5404038502500c7c40e1504901a2100c41d010f03140158131004052141006885000c00d441d11400240300e04080c81e10f541e0109400c0d00d583d4410611500424409002143c61104c02d80380c01c1a0841c6d40011082c1c0541801c0311280702c290783c0c01e4200c0d944690002030b40100014014400e0100c0702c410005c50b420760042218452042c0d0390a0341c04081c40c5424004a40f01 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 495122778 1250 495121528 495121541
    0x617060f07120903050406030c03140a1508030f09040c170f0c0706020d27050c0d0c080d0f020c180a27150513020a12050316050f0106080309030709 65
    0x380d0604400011602c20154251060072004070000303007000c501002003d070180031b0300601c02600d00341032040070030180e1410707480d840c000c06a60402f525141c0104440c400c0751400d0019000150641c1d039130f4075444403020416130014045a01075450050791508c0c8620174019580341f4040c64011002c01e4851085400741000f010700142e2081000f0428a40043d00620080c029419449004503000101840804405c0c2c6c800c241c91507080c089041110000c2c6e808120006814000c59440c00a200796007001d04494515410400852188581d00d00c070284d00030100301c03c03441d07040d42210707040d881000038010030a02d4680c0c02e0030b40000710004154800825013044421080e848001110400c89080d51908000724000036280da44801071641204005401507607880f41c01c2c4148020031980c140c4c00b040c0303550064410f90b5100450041c0b40000c104040c070454039005800b21000045107074500f0a903444d080d454414004079880c281c000148100c0c04002d4541040c0300034082e010b83c500d8032070341402a04d032 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 495124028 1250 495122778 495122791
    0x30a050304290403020c2b15061e08011802060c01151d0a0e0c100c0b010f05130902030303060d05150a0212090f0a020607110a08060601030617060f 65
    0x440c02586441c10b9915407038800000c2c1c2c040c1d41603060030103060283c244209403020310b001d403980890071043e2650b5100313041c02e00303040004003480300b064500b4003401102103540070204403810800009100a02a200904d09400064000903556070712040c960880c0c0c3c80c84c01c200000034111410308094640f43d8090150a5110310012880c24415030006131b0804103a04440941d800e500341400307012103000902948019003030710401410312940212569031035042142403113002c11101d00d06000d442100180314149e4003000d1085c40396100c10038581e07150405c0c000c00d40140421544ac90700a2040d0207000c60b044e8000c0d0117907195880d444244680780c2c9280a081c1d4103840b800000d403183c1c2c0455850940b081c94551001031300c55252203100c074072458026249000c00d50201c410a070301c4820104500305a29070440b181907841042d80303004902c00d12000384240d2b10172510100000c1c4e081c1d02050040c070442d401d83e01001082c0c0c540a010b402c446030700d048544d00703602410014200d004182107ca40020 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 495125278 1250 495124028 495124043
    0xa0302102c0306070c3e06040e130c1508060f0f0108041104150b0c1507050901030203042d02040605010f081501030b1909050114090f070915021c050c030a050304 71
    0x881032000341040c2c0f0201c90040f1400300066041d00c0c841240006c603440903001122203030300e09444c005101c2196500a84050003e600e807007501c07000c106c1c0201040000b0405101960403032382d24000081c0180350f04580c054000c201242e4913004510b00703039160441844050b1102e41d9180c45503100c84403540780f0314038096045551030111032800900f61078040024507800807031079503c56402906500b01120030340d241c08410b42d800c0c00d201c011341d001b4040d680c40310b801786801070b100d58450400e143c0480040300035442044540b4a03080c8403003008200c408449000b0b80c0c1c2070001607550001140c4003e13171414444000355100f008070b806000d802c040c2d04185176051402044030340013040000c6c42214444002141482c0740c0d2700401407010b25006450042c0020313400f04004500749030114040f642c00400032845042c100d000608100e00076141e030f101034600b43e0a08414050111006580c0d000c510480c0d401030544032812070303025441101101c84e0f003840d8601850078a49000020342c2c0315000a40100c8a00c03 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 495126528 1250 495125278 495125303
    0x80d08060a0902070807060f0204030503072409050d0f0e150c0a0507180f020405061815040b04030b010905010305071205210d0b010c020102030412020a0302102c0306070c 75
    0x4610070f0004c1d0100c42d000b0082e00340e890f1803511b018001c0320704a007005604980180420404102d0100648417801d80203041010328802c07a05400c1c0900c1410f21448480724604a444000d00400003980324035000107031501d2800e50b400413400d4980241425a6551106003103405c0300f01001c012024044124002d411200800003650340d0b0b5040074901c0c0c10014510481000703084054a07a03000b0f00c6003094445074110710701400c040c080351b101d109500c07100040b41d40c6c0300101e01c3c1d540c651244080821070800340590b11562138220130300080c1e000b84410740b5090100c1d4004216245607114550403039502000404072180b814840780400b103000d10058400c1c0c000d1107201d6100720f020f0f040100040f5800300b022961080500310070000c9505c2e10860303070b0400000d00788070030060360000200c0b0180c0b880790012036403100301440010101c0302c190700000d4100000400704441143c002c0c8d0b03808521240c031030701305800c03440600c20a40c0d2950000c44c001d0f410351014010480b854018441426410301501010016 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 495127778 1250 495126528 495126539
    0x100e04020f0412050d1106060108040206120f061305060d0201030e161508070f08150303071e0c0e0405100c090b0703020f010c090f0b03090a0209070e0a0f080d08060a 73
    0x40d900943d104848241c0c041c0392040420006210b80001000c0c242402d120601d604440c180d0745901c0240401d0520084802041c29590b483c01075403240f611a12504489190007520701420300340950b4224010f550008040e0545542c40c050903115000140205c005040d254004502074100e00000c44050702420f02a414848290700004015040070350500d505005403e100600001d001444c2c3c1c410000604541d0048640c490281038001180c2c0317510302d00400c030a100107810351042ea50024400301d00ca1078004080034072440705000d80c0c3d0080c0c54000007180da4400725400f109080700d0040003174000000c8a011161154005500b1100a15000c034080703496410300511070b40081d00607030160b0f02c500d890341070000003400f41e03640000b0700b0320b49013801c00d2918990400f0010b95001c3c80c0d040e940044005055640f04000c0031705c3c4a41c0080520020f8109140081c11403001d038010700740179940036180440c420070040a4401210341c40e2006241e07220b11840111520f000c0070304641d90040d40800d00251 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 495129028 1250 495127778 495127807
    0x80934030f030e010815100c0312021b07090608030304060513290606090a05120c04020f07030e0103020a12050414100e06010f0e0c030a0908031e060906100e0402 71
    0x20750728802c1d22140c2c288414000058541c1d440200800003c80036401080a0341e29608162410780074282040c1030301d069540f0303060b0b804a0f801d61045d0601031001c2141c2e010102e204110a02031040c0000383c400703c5466006220a071000c070300501c5c2e15540100007050004080b03a00c00b55203c004e0480b00081c0900980c0d684242030403143c1c07080e00b0004d28085070f20481085e2841550400421901c40f80b03400c01c210041680030300513220301c5200f80180841c00c40458024004850184030082045680c2c1d05402034121054000e840d00781e00203500160085490350280c42180d00c0c0d007031281c40f80600710700d0b403210134805498020021903110001c00301840040c5420081d82e00d0080c0424404100b800c41d0425441c0b4004050b0300c11401d045880c81c04002c95890109001d401524102e00c0c203989558440d05a0080c2c403941d4802008440300004200940ca0002c1541c40000500c0b0904041515150b0411100c0c503c15101240e1182c07940c0d03844030041e406044a001002c3c0064800341c1044141d516040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 495130278 1250 495129028 495129053
    0xc20010e0a0b07030e072103030b04020d0c02120403170a120f05090f060103081905040b040b0406081e060418020301020c010504260f0d0f02160308093403 68
    0x79106a20101802070403509030082000205d190002000400d1801a00b00c3c0c0c4054100401c400582c1c0000c2c07081d0505110740c118030071a29010300199940c3c01c40c0e8180c40014130400042e0780060042d80543c01814070b81000300e9080701e4001c940105408101072080072194000d2881c4130600140403036462102038140104c4281c118007030000209841c01c50105030404042500d07030102c80d0440e20051000074a818181c515540804031000e90060000b642a00d40748183e030405010b00e80c01040004800a1090060080d105c00359245000d60310362802000c52040d020002c1051005200e001408500742a801301d815030020344c0c2400203010090b00461308a82c48071780d40541a075104e20801c0184040c1284045220a40d0712503183c84480d00b880040c0507001d442c45a0148020005410008141e01c5e0005002c0c0500d58904554698581e800c0c1008403c6490040300403900007400191b0059020802011207084000074207407803e000f90f007246507010300b0505c90281000c0c039031011020a008102c1d94 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 495131528 1250 495130278 495130283
    0x130b0409030c0b4c2301080106050a08060303041a040e090a120806060d0c02030a0e0a08030403021309050109031106150a0605070c0305010c0e130c20010e0a 69
    0x94009545034101152401e400400b07481c03500b400c40d0300030704664094070404864914004400880d08004480b8a04c00007500c204004507a000c02d200070415800c0044440c00048024130030f5540281c0100064803164024426100411070500134139070311a004600150748880700405883c601034441110840c45e296054040c091800e02050502a540c40c0e402450b42001301400101070b41c400a80d103400450329080265410444800080781e8161160b006580400e600c010090042c2e03003140c48001e5907500502a10300000303a66262a0320135040414050055544a1002d11302e00342c01c0d40c0a00080d0201c090904003416030320138141000ca4001c4c170880040a2103555003c200400c0080d029107020005000b080c2404241e0480d11455030310140c0c503001315503150034019115a0207080c04840c0152552000e4615400d2440458107154407005245940c0e2041b07907800794441c69150000d04039004400d031140480c241000c1600070541c10300341c0d144582c2c05140080380e0600d40341840b600349060340404 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 495132778 1250 495131528 495131537
    0x105130801020a050a091a160501020d09060905011802030607141603020102070201121437060501020d050304050309040b03031c060302010305180a020603070e19092306130b040903 79
    0x40c0c00c40e90f40c00715000717004090900d640c0180845512105050784035586d85803c0581d142281c1c0c2302045020740507980401d903e813404000d29280350401c14007408020008a80e594a0004008884900e042203a116150003400800303e40c1e540210030b452201c181000303080c50384030901014803104040b4240e0400c5500c01d03400035888040510025101049544214648904001120b001f58404860103940803030450010907080c90701c0400c041c035800705503914120400074904100c1c3c0c010295040b0b44100d42003a0b00315030200f00843c2049a8502064030000e1564108001e046090b2400c0d820241c61000003c090364031b800058400c075841c94040c260411711090b2600410020f43da058850070350310410344103406034168200380902d034613500310020003485414040041818144076007142a00c490010300464042c0400001401400c1641d11070000e0340fa003001c1c182169003081c3d07031071030f0002e000342c000103140c546800003000800c0c903119003000149076444a00000329642c0e07000d03000c04540262203 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 495134028 1250 495132778 495132787
    0x20903251a030c0d201908011208041e08030408010b01030c0c081e0f0c0717070f060f0c060617011505130905010207020306010b18010c020607020105130801020a05 72
    0x200c41d807011448849503400c806007441002983c8152030200e82104482c0701e800143d001c81d010300920104405014a645031501040700c0d40000440310000d6020100c549800039980c3c1c1e03032180800d4609003008020248403041c8000c00c42504100c107682d1400c0c804074440c41c5004c4d02c681081d4556009076001a151b61f4617440c9040c005c1d42c00d40b25a00160025140c00304202a142c4c560385c00c82d214640c20360304903001107407624207001c2c140d0b001e03514002941c560441e903d001500580790789800500845030001c007505042c81002a0000d120011200342e100c4840e862032500c00d00307903660100c002010b000c2c0300420034040d0008182e4840c14000e0f02c0c0c80c03a80c2d4030052211014003421500410710740d07912488070800c140410f0b0b03944400078001040c1003038003140d078001c180742c401c1c068080e00f00001d405100ea5000412548150000303019400e074210050000d40540034011100000f84000207500600d0811108015505c5800180030442d8080414104281e83d0500c0a089074030011046000540114 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 495135278 1250 495134028 495134039
    0x212011107231912021e1005010f030b040f0503070206130611120d020702120a03020606180709140418080a11212808060f030d080a02090325 62
    0x18110310b0034012040c0200309410710b146100004641008000d440b07034001c48030010105108001c1082c448050b580685428950031b40455070b140c1144061007030b070904000001c503000505204043c2200c1c4c000c2c0c00d070700c2c4e0354444c0d44800c64030085403081503400740070401c850405030700c6070f40c001c0502001701550301000c149001c1004100d42d84941e1841c1e015003155080502429501080d140c000d0301d1004c00588c0d4126500c0041c4174601300d006600c40d107024a04194082c03580125445208690a903240030f030200f417400001007514012181c1102050a404041c07202c94101c0301303e408041400303000000c401d60000411606590325030000c07030f45200d001452189003a1700c028211503e91055004080c103030400c0228100890f0503184004140e2030207c1c094520000c4a8880b80480340c6400c41020049000d800041942104495590107016007203046029401c00240e121007007445070f0303661140e0b901c40d0b44d00c01000e0342c803c08200758140304240a000c4908080782030003a01c03800c00c02c1c81c0c0d41001e2819 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 495136528 1250 495135278 495135323
    0x309281704050f09091b01020f01060e0720031603091e030303111810020a1e0516061709030f0406020f010506041103010303050f0d060311040e0303060a030212011107 73
    0xd03c1054011503c04003407044800002403440d10407001000c0b400507500e11500101c3c580281c590000c8050340c20715000082c5101300050082c003c55060365584805401020442c6204000c101180201c0d40208132041130452540c075040703c0300d4440d01d86401c0311940c0b4940c00e9031242485010030071460f8030303c00400070184c15100c1e4035040d140500b82681460009051040c0c3c2900300503070203020f9812540000c100038828071941005070741c010395112140f80705200181c0b82488001d0215a41e110b90710385202041c82c0c0900c2c07031084030141d41d43c1183c080100c03e0303595a0700001410000080c4420712400029519810180005c0c0145078000c0140e003c0c0304602c90309449020b80390a0003203140c950310a0702c0204160450741134035007500b0203594811083d00da8440c20310903000760952003490410044200f00c601d01e0305e41e0444c001280c050207903403100c00500361644820344107a9400014510300b080141031811507041140740b1003000142c01040300031079904540c40443c1c1119009c0c44c1d40403208841519 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 495137778 1250 495136528 495136549
    0x250902040303031a120705010c0614010f0e1e01060e0a0e070512010914070f0c050625030c0806130b0a0b1902060114010804050a020d0b090d0302030928170405 70
    0x8866007178400340142001900c490850003450b041020401c040018021260801d129410003030004003125030795400c100080700858095510198031140104000e01200c440c40b00c480302480f0144031036a441c1100c29200394102c03030301054104003031400000d01440d040460f10704c03594154446075a40d130388060010000c40d5050300450070180c64006e00100100700a018150b00094504107440b000808070340943d411303030184000a0683c400e41c0108070700d06202c141c90303220040c00203100c6044034800c16002d5007526000203001000900400002c1c11a1804a045000390007003100c0006400d002c0b14080b554070b44140d046264026000280820400d001d00b01c0c00007814281e01c06443c0b20350605503c6100e100d01e90103028100160600401c05002003800100801540180210100307203042c54050001e6400715004800c0e401040800301441d4068000c0b00d124580c2d90015200f00c2001440400046c400b450030034200031100b034850f00c00915403100c3d51003201080802c10792554503050821000109 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 495139028 1250 495137778 495137831
    0x20a0b0c0c01290105091804050703021002030903151801290604060905220e0c0a09141609050a08010b13060323100218030105070504030525090204030303 68
    0xd642c3c1c0ca1050120045070071080b181c609107130850340c0d40c0d007030400150380724080755601681c2d940d00418803042050010300d850803280700703a880d44101200310f82c003aa03e03801083c030300e0350b015000068401c15505c1106003c0d50b004d10038602100400b0322000c500c90031548000c014a00642246061340040c00e130704000d4800a00045401038501400e00e88014041d049070710031940500500b2112024a00c00861151018500c11200700708990a005403283d485641c45c80e058007608443c040412810018003412905000000c031105480e1260040b0140b203400c508001400c0118841012515036a1603440c0b0004003c040008142165031030108200c20300d81342c0300d51480f546040403c200007a00c91a211014105201c1110f0201081e81d003102e003882180e0a0311420f4901c000356800c0944628000c0f490803403402d4000700320b15520030400740d610b03108600001d0842d910501000300d54140340452262448280c1d840c5400b5181c0e140344200c10b0b030300a500114086510703811000d414101e0428003414411 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 495140278 1250 495139028 495139061
    0x150306160f0201091406060a08210702061201060203130e15040c2304080105180316050703050d030f0b01080601120f020708040f03030210111603020a0b0c0c01 70
    0x10003040810803014080d0084080c06800001c8404441c000e500011105400040d5586003458581d41e032901d40d101219041c0c426451910041000c003800900301014a0b01520b03098580201e0b1190380c0d10706d0b0400790b4205c1e442001040201183c0d41d0812000380209000d400841c1c96070a8220084c1c402c204940100540d40329050400078106089000625448401d80d03000481c130042401c211b1b002e501402080880d800c2c5060307444981074103036004100b2144c0d0035000b04519183c01c0ca0280900800b000401c01c0d9500910861012980d5140001d0030644110b00f00d5401c15602c0d61401d003065036440100c00406e9954020303040c2c4090301c0c010840844000d20b020326052a100001810500040c9a1305919541d0386c00d007112080c2140e8112100340350000e2810751a20b41c0d41c2c00c1c082c0c03440945d000460050045140c10702180665015440011001e61815401e080300d400c400c00300310042c424203400314800d85039910045009480807900510184040a03900e980000c42c2a0030740355660380f00301204 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 495141528 1250 495140278 495140281
    0x1203040510110705060307261602010e0a230a06050a050a15090518010f0213120b150a0b070b04030e0319150e07080a0201020d0507050d08040311030a0206150306 71
    0x49202150f01025a941182d20360348948503480c08841200000100101c03030442d141618a001441c40b450324441d140d0f0728081c0303031503240c1848200d0070380b607034528540c419900504103800060501403809001c00c4c0d502c0d200c031545031240d0b40e01a280c41c0d040c40050350000c0e07490b401c1c00b000d43d86c0f901032154004c028103800e01204505a00d011101c0c0340ba441031050442d5281c000c5000301c010000d40680c0841803c000b40b01001c3c03041100d02c0254000c600b81907603004844d4000a05c0640411501000394000086003030070fa640c801009000383d0b4103044240c4c4058003100c0401c81c0c003041d0b00505641402404d80220078078203072501074240a0451308591081d0700c84042c0e00410351035080c4d400c45c2280c0c020300003002300b4415071940020305040424043c8074060800080b40f4180002000c41106000360300321103e00c45c40c00c1c0d054545108070100a01546c1110705206401e6014015446e0000c0c403900c0c000c1506041003c4481c2150030074218200160441230034002003034003010081c0b91200d070407406041039 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 495142778 1250 495141528 495141557
    0xa0309092018010e1018090b010c110a0b030106080906010e19020903010e0d020f0c040603021e0d081306090519060c0c030f080408160b040515091203040510 69
    0x5000e6500c4207550340b21498140c07000c1c0c0c0d11461050312804009010340904001c016400781c610703800d0074081c0340d04044842e0000349202c01030151041c1458184c40352402030384152610268008454496500045103003400260040d50030000e5000b0b0445503900340d81c5041040c0e0302e504014041e48140f40c40f6003060188150140c020034542c01c3c6050721000165101106400320707015119824401056004d000040300986402054420b45404110190b44522144604000c01c807444d03070101940005010300c490f40401c031802009050350b240105200808204d507900c45c600c5510912413491270a2180000b0004a07400c01180000740c0000c032010302616200f91000c0c3c10106d02480740c5030421910820100600c103d18039860050350300030302541d00c0e42010b403c0100003035026120b01e0040384a12164001c400d0f607210101020355840d840d541d460180703844100804c1104120106003034580070414481c0c20f075140c030813000f00454058050b503140c5140c50b04000e154011100750070140045824243c06 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 495143884 1106 495142778 495142841
    0x60e040b070c050309090919112d061b0105070207030b2206050601020c040e0c09060a0b16030c06090303140610051b0c030a030909 58
    0x180e03074a60032400c6500c5000e00344043c00315001480307812079501e4441026908281c680e011946400b0b08038002c40c840c8081500304607145194020680f9132810b003c0025000c4400210b941a03803003400071041d190300c1814640e240e100e00d0002402d81c142821108850f00310844540003000a0310382000013a50340d081c14001901e0f94004070300002d10240019030080510640108030b18200c00c019500c2d8800f4020140ca00d9043d4007a0360b40c2c0c8001500d40d8800c09800b03418010041440c00c1610007803000340b000141c8090f00a4030501000d0050301d400d8001c8803004004038112000c02c411604088a01d002003d070f0041a45080078203000c03d041d815004180149142d400c200c00c039850b0311041002180018a1140100300144081040c0c50302000090390b8150000066030105020000000c1c10444060002c4001c1112541c00b0302948185200340d03902c841051800c554200d60b030380c80e0041c = true := by decide +kernel

theorem cover : BRFrame.Cov 494964028 495143884 := by
  have h0 := BRFrame.cov_init 494964028
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494964028 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 494964028 ≤ n) (h2 : n < 495143884) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
