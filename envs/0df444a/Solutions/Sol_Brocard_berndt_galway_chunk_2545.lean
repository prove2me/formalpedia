-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2545
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:01:38.835013+00:00
-- url     : https://prove2.me/submissions/1a8a9559-6bd8-42f1-a673-cda4aa5629d5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 457553956 ≤ n < 457733812 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 457555206 1250 457553956 457553981
    0x20114160504090e030901030612020901060f12230609010623071407080708070506031302040b0a03060906050115170a1506021c031e02030a0b04050f0402041b0203070b0604 76
    0x410341095013070a03140c3d403010700d0081c0040d141c004049000d00b014800c080c0803036005080c0c04400d030308064050780d864050b07009040601c82c900c0b030210040c00150003000c48055801e00203216030041c3c1245002415400340002d8032500d80384005002207a441001607149000b1358026102107440d0400b400d01c2481030040c041c0480b20000e0800650187c0019110b04581c006c10488004690700c0001c1601c44400340140c3d0f81c495010404030350410071072284100b185000600000d49030354148c00140300303c00304c3d520803140f843d01c0e507000c2018000d06c3d114141c010801045000040f0000304c100402c03540c0c080341200801d6125030b0100340395075220303030050404600c0040c9a80300c070b030b071206000b0399143d101c0382501c140070341c50ba1000c1048a12900031915640c04003d088080b141080e0002e60280d00001c10300f00034640d45011010150341c460007010300980919850010354142030041c40152242c40320100505011034460142c0d01d03030b0020444142a0300003a007440103488070320014002e01120210314 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 457556456 1250 457555206 457555211
    0x60f06030a021c0e010b311508030307091d07080a020a09080111090a1a03071d0405010611060f0906060607060905030c0d110a111e041d0c0102011416050409 69
    0x603510401540002890300048640103110804491074402d400000482c7d0351009403900c10a00d81000c650b00949044c4c3c05032220344038010b8507452102e1039604225100710008045000c1008490b030b50500d00d61000c1031000b083e103103c3c40d16400140500001a180210b207590000e035040b0528440d10b00c4038003401c01c0400030b01c446000a4590003994201d032000307074070408010000141c0407c0503d0301c2c0e032620702c0c107a106a0540c1d40345d40c026506522140e4410b1340d903000e800482070b402e03902c92190764060016511102c0b40400b40c901c0003843d20700010001504d0822040610048000c00107489030b00100868820b5aa01c6c440c4c60a24060940500028413600c80410524007180e0045031619003805035540b15071800c054070844036030761011040c010304a010151502289410422000c01d0b001000c48150b400720003801b0b0214040701c04001c1d4080501e8000d110802c021102481340c80e0540001348004d216101c864031581169481c0540715249000142c0002d140031401034040c1c800901441004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 457557706 1250 457556456 457556471
    0x60d05010b030a0c09030c030311030d14071b030c020f0f0306090a11032e0e100902010f02071d060f030631081b07090e15060f06030a021c 61
    0x556000350415078400c001c2c1804c042c00c0d402d02600c0791411008883c3c1190116001c07a14544065030101b05ca011920002c0c00100815030042069001f1003424480c01c80490030fa500c0d00074070082a01c48003060041c00002c6450501000c13a900c0700002010303079012900741c40598040320000300c618840f42003080c2c241c028081040950000407844c880c141d030081c801103501c281c03040105504d90004102141c54241d80c6c02200c9044549404218480c200a4600040704030f64400c040e407400c00d900761401c0e0000d40783d8079a40e0465030b00c41010142160540001c208007810000351080311810540742d4061038041d40e00042031640d8405010038181405419106141061042245000307034540c0c0300e02c034000d07070750546044600a581041c0070013030300104a6820030012050010303034100281c042c401584904900441c194109101c2e008840c541c2d40c00030301d12050510700e4800800720003801e640c4140b5a000846c1c01580b1104101c07580150b446000503a40c070140b43d48103184512003103482b403500b407a1102 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 457558956 1250 457557706 457557719
    0xb0d03080402120a05030a0e03030403022e0315050f040212010b041d0c16030e03120c0c030105060a120f080d09050c09070f1124010609060c1a06060d0501 68
    0x6186000701d00035299183c1d502a0301c1001d0b80e0f61850703014014440e510410040c000f2a100d00b4034506071050050603245895a640c00041c5100c0d040b14034407440d81407541a402d54040752001c1d29000800900f0248903d01b503d208040c421a0300340300703e41c010700c248010341c1e80e20703503c9034100e034001981011800c81558450201c52516081070142005038007048502c2c0c00702007211030742c041c841c0413000240d038909140309507084518a40d248086040c03040c01e4220128940e001d0000c5160b001a00740019103d110304181301d840d00800019082c081d0745018180240390310341c0141c0da015039902d501c4071520964645442142c017040003001900c40d03040880d01c00c1444205070801c000e4640200300f1501200070f50782c10410054400c2d1404c502082c441c01c0e960b0b403c1c1d1b000305060b805801c11101681d200140b2180048c002018008207030312200c115134018031807140c022400b04050031700c6282020b01c0401c269151925071608103400b08000c5010350003d241640e41004540014140400500c41540e449a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 457560206 1250 457558956 457558967
    0x6060c0a080d06031e05060a11130303111b0904061d0d02070e0609101505040e0f01060311030c03150d081801030501090225030c020306070804110103060b0d0509010b0d03 75
    0x822664901c00c0c5c607880804170401810112410703009005042c89480e00003401d40141004641e40c6031140e800d025151140c160484400029806512031301400040c014003d820508981d0507200322114003c1c400c1c13266105c03114450340c402c3e4801c0c000110030909903000e0b020690508000c00c075074852003030000041a40418040115207900113030b40042e0b01c2e41401c10030310f600d00701c9080c2c11540003403000304541c0206030040b04100c0320700d0400d94a032035280d04001070380c8a0f040b1028180324644500404c80140d0500c00c1e000a6807074522810f040d42404c41400341a0310002d860038002485004031500c7e155034811045040395070004516036541b03000076508120802d40c00b480b43c0071a10340b00000440c2b05460089070440c5c0080e4070700e01d4031841041c0704140c0e0303541014800d90030401c0c20408000142c07000c0102901403100780d207442c070052800d2f26104640e01c4003494190304243c02c00608020340c80e00321080c0d0382c40451008000c507107692040c104900605a841055030f00c00000814001810b0b04034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 457561456 1250 457560206 457560209
    0x3060f0603231e0307020f04020d06031b0503030a05071b0506030103030807020c0328060f0e030d1109010801031115130503061b190e0d0308071106010e06060c0a080d06 74
    0x541a40c11030400000c0d1194a000c0d11021a4800c4e0010080040145414042001d402000130320060501c0c181d022804120788254000f1555102c05480b1640c01040420400c07008100841c020351a110940000074100e0080d020f005144a04070450142e41106580205001d403001920054896950b42402403504078251001005400342c0e0401d42291708010074084010494691201c1e4801d048418400710149541400d40c1c8072036480d468105800054000c0101e0b01c02042c0056071a00d600310324540441d12413900480800c0c604000a082598000482c141180c5c0c00848000781c00c250072000ca00d00900c0d441903110400c100046107203407101207450391025260309600311440390b601e100000c501101454282d03059000c0074070803a0800084208003108642e0a460529082c25256012560004000c502100403a03001010403060a40c0b140c0090b0814186c1c000425495141400700c12801001600c01406030340000b403141a21179041240c00c1c0c0607541308292581d6840c0c456800030040c12203 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 457562706 1250 457561456 457561523
    0x60207060c0327030e04020a0c02100201060608040b370606080408031b0c0106060203030a05060d110f030309190f060809030a080a0e10060504050a0c050403060f0603 73
    0x81c07141100c0503501c0781c807030701280f524100742201500c6285801c25180d070f400042c0482c00c00c01d0244403400d03140c03201d001505040007542c076465092001803041100c80c000c404204411689480007c020740d650103c44aa0400c0d0021507400c1d0301d0310307182c100805081084003100406a07011002c80c0d80070095072409010101c16210403c003158403200215414001650040c100d41801c0c0042010b007584003070201401d0095a0300c0d1454a007111242c182902d60300c0d80100b025800c04800c2000d51100c9000c0c030395101038211100791102c109651040607204008140c0c0d0b0061b00b2022010000380c50400840d05044401000c1121510894260b88400f116074010f0b803810000708040001e12500411215000e46880301c0a18103107195041c1c00c80e241c1200030b2041c20f0460300c6281c4400c2c0b0f035600380314190740080582030100d46142007400b444192a0b001c2c000d4148035142c09150460780d540241501d058951120b40421002c4170074a902c4007900c59074001904401c400d10002003030400054034009200c01c03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 457563956 1250 457562706 457562711
    0x20301091109100308030a020d0b21011b121113030609050d02060603100506010c020d080d0b061c0504113703020108010608060103150803070309080c0303041a1606020706 75
    0x1d400c10f02030745612091000030718462040c40460303c0d20740c03250003416610071001800141c903036440000441e0302071001414403050041c17014400f4045002c1c007818840d940440e041e1181c96440e04001810012155810b10709150b03070702800f0a000c9036450441e00600d4903801c0c0348411a40705c1c280a00240181c107c11282c40c0301340e054610f42c8500104040c3d2107070300000c0c0501101c0000e05031405c06400010310150400510b0442d400050790b51026100c80381d4098070040c0d840302401b000b41f6003100c40c880e2205100e0402400807403100d8107403074820191302c0140000400c0c0e0342c4540c0703040545280078007007003540468803020016038605a41c03a10000c0070108100030319403a000713604443c14081a800b02030300080010005000d05800b400110b43c00010600d00010804d00c15503031140314203110740143d000e0b500001842000d1650203180f46000d05000d50141492440c11400259a8403c5120300e42030381c072a00c1d80c0110b113503001c0300075551112590395082c0e544c0034052410000039070025804840c19032 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 457565206 1250 457563956 457563961
    0x10515131b021014130b04030309050615010e0909060c0a0306120f03090b031302010c1a0708060a0602070806130201020a080f0409050a0504020108010306021b1504050d02031c02090a03020301091109 87
    0x102203071480b401090145c542d030341d00b40300540f14170a80d4100100180c06240c1c0342c100d40c5001034001c1000b1403103000c03840030705000c40030964001820340440e00010f512403945441400b403814008282103401590401c405903940081d00416005812168081c00102d0020104441800f210703104a90070039111340d0740d81ca2020740f103507089440e500091700c110401580890581005501880106e200c1c140500d100c2d0200500402a404a80c24102c032407130001079040c0d003888914101081d001d0040c141a0004e0291141001e4651750f0700c10004201d0030f180d00d207848211095900a010021030150040c1849a90b240e0300320501d40c5039401882400c0380701c1c0c50540002c00728900c0d80308440c052541651140c107142d2a41d12100003a4100c03007108803035001842c119841b00c0c0000c0121a039503c185190140640c500341c1400c604101d480c150035001d6410401240c00e80144040c0c16030300504410100588600140c80491b03421111600000d4040d8030345401d0500707200c640c9502d0130440004032002c02155 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 457566456 1250 457565206 457565231
    0x1b020a091d06010f090c052701030e0109110d0305040b031e130807030e0f1207180c0903080c0304150c110f03100f09230609010515131b0210 62
    0x42d10240304150100a002c041449105041c0d001100c031a140c030300d09241081e0a42c001068010b1ba00400d6079040f07c2c7c0070000c4121541c05002e08a130b0120150002c000442d000d03151140f00d000c002d0b0700070b80704503c0c2d540d140003018000c80c203880c081c0459619040d10b901c1e1500c02c1a041c48244903035800c0a5104400003000c90020113403003c1c05a41c808643c03410040269004c2c3c44148044450740e47c00300c01e0074840c2e81191035039040e001d030a10700400100003031440c000300010842c1170100e030000c0c91420007401d00100c1d03401c000000704032030b0301200340c554030725109210a0850155803c00b1410000596916110030380c8203841e02945802040c0140724190600c00300f04210f040201c02e117070581c0004640c00c041040c00d81c4400c400113212080031401d1441641c941e8845048020280000c40e29011180c3d202c64040080e6503004c80d800b8001c05c12400c00283c1c94205a42911809220fa951416041e01005040d0070030390380c08006076164902500081406512420480300d240030103442d1011410ba02c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 457567706 1250 457566456 457566463
    0xf09080d050f042a17010b0103150506040e1b070b01062607030b0102073b06060313020301020714031e1204060213030f060b090708161b020a091d 64
    0x2072540401e0120300c510080c4c60003a4058042c1c50041c600e40341d5003100041414900150754510960b03c00005034402040d400035044900154078040020610300d0300f84099181d000417102640c3c1551500469660345582075450032254030070040803c0404140b40c0200404111914141e5455481e000900b040c0381e001020000e0100680102003048039002c02c0c4158000e0740a09800ca0b010310503100102c0d154207140081c021914003020b00b011100400300689800c2043e405d4540c00b00d9002c4004500b800000240c55000140034501204280c0c0d0302a01199000d5040ba001c84e81d2081042c032650106640c40c41d01c0390041c41243c0602d03000f07041d06264801c52142215a08920680c5540c2661503a03141c020007500200e44030300003a4900100880810350006203c01664414800440d9005092f002c0c003081c040b0141581041c0300c0c80703800b405440844c8401600a210840c82c01c1401e2aa811070402840c03030301c1903c040d4100c41e00480102d0300d0103e541040c0c041d107540030641400001e44040392a078 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 457568956 1250 457567706 457567711
    0xf15041205060a1d07030623041b0b0c0307030e012007090f0e06011701110d020405010f0e0f0f0303040b0a080411011107030b07140a0e120c0616060f09080d050f 71
    0x1303482d0840310080c80020040d900400c0d401025440406109080f1641040040810354042d1031310340744200d41c14541403441c9c9034807002c0d11200300703901e003052003a1008503928019440b0003018490382e50702403d070991051100a0700c403007003010780c2c200c001c0540000d1030304e50200340507801c001410080070313001003841030041641426600e4024016a844c00300004845160000c44001039500d81403003000d2601c0000141240e401403110050f81c039882d180000d4240c2c0d580c0c000c8141032290000c6041e4031a03a4120400c03641500c1078400307105010001000900b10b2003242c11404022002140d44541c03140c0c004100d910652042c00c001a0713442110006450441c0b10b0301c802041030340140d40030b1002038000c02190740c20108034100070b080641403a82c40c5145400803102e04001071000d4441c44120303c1c00f160002880100c1e040580f42c1200b03030001040f02c621810001d080400a40c0110404020305980b2074075016950805c100410080e0346018580c50f40403441c4c402e42103081201162401002034520350 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 457570206 1250 457568956 457569011
    0x70f03031b05041d0901231608071e140406051b0601030506011a190e030616051b0703020910051503250201090b090f19020f15041205060a 61
    0x1004040480021004000e004007502a25522103200402da062103c02101855445000c004028600b140a011744423040c50100340804c980c41d000d100d010344e00250082a14441001e0198682200d81e200355040b155031a1205800b20002a00242d1706921001400710145c00e0800d1004c00d1410140301592410b0a010242c60350b000000100840314503441e900c1c10f821080c42060b8204469149030f4a884d82004007044003048131011140c0191a00b441620342c031440400c52503001098186009007107015950b15502111010520045004810031082d07004560082440c8254901496440b50024461145034050715401802c0d81414862034107072445002c000310101c0a160b503400020f021001048441001d6568443da5403011403086a080b9100740c45107002041002c40e0801c0041ca45000c0102c0402004082e01e40c000069071802d000c00c4c001403048840300c01200009030100e040388203aa004080700c5400d0100b03281081f5000c20081d11560001201308540c00030a2803000c405504180c222 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 457571456 1250 457570206 457570229
    0x906030e03090f1c050109051c0302191b060608010c020c0904030c030c020a050603090c01080a060303050319020f040305160501030c1b05030d090c030b011208040603020f070f03031b0504 82
    0x405901300440f9903801e1408280c04540c000c01940c49040c216030304603500740c3e0150013551203014411011000061041128601107203410b18900c5960700031031490302c0d108108409001c0301d1461102124a20100d160070100c1004280d60340c044860090600d20b4401025005030281c0e445d15190582080e84966050345881c170716000150f90844822440e00f07070407039000b103921001040e0b90304c40401542c425100280100350702e4000c9400913204400003000e2040131030910703d0900010b90b2007401d4a41156085040b075030101c48001d801c0000c0d01075081855040d40000c40c0000030b00c0300002c0c01c1410b0242145c00c0c0c50210b52244c00440907516040488400f01e00140c821022081c00d00c01d900c56160b0048060b00d0030310584820030002d82d0603601050360100000e420500c1030040c05003d2900408800c801132101002d15a41c852032030143c0c1c400c075002c1c59408030b804008034045034200c400599200c2d1174501e48281500e0068004c001e20078943c483c071140c0c4482400c4481c0100d048409450812404 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 457572706 1250 457571456 457571479
    0xd0305040614070b0c13050406080c0607050733021c0f0207030503160c0909020108071b02090a0515040605030309040b0315010e07080f0f011a0c0a030906030e0309 72
    0x9072a95240400a9620000100b110201040c4e41e41409070049410fa15503a0381c0e582c07409a60075601c619504030030f105518000382007280c1c0e500015581242a0140c602c00d45407800c5003400f03400d0030001c0d4814400c150310800d003080d0242e8900a460984050f044000080c0780103100102c1c1d51704081d0b0443d100bd0380c0383c05000f2520500a1400b1400d0140c0c0e4812140a2a02c1c5c0d40c61a0850b00401040300200303044504610030000c3c40c1808801502d000141000b1500180d000280342c2c0078050100320500c100310642e00e0810949903d010051034000d0308004e0941818203120004250458090310100120380e80c1f50b0b1a480c00707014610460300014011030400040d502004002d0158a0f2460340c5071244400603030402d860761560900074410807204150724902000d0207031034190020f2000210700c0c0c81c44200011a4a100401810344111000c1e812072a07003818400c02042c440d0301c00d620f880344070b13a41c00c400c01c142e40b020241f03003a9051a0f03418020941c02d00c440311340c2c2e805500f01c41d030740c8410000c40 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 457573956 1250 457572706 457572719
    0x90613031d19060e01020f1b060313050607051b06070c02060d1503050c01030b1504120303060308120115090e0a0c021e03030703110c0d030e0124140d030504 69
    0x10781608504004000e01e4a0507105031505803410a250700901c0420f84a038421900b940c0c06000394a00340117480042c250000d1095084034103502e208040b5442030101001040c940065489415801e81e030090440d10b90b41808580038001760490b000c210404c3d00c080c3d040c003c2e0080301180041c0654601d4035100040c61646e03003000b209801039881501950b03600c0d401c100d8032842024203040114001c0b07001e064141401c03800181911410807032940104141c86c075038035007a19210100e404170740441c031b460070850342c951a04401511640d4000f42c02e012000c00d603550700d4181101801e0403030701c80c03003a1f1250016002e8420340c0d82c0051031040084084141001035070b1001550400c81c0101c1d1144150b411300081c0c0801203c00c0e00000710800c0e40c0d0303840172003080310441e014401c40c04899030300c40505060001d00c3d0b1401d50341d19051203102c002c1607103c1a02d101c0c1c0c88000d410590031029000c091482c600103046403243c440440d8031504a004210400c1e400b1782c0d00f03105072544102c40c0c06940b4140b40904210 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 457575206 1250 457573956 457573997
    0x50a2310081501020f011a040624050703030f0c1d0103050702030a0c0f020d08040612020304080d1e05090307061a010203190c0b07090e090115140a050310020309061303 74
    0x502141540074800c8100080d060a1203960840341f501c541104102100400344070441e030180c1c101500d040c601001c664020000c13050403403030b140324614002d42e9400861400310040c142c4020202c01d004c0c18680709200e02ca4100907400d2040a0305020b440c00c802900004505444090f103000b400f50b0820841105a113120721050340c80b40d4000c00e211140c8052a5011520000718498251000f140100f418030085500c018903220012040c41c0079400c504181c0c5a265140c0301e00c1510407045513940c00c40901d41d402028402d8103c03030340408108924a0f0204506490768040031080343d0b00b500d40504800c540070003001c1214050810307401542814540e054102e1640b42c2507441c40c05000d0402e41d06800240301c100440d10a2120342d071680f0005141880915100c0c00190040c1c040364107184e201c6108504c0951a03008540b480d1091494107808480407070503140c81d542260f50140a0700550141d94041038008501500d1003004071070b815506e0744082495261161401000102c0601c03d4030050740340380 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 457576456 1250 457575206 457575241
    0x1a2409060112200c010518060402010207090903020c0d2001090308030f0907030618060b030c030a080f04051804030219050303040206030612010203040b09060106020d09120507050a231008 82
    0x705840711100d150f40c4002c40240d048a03103112001c1e13454804000800f208038100c0595201120020315490130250b001035240e411601862000039603035240c845c14140700b004040b12031103000c0c112040c48001400c1401e582c030030f042c041822620721294025160f51042407240304984d041315119085440d40b200c00c0e0142400501143d8140c0b16048020000c64124491a002c10409480e50000c07050180341400a903801e0891035882a003140c0201207040d200401c4c02828607901c0242d9640da42c241c04005242402981c01141d00041d2a4040f01942070f15160030f2405070740071360226211a1104800400c0e1080d4601c0024081d81062020800605140010355041040184440c0b80c8068020200d82241c00440d400d0710f07c1030365102801445a0207015103409001c4610281000003030741480a00140c0d910710a041031801c240310b440d014400c0520a000241000912030510640d03a22180d002d4944203580e50900e0541620a1f48a64500000c0040880219407244003030b9a0f18070a040304012240e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 457577706 1250 457576456 457576481
    0x60503130606030c0b07050106060503090a14070f080105250203070b060a0e16030c0e0f0d0206041505030109060807053f0d0224131a2409060112 64
    0x20740b070780031001600303407500c80c800391400d0071845899440743d0800702d0944a095111200740a001c005002da40d20000c41c840a005030446440c210468050801500e03005007584440c0c98451035400100f4500019000f460240d03031022500d08809020f0310700d07000740800100c24800943c1c010000d2100044482d44000d034040001050701058694490a151449104490b42d0402e110f2520311682e000d134041c03041a2124441d0300e4130074840081c1c000801d4411a007503048610400803643d40ca4119900e00701102e01400c10060401070102508001404a030000e000324039145042c9000840c080c480010558200c8200030700f0050641501c104c1d90400c1005040004110f000801d100f0954140c2e540302821054518001091840000040242403402c026400080000600484417045280c00c036a10340008400d00002c501180600d082e060480c24815100b43e2031502c0303010003414004540320065022010150f040300c001c0e0030f000b0001841d400b11582404a601d40c15450714400b801e038070801c01c5804 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 457578956 1250 457577706 457577711
    0x12030f05040810140915180a02040c03270206190309020d080a0e0904080406050a11060108152d060a0302090c04031e030e040510120f020909070605031306 68
    0x44610209003040c24040060600548540b136085003800b0300010558000700341c00c09011840101060419186005004210700010f10460400c000200303011f4402c81d943d0040081240a01c6002c001c2c02902c11040c20103a4101580c450030700c00f160305640c1d04200c2e903000b010701d403400d42840e9140d0381010102c00301c1001c040d41ca07022280180c842046d0f080760940a0032180740c50f408448002005c0c269120340da00d002d202c544040c880081c810030142c409451190500d103440c0d0000d200e00b115910888030211140b84105070001600e52004110b030443c0c0d403990b078076910250340c440400322140505000303400404045140444458400380c0e09161b0040802800d520000d5620380004681c80c50648442130300c203c1c0000c041082140000c40f44448502003415a42e40320241d8501416110103041c4007030149403034a00090000c50020702071000740204407440c0e002100715041050b8064040e00f8101c0c050350414000c14450032002805a0460310555036951550b51240c5084042030b41d0307202c0c101c03038054 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 457580206 1250 457578956 457578959
    0x521072106090c0504050a0b22181409030a0c0201050d0e0601050f010314040b07050904020403030302071703060d080f04031a070201060b0f03180f060a0b0102010605040612030f0504 80
    0x40100e0898402110080100300300381001581003c07102016211001e100c42000700b0049a2500c840c0d0b001107030641c40907507480b070b401104402c82c0b00642001c0c1039a0503495110100d50100340301c0c1c210f140100c031407100b0007281010340c142c00c1600c40c00307443c40015940103010b800304091143c520503406510616286052580b01c103c010191110211425029000307080181f100e0b0820310700d5608040303024a400d014040d4140c40003000d0101c0540043c114035041c80000d074010340a41c00315807090714007800c11542c1d26620b05000b00290000f0a00316040010000500c0c0703402040c20660340168802230511075000ea1a0361031403401d9000b41c4c041c0310990310030300001004c240001c03e40c441c1c05280d1901d51101d40b074901f6000782102c096400c946000c450a000b0b030010301c4c22500c01d0726805035901c0005480c1c01e5030b03600d280d0b01d0181a00d0440c0741a1081400304450f410880d003204480c06030a8000380b000703980710300800c400e444490188625512501d6103182c0403a2140300641002c0395a8205a0301d0305 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 457581456 1250 457580206 457580237
    0xb0105031209100215070207170a080a0f09080709051e240301180b180d020d0f1e050d2018011b26030601020c060a050f1803010c052107 60
    0x1d940c03c803038070302c0540c011500402103000b06e62040c1c003c20b030214000e03204001603503403901308900491007813008009840030380b5063701e401221088040c100c10b804540007190b036000c1e02c40140c40300b1910740041c0b00b03200101040070441c4484e024061600310509466a100c02a030540c002909120480d926640311100c4600b81c0030518188400203008603403003a81494026181094980020340d00d032240d0b07010388004a545070303010598915240191a009070b9400744c514084944207410b0b0310740d840c4034110b081d498031103640000050400c060f400300180410400100b900841d8040e2031828103450404008114035410114120007200700141440341003d0309000d2018240c02c03004404585001106d002070380340c80405440c15100100340103042d0b00e103107840c1d00002e48071881d2442180c043c04010450102c3d10340208240c900003000c071a400c03a22a49000070000401c0d800c140b9041c06546440000120144180c080390304081c181c140c6040002c11202c03592010718001480f02080080107560b11401 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 457582706 1250 457581456 457581493
    0x204090606060e0303191d03030a0216051905061e070305040302040f060311220c021b100512061903030e01020c0a06020a14030d0c05070b01050312091002 68
    0x2814024030380081c04034204080500020014426284654000d01c01c1035080c3c1801495900c2e608024905082281c0d07002d4120f8181156104807a54540004a00b821354140e0018400c030b150300180d10420305059845050040c4560b0708115005c032048810710038070141c00c041c001890b5811003802c02030182030b51109115115000302c00118005038000a042003540f919000700d0020b070000c40000c00c003c52030355644030017024115200da0b025070b0120f0502c0c2005910b001e510403000b501c900342448840b0090300e0080d00c8c6c02c0b41c0c0004081070b02602c00c11508a0a150107010a0403007151161441c002800c0b1a82c10204001400a036009101c18084046800c1c211119401544240c8448401040d40400a42004205000c04e1b02404004034100101980003c1d81d40300c158009505034007052440003068291320440d003250281e10b041810413042c899100c0c000f440380c28050034901a05988032030400d5120a22641e103900c0b02c5400348a545860b180681900000540c81e004492150032241c0740c1511 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 457583956 1250 457582706 457582721
    0xc0d09060215190c1106011d04060902041104080a020114030c04120f080a03062405090f0303040801090b060111010b0907030209010c0f1b05010311031f030b090703230709050606070204 81
    0xe00c000081d4060707402c041286c103000d04550103404045004c000c00b010845040200301034003a80d01c40000310199203c0e60b1290040d680045070346136446440d070074080e03034031001000101d00003102601200700620100c0240c074000d01b240086146400e1400304099607510a604080d92001c822842c824000b80d401c0c8002c100c1c0c03010a80700400d01502c0c04034100140e40780c2c40d4121503483c0c95031440000c1660b1020448030205003c442c080500d0b040000424903500480c1c000c205031b5071a00400b1014804100c6050f403162303500f646d030350604c201c41500c2282610118500340750001c100c00046041540a60050614110306150244900000c0d4480c0a0741b40038411040c0c4083c1c04111440b82d04c518006e10001c0505020308080c0407039501810010080c0c40b0040c1001030042220f103108640e4001d91241d10011a08804008282e0401242d203e4a500c0d15210460724602da0202d501510703201c82056801c41240800501030441c981511030018180c001d00c180d6010710108414401640ca0340316401 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 457585206 1250 457583956 457583981
    0x309070519090212070906050a0804080f040305030d09110109061b32010c03140a0207080c06040b0a06170309100905120c0906011803061812050c0d0906021519 70
    0x21140c10010009000246d0b0794100c107081140410642c401e09411180540d04075500c0041550b4404010b83c0b14070b03450040c3c1d0801401ca0000007074414040700185c000c14040d82c007804040b020024081c1c0155074211740c0b4420400416101c400d020801c0340c1a90681d0061400b8081c103891924113a2800100c0a50312514540400380300741c14008900005d1040e412003c900341020050002c0f02c0c1c0d440880084000c1010f048690009000020004550240d500c030a19070401ca540c0d074203161504084000d4100c4658138070a20f08080040e4a018002048400300250400741d441c0c00c1c403120500c0701c11994810b0041c14466002d1000078035443e8448000300025240001e8030ba41c0c40003804220744120f0190807141084840c2d480354556900c5413004008417a4010000180000356507800f1007c1145214050080a540c2c01002c400c0f82d0000001c0220b4440b03002a03c549642c100d0064440c200179000303e1006174040c00203486507108580505401408103a502049241d604140c5000e841203018101c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 457586456 1250 457585206 457585237
    0x2309130b07080903041a0f04180e0106152d09081509061602150106050306270c180d050a05060901020708121f0305010b120303090705190902 62
    0x144280400340010540051091400c80014100465015640c0c001c41c05400040b6100c1006030f013032441c45104517204141156007007622669509110011410f514001001a60034082d070381085c42018403d2100b40e404020b1102c200a0382d00200710b4460b032048000801031111003c4100390b02c686001410354507080da07962a45da89003004040d50800d400003441405140d9401d0911800700d00110705540d02c0329902c1905803054000d908128603091103c02000c0140428000200d00d040c1e1080045120380019145003c02c0401050b510a000d12064044001040f040001c5041d40c1d541200a0a04954080b440c418031101500000d8091020101c2162030b036001c0110042044414002280c0c403140e224021410901a41c544403c648680c0786000404002c0c440043c0d1200505110700141518800c081d614a5880e031034007600070700100040511071002c0b0300074000c0d01400001102c0c0304032503503009002450b00d040144980442c030518815204807240f82e011480c84403510243c5540c09640c440e4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 457587706 1250 457586456 457586491
    0x105090601050f09040506060108130b0903130b0702150d0b0913023a06020c1e010e1b0d03020f030c030a081b0a211d01061706012309 59
    0x401400e8040c1030000f5008002030380c1088045140860066031250017801e0588c020741e605252280c80140d10740009050910755414010500e40000c094020000c104100c0000280c80b1841550701d0b000300f4500079030200c045c01c3c40002c510f02a0000d400f42d0000c100c0701040b100c820f0f200103045200100d64048032180c60300c07620300643c03600b40b00102d0700080444208039000f41d1940c0d120365020020700703004820310000481e002003100582c1150b074401c41c00f400703031401c0340394041040d075142603a11214980d541c00c10840501042010480b100c081640300402408501740d0b034240700c01210103c03c150207602810000c04251101403009211407001c050107940c1c1c0300b0402c1c030090700c417110240ca080c038400f01025419024207038180072200011214109040340c5036028481c020300103184c5400802d401d08051100c04200490b1604071701814100d03000f4030000d40c83d040808544850258080215800f140041109005403000c450000d03441d078802d050b1540c1c180b000300e020080c00303940840c0b080701c3c0c5581 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 457588956 1250 457587706 457587709
    0x10503220212151b0f03010909020f0d0f05010f0b030c2412010f0e131506030212150a0504020a0308030c120c03070201140405030301060e0a120302031b0325080c010509060105 77
    0x484c4149607601c0740081c100002e002c01c40400340414020000c00b143d1300c0d190502507684130344100c134520368000c0c000900c810707442c80e1440901c1900c1c0300485141d801d00c841c0006070302c0b20b8011514403c0c0b0180051118124107401c00007030403a500d2442140b040c050f20610700c60180c800062104441c54044460b080d450024900480c004a07442802c0c1420a0070500c0a0f0119028600319826084513940040c09070086c20301008000d503500095100c0b500b4500f54440c64008603041d81c1c141c130340b08444c0c28185e4401c0819001e0f240120b4009510912181c0103000040b5010003458210300b0001215050000e05c43d12415030540a44e444a4500e03008401c105550380d09004100091108250b001c02c1030400d41d982c284c3e203000c10b010300380510125030703544041502c9030341d0f51200400090320310304a00d070705a08000e902d03a480542c492417420440d42288507180300001c202c2c0c3c01d016404c40507901d4002420010414500144011201c2c0801000301345000c8a00740642030054120301d004e00a42d515000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 457590206 1250 457588956 457588981
    0x7030906031503060203060f1e2d04020304170d0f0c020d0c0b0606121503010e0718021b010e060702010510050f0f010302090d0302011a01050322021215 67
    0x80c4140101030604421841c681d00e82428582204d0f8080d5003d030b01c82c0c58040c0012140000e80000740d0300006c040c1e0035410a103207108642d4142c1003040e18070704211540f020030310402c820624440e10701214010303603500490529034001d503406070090a44207204c1140161b1162036500c50102204a00d4481c4585071020003507215005000820b40000e007c40c1c1c0c1e01c21409001d940700d074400542103500250001d811511810101c1c2d16848408940c0c1c021440c251030321507148511a46014001e40c60802d0380700061100041c42c0051b103010340d0100300001301762100710019510058a040b10441c50280042450900740940c44071924001c000d400d580c034240200030b0031510020100c0c0345144070040700b044a0b869038000e81d0603d210940307884034048000e0f001a03010b8425003a5990308890590104001c0c1359040d4050f018440740030280e00e016019450044454dc0010342d042286007018070026004041800d8040d4130b401c3c400f400094010342c8410b071881c24202c4004642e147d00182d04104400800c01c0c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 457591456 1250 457590206 457590209
    0x60103050a140a0911130509010605030a0816050114040b0f0f0114010e0301060f0305161d0604180803010603150f06080105090c120a091e02090720070b070309 70
    0x4000c11050100340452080070001500b50a00d5682d10404d8400f4004c844c4400d0f40543c001400248074420310349400e400038641151841043d519011011030076242c0825044203030b80e00302c0c4909040100304101c01100504840e402c641c1f965a4131003a140c0c06003c888450700c1507025510090a80c03030116075091010390300a09000408100c1c40041c09401001e0119085424003031034a017034030f02140760100380105601e030007410b91071740509800000c200b80000c1c5807001080c440d40b00403440e55a1003050308840f1030508500d070301d0008400001c00314202580880c20f83c1d9a12803060f1110000340d00e601415a000380c0221002036200c3c0340020510805c421504010030700391440e0369040d490580c0041c00440c1c1801620711689400010408143d1900d040d44d804d18011403030030a1a09000a0481c0144a070310002c903412100d011b500226032820018503885680c0160200030203035290001202c0e080c0c000703000c07607040e00c0c583e1481c2c003c20700c1c0402c91036001d0181103009695844182c28098500b1a0700d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 457592706 1250 457591456 457591471
    0x7031b0515041e0510092f130507080105040b0d02040f06141f0807020a1b0f09050609040803090a0c080c030601150905130f0c020115090c170a0b100806010305 70
    0x40f0b0710003200094001a104004d00c0c001100002c12001c14078089500881c2c0406e480c10502d500d6003095101c0360303040c26a02024100700c3e003459190962500840907a141100c01001090070301004001504144d00001d4182400609100c43c9181a60001702200c20200040d203180c0d594250030f12814802100c0055071640446005802842d010040440501003a14403000c11041c5004074101c103008000e40740c4601d5100c5041c009950314610003044d405850301c59010554407071040000c15084038819280202c02c06420b18031155030344c0d20f4095a41d480a000b208030f074803c142041c0c010070b110344800f0003e485441e000d0f14000700d9802c01c01d4074011040e00040f104038100c0806600c6a0340182e10b00e4121001070f00c0329191001c40602107002483e20031880390041e030038426264089641948035020300744c500e0f5001a203154403485d4030821a09901a110041448070820324001c00e070707911616500011440c40400e00441d134401040080102c210300c10081a2810103120b402c0d83c045c040c46510206 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 457593956 1250 457592706 457592753
    0x1104060506071209030206030c0a030506150a0c0305221403190605060d060219030c0201020c0a031809060f03050f0604021f030e03041e0902040b07031b051504 70
    0x800c00080e0491090000c001c100caa41a54032000050050001c0002142c00502d000c0d01c91400032080da905034444024100000d06e8000020302c1c620300761400310417031701c511826a804c10140600946030916404c00c280c0500005009040c2e1303103004044205044203031509540341061614a498101b95050124107109403c800301c040411940c442100700c0040d045070010545032a40d20200b0354408039100b010b4001400098a403015905260b07107529404102ea03401c1185220740c0364203e08034028075920b085160030805501c0007180c40384461110070600039101a12003580c0e01070110844141d5031112403804c00b81c4000b0028010140800590314400b940580740310702d019070008140310702400c02180d400701081c061584180c03180e484496000d051034101c9546580700d88400b0100ca040424251044940280c042010205402030740e080702c0660203170301d0400c1409e580a80e180030035080902d110f03400405061002c1001004400c01c00c0c4159415036240b03080c5410614450344121250341451071 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 457595206 1250 457593956 457593959
    0x6060e120c130c03050a021e030a0f05180c010801030305040b0d06080d03150605120601050d02070209040309050f04020c0607110f0a081c0209030a080f1b1501061701051c06020a0309110406 83
    0x540003042c0d81e08501848002350350320780d2405400402040040e41c400f464610345400c010704544040801100100d10300101d54100c1d4103034004403680d81d024080200015000d100803c01880002c0c098125a034590401041c00354031042c0c01032610415103034540001e0f44a1000c018411700783ea483c030000e000249001440c0a0782415203042d220030140040d0304003c0002401c0710750404a5041c0d492040d4000c00c075081c1c034101420002e06005a40c01441c0c81000414155566880c0c5407003101c908950020280c00c1c00c1ea42c0e0304040e264105d4007141140c80703005035603c400030602d00740400e032582441603982d1a2074214040781c81a00c2043d0601c2d001b21079104101a400390740c0d00003507003100168030003c400c0e030b02d005d140d25017101805003840b40400c454448130031414a203004551400c484040c10810b02c0c46a0b030f00c040c11070760403ca103084100310025503001170049044c01e412138030850468009131038082c01d0f070741c0d80c0508980c014044100000e42d135138003940c20000c00369200e040030300c0101c0703091000f030713 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 457596456 1250 457595206 457595227
    0x9180903340f0206091f02010c02010e0a0204150305060c0a0201050601030b03061302060d06090e06060402120103150221060f120d0e04090804030506040c060306060e120c130c03050a02 81
    0x200c807050800b50040b292025400c0c115940e920884110000c0030701015504403a140da1100c0c11200000c051002d9400c0c140c031126020720510803030710000e05a40050040002c00e4003480000d00c7e9455845056611011000c40851020840c090044203450083c6550b0201c0b01002801c484002d041d2a04041c03c000501405641c0028000e4100c0d0100d441090f405034184000380c110320071034040c44203441c1001000602000329501400301120302d01e05440c8155038a900b00800c9100c3c0b0462540340b440920014408100e2040d12001684944203005280810520041c2100c140302407111000040e0b540c104041828101c1942c84051805e458441c80b0303031222800a0386030304c06988448200800080c85101310b5560b6003100d00c04d1034100e40e425581e80c1c0c4a0800a4841008550a55801070b4240c00082e01ca8440e200750011107446030386089880644208101d41c5101c0c0c5c1c1e82e100780910035108159010f55581341e0408a00120384800903440016a00180903a4401080810103603c14041c4030b028 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 457597706 1250 457596456 457596547
    0x7020a0b03132604060e030c041a030114090a030f0203090301050a090510060e150303090a0905100e13080a0e0a0608070215010b04061112130e0c03041709180903 71
    0x41c1d4480341405106c101902c00860320309400e41d02c00e150b0040c10860020b11080d0700740c41c11b2081d401e05030b0081c00f04800c407401e25480001c06650400740c503800841f028010a101e456207404079a12803060343e10b00a107640020342521710544461001ca99030306a8401040010000348401c50450f283c24043c140c03400d040750044c207200418040000c282c40030940010356042c0112848a0001000d180f504d81d110720b1002d0007031504860303a00100404140100b884100c894106100d644c2203400d00e040c0000310b40e1381c400300303400c005135610a101c1c0b2081e04044980e546961480a8a0659a030100519000000a241034180d0405c65200e00c2e1080c0148141d072594021101641c2d40e81c01c4c4441d0441507815190f140c502c1e0301150a210a0010445c107440711402c410010444020700c02d04200d40d15600301c24920b52000759002070000c407159940c0c50040340f03088068001c0c003400400c21001070045801c4525050403c46000d502da400001c0d581900381c826108242c41c10200c10030710039a51445681d420740 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 457598956 1250 457597706 457597709
    0xd11010818010608010617030c0a030c060b031009050607031401261002070210030606020c12013312120309050102040911070c080c0f0607020a0b03132604 68
    0x100006000001e0149401d68180c0707400403441d100800c1010754802101c1e0081000d0701440305205400b40b54810751b501300100343c1d21b0300980c501c00347c201924280c0e800c1d2804840201300715121500c0c3c1125480c540d034280310070a40314450302070100b0350421915115043c640d00070b00d01c0007494645005002d515000c9400c0c06d0540703021035602d0380c6003a6645440c03500006040345100c11442a0300c400da0a00c12a82c000c1c000b02d0707100b40c03440000308a4005041c2c0980300b040c040c400041e40108000c00b03261034440301840104034400c00000d0203d00e00c80c51407509442141d00b50100c000308001d59600107102c192007100130220a030604840044550b904888403c09100b1503040544950708581408002c0d41240c00510000400700100101e004809400e90416030060f14101701d10305c0000351201004c1100e0034802c01c02055845840c5410040214580143c80c0a1340c1007041d9410106440014400a40c0914004404c03132109242c00d00e05070725600e8002d00185484201d00040304800001801581d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 457600206 1250 457598956 457598959
    0xd0803100608010f09180803041208010f03120c030c1718060310030201110f0a0b1806060603010909080717091002010605010c08091915020c0a0f060c0507120602030609060d11 77
    0x350b846c40c01140d518800b15025030242c28488008288401c10040c520500f90211154603400c02d940e0341e90003d601c1c0c2442074030024103420000703441345580303e1103080503840491081c200440a51005c0e00c406409a0425118039480f0741c0004204405003003592a4020090003184c82d0352a5140c0340381d8040b003489051100a044c0520314001c1d0300014010711800680b000c0c1036085507004403182c01c00300042201034034400d180300301685000300781d40da0110f0614172494014003018070356440c1c44226801000352030130540b90301e903040c0700072030001d9506003608401003013060311940c94141038001c10952141d03e40c1c0490039680340c000108031690300140c0796542c040e08200459101c421540202c1c81a80e140c01c0c0c050b50750b2140d07803008107400908503221004032a9503821100320702800e00a00544401c14000c840c4081c2001c0030800103103102d03662240c0c010740300300c1c01e07246415950020200c4410b02c01c20101c43c4103030080308000d01800c115103907941c0b00c03500301d81c0d41000580320b458103200300c005c1d00f0846 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 457601456 1250 457600206 457600211
    0xe0304052e02010f051f030201080a0e060a0207050c2211040b07030f0e0f1c060e0303070207080d08040209040f081e071109060114030a06050d0803100608010f09 71
    0x5040501a41007204805000411031528024140d07400900a15140d04080383d25440d01010824045050b4903820b6580d002d40300404400c4d007180c005442c055001809071014503141c485020100d03406101d0b09005103035410026881348114606a802c0c803102c442ca0a00404940c88844007104000d800b8085100c003000d03002030303018107444910149114640001c0b00f03840380080c48204041d4000e09150140c6001d90b1102145a015002c2004015421060315440b0400a140d0380100f0903400c400840c45100b0389000944008a145030390850b00b08851480c0960414070040011103428844600e070b0500a1500e1105894958005a00c021019102601c003000103411076080181c103000b242c03400032800030007079070f2031003a003c04208541c08603008a40800c07048e041c189940c20685d11182c01020140c41e0400c0d41e00c010b03000580c490704000d001040b03c58072080005600e4580180c0142d15170301420341150303a440c10690347c0b81c2000f03c540c85503082143c144010007114074040402005e44e40d000c20302 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 457602706 1250 457601456 457601479
    0x24070e030109020a0b0d110c030417010b0a0303120e0c06190216121e020d020d260703020c01020601080d18030803090601081239060907050f040e030405 67
    0x100c0c1c010807850070001e40000c9242c001182d03d04100b0003401240300d0300c0c04148604000e51240989178020300403aa001a0b00034842071115002002d0301a140c00d0340480005030132100c500004008150991050700480e144907a80b040c150841c0c000d004090402c44002d00c2d40c20708a1010900c20b1243d41c0c490310100358044ca58241103442130080310005181c24845a030400c2e100c14001d01c00c503035100e1003140c0310703402d208644c00a203822128ae1220107400500f40703100c0c0484d58003880b400341c0c4404030840310000300790a1200085130081405030300700a0f00e40416190101850013a16060700f60603141c2c191340c042001040843c0700081c8502e940743d41454007041046409406c030681e00715a800040c0690303000710400002e144000340c09812140c84604996403d0544106042b1a115960950045407808002c0b41c0414400f0403400250f0400a07000c2d2801240903a500350070003a0a0b60190700c03d030003d02d000c0185243c1044200255030045404020452106004690700d20980c411540100c00380c001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 457603956 1250 457602706 457602709
    0x9010c0f02190b040501030e15010902071a010e190912030f0b031f14040f06021b01180201080705040501051b031309020909011202060306130e030d0e24070e 69
    0x2c0c2040b0200041010b49046403522010019030b04503000d4203001030300c0d01d10013a01c0f25400042004400c19070802d100382d01c0e420721003014065800100b080d20b00100e03a01049020601071040d250007840a50001ea000b0700304411009100f01503001580a12800c1c01c40c488003040703010a00c068076007914180090160080d032005009170600d03204e070780c0d414024101c0d1981e04081d110180180354801c841c0c100304842910451040c2036070152800b40c601820820f101000401c15801004030240101800d00c2000006003504d003596803007006107100d81108041f03407003103580010b5040e42100c01070400e0390800303041c140001c01034090283c070400108500f0b100c55100e450b081c0100c82140b600f1200680c4216120040c05000e5400340352818011700810b400050005405044d07604959130050099280d80c64990030440c400c4094800c41c0c0d442656500421a1320404100804c0214503030100421604c0b00a040c01d4102040400c0c6545409801010b050303800b928a0303d0303180d01102905100c80c1c090920f80 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 457605206 1250 457603956 457603969
    0x271505100e0a0c181e17030d090302150a0905010b01091d130b071106010504020403110f040609021605010608012f07080a12180c05010c0206070c0603020301030201020f0309010c0f02 80
    0x1990441d0f10000042c0442d110040d034140c841015800c85640395041e07030342c2c606544000406d40304050903810900081034403a00b15081301140c54001d1040f201c40d240c5101d07a442440c00265226114103070340b00f501c102005000e00a45441d00001d0908251442c5420801d0344411489020715681c8410a8000f075100da068210b00c4481940040c0140020702c0e2000004e05001e50704800c00d0250710403440001000d1525008132001e0b01d510800c949800b06407201401404881050300a9226850710f0010a039900c05202610f400e030030050078001a0740840c03c1540c21601182c005040d01c1c1d060a202407003013528058155100c2d106280c0310a10765a01030408030660040d06002008840c00140480c1703030b80c0e840601c80304006201101000109401480c000740c81c1c4901e88000d04c50700070010208543c0d805138540c03203491400500584d140481e1941d6094064126401c800701003030780400140250f5074108001903c050f8060b00851400c2038030400a400c402e40340d10014001610384141c04115203070717071 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 457606456 1250 457605206 457605227
    0x7090e120703030507080a0c3c02070f0f0e040f02010512070509120c011e09090e01050417120105090c1c060513110d271505100e0a0c 59
    0x3805941c49503040c2c500240680000e41e003503000908180041054040709115400341164151141d000c0d100085000789410104000d80050600d82c1c0c81840800f1340003032161501e000450780c00360203820700301428507d5195150b00203003102d042056081c0007c107088500c075038115400043c088030a071450301c0122154030030905480c4120001d04103018056070000c0c082c00c0c681c0c004444c8803881c4a12145003903910b000344580c3d640041d81070124845810b00000904070a2040c81c03410010003a2a0240b2009a5078102400c0003140e5542c0100002c1c440381000b8851071070011001c0e41e1500b003100c0c0200c401d030101030107074030b104c4c0307014030b01041450542c41e04441074180f010910000003442c031000c0c44001c22103807007010700464080009603031a501c903210b0080902010a12035081101160115004040c0d521592580d44048004058a4181440c030500c0c1c2c0c0e4030803000d1400314441c1c580303030106440e0041e0119090007003002c018000004034003c925072212040340c00040c240c0f8245411207120717004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 457607706 1250 457606456 457606483
    0x81305060406110d03050403051218070303120c020303041709180115020f01020f160c030606180f14010306092604170d02060103020114070803070504230307090e 71
    0x20001401c603040b640d5180800102d0f415150300d016244400d405440c0d08440c010000f480c20400c0100364003041417215004405d582c59038212440f690140c034540b048d1070700180d000c2083c1c4c4407200b0040c0070074095000700c96058400340d42541020741e00c2480045100c1c4c0c4400f0b0943d0007092244a6881c0d00078601e401859400b02c0d6511941c1d2540e480803100e40c0d444207080140901d0000c000c080105008896890003041280303440d03e4114009502401c0400b001100c4e000f84410f8004049201030141501800d524400048907c1140892200301c582500380d8044c0f00b4101141403516415061000741160b82183c00030031038440a02c0d040c4001c0915042c900d02c464112403401d03000c0d400100203001502e400381407500904940b0715180c3e54514025680c11b0060348a5401400103500c01d400c10848105103a45c0d103820161107a44152050b0412540e0f007000a00110301000812150803410400d038444000c2d040b410300d81540481d4462003d402001501d81d1600c131200b0300c4050130007441f616403c1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 457608956 1250 457607706 457607719
    0x1506012607050406030b0a06051b0a0602030f071d03070b0901031d030301090605010e0609040903110a0b0f0604051b0a050d0207060207020a050604080706030b0604120b061f0c081305 80
    0x41580001d030043d0024010b000009241000c1c00b141424090300e15420790f4099110305040c03042c044100b01c4c1e03441c402030281d036040c0a8810010002001c50000d107000300b604d02d005c80c0c424a80071000410040a12441d0089400d04827500c1e8002d031000710f008402c1d584d0b2811107640c0c1d1400c040042e000742c460450418100c91208550098502c004000b841c142e800c00842801b0403a51400111041085282030715440002000115090301d4683e0100c0f245178400c1c10212020000300c0c0e072960a080d659081582c0301c29107903041080a00c0c1c94881c03a50f01040803034041200c0d040001070707201030348049005150440c100151080c10a40504103540b09000700c20410b540d42d8000b85805006500440c6c4124000d64826002203090301d44042542d042d10340300c4c2d00034481c01e46841c104902820010f4449508004204004101c148400011840060095080320b40d682403030414044149130454040048103070b100191484a5032102c880f40103142c0252020f515480da02215103041d505130350003190b0001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 457610206 1250 457608956 457608961
    0x9140307030c0b150d120801050604050f04050703090c090905062203320405030d140313031205040b1603060f05010e040f0501150e010903021c060b0604170f15060126 73
    0x1b00d00c0142c00e030304541d986d81e000807039a0300d10600115015601603035900004080b00c81c041030a06600c03140e800740d11440c0104d54000c113500c40d0b00d0011400d8100310352003a10789250780300b888070401c10030b070700404410000500c55032420034000405140010080030031038040152000d4503554a841d4900307140040080840210002e00f801e101e80c0540f00d068028043da505404005000d4030041d08110710040d0041e2440d0340303105240c0d400032044c1d0800c800384002d9002550108a2602c90f640c4034620621032205541410708240103024441040c08003010300b400f10905c02e6040000c5c02ca0b003143c070282800140f2540c00000580540500c0d800300e02800c1c82c290000a081140b1170b090708441c00f50340c07520403181d082c01004481040160001a420506103a10f01e00802c842d5100c544d2110f008401c0040d200d6401030000b03203654082d0744800e4040750003043c0c0d07000705d12052015243c03601c001d00040228101ca1802030710000d40017007515060020300b4800300c26801021b0010041480c044010b914a403 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 457611456 1250 457610206 457610213
    0x90a0c030b09090c15070210050c010906020f0409200d090201121b08010608011d060301020904060306020301182304020a1505041a0a0801031e05010f09140307030c0b150d 75
    0x1c410b161400e510510302001d8109400f105c010803100c001d90050120400d00c10504020f4071a580010010400c6658408a0f04003040c4644003030304400380311405507a40c840c40d003010390742034450740401f000c201504120480031140031442201c1810500403c089044040c500050703420142211440410b1824150a0184400d403082078010068680e15402d101e0390301c880303045070f807000c090207004443d4071590715801c046183e4203202c6921100040000d441d1010300b0000c6001e84d0075a238001c850660b008401480307410501c0d0060100b2030190b0400708600201c01c000e5a01c894240846542c03440150303c04102907441e10ac060740c0c003501c003a807241c20746603d450030000c05640c0240320301078407440c06000021110711543c08a4178002240d40d1032030f2003a4215120181555204071210781030740040380490000039428065041150002880040c0d950010b04000041c0b001c8003003102c0c0e444d0010411000080d8102e520340c1400f039041701c00ca090594503024100407010b034940714180e11122148500c5c040 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 457612706 1250 457611456 457611463
    0x3141927050a17030415112101090b0402070f06020d06030203031306030506060702011e031b0915030902240f1206010909051315020f0708070507080606090a0c030b0909 74
    0x62034450003d440644402814107071003030005a50003801c0c1050300b005d902c0394500d660800c584158010b1426441c003566048455548064100d900d280d440850b001040a007455100d0025a04002e50342940741c04040c0e69019481c1c04502ca0041200c1d030f01041c0c00d80300032480d6009801465020381141c0e920b1234031003410070318990648120300c00203044c8800610642085000d8511070707a07068503600e400f00c90102c0ca041c4e009443c000e000c1c04055542425008600451a020b00100c1c4103450740c01072641401105006240c440b13000406260411110400580750700701001800e580c451540c40c025121400541d600e0702c505c201c40c451600c230104161042c40d0100304114010842602d4041400f80d6450445c42a41c402f211a0090000d05683c4040450b516110351518264048401480c002d400c400c600d52942101006460b010404030b040c0b810804100700803009480da0100400c254902200003561384003000303101503003a688030791445c0c03111400794009039802d01d80202151078a10341070003207a80c1c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 457613956 1250 457612706 457612723
    0x1005030f0318010c170d090204050a140a0921020106030512180a03030e151303030903021005090a05041a0d210e030309120a0c080a030314192705 64
    0xc0c0d48402c4042e00ea070b02c0d80a1910450311a9010700e61220350281480302c404076030098180c0042543d1114006401a6540c0c450700d84116003403000003510030380d1072407102684031006204500183c41e0508030380c00300b03804c07010040700ca6454040032500c0c040ca07441d04a003d0922079000425511403044c40304040707415040580902440da407007041070003040c0c000f001507403546444050b003c11007d418000c10780c00c0c000c030250404c02c440c0001c2843e012203901c5001c2407051550040e40045c0729041c0038001c529003031007140003036403441c5411030414000e44c00107003075200c1511546115940e10034110083c10b42e452120aa40c40e07004052001c00c02c107900381042600003a49031103054200f8038419000060144600022040c0c019009609200780742007404040d07880d01044002501c940580040024440c107181e038040d011450242542d1a2145400350540740c48624804d0445070103030401101c0341500d4407a10a03400f8540001c60b0144112424448044808020729031001080c2684014040d00286012 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 457615206 1250 457613956 457613977
    0x32603150909150c1305180609060904031b15050f160207030314030901110c1014010303080402040515060f0405090a050c0708070c1205010b01021501080a0b1005030f03 74
    0x74801c1e0b50b180d4200791902c9034001c00040d000baa450114070303154460701c0a00828100101030b000d01d1601c030b2000030552070303804901c88080500301042101c1c0381060745406401c0402681c9140300c50810395406082051180a0300d0100320b48610182c0c144603a0806a051056100d01c08004a0800c440200c943d0801240c00c4400d60544045d107030b0040b071000400398110fa8243d0b07502225044007030100280e5500181c10700201c0d41d02c69003c02141c103407850050041080301801000c0008400304888255407054040503500081c10004002081d04600c8060b8020341c1242c0000c0c199881501841c80c9603000c40b1000d8011002143c1c44400c02d80117801030080c0ca8089400c0c000360b81c1c4940790308040ea4007c442464100d4414003d03040055a00c0e0003070207215110781d5940070880c1d143c440017158a2294901556540c6d1501c0c407244031540c06005000c40c444a0600b405141e60410b0b00140d42c030504188018800d40c0420006108089648120005170000606640910b070302c50f002e140d40c1c0d800920214 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 457616456 1250 457615206 457615219
    0x106020c01021507120b060c070b03011a34051603030801080607020a080a050702090a020d1a01050306060702030708030f031603020c100c0345050703260315 69
    0xf0300442e100d458030720310842c40303955003042121007108054058000b002005800480038841c600031842c061091202401c0092801a1250700d48a030070486081150308a1103461703010800b9003a2030104010f52200c40d0858140014240208075524540f01c245007405425400b42440429158056a04c120200d9000c0c0d1341e0312096980f1164101d03110032081d0748410160740300380f05d0807000070506000741a10711402c2c2405c2d8144082500072a450708800c403000e141c86a4001108940c40b04103105e0031100441c4a101103012400ea180040c004e4840501070302e201342030110783d100031542d003001803002a10300d074000e403611100100810848c542007a1004e031295040d4244081c00d80784a80b00341d9410f0300040c0001c0c41510360340c0d5104801006000c818604040d02c5a0045c8c640000c0809100141210741d030a8490446040c1040740003040c1082a2039a40c80103007548001003000001c140b4290380d000307504540e0442c2e005042c1c00e902074544008000c000c0020041100001d078a03200e8001003030003954070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 457617706 1250 457616456 457616473
    0xc23030406021e19050717071503020903210702040207150e0f0a020118091d190305041503020c0a0b151c061a060c0f07060503010b0a111002030106020c0102 69
    0x40c0c3c00002039995041400c4c0c2c404c01c02070707002d200505603408400307003d901944e9000f40c462204118040080742403903050b078450601004003000203d2000070280700d030300d003c6041c030754100002920351034413242c1c04900c003207500d800c1e044201452040301d401a0f0300030821952900c06243c0744003204255005c07600481d19141c00303001c0f550400b040c4210000f168401078000c0c00703a03035401901e825803065032030410381210b0100032900b45020b2003102400901070004400d58041e8008980c0f6148041202c2032014000f60007401c00283c02c08180c1b0b0903100801d0030b01601518101049000380284594101e0354070509200c00140070305002024002c091100d14000000c240005006081190800e40701001400074070f2800454a154000d07120010180e840c0d9903645c5000d400104d5a801c2949c207a906030700520b8038401002d40c10005200103000b80e09020b030440d8504240e27410b90f03000e40c8100f00b00f0305c081045410301c0d070103040c0020034407101d410408644a51319110001d590b810000c4113603003d0b2050001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 457618956 1250 457617706 457617733
    0x40903020133030f050102070b070e150405100e030339030a0f0f14040b0d05060d020102251a030f1e06150c071d10030b06010c2303040602 61
    0x5100203051540d880c0885900d0f5a40b00403043d68034030415a0195800d0000d440003c0e03044003814010742c050b946481c101c0118074204030450035400c00d8040004000c100410458440d40750908404c3d0390303800c0400101c0c5d201c0700031030704611072500b48821140e100450411041c0741003202000b02045c0d40c0b50f0000000203003190030760768440c0112503c0400e544164001169108100900e0710f00d02a14000307400c0701040030215990781041d0400e0050341c0011a00040221045c894030368046000c4132103889034001c0d900041d40318018080000807100140c1248599500d403020000018034282d80c4400000c00c044003080c04e25001902c106010800080101d04104401c0098091030211100c1186858a0300d00820002070100c2d1440300403501e00740f0030180307000003e000c520000e00d0140c12410302109c400203000040a07000702108003107241803405001081d440740e0380390b1744603a0038200540a0110390420056040c18103040c0140400115018040142c1c044085d04c00c44000760201ca07041c8031642d2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 457620206 1250 457618956 457619021
    0x10204060c02090a09050607030b03100504080d051008030c030a0e04140a230f010f051002030d0b04020c0102160303180209060f010e030304080f06010603020a021009110409030201 79
    0x1041100180225041e000545008001a900010264000919084140c1e900c5041a10031560400481d58034600b240c46400c0a114200c007081c4c04450800c0f0130328107680c0e04038040c09a1111140445c0d540c00000d0084030030018020041c080d0f0b4011242c441000c003510580c1d0b5408920110002050701c2171040a03030625000d0507044404c40d281d101142e540342900c460040418201e813064100305200e641c001000314a1b19280200042d41c88000d8030360404600c080100482c1e0701c0a1f018442100c81e0800660f8040140e400e0302c1d44880e40494002c00800018010303008501a050803540b002455842e403152140b148190640300740c4040c4245503500b480141e05007106240603402401c03a500013a0b05c0d1070080191080d080d0b05040407441030200c20042446c0d900180c10400032a03110210b8140508003c10201307006000902d815450300203160f10003902c6104401203040000c0e1500c000310100180510395103203005004c0c10400c02c6a00b6424000d0107800ca40c40c103080d00d21200c9500c0c0e0129070401 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 457621456 1250 457620206 457620209
    0x90705150f0a110304050d0b010512030c0a0b0405150f04030f0f1704020312040b03071d011706030a061a0108010f050303072301060314250b0f07050d0809070602010204 74
    0x200c00c0c0078103021944000741d43d0343d0072042212440d07000402002c1030940d140c00c5001c5000c0c1c0140712140349036040200f4413450602c405481400b50780240b22018002100184000540c0d6105610000c0390b00c4500e400c52070201500780800381c280c243d00c1004405882000c065121701e000380d0b111210101250426105030490100c000000307040310a07280383d13102d56590715913000303480503041720240c443d17442038041140c2003034222860032040041030103131041c2d0201d41240e42095030301c600c20302c0340c0130400040c203803840d0211100080481031002620550b400e00110007074030740000b014420700402ca4200102c07540c541c8041c0740412030301c50020940104060701003060fa07001500071441c0103c00d40391300201c0343d11198070084001500c00d8445020100b8061070b0300851043c03141010070341d0f079100b519003010032448010054500039101c0c6042a44244c00c07071001c49940550305a9240003501094a69120b10807014003180304200c0c00b080c41d1030f4800c0030280700340a207100b83c41100c0c1d240c0004a081c1e2045 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 457622706 1250 457621456 457621477
    0xa05060307141b0102070b1e06090604021603030c090b0408030a200d0804230604080f220602072c060f0909070609080d090b0c1509070515 61
    0x2440080c40302402154140c060b066804072290030090300041c0c00c02d40c00c01400b03a04078281d401080d40e4080100d4241c2035501b00e002c05000c40c1d2030300346e0810101c000b8400102218410452203000c54005d84656048840b4001004450000c81031103003070190151041440d10303030004110380340001d26120140c00366020307619900003442c9040300445003101c1000301c00e03000c012401c01048210142031010810500d1007096038541052618050911410700c1441c1b0f100c019a003805400e401d2000b9001040c96079100e42c5c0601c42ca41c0340c000448601816008a4030552071000032010a0440303c0032009080e001c40301c542d0f00303c039603035a222040100640d420824201110040d01c01c1e54030320f10a0565400d80c0090302501d0007581035402ea0001e42e00010130f850445036034201100a1003119400065a00170780400030080541c803003240d6008025034101d1003079280e4058045030305118403106203c008c4a25140c9580041c0a00340118502d0300e44c40c03140b0130310780b1606003140f2401081c01d0520039540b60b401c5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 457623956 1250 457622706 457622719
    0xa0e0a020703090b030412020105010906032a050d110406080c130b01181410020f0c190b031602010e070302091303090806010b130803030c040611030408030a0f0e0a05 73
    0x121444080003039048503504506000d03640501040c40d4115001561290340107400340c1400c421100b20203401c40e541a080b07100a507090240a0001c1038000c1e10700e1500c203020009801c210182c41c80300d944c01e9400e070742040358040e03101c54a42007032244042c006041c1c4181148e0800005543e441816500c8a05046158000901e541041c030030901c1ea40c0031344483c5170103040c80300190410791400c400441d066003100d80e415942c0ca90320342081c2080c0801d40300f004007500003040000300280c0c03059034a840350303181c55102d500300c000505501c10b600307509a0300920303041c02c82d03540b2814298590408000380120b098015827a100d90440304900014501e01160f0f00a00018025141c01c03000102040c41d1070416803c2c001c1d20140051030700401c01807207000301b40340700045844405920a1450907840c683c0f00403050b80c800d00c00d010b40c3c9038800045800316121030420507404030310a801c01e815402591f100040b41e002c0070495030f902c1d1350003100403e400b10039603486490030200f80042201703c1ca0306024098000c079 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 457625206 1250 457623956 457623961
    0x7020c03012c1612030203071704060201050603161809080403030504051801150323090607140f0a0e0307031b0501080610020a080307020f0f0304050901081c031104050301050709030c050a0e 83
    0x41108070102166000c3d2042c1c1345030010070703150900c0c4078440820080270039400050800206074288103164121108402500f048260b43c100c00300c4a84590165400c0050010201d862200e81c580c42000342d107038800c6119803a6552410003070400c0d00180700d0760703000e20302d80e0380b5411958030325203c014140c030381c001c81402c0c0003114010101d008099203980e80000403100d12425201340c41c14442c07270303108103034241c01444c01d031821100090005103e030a8400103103100348040c10010402070705030340d640c040d28074010071480f50300b100007890042c0e15400904041380c20941d4400700104044000207551080e201ea18468507542c0c02c1c0103000e801c0040c0f80005810801020b40007506d0700c1c0c0115082042c0e07204907840403285c90101c500742264001001559800007408200e281806c1c0d80c458010002900038014a20748100c030031683d0a140b4031501c1c2015911500d070380b40101020140c801818002e0001c0225203000840600301c007909010079a0481200f5600003000d04e0011071107819141c601038054a2078 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 457626456 1250 457625206 457625219
    0x19021207110414101401050a02060f15090a05150105040b12310b06010201230901140a0f0e030322050309090705071a070905060307020c03012c16 64
    0x1501c1c034038103a0b40d0040e1101d81030000c2c02c10a0f0700040c011070301c00701c10803003261501410255019102d154541440b10034445049415004900702c3c0c0e0000403905404519514460a402c4c541401415507900c02062010b00110380c085600243c0318480d0b000b410b4101d83c1083c001520b05000e2441035600380e074020007000412112840a564004084d40d00c07024904a202c46c100c150207003020382081045018640003403d01c41c41c0d01c40690400c0d4280004c0101c007401c8496985c1140e02441c0d48581103000030046442807900754052103000948040380100b13818116121005815210b201c01052404c103100300300d40b0f00000c01264007410708403411a103c92007241281c4062480444280d035503010912886c1900d88070b21002c140b041640d5601d065540059185c07121101404800703a02d0034a420b1010006180c4c5c0083c0590280c542c1110416101d81c0c4400c4c0c00c80c50301000c0c1170099095404e00f05000c42d61511a40d00e080781940742e80f4001501408682150f81d50044520030141988000c1400c0140 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 457627706 1250 457626456 457626473
    0x30c0607031107080708010905060a020f0307081306051e0a050f180a1e02130b090604021b0d020d020f03090a060323012903091002030603150c19021207 67
    0xb03440042941c80055603500028207020326a44000e0259440342e5084040010034410540d00c13071000d110460510882e409000300502000b48490280200c0c1800b091801c1d52600c0081d80d060351015080c0181c2c9050301b9110804807201010804000c402000310b041c176400c030b00030346100d601c00114045441d511071040340108105032000468038021f948500e0003003070001e074080309c100d65140040801143c4d18410300c03140c00d01244410f50000d26201007507070203543d10402d81d5000042240e0150320741810b403500074228888009420328a2080071644d050054002c07680000380403142d0240c800e0512124030458480c4588100d0540c0011708810a106d00d40c080e500c584002a8180c510394000400da00b0802c2440700300381c1000c41c0c0c8025030850115a801c1007510001c1440c407003121141181006442c0035525021110342c00722481d00030000446c030351820041c02052540401c2c2c20030142c2041d1001c01015400f940c0081100c1440c802c00c43c00d124000500c881000780400c105916140311070310fa8024 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 457628956 1250 457627706 457627727
    0x8071706060f0d05090d0f140d0e06070c0b15090105120a052a0a06020a022e08090c0406050114180d030512090115090b0310090804030c05030c060703 66
    0x501620510080c2e40c0c0d016148060b04503074441d03450009039410301043ea1850190f11080780b03420800808a0132142907807020310780746484804020300380c0b507101d00b0b924103010301100c1e000d0a50a1003213004100010f5800904240c595004040c010314a0300d5882a2801d545654505950230a243d01c0c0104480d0900d041c206080046103410795803200c00940c1c85604000300c04400b90319071400307070583c94000c480700003807410052001c07140342e91142d25180000e5101c0240f44400380c0300c0c035000c9560411f110100c9440a203a59000d152914808441c028094414031013030759000002e120701e401100c402c0c10144201c00a0350380507140c80c08c040c03020b40100030b0290f00290b9800395103000e401c028805600c038103031000020f610079115a41c450150110484041c50028a102c51982c1001030b40e03140160702c2d00141c405c0d244c800001040544100300841d140180c1c41110000781031405105c202488101d03405003055a1083d4480301209035184100350362000220855984001c0c08c216160010307000c1c500201 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 457630206 1250 457628956 457628959
    0x80a030c080c0322050612010506090112110703030e12070210020316140114151309020a061806020d02031903091a07030e03031b0702030304030803010308041508071706 74
    0x51402d10907104103400c580000034850f05820300108151010f0b521920140040d04058480a003442c02502c0c80d00c400f803c041c0302e054002c00000a11100030391141b03440405500c1e128105200d0b041c55180014542c0c3c1c000c140c141e00091815a0040a41402081d40c10f052072550320b006060401d1a020010012a020542c03810343c8000c0140360114102610341d01415030041010941481c55803006138203541c204484074003c0042d41c0101300c1c149404145401c1442000c2d12800080c1000c3c2821100900002c00b01031741c45408803200158195010046e0400c401c102501c0c0070400c0d60355135080e41da4104040003500960414081c4215031080707018032040b00909890049a200a0342e00d400000c50306104820514103150030070480000d030903000310708108414000940c40c51502108150305006052034244201c000020300c4010740d981001030f200555004014142d507542c1da45404400c0758024415294141e03900741108c4490b5010344455841054103895000c41c4200c2c50845024980c8000d02c4507 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 457631456 1250 457630206 457630223
    0xc041e020306010c15020a1205090d050c070308041202150c151017160f060e060711090a0c08012304150b1317030f0a080a02190f0e0109080a030c 64
    0x1413004c56400502070054040301680103990300e9100a00410010090303c40420480c200342c284100410001a030032a110068a00240c0f40c40c400d4884c507041504640c0040c0c103c101c007050100d42c505d8000728034031405200303d61094062a05403681130241c0550401000c49800910385941d92080340c01c2035692040c10109100072080d100d8030402c0e040c04400c445d64449078003a4682005109181e6400c1c1d020b0300c0c00110341c55841e4500000200b01115403003243e401800089000010000d03041c095024410004200001b00d15180702010b00421050212400140c140000010303085402d00d4003010118682e044d09502c00c2d04101071001031310500c654022a244104000122600d803a80504101100c018494511a2400c0001030520100856150071078104101002c1010034100888e50a15050b041000d9550340340c010410090050011500c90307442103008155400d81c1c04051441020f0060312a1002d8641d03440c01160303503150306e018101303ca6001e04d0038040803a000382d0040ea60710307100e504807 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 457632706 1250 457631456 457631477
    0x4020a0b0706020307080f01050604171e0609060705270d080406030609050a062402070302030304030c030311010608210912071805070801060e031603140c041e02030601 74
    0x2000c264440081610841e81c04000e00500b1548245081c1d00f210403139521030004c4d4148030008850f40304511440c896501201c01c607200c203040901880b1006c0c250321004500f020f0f65040c070f131a1124402c84103415a40106000252900e002e0002e8401174007130b56020406412a201d0388107010440d4041050f8040d4010743c81000280f0701000410160040359004680f0510700750301901503685c0640540301c82400c007034003030103428682c1d801c02c0702c003800b00104058032050088040c0c0c00d24290b9040603406000c00200070051128550320013041701d120f40e8034005400c5d01103901c02d08844075401000c1c0240c000c803452600d048540d50343d03d05409910345400b40341c45800c2c0f0001c2d0380d101174000c614004d604900e608112002d076848860003800a191402d129900d45814002c10582c0140644000d11002140d15001030b203081110510f204013213400c0901e05622814021b00b0150144a5000507100d4203000c0300203030410f0b0081400b05840150700414504000300030304087c1d00700800003410001010344 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 457633956 1250 457632706 457632719
    0x40609050d020c031b030c0d0c09060e100603090b06130b19030b07051318090605101703041d09010e030a03090605010b09060a03090624150212040e04020a 68
    0x81d02107448198000f00046040a4241810006404403940500807405140d988517280400c03002c05680c0101e41442c2c0401c0c030fa00c0c1c82e140900c0207400483e204e5241a0020414400305050540145545c070001581c20782d84503411000c0e904000c1c00248402810008a1014140480c0c1403810b5040130b1400301b29414410007045031f00f080d141c03801140400f100300030000d00121080c0d55400499038913001e49030402d000919003000d074692003000344014420346d91480303942450344148040c90f80158240b200f4100b812921442418900800c0080c507419403544000c241d000044500b2074114940505c0b0100d0a0200042c1c0c1c0d540c010300c51081c2c1d540740c00c070b50b6107001c406000a10400c40f80ba20005520300c02810704408031901604001c50212082065007901d075544e4050761308040091a01080c0880c46152110107810031214846541c00760100460030401c0d051100d07001d0b2402c201c0840718a011410f01280d680074161350207040700d0401c01c8140054191610340950003800a0422164240d41ba031 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 457635206 1250 457633956 457633963
    0x4140c0d0e01061a0310090c081605071e050c04180209130f1a01060311300901020408100507080624033306041806050909030406020f0102120f04060905 67
    0x10004e241c242e0700204122101c0540c00c0300e80042c0c411030004000c003c2082d0702c050490310010f400360101e01c1300196000241d922500803601c2d2039600c442d1922000c20810f80180d00100781d04811038050082c940000460300701440ba5000180015a000c60104840d400380009220701501004406010109000100c0e100030542c0305a41e110341e01c242c00030061101c00840780c50f010f821000c1090f08080d40000080c025400b0b580c40119280603201200044030700d000c403000e03070160a03540e888101404100810741d040d4040d10440b0030a0040d5130201040c0d1054108030b94080b240c00e0041072000001c10b246051520f40000e02c000c01c000a0100d42c4001c1003182aa60003c6070303201d407400700c3c04038084c0320b80e2408403028081c002800c00b8225141c0c0c912001504ea8001c0d405420742028922801c0140f142c0d0a4100c0f1b4014000030700600761754189861000d40702da1080c01108058468101200301206051080301c1180302030b50a940c40c603844807500c00c1d03110f00d400b800645110341ca42e030302400443d9091 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 457636456 1250 457635206 457635239
    0x260d020f12040b0420010905121903030c0935100f0207032604060c1b0510051f090b060c0114010602101e0213120302030904140c0d0e0106 61
    0x40f403000c4042d1030980380c5151450074514901401224003505d480c00d590b000400c0700140c1c0e804842c030583c61b20600501500c0c058a502d0403001ca03210100e105c03001d040d01544018440c651b10f954501e0301c2501c2d00011031811a0b0f07480150b000c0030500400342e4000c0c0704204042029510b15069451134400f1104107025101e054880d4110386d60300092500030190840b0341e00d001c0030020301d90390050460b109600c40820314004d00c058955038817540101c91207403203100c4e01e02c0501c10101880003c20386030b0400603940e1408160b800c034840e24000106095054460701d08005080751001030014a00301942c12000d084034035142604000d00303004181489000b80a040300e0007608070007101d5250303d0810001d20304030f1038081c040c034507515010048184c0d19031015103150a00c8a80c501694524141d440381c0307180d1801d1340c0b01080c803402c81031038541015400b00c010041e684040300c0500490812900001040d4029034510900307410402c004e00a46030240c00020070340d500c4900004059079103050071108881c50 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 457637706 1250 457636456 457636463
    0x6050607081c06150f1b0506010e010e13061a060d0917090f010309020d060509030d1505010e090402010c02030d0c1703010e0606030901060305010c0507260d020f1204 73
    0x301d8a03200496200c105440d028035401d40900a0901d0040c0036902e408403050842c0800c19417035490400785000340d1400716040f40300500024400850300300705c3c0d1210001c2c001c01e40d890160100000d410b503041c682c01c501030800c00d19001001c03601035803108010205042d0b031103105180b006440b4600d03980d40c406000d0f8900000c01c00f280c030000314509442c005800f0044c03030301020b000f40880c0001e5154514155850301d82801c00240c00081400090400524024010a040d080c9020800324440100c0601321103204000140315040c151400c0b10b071410360b24001c085c00908001182c110904d06841115007240c010f041034400c0c00e240b40c020904108a682c411404111592000d508004150442114445140709007608650400b6889080d040b0003800350b9110300d00220208041400a6102c2c1c002140e0100007007142d803820351405003058114101c159400c0d0701226100b440e60f40b642861f41d950f5511300100c503282c820056459002500000c110610380b140c00c1c0208020340e9006c42125001d80d00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 457638956 1250 457637706 457637723
    0x703080c0d03050106121e02210108121804180c05190f0608190606020a0b0f090c01050c0c06040b040e10030c05010e0d02031b01090f0602060a0f06050607 68
    0x28030806900e0291216241010103241000401086500c4025041a20000100419600c04c0c0000e40c080c015210700b40d00c07800e1440055042858481c103c0c2c445d004524505031100700b41e0340c07480308940b5180641d900140d100c804201040403482e900d000c4102e0b81d14010300004424941a8a442d400820660226415040108140000c1c6440070070105103074003681903101001d0400c00c10151300d18051003a402444550801700c1c103180724a85e034450080d0710442d81003203440daa03807070025510341c41d151081d00c1008030203001c24000400e0040c0c2500ca015104010322500084c5401110140e00c80c404000007400368414001441c0e031070900500052005240f1141c50360309211300390000001c003404886070790707091000400000300031560003400ca407800d0a1030303c00000348501141c40c000081c00c3c025814054036580f441d10700041258104011002c0c0d0724012851b4a40a2001d6881954001c200c0581e01c810700003180c10983d500480990040c280000c80c2141d5600046a01c58001c20000c886282 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 457640206 1250 457638956 457638967
    0x3050a050d030e0d09090908091c0201090e16080408040b070312060f0f06050f0d0509010509060603031602131b0804050f010b21010b0618040617031b0f070308 70
    0xd030300d40511080302100340c0c0603288501844d1006400d160843c40f842d9034550322884000c00f44213417082999405100035080b10320740c054008010180b00d400c114102e021402c240c0c0c0104400b6000c1c0792042c072849020044501d40811080181d1304132800503c1150400000c200104940c0c0e40c0501400100c1e201c0d0b124445c91455070686c03541501c910703410443d03c040794544200300000030009020300f01c80003400e140355034450110300780e00c03117120b003608150b141030604041c84607909055114504c105054801d98040e91a441e04243d1284150440c01c40075204858103640076203040603d07585c51081c2240005a084046030082984d140e000041038007054003501007005002e001d10040314644003000007000b1034000000001c0e0ba090366140c83c0c0f1340d04241258912501d520950250714100c4000745842e85a1444003d41c0481d960f00c84d0125000e1803d0403000181030350642c0d4141c0d04440410040c0d400e01384e0520240d2400d50360b00001030b58038400e208036052410301c01d01050010307500030880e01c0d6030f44 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 457641456 1250 457640206 457640233
    0x120c0705010f0c1805060304022b024b100c06050106090f17030a030209030a02090c0901030f0b0303030601030b011e08040b07050a0918020f13030203011d150601030603050a05 77
    0x120b1342e079000301d004080820820005a803840b2001c2103984c1e0100c203005c0701502d00c024062000e0003030340c0001d400ca2081c034441c0390002000c13410600030650480c00d42000f4a4400140c00010000c44840240382e90146284500762404801ca4650f4501602d0314078418599900c501080e00c000780e110a01040c040c060a0000751001a80d100c0039100680580c41c0782035a603200c00c0d80d00e109e5542514101640450010455a818011640b02c2500140110b405040c2042c6070003040c0c0c454180355000c80e107403114400c65074034580a95140d00a00030040c5003103030703034600064003d880320043d0581001a42e400302d103d102c0a80034641c001c11002d59513103009241514004200500c0640440c003807183c2800789082c5694800620000d85030610182c05144208135010300103801000b0f8081440341c40441d0410b0f0f0034080301c07019401c4034001c800a00a1401a0307500840c100c0d11040501050303004201449002d108a4034042d40180041c0340001d14035a4030741f45c10382085401a4203c0d00d070f41120784071402c41d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 457642706 1250 457641456 457641497
    0x415120209010b03070203090103090f020405090c0102010f06050105160206121513142712091008010503060403030902130608010509100e0d110c0402190201060803120c0705010f0c 79
    0x3d010401c940314650f04000c48044e540b070242c964080d04158984150f4030070418040c00c0001a268040c10500c202d051100140b61900b01c940d0340b0600540c40e0003a100d0681e10540100b0048030b5060b160320f0301d0110710f03c060101c04c20510400f641c108104115404903011144400c0b84100b4801c602e0050b4110103200300614800100348407000c17542042c522500344901e400000d80c01924038000100c0ca04204d001d001c0e400d25101d2007410190080790362106140b20240c001781300c1c40c502220702c1c441408078028140e070031880a009840d010762160700040c002038080d9003d50385841c0024400d014040d0b8808404080c0c5056810400d40359450301c0a105085c6000c1201981c010302420007846000307004e080c0f203690b400c4505101c0c02008400c01c08105d1050061041c100300c2030300544190741c1d4061801e00741e00f110b0780c0c485e40c0000542c17074640005010007011094079540c0038409131400d501d0f201e040401402d50050802034600d55603c400409205000c2d10170300300d02441d162504080c200d000d40d0b64811 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 457643956 1250 457642706 457642709
    0x120a0507050301050907080618070309020307050301021e1b03040909061406030c1324030b0106020105100308070203010e1509191a131416150f030209041512020901 72
    0x28080140b006201d583c1c0c4000c1e0080d401046403800030b031aa030302c00000400a5203c92203a00c000b01080c1d0600c2001503040c0c016541150003030301101d6003550f031182454200e11611941c0410f04141181034019500450001c000325042c00414869440e4003880322811036010743e00688645580341070100070172099000e58192200039446a903450325040012a49941e80350958501c640e090b03448001080c5800d6021f0f1300c0107d502059061204043d001c12400010340e4003040d02e400301520700004a061050203103d21411f01075458100c0545107558242c2607030403000080f40d165403107002c01841801c0030403000d1070007059018605040c0c101940c0c42828912200c02d0084414081800040030482e0145042c0e02d41444203140801e90750394105210442c444140014908032284900c0415000c002418400502c81c60400f844210341e036800c0c014030910502c000c400400e1030001c5c0b20402d61b00a9000c2c0142a00242c4042040d1a80c281e004081e600c00d40c0000310040c0102002405604003c0c410a0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 457645206 1250 457643956 457643971
    0x30d0e0a03060c05130608191505060d0e06010b181905060310151805030708030313050a05030c03091f080a0905010f060308220f120f021206090105060a05280308120a05 74
    0x2c140300c0c0c944122142702090080038040d500001d08495141d00941c440c041407640c640945005585540c0c0c9a4220340c0b00d1403400e981c0c0080c43ca60089540740442c81c0701c81e054020140504e0103845c16040c00980d0b04000d003140c50041010200180c0c072072090354650695034155940101010017070350090401006a04458000d80c0700d603000b402898400011030b07410160704140c00c0c0c0b6064842c0ba025260034942d08000f8000d00011a1f542c00051000000e00000c45088503010440fa501d80d0300c030041c151000704c200700026490801305120b89442c0c0d1144480ca8021380011405840d00c000748000cbc0d03900395001316420300c400a105458074195103103180b12495624104110f00d07240204005450015005446a40b6000c0c2c0b076104c1005503824040303a00360340c041c050441120109482c144c80c0c1d00c0480d80b00d031035035007840700243e0a89003141c200410b8541c0103225600e1101d080e903d00d2ba08a80c0c28a0800041c45400808030215640c1801740c0420088403c0a800e586445450081036a4000d42043c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 457646456 1250 457645206 457645211
    0xa030902032e1802060a1805030d08010303050c0703170702121c050f07021c060b0312180d14071d040812040515040b0105030d0e0a03060c0513060819 66
    0x50312a148000041100d40110b6140030489694010301c031400c00001d56402540001d00050306a400b0390041c20f004603c4250048003500ca83d034440505071100c202111020004400400500001e80100c014014000700e550440c3c081540382e0fa01c00c819600c0100312000000c0c00031914104610381441084400c03120071000c1d10381040407007100031100061010120074420041401c600080d5400103840485030010700700e18106c00a02000690303002c035030300141d1b00a41040d100342c2e52410f002602501403600e615044c1d25010050810480c00c1d03041d100d02c076500c0078a458008003c03486100136850b41107918005040309a03e1702004e46100b02007002c442920001d41020000420b40c020160303100300c405d90364136804654540ca0700d24145410300001070300728140a404e0006002e00494151306a4100b5011100e012350401400e54030482054642580041c1c035000500008615030002d4003003d1031420301e9030615081c81009043e004840e0807907000100c94508100701020107400311105499030074001c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 457647706 1250 457646456 457646503
    0x1407020a0b0c190b04121112030411060c070306020d060b0f090307080d02060a0504060209130b09010504140a09080c060a0c020d4d0303090601050612070c060209060a03090203 77
    0x400301c1c1210003c00180c148081c6d003c140d0784950090300720264420707000d801c0d100b09400c04a800c0e5000e400035030741503a201c0142e203180304203828940c003200d200300d8046006111051465131200069400042d0b60020180c84020005068404101415661840c41d2015846900c402c041c145031145c0b9511100080d44520001c00700b00c2d07008124030350490f85003074000c240d41c0e031182428400382c410b001c050b540210440c807194110312003aa0100440c0b40003107400c01d11a0b40c1c0ca10412066074440220080c47e003400001180d00342c01d413580403910184c81103800d10f05104c0055034046c00c010003103440e0003615890302d0361303403490960511607410700514500b02851a04140e1031265140309031200d09007802501d00c5200e18044003001c00c035513042e0144130b0030300160440c44110562a900107544043e8148540c00000c1420328002095400d40d8290f2440d1a40765a2035510444403c2d410a07001d40d03003982e00f0408402c55888601c000c040c000c059450104174611a403060528000c05134001071a6020500c00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 457648956 1250 457647706 457647713
    0xd06020405042f03100e060d0b01081e030306100c0c0e1f12031209020a0807080a03021506011407080d060308040e07031a120c0a030b06090a0b0306071407020a0b0c19 73
    0x1004250b0b46c0103148118181d840002042c1d280b070840700301506007040340000080303684001032406c50195001c0d5000c80b45841881d11a640e038002950a6030340481c1c5150011030b014829000e0f14002d40c020b44403608400c2e681d0782c130000120410344412440042d00055840e08440c004014002410001102c0c0d0200c0001d8400600481d00e880c0400030715512280c602c01036540c0c1c1e00264018090640c1980c03020340e620f41d50079076505a5120100c025015018003a840c03e107002184911540c1c0603190300c0c0c210090030043c800a60710400302225054028407480045c00050f12130a0050741c4160411681c072818a00b60001c50a4028940c404050500b55000481a40700e00100e132042c0c025500c005040c44d050010728180525000826000312620a0010903c150300003020300400c016034919100b40c9a03601d0300000d40311145000342c0c050344010040340d0001e1003081c40c600b1032209d14690b1410000a03500141d02c40d04c2036800b41d1000640030900f0480300106204042001401a80c04141d00a581c1d4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 457650206 1250 457648956 457648981
    0xa031d09010b0304050331081c14040b0a03060e06030a11060307050d110703171003080d0204050414090712050a02060307050f04030f030206070f0e0d06020405042f03 73
    0xb031070380c0007801201180405c6010816295800341d02112101c06841180c02c07a42c480c01016040302d00e202c03404400280106001c80c50b129400c210320051145030150f45130544d6100d44011120702000800c010000c2c8005400c000741c550781c100d0340d038045840380c034142c184405190040d100752310076001b905078400000c0c1d0b001c0f01040003640607a03210751a992400e5040e1a02c5c064120030b03400440c28503155101c01c410001c004e058070392203601c40381c0d01c4881128a4200c0302200301e40c0d500010500070700502c04100c0842c00b4003c2e40e0700a04001d407800791607001280a40d18502122200055200c043c441512010b00c2050054014203411905074082600e50b0f075601d245181c0068001c1c4e0b80000419a228480c070212030100350b0f00c442d600da60741d40c2c0349003c9201034011401a0010300686020400440c8101301005004001e55070ba0300340001d0341e02c100440c0c4900c83c03001b1900e05908000c00100d54441d40070b015110030f9040301c0c8070f00744800383c880c1c800048034007000e03403450803020820420300c0c09000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 457651456 1250 457650206 457650209
    0x708070519030e1f1506120e120c0a0b09030c0d0302090d290105010f0c0b090a1b0e0c0c03030403050d02070b04080405010f0c020f010c1b080a031d0901 67
    0x1400c42814110310302005030300905040c3c5901180e40641110709a1800901c0748601c500c51441c5001c02c0078010b1092900b000c45918000c01000509030604000e56144a80046035000510415074400885843c0500116881040e907622a50400c82880007401242504582d104422030091440c0c494004620b540340d4010110301024542d01082900c0c0c9a1207051054415a0707120b1501c1c1700045401c02214144440e1448840c0c42030150303400030895510950000c40b200c00701d5101c018034503a581d43e4004505800410b40c1030107200340300c7c00902081804011818070709030110880541030402481c80200c1c2001084003452020801c003022009400100302c81e4400d402d403800c1d544030401585207078040c3c071400c83c015240e504002e0034041400310640082044540036221001c0e6824440da080e64100356105000e035010100404451165004018a10b416807140c140140c000700d80c0b20404000c84003e1700000c415901c900c640c8002c140e0003000c50b1600020940c10804110200c0d0700052200105 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 457652706 1250 457651456 457651477
    0xf02070509071808030a1814090c0a05121006020f0703051b0a03080f0901120b0a030b0606070203151512032d1c1d06162007060807080705 61
    0x22221a0b16490341c05030081000f44c034942c401d40341d40f052509030040c03070103e90400101c2d40046104c80003d5401030784030780c1381e8021006041080c45580340c4c4c18812050b0400400f400611400300701c0030800340c1d041d05001c3e120f42400c0f00c503424120b00f850030080c80c100d140500e66140c0c1d0300116060021900000c1c8075803115040200710f0b041c48400c80082905c606590340f004009010100340c2191000f100409480030010a80c0c8415207582c488140405607991780200541145603800706102195102160586c0008090069490041c40758046440c050306130141020344d042a900b40508400408800d19052504540041b00003101c6106507480b0303c1148503030b1407490884015500b070601803542041100c810358541030384810001c11145000302c56401e48610342858400d241100b01c0c0d44503a100c500c500090014100f907a01c6141c01905e05424141080a10404080c1403070b51003a800e0920280f00d151304090b00005103014006024418050084c0080c00a840200024141c0c41026541c00c0c024 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 457653956 1250 457652706 457652717
    0x14120c0d140f010615081909111305040501361b06030f050105100c1b050405010807030302010b06120403051c020a112406130f0603060c0f0207050907 66
    0x21450712203a60340764003000e00003601410407810120720b410341c0b205084074080c1e410420104030191089800e118201c6511000c41c1d09410b4030700c481c100903444514494440d141c281d844044070f100080c45803010750a0320032103a48603170400040040c217014001d00484071001800f03c3c4080f10a604048500b00c12041074010410f800703010a01441220400f400904001040d00558036018001d0240020342e42c0035100c80e007410000541818441686018150295541c2c14000c806607160100704010703041035005101d03001070200705139886210301c0b802481d0b101c004104692451a0290075941c0062800c2c1c0304c1d140601103041088035200040d0b6215a241c50020b03590300312141200c0801c984a100d20a9051010404441441e08001284007040f521000c07280001003010303000031100340070b46140d02000d0b1924041080743c2086003408161424125002c500c4070b9079025510101d0b44a03620907182592600013901142e500102034a02c680410301c09440240d04110100700d6102001d80920208207 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 457655206 1250 457653956 457653979
    0x3071e0215031009021201060e0102210f13152d08040203010e0a030201060602071a091507060f090209010518040b07020a0209012402030a020d0f030e0a0c14120c 71
    0x3c90741c1c0e02c00001d0300706104115280c458030b1344985810002409007034081806404025034560000541d81c00b805000741c1244c1002c1500081400690000d50f40d00c20001002c0c40102d103232640380c0700b204d030150500701d2200c0c41151070f40d80d0003494071010300761849804101c0e840011484143c1d0140d1003d8035624140864692101c4c4003190046c180c40c1c001411034020012a441010341c19001201102d40c60350031a4101c1e078a45000300000c003100385491081c0c00c3c0400034100181411000d805125804906146c00c00d03409460b9501507440d8a20301080c6035940b401e030f1004524250407030601420044d02d0107520500e50064021029101400152416401c28000380150744200702c8014840d5018190303110a5a640040317250b00180340d407060603a50f00c100c5040407868400000c2d0b43c0901450b0f4000d144504602d075098038020071303041084041588a0040d407003880d2003001010b841901c103156290406250480042e1a2036050710440e01c101d0100d060b0748020440092a0950301108031a01d04030305 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 457656456 1250 457655206 457655221
    0x150f0507080c0d080a0e03031305030705070306020904050c040522180c051302030403090e09070905160306150903020f040e060f0a14040b0a0c09080f03071e021503 72
    0x1030003044402030078a080001e0b02001c1c2e10000c151810f041549854246154403041060300581d2901c0425820301c3d80280006640b801009082c04100b5010704103607407810340c232074680905008094209544c025000135442d483d03410079100f280e602001c1c9100080c00c2600780000103420074003000303d040044581100380701d80e0404030b038010081074500c101e800b03000e01c80b81d02d00058000c00510031207104190804100b0b0030030004d8001c680c07140c1e5155880100190070840d2a928508018191070928807910320007081e00340303281c8500c03405034010710ba0100300126030f100014250f81d459080030190300b2200c0c0020400c5500108040103403641241e82049031040d0602203802468001b62039400380c8a11402d22030b42e05080c5c01c1d031030300074942040d0910081c030200d0101d5078a40d00c1650002c00241d5000005000b2845a903c003d9844400e844c00290190359000f03000d183c802c00301500c03e055080065003c00b04801d82290841080440744800c04425003074000030030348980004020242c240000025110 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 457657706 1250 457656456 457656467
    0xe060a0302030a1b091d0108030a1d1e030606030f1c1101050a0903110604030c08030612070312020d111c050705010c0309060b0301020c0a061a0904080d0510150f 71
    0x110340d018001e03001041e04c24130041c44544684640981114440c1481d450381d19070040d01e5040e681080000c503c2d00100c044101c030300310300701d18000c07054004020a2422598425600b0801c90728001c40d8400c1c1d01403500708040c200b06c0080c040500c40d40c00642c000c001da0f4004201d011080d0783c18448410a0107010005071000b0016481000300381d441c0c0000c100d01c83d002980700505150180e901c000c80700b11821001991000d00741c0b000707804501840314900020710400c2c01107a2204001e48101548180c8480c081d02e04404d41d002100ca40c84600070b1315504650410480d5089141f42c6090802c100d8015012500d55000c01c080316009a10150101d4825000718100c550840e8010000c21610304941030003001800e9000c802ca59207821301250164504c0c050003600c10141400307000d8541132845650b80030081c030340e400d104151001c9440c5010215074406484038400c1e805001c41640d107c020346652000c4681c0148011081e00c1d1002e0184a40200200c044243d450103040c008555481350f50203960 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 457658956 1250 457657706 457657721
    0x6081f1a04140a0c021f0b0f130b091003020d1403070b01060504140607020907120b18191503081e0c010b01080633040302090702070311010e060a0302030a 68
    0x1c009007411540070800c00c0c00e20030188166140c14081000310030b034220490b201c604a0403c07a824034411030b42e80807070080650000c0300c00c0030010940842010180c021580d00e140300c5c080000000c0e510000459142804440540c1c00a00c0c44000b1b83c0090440d0700186a80d00160805485240d610400c0c4074000e03410011070344119000541c0b02819a5641c20043c841e40c0240517140c80c01c000101c201d00f00d410640280c0d54140d0f4002c5c000d04041d50703403c4080340e1040075441e02c8240b0646a01045440c0c1d01ca10345071203618520081c40318598030744a100c1c01400ca80c1c032999000058a00000f2200000404a65809603580540e941e40e8851410101c00a00000c080d42800e12442c000b9403040540310542c080d080c0c8900c01c1e201c0d00110340d20b150410000300c20405041034542c440850009031495a01c84000b0418000896103040503102d40214070460022686107026070f211400901c10702c079024148508c0d899092034080c0c802450400822100e0207070800060606801101142040c00190842c1c0c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 457660206 1250 457658956 457658959
    0xe12030a0f140115052b060b040b0a080f04031713020a0b090423060f0a09050a0b0a0b0c03070209040f1722050d020f010c08030a020d06081f1a 63
    0x6180b44607080c201c0145401c0c0f00302e0400748050210380380054094800e0302c0e01a01010f8521100380920240c200c88007108202c561100380d45c0d650040340c3ca44000d4007500180070f070f11600f40d1311003104075005059000e010300b10401403130741c0c4402c200020340c4c01807488010361030b0300c3e040481d03544840702c2070120f013200342c40025070104481002054101041e0041d0940100458060240882d8401207a01442211440504240401001400c14203014032403280c1c00c51b015140c045003980e1103070440102d81068640710300d15a181c5940c00e8a500c0d190500d50041c0c00321040329483d041a25a007103a5030f200e10364000307008180300c0e000a400e00c203240f1001c09100f604121040404603024040364a181e202021036103c05644254401200300091015002d4402c0507000c0420031060380c00300301022400006140c10804006500340003d000c07400510b000d412030350780168031202d445540c83d054400c103401c0300500303512655001040341500041141508402e802c001540020591880561803180140700d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 457661456 1250 457660206 457660211
    0x5181608061f15120f05160f1103040e1503070807061d10020a0506090c0f0603150d050c01021005190506030f01020c0a0b060108040b01032d150c030e12030a0f 70
    0xc1502d5500600390011082079401d007003080105e10314075103089550070755031169a5510b41d01001c1105e030007210081e18401712410184007540200030180d10b03650040c3c0000160302c84900502c40d039040c40480c90f1207034a0049015043c2c0c0d60070000c000c0c0d5120840c1c0300d468200030310280c0f12010340305590004d8103a000d01601202c40a900705c05c2c081d503110703c0c1c0b01d0112258484c2d0b80000d060500041003149942e04000c1807181881544c0e01000601c0c0c00c0900822440813208001c050700b90340d0003c04080041c4140d010340311410564001a06140500042400103400c0c407080100202d912080380130300011200300055907848002c0800e241a0001c02d01c00710715840041e50340c5040c40000340c103010851180e40d01100503030320b1500440700c500b8166002030000045a00610000d00780b20340d07035402d40d01c40c1c03000000b000d405031030f40c8031540280c203100369116440141018113501680c059030310510f405080074001c1c904070107080c1d580c9041c0080041ca540e81c0100200d2030242e1241c0080ca800441100103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 457662706 1250 457661456 457661489
    0x20a090203061e0a0b0c070503060702070609060306050603040f170d09150207080f1605100e010e0106050a06030c030908030f0115030b130903020a020405181608061f 73
    0x200000c1d803040e40e503035110742001000c00c0070000c41a4040020040d000d4440c0d6001c40c601510740010f9003003c0101031481c003072400003103882e84080080d144103c40950040c009075280c044003604d01102c3d600080c04042c1804401d00a0780c441d40e04403904030b6803144112171550340c0c0cad0a044c0e00940508002240d010310028500c0b0044069400c15280c0e03600490040c003080b070b0b80c00c0c1200100c2c4510b0b200140310003001d0001d001100410f0010340500740f090303000c10b14902038540e940d42c1044031420100a4050361810f030107100210034440d5003100c2c29400000c00c065402d00300042d01101442c81600201034030f0308020010548030b50042c18800340d10020b12600d03800e250402c144500e209020301104d0441401031608030511034042c091044501504000325507204007101000f0705402d070350942c154850400f07007100685a5101e810b1080c5a40d040c280200e04454140703a043c003900e0458201c4440352400b080c040d03410b01041007901720b103485000c141c41c60060124401d41c07095070341c4401141da021603807 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 457663956 1250 457662706 457662719
    0x6091906060e03160302030d080405031b03030709091418010e0303010b0702010206310606231009180b030a0c03060f0c05070b0f07031506030e100203010b1e0403020a 73
    0x28030782c503000080f400e540400d024042000c0801040340b10107503140d40021940303c821401031515036003041c040e038180c0345414682d1000700200c54221880c54107650000040002117680015004060200440240014600c0402e41c041d000c8015201801d08410f500c4116074840c4254003c01024042c041541c0d202d682d20001e60180f60094941603001d4001c0303a0014144c0c200140c840c4135010701c14924544c28000013411a0540300d6100400c42d42c050f46c1e0100459044910300c40c0c8540d0f010a405240c038100000014000d520b682c44030401c0a012030030209202244481c228902802d04d20000014401e450900092610b110b0040c058240301100c0300100034482c1c0ca4212001c003912054041c8190710310200304071101d00c14500054001c00303000012030311129030aa100c917000325041c0b4020078480400450104903820715480076010960b0344a007581104401d01141001c158103400460566140c0b04141e045446004608072a202c041d01c1151242075092081d40c0c05580c010340348105440d02c405 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 457665206 1250 457663956 457663967
    0x118030e04050a0605031002091c06090c060e0f0603100509010b030901060b0f1209210405040501353c0703020a051903020402070302010501150f080609190606 70
    0x426000c1c50070400068540c02e0f16001d2402102c101600801045050414440080d00202c00c0c0c2d540c00a1200c40c0140c0c1203864410181040e8050800054490387d1032800d80007051681d48080d0510864016034200d690351410340c066510070a4070455925030310524148810400c0d40c10843d40606000d00108400602c1000741d441303a040d001c008c0081c25140c40084082d0702965000c400700f100e08009000a880002c03911540011007501100d5900101c0700100341f0443c0d203038140403d54140841d0410440c0b0702800381900402e40b840003d603942c004125294012500c4090783c0c0c0200081c0c001004c40700000700120020a010b08a21500803954601444141c2d0741e4019055103111041c8121444507401044010440b03500500200400d0715007018801d0240c2441c2c4101d440c608402e6000025031a5030000300030840c0300703a0002800c4d40c10b0014004000102545401c104000840c1c126042c5410209040c2c20441c1110000c00c1c4d6620700c0185c4a410700011b690b503484a0601c17100154654002 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 457666456 1250 457665206 457665227
    0xc040218010807030905030301030f15110d0605041103010e22050307030306081f0b0103110f090a0608091032040c0801020a020c13020f03190b0f0f0f0102011803 71
    0x341c0e01d0800e251502c00c811021748a40384000381158008000400010f00070f24003e644803072241c3c01d04595240d0820145085034820a60100d90380c0c00011100b1204203684998000342a003182d040203030003211040264580814022406015160b002081d80c00d100d0720048901c50100300050700552160346441510f941109404170082410100c01255010b40880c40d003488542c0710b400440b5415900300a0001307001c06081d028141651030100c84034125088006001a140072400169503030845070070300c800e07180103620070000c0010307510600080c46030200b00c40c80f16405080012468000190302000046941e14820304020034050802e6818082c142c80300d40300300d009034083d4054942e110200f80c242d10501c150600103030440700c80011645040d90b185588242104001810943d08940756003041d4419030b0030301401c4000102c1e003c03042cbc0340c0d0302074813000310300c2910704020040d0945e02207041400b0b203400d560300c1000c80f64200d840a91007544600c0710148012030180413014942006010100034 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 457667706 1250 457666456 457666459
    0x203250503070e0708340507110d050706080604020904091b060f17100806040506011e051309060b091806060d030906080702071d16020106031e050c040218 68
    0x28900b0008020090402d59841080c040c0c0760311140c1c3d41c80000c8070200c5200c581e9a500a4030b41c1c1611349840c041c20040c0780c01c1e06180380e01c0301550b503070840c207221455804c2694810f206110080488000a1000c80d200044442c5414085259142c1c0c000140c040d00519941f035400c0751400030f460062102d4401000d100160a111588001c1d40700d4a08a0351b280040c20010301041c03224195401044030304502c258440c0c40b030036400140980b11060a41040815901a2042d60002d00140b041d008402e07801c034045150038014003001890500440c2810107407200300101e050b030382c420f28404d0001c3ca03003149500d210300520240b210b00c1d108107a1050102c1004040485215407000201e0310300b02040701d11181038140d101c404101d85441000c540856000304402c0450050140000e40c0c03102e10507000c02401381c0004040983e203040da104408003904201c01c1e000310782c18410100041049000101640e20096100080810305820401e1a01d446954000e070480d2000403581c545c4180d0401e0801c51100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 457668956 1250 457667706 457667713
    0x1e08120906010b1602040b040c030c170106020a080c0109120206010801141b0912030a0f0809011a060f04170102030105090105030a030813030e18060103060b0f030c070203250503 78
    0x95200d5480c0c1e80704000d000f003100038a8108104141c02c08501d0180c90700900c01030010440c1c0000b04041819174405446e4a800700e40c40b4146081c1150300040340681c5022210f0614809605d0107070000e6440300c0c400400351003072000140300001c11401b034002c0200c203500607011031000b120711800259070b00801d10030402254a040c80002c10380061a42c510f00844040c0b0144483c0410000100ea690740300d0240c0951044050780d4000c07842106101800e100046929502e02086034034102609540d80244004c8036170345813013880c0301d40c1042ea42c10080c1004055620340e88802c46801d800c0c0c803c0c40b8070b8100004845403015000c491410540046040e990203980c0b034861a6070760000d1580c4c0f04c89400005022400c1100001d0050040c080c28021042c000e2511184036800c0c440030a8a9240224051580c060503508004003541c1600802004009a030400303880c12032054000030b06400090658031680c44000780030819541c041207444122003142d4071031a05110321045008030f05106105a602900 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 457670206 1250 457668956 457668961
    0x307051c030c09180902090f090d03020319090c08100b0406170d050319020a0509030c010504060f050306030f0601120c050a030c09230a2301080304050d1e0812 70
    0x501c640581c000c00685a1103801266041906040b446001c2889014090b540c802c1c0040240e500c90200d83d001d00c1c5841d1b00d9081703604041c6905400c003c280c002140c14140100280030b000100c07248140031540f2503280c001442c441d030b403800e154041d101c0e60244166108952110012501551182003000ba04840400225070b4544002884400158110880703030440d003200807204d40640021903205a00c06001240403444010301c40072a00103a000307100080002c911310360300342400c01030001c0b40002400c3c03990503e45050310040c9031114a500c80c00c1041004004914244c45c200695402405a80c2c240c2d041503031902c80300d50359001420800e4032450402800041c1c241008070119094136081404502454107000421014003138a80034508a201240c05820781e0b603000f1040540203020008010400080b42104004658550b540d991007141e4900c00401c550f00000084404568060310225560181d03030505a0a90b0b551b940124030780d0300c81c0c41603c810080c1c840000c0440d840901600303889074 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 457671456 1250 457670206 457670263
    0xe100e0117040f03080a0207170a02010f060803030604091a04050c01180303020712081314010905030316030305060619050307200c01120608030d0209040c0f1b060e030705 75
    0x1c1c0019038018014400c0ca101480c0840e2107054640d80c03240448001501e0100d40e42c0d16010600403440203001841004107055400ca5828010b155140144400c01c2c450340d800c0c1485030307403607201c09000f1601c201d5a40b11074070304012000c00250440c1c140c001e01007801d40b8003803c3c1141c40e504200011130018440d811130180d040a400550000d03280c0644c0101000e0381068030083e41c44003c85801c2c0c130030100c28401e4150507007500340d0141c064811121b200a002c840100054013621182d0070583c8030340c2062080c84170848111504400715034041c540030a4a40310440403904030b00c21440155501d1075515030340c0c1143d40d0044015409408156103000c1003004244050303044400007140121581c0142c0d41e02c980075031150000555203001c01c100001c0fa19510344080e85580e1105030b01d880d04070b4001c562140a032400380f2502d511a021801c1ca0710f1400080000200700c10107075820039400c128403040b45400d102e410350109100345101d0040b1b035612140c80c2412a0348d28940d83c5904002c4c1160036281106 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 457672706 1250 457671456 457671497
    0x316020c060f041202010c0602070c05150f0306131506051e0301080a0b09030c0709062102090106030f0b090c07061506091205030903030703090f0b0406090302060a0e100e01 76
    0xa40301c0150306803d0a003884400340b2481120581a41000b114180200101e1000e20081c80314038450b0903c1c80441d803908e030601c4494400c096a04240035010b0055030380e402000c44c00c881d4003210455400300c0801d0009840b00080420304103604801032440008078203503170810000c5c09034101c2440401003541136090000d0403072009015a040b02d40001c1460342c0080c200c01392041e046980d032000e03282484240350905143c070003154000c07800d841c0c8072032007042140a1146848200c0f1500d03a10181003a64603004101d48802c1803051300c040594a6909a880700b11ba54054195480000e0100c610f609025038003003042d0704545400e0750305030b2030118200300041d59230309403108464142e141e1480c0b0610b0006501c41d0710040700c00c2078429000400684800359000e100804009100b030300c804103810f0521042c840c3d04140740d0030111000008103c2409607a4001004004482e4103c80c40c80d0385080051088481c90544a6503e40000c64811002c990300d40050029230b200400b070b038640000a00c074480d40e442 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 457673956 1250 457672706 457672717
    0x60203130b07020d020609040f1a12061b0d0b0630012d0306050702032109070b0a12090b01080d030612060513300e01020c010f030b060316020c06 64
    0x140071940303203400401030400101901c81e5607c002c3c400a008900e090342c1005030b038012000d401005060202000c12031038490b60b5244601c90003002000d2030326220041c0c01c100d80f801011080d4503400452031080703148058100440c1c0b8000942210385030030454400c2d82c1c400341e5000113800d041d6110080e03901d04910385002c080c1200c3c01c5002904600b500d98a02201c0f100e00c43c902c6003003118201c800400441c0f03850040a0050707601d940110303541e0f0316143d50304002c071181c164110040c800e5a030030b104041e080004c0e010b054601c69100310b030383c40b04480e405556000710840e982291600b0030034000c041c0503508120b541265000001d548180c48540002c90803a583c501031000c0e03c807081d0940e440450501d50106a100c0405179180050100e1602c840803410484d0021070201e07030103c04600c0c05170a01382d440d000d1306035590a00203180202500040d46440c48030103414100214038524140c640c1c46504a000f5080e800b504165a070705103046078408020b2007240010142c4a450074003845401c00320f04854 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 457675206 1250 457673956 457673959
    0xa0306080d141b0114010305010510060816051b0604031209032a0203060f04020f01030c05310305011a01050901201c031505030f07210507060203130b0702 68
    0x110220800c100d00c00380380c2014034034041c4582502d243c020300110910841d211441c09101071119989107180c0079007034440003004401381d101800000c1008a41091440c0d0700300301c482c104800d4007809114121494000d007800608111026004401154808207542c0d000380d0003590b46159010400141d00146c91001c0c5000300003614004810110b0101d9031711101d00300000750700c004030054241e000246015003d03146907008408042c2880214a0320032000a00070f0300a00b01442140340840e0050410300641094121030060000c007496176034100d801da070005107010055500c80503100d04041d8000c10180301c09103070614076088250340941c02482030b0350ba03212050f594603142c002c0140c02e11102000aa103020174030b2245000052048403640564175043c29203640c000342c0c1041c00394451382c107d0700c19405507009030403100702c281d0348403804640c6406603003285181e2075280c181c1900f001c54a481c020300203046801200c10209040f80c1c003000130800070311114101c0901c1525400303007140fa88120038009 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 457676456 1250 457675206 457675217
    0x1081002040e0f0919060b15030114011103130807060e040c0e0d02032a0108010b3c030403050d05180319020705030312090f0309061b0c31050402030304061812080a0306080d 76
    0xc0be01c4c2d611a02400c42403280789019242095800301212980b001c850b08551300c55000400b05002d4558031410381441300c4000c45051103400003400c4050300e40201c0c502854001c0c0385100e00d20702591410884100a070b03201ca88441504001307003410a524100c2d00d03034121300140661000080860001094414520b1084213098009a8680d82d111241c030b0707405103900e040d40c8071150101c48042c202015620550003502e40651341c840c100100403c849000b013007001d105020001480500710b00000780c1e4002c40341c0891280d00000c5159090385081d440d60f10030b0b070b85440001200102100080601d601980ca04402c5921541c6071110305038481c02240d0045070400c400780310070700c86804180c4031441d02e0b500b24429114401c41c10000b24106403c03008840f02e4804a0307604880e180003c080807110302c00d14644003000141826400640c480c03080d4031600d01000000907040000084070340d040303001044104401401c070241490005015085001503802107450172400241d100c101141c2d0071913080103591603 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 457677706 1250 457676456 457676489
    0x3160330020918041707050a06020c010b04060509090604020603090f101b0903030f051305040912120b09011a04051003050109110403080d0c0203040b040b0301081002040e0f0919060b150301 83
    0x3201564128810599491180c00f0842380411643d2000f4503d4401507c004600301c003640c401c0c8820b80c4c01941c00756014401200030030104810208501c0d4119604031011952070b214405446e01e065820703000c0c150320340203981030709902d40020f900c03038001900f840c00c1e0490300c00702410059a0100142c48080d0100340243c0440300500e00c148014000c1000c0c00203035036040d50720b41000c1412245080022100e071076988007204045c940028030451400b0303100009204213118040484e00419042c403510784408800600e0008411400c1d00741c1d00581005850594a5100c240005001d0082031056049031132401c01c620030f02d004d03031700d0444003929000804540313069044d41c100d00003024034400e00011400144404207010280304020320081250b600007a40300d5040640d02c0c0c3c1409200c030110080340e48100801c01030b64120401d20f0b684441c0d074040300002d5680345031040d414120301c0e200042d0501d20f006c0c0000204006580440c9a0307a1080c0d50390f800e264180d0011000c14402070295000342041840d8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 457678956 1250 457677706 457677743
    0xa1a0d05090102120906040317070e0103020c0f030f031902070209040f021f0504081203101505130905041109060303090d0f0b070201020306010f020316033002091804 73
    0x40381d084603800c0001454942c13400b2100141d1681520030b41c1d0301d50441020322041c140d10081016014401c45c180303809a050103400641421308409a0078141500071a0f4240003180034001c039480f2a00700030980755030702210303410420a58400c55002c0d240e0140d010008020035aa0701c26140c2d640d0f03000d0110300c91615592290310b5000d0048208076400a402401c540c001001c404081e0320105254a406458604040e1801e042c000c034050000384056051080024426080c007003a022207401c0c0720280301201d19007030220345612a1000d8044803480081001901c0146a4015803244c0e0254104129280710041040b08c0303a032040d03880b298160720500c4505d48a00d4056103039204240302d602c0c103403194019075440b1a0b01d004200c8003c00940d50100c10803031656006002c2c8481c80040344007039071400545030040b0b00b59130380b00c10340941001740058500d0700312020b00500c0d0b88980c40301241c03443c080c0d012404840c065403260042500480c4482800b41c0020138115690f030142c0c0e84503004404c0b98103a0304 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 457680206 1250 457678956 457678961
    0x5012c040b121218120705120f010c1d0f01091509080615010810030803010b0f0408010213030c050105160803060f06040603050f390d15050a1a0d 64
    0x1c0c911075001c2d540c002000700c80c810030041e038100c1050030304500c0d80b101d0008411005898001c075016002d6881c1043c40e42d00700901041b01c40580348100c0d0611450201800307124030f002c000342c401c1d04c000d40ca001b1071a8805500203041c01c3c44141c0c003841e203004c0009808107010058000540c480d0110703400200904c4802402001c40c13600340d1040c60700c1581240c0c0c603012685804000d071604e140d00300450444881c1940d00241080d4816141920140402d1460785c555448d84014820003c02c52000704e0400c0f9035031281401c4030002c25204000355200c0d01e000303a01d211a001c00f440f08882b20b2100400009041d4003d00956140070307540d101d2840e043c0321030303120301d859503000408141c0d200c442c015080741c1540d10071024101608070390341c0004052812a01104185802824031860700c0700030f00c2810b8664a0600e0f545800c0003900001d2259284a8a010110b07801124446108181840a102486186000d0700c1045403022079011071040d6030b84041c0300c641c07142c0d4101c44071030f45410820140c8009254 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 457681456 1250 457680206 457680221
    0x8130f03020a090e032a0307030c1a0c22120b091c0e060d11040b04230f1c02090a0b0103060519150e09040f02010314090d110a0605010b030105012c04 66
    0x1b400805402c028440e40c50b41507600400c4100d000c6102c02c00340200344000e0140c444410301030342120315400d0600d9240703200c2501501481403a8611851038001a203580b500b2880300030500901700b0b45141d4081c1c41c0803039051a044400d07620038460309510303044114075000d2882d00c404090b02c4901800601400707101d480d03070101507030761142a29150b485101c01070440083c0002c1640c941d40b50388980c10304100b10510300c0d881100520070f64640001d81001c4d0740e0845140d808141c107c2d801d5000e03201c220442203141855071400381d40004006c00f0040b040c80a80c107e1100d400c02680c0c10000c4645810070403140a1104510001091650509005e0a010004030070b1041c3c0c00ea0401d1685916a40b0001c2d0141d0000c507421141101c03100207070b01c11542c0600400d000302c01d5088100d50b0603e0300d0380700e455580007401c111000f0030088205e27129010100384052080308d504013a042c40340390f85400031890300394001e100e598002800c10520107461161600c103038103a038205800d0342c40c41441c0b10702040080c0c004c2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 457682706 1250 457681456 457681507
    0x1150504080319020f06070e2709011b0207080d0f120c120506180f0703020715061401050304050303060f0a081507082a0708130f03020a090e03 63
    0x100804222074804002412903003412a03d80064810902c4009003011440484281164400010700207103642041a92019440c155414100381040e0100455030098044207460f1108400c0d0900c121480190000440012200041c0c05144101e101c03c84c0d89440d44c0c802c0707402c1034001c0035400c105148583d1103041c1800040c607201107481407144900c0202c5409581d180c0c0810003510710a02c10403500e000740c56101000b02e602004401c407010410315550002403020300d2810000c800101140e000e607065a41d0150051401048022440d81e414020141801809289440d183c0411295032160088921450340f01c0e02450961f1140005e1040100d990442580d20a44c41030b800309410808101503c1140303041644a051800c00c804080d0072100081d0088008520144040329060244002510f00c0c10b40c04014507640c200b05c0c140503540b4000c0780f184000c291180320000440500584560040e280202d500c00d2506641c2c200400490344201884c040303640080c05002210045000118000e500303 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 457683956 1250 457682706 457682717
    0xb0609030c10020c0a06110606011b0f0206042117070302030a0c0512030a0c11010e0705091003140304030b13020904020105160c0801020a0e0f010212030901060e0103030f08060102010903080115 85
    0x68040001e10450406e40004001500813101403054031810041d003600424203003004042d0300115041084405901a405886c0c000f221040e0811510384400b20b0300101800c041c990080305030500d00001403000b00724181c6042070410000c090b40740b03000044400f010b5164005500d81030a0040a032a0031038200402e0743d00303001c1d801e50701407020310000085125100004c4005600e0f44a4100944081c00403003100c146680f6015500855070300008076a400e40f007007101c566042d551048040c00141c4510307000100607812103200c82581c2500000600141d03031041101d8041c41c0d550360900f015a46034000b002c5d500c4a000008180954064002080d0002c18030f00701042c050502c0e02d5a907858002640000002d0f94001041080e0503888210548030b520201c0c3c0c0c25458048100000b503440c0310304070948040c100000041050ad0400354010001071000085281542d82c4d6420003a004030084070101d4049a403d0000404c1b961040c4200c10b8026850707201e4040d66420143c01a08820340590307030301d05004 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 457685206 1250 457683956 457683973
    0x9060b040b01271211091503060106120219020d021b09040b07020109021806100504081b120a080d050a020a02060114010201060305070806040c08070810020a12140a0b0609030c1002 79
    0x159620f81c01e00d9410b01819030190100205c0c1c091201b108401050011000380e20441c8156554011071028110340007440e0100a000000081800174850030070807100c180b051b2240245c1700b94021800310320405007038090303e003100b080c1d20b42c03007800d0f0301a01d03401c9620030010000070f8001103020340000e401651030300c000030b460000c0340e010075aa401c840d00c801a505040070304018140c41c10307500500c482555460164102460402c8103030781c4e111403030180c2c0308945045001c4200c03625102e001c910400c40c01c03011100540c9050800c18215400010f90300c000301d04001c009440503006008588044180d64003d201980c60503d0140c03011130701100850455484800002c00305204011020107429020081c2c0b50701e0400d0718202030203080f10341c4108031941080c01c0c00c105500340800c0054283d008180096540c2c0d001c294211030421032003010520403460310b002402002030f0f040c02903101e480c28020400c2000f9080081048500448118552592051080e0442c2d030900441100d038401c014011100101c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 457686456 1250 457685206 457685219
    0x160804050603100e01080c090f070509090a0b010e01030c0c03120b190914010f0b03092a190b0f0c01020403020d14010b04110316020f0d0309060b040b0127 68
    0x1030380b050b695004040384202040c0070b0109290700140c01070450400421101e03e03040040381110b20003e1a2812100c054000215243c1c094822641d0800004040d000c59142c0390400d1b9000380300c040c40f2140040c8161504621550003485130b15004c0103903403111194021203540841d01d440c601d01e040307082e00c0e80f12002108075460307054040c0c0100e601215002c0070141042c41d18800c5410b034808003013040c0180001000300d00c00011200c019129070030a0560b41e6500c0c04a61407818008032a10440e5001e5030081c81301c0c841c3d150305c10f007040c040101c8001e1581c1010101a02840c0075600907a181654100240e5a0100b41440188800c0441000141c1020340d01c0d0006500c150200c0e03002e541500459405000b03040e000c0c0304000122008940410100000304007002040c0001060000c1c02c091040070520081c1c02007020440120b8070340b0480300d09041e1030000070701421118404131401c80c00c00404003c6031070103000721031902206a41c0c020018400c060283c070110368a030078000e001c0408100c0031a41 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 457687706 1250 457686456 457686469
    0x902030612071203120b060a232a0d1d0118030803040b090f0d0c0204150b0a120b0f010309021c0303090b33040b0d1a1b16080405 57
    0x20700624010100f164454103000c1c045094144149040500d0320b0b0048583c0d81c2e600081d43c1010003540740c01040480c0e11800c0c5e03e408a80400005040400071890704203540e4290f6264141080c44103804070851b0940f081d643d943c18400d1402d6000c40e43d0282000d20050410f80f6050b402181403406c102032607c1103401000718595500140c1c0d48480c0042000706028511b0141604003e41d00001c1002000702422a601d501c0700c9403414040041401143c3d040d9661500715480112480030301e01c021680d9440b19aa980d4850b0005d400801c1c1000700c3e04d5001c001c20b11034144582405000d098203a0303101c10044008022005041f80e0100110420091604442c03013004002031082c2c4000402824a06040c521407400502c1029480a0410000c6041107080d0200c22520754203d495058000e030340d03000070040e20000340e5440d000520b4002207400c2c00040c0540240c840740300c060300101c0e0303100c1c0e0603080111170030010840359121040080e0044c5040c0c0b0344c031a00c41180241c01c980d05080e1110001380c10b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 457688956 1250 457687706 457687709
    0xe060f1504090605010806060a0f0902031914040203120903070519031a01050f090105180406061215060f0e0c1e04090b030609010b15070f2a120c090203061207 70
    0xa0f60342d582d00040c0300e1101c04204194105108039001103080f8584031002aa00e501809048460381e00840440e604c01206885000310f00101c98052007014080006a169400700300c400b40d21921907140782c501c45500d0f00080340d8103254050081c2c18028100014003443c01550f1400040c9184000c100002151402201d03111868104455101725403400080094024203c8001442600044010070181d42c9440b45041d80c1821800090385c59903840c10458001c0040b40d02075000700e01450305040401c01c0514000c2164085440200b02c10f50325006c0c0c1c188881428002d4101d070076000408140344c03458500240c51001c0804142c0040c04030030941c1594542c0082e40040b40b160f4a038144401145000d1103000d501c00c5221780204818190580001c0da41080858403940310840000c0f40d100f031108038554a45601e40188a256089084122805100d0544a0200c4001c0e04540020030307409c40b00a80102115046003081d052075060400002c020b5001400c1c0c00e600806030620b6102506041c4031020 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 457690206 1250 457688956 457688963
    0x60b0a030b2b030f020607090603090302011b03140903130e1302031903020105181903031506090f0e0f061c05070e090f07030c291812010e060f150409 66
    0x102d40c0015140c0a01000c2e103a4400c41c0540d000b240c10414041e40c000d6020017110b0141c038002ca0702607034a0070b040c3d004001c100e40c0545ca161100403125a881d0b0541c0040005418000e41001280e1310548080e86a01403c0041c01c03c00c2c5001c4010441d40380032040540d0441d40c0c8184201e0b8603c45030340004e1815040040010001819140b00f1007415028495103034408012410541d4502c1d10400682d150000d03521100500c003000e21069090601c01c3c4d2006040018035190152015201e81014240c40541c1c03003a200103503c030840115040d000c01c20900d01401014001b0b8107542c440b1410400c0c160040d6600c5c010029240c2071080103c1c10800105005200e240100c0705682010b41c400e07414409000d40d07503a40c50f23100c07400410004000290400460308440b403160b0488902c90041d206406d03440312240301040001c50750102180c8141001000040100c1d0b03203003075078101040d0180c26143d4101546100d0703041040022041c6242d038440301d034008180f0340701020f1290217000282c11241600800c0c1d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 457691456 1250 457690206 457690279
    0x1b090e06071403040b1f09060807080106080706020309040518011803090f050906040f15030809040f050708040221100207110906030d030e0c120f01060603060b0a030b 73
    0x11600366001002034004490042110340f030351a0a482d81500c5540203407101e801ca980700038014000d40c0c0b004003104060543c0c01d01c2444685d81d00c402d8036940c0c0459010704170030f81d440c0110000d070014001864a0803214160065410803881c0c9041000612008000c80510f105c0c13028503d01c42c800078401e50042c6010881c100c0c042910509008240030610340040081100c1c0140900069680c5400280e101004983c041500c403000c2c07004c5800303402c00724122002d00040e4030f408020010280068419001d0641c1c0802100e1f2808005c40141d40b010703600c0c0e0340400d2076274012901504107105c02c0c0c0340844802441e255007207030002e1000c0c5031105450308510010750110b80142005540ea169580440c012943c00e046400e208000030f03110090b8080344000e250390ba00c0e0202c6041001d10646410040041100c03814004d0703400000c1d1108a091000c0000d5403030443c0108105009202c2d000540348403003105400c0800d2a42c0c140e0040040d4903265600c45000c03110014402c4031014500710050001210 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 457692706 1250 457691456 457691461
    0x303020d0e0406120219030b0c0307020105100e01120501240314030703050f0a032c1516050c030d0614100516030c0201110114091006121b090e06 64
    0x18140c00e965400385200d43c0c00c0038020885228206904070721070f90111038100c402c00c0a4000c04892175915403008045030080d10401c07012210700c0340514071810b1a6002131049540b0110000000e009a00401601c80324460040c00340355411281154414418000040c91300c43c1c01400495080700e0507801e1400b000d01e500d0034420000c90500c0080721341e0700daa004504240850b500136200d8040c000307511007000404a0b21400b5a40b09411040c0300e00c6035040044202450b0280304501c60f0515407250f0f41510514000c8071940070704441c0c0b903210300310034480080110f2504e0001c850300d42c0301104803451880140b10b07103e007040092142400510219000c0186241d0100503c00700c900420341040c00d02c20240516402070311009000804554140b4281c07401c52450310050380c898134040d502080702d6103441c1d00c04080110020916001c0c1c039a80c8100e50720107003052a19403e0710098002d640d1404d90346054100041c2e240103000030400404520b9840d070a88070303e001000c0781c0312386c0c075482da00d03034441e006 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 457693956 1250 457692706 457692733
    0x80c060a0b0102010612020d03080408040320040b030c09040305031b1c0615091a070b0a050402120f0703060f06050d050c15192a030314060306010303090e1f030302 72
    0x7020006c000d4006258001c960503000107408420388000a000e10001c5400a820410810201c4001d10b601069207210820209451a178540103d411030303009600c1c20101260303038a130006810f03400da0402001c1040341e685685d0105c60680003d05481096540801c40c440707490345031405000d04c00004410f4a1590314180700034410b0300d9644c1c2c8610000da8101d5403e520320741e80170f0a0703030083c4c601013540d121205d004512090317a648951200500301d06425001d100c01610140c100c280214000ca50b40d20b540145c0044503a140d00180b083c0c00c8a030381c0130303120400000d015508140e1a82c4000304000a141d9076030300214a4044403a1000c90782d0782c000d0006400c183c6801c03088007142070380c0c20801608000700b0b45590115103c4008801e01032101c0144801002c0c2d00030b69506850b802c3c40251498203009600e00a130140c03440703080c100f60303c1c58094002411400c0024406048a405a40b4010452301d0a10360301ea50600262542c41010000160499501030344050350f00118031950051161048490303 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 457695206 1250 457693956 457693961
    0x1050d110d110a08160903150f050105010207050f1e0907050304030f031109010320130e060301020702061e0904150603050604090b06042a021c090302010207060804080c060a0b010201 80
    0x151070b00240742c0c103000121406a01c058440d0f0f02c407619503000068110130795000c1e40e2000031644000c00196000100e040c40d003000390003807024080302d20024441079880b5801640ca844940c0501034200d826449111401e140a103030705105040c030102c4200809a00c0707000314940c0a411100c3c0004204000240400c15602010b410350429035481c1c100110a906d4014100621900404504054850041040d60b001044820941460b03c0d41d282d0b555a048041951100b00c07217110b540401402c0b00000760050906000f1280090781c0148110300d40448114000d0b19003285410b4000d000c4014441c0481c3c544891083d9602f03500710310042141c003850b050004041e200c00805c864000d508100504001503120189039400070021a00801c048100d42d120f520032501e6408211211011702c0c44021550742c011400943e04503400c03c010500c1c25490f101903410401910000b801030703011200410006201c0c801d810780244c0b00b4074980b403074042600401490150246c5450904582d60141032900b983c091 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 457696456 1250 457695206 457695221
    0x10c08010909080301030b0403030e010e0706030c08040f080708070f030203030604050c1318020702130c02010b0d050703030f0c08030702010b090109060e0a0903020f0706020307061a060a0e01050d110d 88
    0x241c00b0b0020809503036801403103002c1888014070741180b9502050030503000350030505450041c2d000070401d00c1b03c021420f654400320b901c03895020030b2a048148070f00d28440d82140d88216080034444010300c1146c1d40b1010598031985080e01c40c1c81c024808000080c02d50f940505440740a82d00541e242c0c03c000080004030340d40030300f205c1031041c420030a880c071100a5080300300480e000300030b0004280201008c2800a8072032200d0096008110b0b03da2951520b45070340c4100c1c901880f80d0b0003000002c1d003240030f01c12900402040a80f4550100100704006071180401300301e90341603454900400842c03903503848015042a600340c40583d440300490305090408281460040c01c1e122410f0003076614094014129500c06420812420b448110007010315008003d2171070281c042c1412140800c1d5190310007510b9800013801241e02c00d0822034555210b41c0000801d0070040c000400c09442c008100301c0a0310614945000c0906004081c40311900d843c11718840c4589882c2c10240703da5481c40da07042004100d5100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 457697706 1250 457696456 457696469
    0x1060305161e061706010e060c03030a0501050442080a120302090105180609030d0801140411160201120612051e0a02090414030a050c0d0906020d052a010c0801 70
    0x50004003c410b44c003142c0b52801a8014100c0081919040300488a0050344080c05030006c100191800c1c00501c000010745c03058034000170030070450340c961003044191900a42c4034204125608589051091500c40b07903001c806c200c0001c0e240c441d0400481d400e01007803581c04444103410044d40c08080c0004074088202150032440d003140f500015400107403040c0507006003e0700c00304a200e5655015100c403011110000d03c0201240d03100506904018801042401038280c0b20101d40d800c0002801c082c0503c00001d03502001840c1044c01050145032004e4074010141d0400c1039000e21002c11010a1050314003078a0403201d03d9403062403a081c65807401843d24410403840740405500b884903c00894503814455048600300800d0312182000c49441520841d5529076010000f518184503030400d00a04030b4030b40300c20640d40d40103100304090300d00c006107105d12000358000800f001c0c6141d1158000300ba18802c2c03c4071303140c24900f501c1d514480541e003214054019a5541081001c420341003040d140c01440d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 457698956 1250 457697706 457697759
    0x5030618010b0a230105040503060c0318030f040e060d0c08010e0d0c020f04021e0d0b010908030a0906030c14070c1a160b0a02070f11090709051c050106030516 70
    0x2d000c1c4d001c000c3c0c416540b040400b5454051501d45560301c039104481c02464001c3c2140d20b14182a00c01c01c0840e03006a44c0400c03100300040710b0300300c024400b00503216200c0480764040d0a00b03250940403181c012008024a9000e210210403800103960020750001408040f00000341e030070f00c0c0d11034091800b01c0c484a10010300104400d69030050351603540204a1150030ba4016031505000c80700010070062107003100010703080118600c4041e181503480980c1084003680c0e040c03050b603075550400381c03280f107404800c00000c2c01d121010700006000303402c01041c00c506032400c0c0c94404500c101e1000f0310b41000d031007140d2405405c181000503d40c0a107000f1007002c200c510301c51034a01d00481c012203007a2107090042501c48802c0000381040c480b0350658802c543c0040424500e11498035102d509858240c040902c42e0030140081070940e407080185c007040d03560240c240401c42007801400c554010044000b242c4941d00c8900200c0050801d01c2400300c0d0068180b10244080d00f00412501210b410348601e448011 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 457700206 1250 457698956 457698959
    0x1012030915050c07090e160e1902180904110414010e060604180c090e0a091a011a090310020a020d020111120403030b0a3c08030702120705030618010b0a 67
    0x10f002041c42400c851209400141940b8284401810b0160074102c0250f42c035000440000c0218450940c1803082c0088200c5110700c1d1690201c0008900640c2e0300100ca1902c42c46800d81c190800e92000c1d900325020301c9070740f0300c0500810700040a03202000343e08044828641c00402012508482c041c0e00880b0841d075080c01d060410f810350004183c99510310502e07a444034241d000e11805006248050403402e10b2140c4c41d8600400081e0140241880403915104200d681224040b003916810381651242e9400c0319150400b500b0902298210b4083d4540c903004019288c40e200040303100901d05028243c0107001101801d0a002c1d0842d03803005406070030f5100c10040d5206c3d4809070209170741d000703515040c0003c400e504100400c1b001c000715001141140448184a02e040d000c082c440540c80982207203416191007041c030fa07001123012a100700d00d100d90040c0220300c0145082080118000070170001c981c00c4580e10f90020786800000d0340c00341c0070501c040e81e100c50703104800e00032400c01150646225a089 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 457701456 1250 457700206 457700227
    0x30703080705180301020a030212060405190c030b04050f010e0703020301080d030e0c09040606090e070e04030302090111061510020d0c020f0a030204050406020301080c09190203101203091505 84
    0xa000041c4264208100002c2001e01000310351400c030b21044016000f15111020070201400a5000038001183e80e5000000a402440c050246a01c43c0310071070740c51004954500b03001005000413417041e509042c1c60750921031441e1550f2042d103214098010f04a038103545421007070245003401038001d004150040005001c2c1b0b10f400104220b851146141c005103405440c48134604100208001030780c4100d0007414882031041da038101c5400d403074007002c040050321041d00c50203980d0a01da1144010344207103a40003801007400f07580a01015081814520240015002e03d581040e10841c0d03200d0100c2c0c0070501c0000c890030410040b03c08050b07540004d110909007188058215a50342c50001c2c41840c1490820b1202e48030400110010f540c085c1c014800c17401c20703280c01c0010390003d00178625144540314081d40e0b1403505815a03401107008a1108010301403050685010b0740c80200008000300e02d00e0310000d89942c0248600d400c0c03034003980d5034142d901d080688028142d00c1c5440391038100700e0b01b4040507544 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 457702706 1250 457701456 457701467
    0x408091c0b01060f0c151505012318150a140a020a0f0203010f0608010209040b0114030f25020d030b0102011a040e12040f0801060608040807020906221508030703 71
    0x54803c0c90501c008901c0000b40100d8005115003401171204032440d4155171000c600c0c2e004181310010b45d0007544641a1646c004440d041c0114420b252440380c1d190280e03003503030101c40052506145200000b802016100081a452521580100c1610000256401501c1c3e030107c0002e1550100380320181c85c0c048400070095072048411400381003804201d03058002c56401f5801381881040801007809510b940e020000d000b5040b550102e40168100300b8000305544c82407103c03010b00d488000e1000d0554855803128107a0307a8000b05120803410089030700311017038004010030f601d56100d994010242c1903504040182610000d065040c1503a05141d43c50f540c0c000344042c60170301d414040d280011a420032900c21850305000c4c06d01d907200d44000203404241030011000400542d007044000784105039964000700c50307204c01254003800907001401400c0051401020321070304076100920800030a01c2070039130341200340c0110b1040a940c2c0d030744250500d403044d054a03143e0004d16811028608025142d20003a08 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 457703956 1250 457702706 457702709
    0x504030f12030b211c0206160e090c0304021815150904091a07110709180614240f040209190801021209030a120f0f050408091c0b01 58
    0x4201005140c0d148580e101c1e034070408041600415801c104030030f10504c2c3c40d0068130340703074602e0b00340c0a12001035014100c41014460f5408039540101340b16612094020905400b1481410030003d080014500276540c0c640007030b01594080245075600d003454410880310100301c0c941c20400d4400403040081c0d00000200b4180041001e440340304081d004500d4100caa8400c2e0311001d80e005d45024040c3c014880001227603410000510f41e4801e05031981d680607555410010502e45069200c0c41c4107000313466076900700000043d100b50001402c1c6a40386c1d00c01d0281e80c000342001814598440070001c4c000c2041c0680641e01448418180748800c0c840d020500702402c500a29020b140c00091300311803a20344010540031022041000c0041c44d07111800107020354814034880f00c10110600204102d00c0002c0201c0740041c6003a150801c1d0758031451601d0f0301511801c280340c00e2150361003440700310011041c01030900c100d00c07c1c10340d00c5e9250804820400300701c10ba0400d50580c1040010003070000f0b107034188100e0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 457705206 1250 457703956 457703963
    0x513030f0e0a03141b03061315060e13030912020108010e0408070503030f04020f01030e0c040914010c0509040f050c251e0c050609031002300f01060504030f 69
    0x711074101c1040815965403440e44002d2030f802c040d0745112041c4c040810b00703055002d00020f009841a00e884100340e642d580958101320410050103488002588880d000d205605a0060221b14290703505001800600f04550094848441c3c03405c4008150b030240700314002d08450842420114481c1d00002c00c000c10500800400001070720100d028814068143c0d04a96807050840b5035070320301502c01652004007070360103d0041d0038850642c7c0d425800b9000d59100c10b011580241444c84440040002900d0384000588052501c1640d0403007245083c06566041344241c0c035a550313143e580ca01488110340114402d800d12914040071310103982642d00c111818031901c05d0011006460406052072414540384006003500c903240303a8004850810f5010800d164081e114200481d039440c41031000718419251026459007211007070b4200080f041e4007030907101d40c0da0a040742c5828a91010200c007179100210b12019810000308000403c139500c107155014042030b28107142030514607070ba5078400450f00c04004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 457706456 1250 457705206 457705217
    0x619110d11041205031c0507050d1a030105011202150f0316020c061c14040206031303020c060427180b190603060209010909050f01171002070309090513030f 69
    0x4168001c00881600c01806080c03114191078441407070301903501d501695000c00c0790141440660340b5072a0510940344039480f10b440711440e11141e11a1000148000780c41801c40004e40040300801ba03d00b40b28640c013030800e800686209004900400c840300c03080c03069074a800303801044131003070a4102005072600030000c9444444041c0c0d21210503420403548001c0181c1000c408601204d07007040c07400c0d4400c21918a6041040244c01c41c105001c0340c20b10171580690481b108001042a080b0450b603558982c034003030310594641c1030200002a4280d070042d880003464802076100301140b41c14050341203e001540a40030071101031022440158603108100c003038400b615460000700030031541b647c52100005906410440c6984070715041c4025000a43c110703000405120f004070300e89466201c1d0300d00801500000d42c480303070700e0080701c10185602c010441c0c04600401300c0c4c1c001c0d04c034481c2c0058021648a911000103c81c10b0042d80d00c216800106062192100c2c41d0340d50b03000c640c00505884042d585403912 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 457707706 1250 457706456 457706471
    0x1b18060102030c0607050703031b0f0e1c1b0e100b0714031b0f0c061c0605130507140403031215081b100314010b03060f09090619110d 59
    0x140c0c114000d540d0f02c807080d40210010081519841001400004d00c00d84080015044001480e2103c8100c906194080ba034800301500c002406075410070801c1000030800280030717036481440f40b01b05020040072203442040b1001800c12084405040e00039042e0141032503483d1420714500c02d0700784a1481441c8070f8500000c1c40600340401c0d045801d00c400c01c0b103c1220f98a0160352600010055400d8013038440b400307064003400070f4100110750140c050600421007030402c10001d6072201000003c4001e030780025541c40c0009140d40780e50b500041804200900042c0600e0132000103003980e0030142145170074800401c010300000c0c2d00304440a042000c4a640081c0c8113485c1c0d458075515680d960017802a9104030410001d150740607092840d440c070004c3e100507501d41d06552007501906d080a4000b10b0f071006110060008019170406142d002800511010801e0114004641c4084047d02c00c01e4090300282d0802200600c400c2604404e01c1d896902040700c600b403a890000e0b1343c002c0580b00c10f162a2100701c2c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 457708956 1250 457707706 457707709
    0x1211041a03060703150f0b070b01060e130e01020705070b040f0e0f0c070f081902070b04240c0605040b011d0f180304050a0b0a021c14031f03141b1806 66
    0x1485c6010b40030310103150044a46a1a0201c259086942c040b074140741ca020021070f0aa00c500c0d030801a403a0302400c0c0c0c00703201c50700c0c8104202070405410962219075083c090140841d1040021000500c103150341c940c0e40b54241201540301c1c0c5082d401140c4507540027800c0c40028210380205c2948258640d0304ad0381c44442c00d14004140406070391740a0610703040424030324001d0488002000003050341e50201c82605640c0c0819a640d8056803003000c2907030500b980c0c0241d58210082922140c808185402d1a03007410307560b00d8104603502501c003030301d040305408014000c038568903c1101008602c600c0c095000e14041800c050703c414000d1282d0300c0c001c0058096a0a0742080041d0b90207171600900c080c0c103064407481c01c1900b64014209030401440f4004420320a224546030b490a4642c032952000c507100d140382c0500d04654809844c2d030a540550010140803401d40c4030724000658413070400181a07010064041e860711401c40d002005020003d020005550307112100344c40f800c01c020414501c0c4d90385600 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 457710206 1250 457708956 457708991
    0x1005160b0a0b1509010e1906031104080d0309142a0301020d0e0f010b0d051b0a0b0706050603061b1222060519052406041211041a03060703 61
    0x11215081200d101e240d003c00070100002d0310b1200c20a0f40c0b90344030a0840410400da00c5a41380416584800304581030003054829001200e100700843c00c2941f4055403460810300d0640011210000203a41d40391200411000c1d041c4c180300d81015000400000c400c01c40d283c0c02756422200c14440000101440152a4400f0740689203107081c1007100300724213456a0301303070b07078403407004400700405946000440c4000d0b14000c0c060701400c94101d0010510941d600040142c400c01c032100032548100201c0e0001401c0400d88001e000b240c3c81050045602e050080070302d450030101400200345c0c08050704c51392030031103800360640e000b28031141d501c60020349615410104e1441440060b040c403200700361144052045982017580114980c88206102044016801c0700301c0d5010b81c0c83c1ea241c0030100d1007032800d0504080c124403000b84005c16803840c1136551307e0070b92445604180211000030705070a00010134640b510070118000c0c20402c00000107200a000039403102402031981c41450f54410000c1d00c1d04140340c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 457711456 1250 457710206 457710221
    0xc0e070503130c05060d06030b160c0f0606030c0b07060e0708150a0b0a030c0609120201080609090f06090d0806030319140f0a080103050c01030e06010605092209021005160b0a 77
    0x6000d0399543c086d41d92002c0f000d060980800e030f90825041d004503031190210020744501e40c5140ea030701041c52429a844410f08503650740140c03181038440c50040b01044120001100030180b868840f80d58108500c0c0203410780700c10400c40700040d040315034100700303040000c64090350302071290314a0322843d0303142142c4e0002042d0702c00c0f01d00e400203a101404000c000d1101499020f55138036031220404030b40d440303a04044001500074000d0000d486040800da86041c4001d140e900800c44405440c0401403000c04549003080c100c40111156100130006a01c6581001e0784580184094003c3c600c0d08290003140100b80d00704600e4581000b4070130301c850341004543c005494840e0b034048101c1e030b035031144401e00400122003030005607140d000b6101c40c0c00056002c0c0c4155140030a680002d0a2140e18002090750a60050742409030002c544181304822090500d400c42503031150b510000071030161a00501280100385550982886020060800902c0c55070b00340d100b03010340c00610290140c0c1c43c549640081c6c20710 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 457712706 1250 457711456 457711459
    0x206150634030905120115050d0f1709010306060c0b070e0303131202040f020c0703020f04090510060f0509010806060d1104141503030424020f07030c030c0e070503130c05 75
    0x6a50301c5604040e84150040704070303078084940403100c00002500c28200c50b20010040724402800c80704100a050a1f09940070f03642c000d521900001e003040d01c44136080c1209919407004440e00144c03010456815108003c081c0c445840c0c101d0b22060a0f41c2c03000d543c2c80c0301410007824031102ca80d01c4819a601081124152032a0149018a1340da50302c84a10145045100492099041c81034010315003c0d1391094400704030405005004103461a024043d040d6010340310507800c0f0b0340395a84c22000c00ea040001e0361000800320400660340e440c21a645c1c922203141c0d000750340310722a410010084490001029070300310310100d4100040c44207501e050070001c120b140b00d1607001810701c1c003a806c5104d040007140e0710400c04022500311461b40300040640ba4403607801041070424509542038054160fa140c0b040321352002d0f004a0b4680c035010751006150940541c0100c6540c9580c580030310810003034080c1c00008001580c00020141002c0c280503009000050011001038003551200092003404440e02008100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 457713956 1250 457712706 457712797
    0x3090a0f0609060f02072a090608060405010606020d0c0605071205041b0510050703050306060f0720040b10080613051911070305092202120702061506 66
    0x46240c108080c10b48403500340ca00d5441c0086014180301107008480159510644e61240d03101c500d524003147c0c0b1006208842800c10301c04022072100711901c82c5101070702541d0010071080c0703014907085003511256000801150807001440203c0c3d0703004440341080d0366001001180a030340b1060111940d066000404141301e00b80b00610042c01a19201c0345a0304056003e601c15183e04c9005120179001e10003410b40010348200210408640f092015540181c0018603051074600420314219894208170415503d40c0703010100c07000700d0f41c1c0b00180d05140e04404e44040c040607103050001460503032000010400c0c0000400014200d94940060642840342d080c0c0400c0315007041c9022040c80c20000f030108090718031b010b00700303404428440705a602c1c1c44d9160f80e0340c901d00044141480302c1c01c06411088034440942404441072841d950001e418002d410400040051801c400003e00e8504094040083c3c0714240d03401d0340c81501c0707001c2224008049804003180c51254002001006d81840904040190 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 457715206 1250 457713956 457713983
    0xc1204021c08071515060807030c0201060803070605090d0e06090d030c02030a0308070f0815060a210b1f0c021e150c0609070b030105240a03060906060306080a0803090a 74
    0x810740c840d215884c82c5580070003001031652640000704500b8040e50340440c1242c00040c00d1188a03821039480d1403c140b001050b00eaa96108951031078020380c00c11111691100c0c100302208400b0003842c43c0320800c030f1409040100300c0c440030074000e01c04c2001c01d40c007888070f5a2003502450301031500c40f1001c039400781c00c546007807446040003001180103481b07280015881c1c003600f2244074414281c01c0c0c001d0400031414034050041e482000310300e40c030980b42c040901201107400d915100d801c200794115005800300c041000c1e5845400c00c100603644100000b403004000000c220750581c816000d4ac002641a620389003000b124014100c9004102551150b021440854125440b100341000c1e194841b000c4c0c045603440d480b522607103500c0301900c1c000c403528118203100401c028034040382d68032040581100c180d42c4000007422242c076a41c4c40040036101003611a01d04004985640c400c1c01c0041c000c92804108090400c01c4054031150b10f8030015055000210102e02ea003030007400046403a40d4170007a0958440c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 457716456 1250 457715206 457715213
    0x1e0f340b04120c0507050d020d0f0302030c1c0e0915040c022505012114010e070f1b060b0a0f1502011416030f060503120705060c1204021c0807 63
    0x150084404581d502c2c0c0d159031070301d01d190203411642e810903030140150001c20700702402d0007614403070001e0030f9034081e400307400200108082030840c900d5a1f02903405507560f9001c06841d18580150752505c1c04600070440e80305148103034882e0a52241c07410489150005482d0b040f002c100c07100000c0309155100e454440a00700302c1d500041c23507440d1106030310184030264510f0055045100c41034400c06002c6102012004040c404000d004640000348440004030030100b21140e5100e15005d80060707003514415018069000d40094420000444034508415420b015600410b41d900c120000148925225002441d25981c1c00716240701400f0079140352000565540359108042008202980140d40303040e00c211901e41825403400d00c02c00ca00c1c0140100c100c95002d0445c0104402c042d210348040c1d0340e16000c250383e68140000b0707070700c0000c2d4031007151a100b40b4140076040c0a4007074042200d03090300b0030040ea42d440c7d0914111364081d40448280b071002459000442d041c800c41440103010500020301041003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 457717706 1250 457716456 457716473
    0xc070305030d140f0114010804080d0504030c14010903021b130c030209091803040302010e01030213080715080f060f0d0501050403080f15010806040c0e0d081e0f34 72
    0x410716500320095040e140c0c003094845003d006e000f0f01c0303204101101e0004495000e400c0b11508a4403540490786810302c9100c1100444605541c100d00207103d0000003400c2c4941000c903001c05089420080103007010f16540650341d0912281492103090110095000a9a507881e044022214071070701480b4101706200c0040007584151038041c030800050002c1543c00048508240070b509292000f140341a045400645004040b410300d981099002c1003070349045500303000198000c0a081d0000d02a180c00c080ca02203900715512850780421052a04101c0c1240382d80d08005d422080c1a0769451400001c1c1c2c000ca49000c0001d84086c0080d0700f03000901c010503621004107446034510001078052929421a43c1010f40142c440c02c600082000c80031508e60b00d440c1e480340300300b00a03a08000c8003000b00c10700071400d0030040b07810030381f072280d400f14444488120b180301504003158002c0c100f0780343c101c40244074135540c09140210350030700c04206400c0d4900d25250001c11412020144004072001003071030007061 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 457718956 1250 457717706 457717721
    0x61a041a1203040305070501140d2a23070501060b030f041a04020603060f0a051309110a060f0c03021002030103050c040b100e27161b0206040b0c070305030d 69
    0x15000981030761000d0440070007030703500390395110018081c210300e408011114454801080701c0528010018010200c046101d0680c4001410718844924860014001e202c0e02411304c82c0000c1c04001d1002460003011410220079000305c2d00e454980315406401e0040c01045203400c0070300300318400030521000f05041c400440c490b620504d9040c2400000d4400840010002c2e50001d4016000b407000c502c191401040342107203040045d002d0900c0a07540c00019070614003140c0c1c0f02d180581d40303000e501c0901c540d001c254296544c0603501c0a29180c500a001003180322111610820851007552550802d84240300051041a50803001c0d0b45a5840c0c2c1006a10395078401c055a20585c0741145021903401c141c2c2c00c103290038480b034440346034001000d0706210601040000000f51074681d00c14401801000500c414003a24070141c9103140340d50345400c003901c404000444444031a4006d141000142d071800111001c2d1003061a08a450306503c641e081e00e440841e40000f41a40004182c004078245154040d86 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 457720206 1250 457718956 457718959
    0x7080f041e09090b06060c01090606060e1507050c0910120c1d060622080106260604052a0a081b011404060c020a0902030a05070306060f0903061a041a 66
    0x28030301503507240314000b125404030008242403203201c0080c1081c030f07181e1b000d0500100c4800010484000035039841e07040b21901d270000d402094007042d80003010f0130304040c41ca448640611440340341c01d509450391a501e0344401c03d43c0348a4100000041c1240144401445c010b00c44050380c10070f8040c2503d8803c0c5014000d0080076030441c00c1d00134011000c400080c80500030840034008174603102602ca10b080007001048441140a0900c07040000c400e803092107080f00511200854444000d44420f1120015210b030071088031650190741484040388001c00d12010002e028140940034400c4440f8400c50390f000d10b80856401881c200c00007030001804100004400c03204100580a2851940107417442d4216045070852400b09200901c24180100841091140010300007142c071543c8240507401d03030340211000e441441d12001071092441c2c050180001400382303400d00708048191420000d2103480d042c4005060152a03181e45124101d000b1115081004040c0040c00481c14104820140f040f5542546 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 457721456 1250 457720206 457720259
    0x20106030317150108060102031c05010305150709230d05060702060703110f0c070f1d060a0b030423011401080d0207050a03060506130e060610050313020607080f04 72
    0x4407081e00e00c601d0b06441100382c3c2c2c00e080f01c400e03452401101c4011005000c1350640c4420032440701c54078010300191850106c269004629981945000707400c1c1000d0740c1011080ca550001400f04468010061506585050000900b0210310300f5900b25114100c10f0301640004d868686e2006225012840d144039104e81d4080310b80584500d00b0440855070b1100e03841c076410707200307209031003140741c0c080300074030310000325108481d56141c48199803409195a6409021300d0b003960a00001040609450701d0307444103085402c1c80f00780e403400b2a24041448020001088204126110707090094005903d04005d8840c0e030017041004402540312242180a02032501389108004900f03000750310005031801641c60203482401d9540c916a100c9010b0301000d022180c1c0304001d0303d030500c0c403508076201e446401501c1c0802014a41488001e0000d0041908040c00410404108000481c110740b0764240c00140d054410a42e604083e0a10b005180100d400e0116030000c00140003139503001807821100111240007d0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 457722706 1250 457721456 457721477
    0x1803011d0a0605280b0d060e030307171303050c0f0102031f0b030112260a03050412030905070b0a0509060f070308090c0f0f03100c0f0e0a0e06041107060603030201060303 75
    0x300d02c01004244c580c58982540304107034840c4400ca6002200910b5018201c4a400a43d50341c5240541310403c040291691000c802c0242096000c160302400303400c851054492814003440b4040e52140c0060040c0174010002990040d985d002c010500580c4a81c1c00215241d040c225801606100d1459401000c0601880041800401581124100c803581c7d50015000b4003580e80b00c40d04002004100c0c000c401e51035441a441d1044400180040032081c0c0c4c1c00104c5262a1400c51515401e02c3d0864040624210040000030000100e00003620031108407251103a48030b8801316410300c500c0b01c4031504640d0100b60b60240654882c00b91950300e22036110505640c0c1c0d61044507035204000e000c681e51109039040081e0540c00c022281d110394050280a0764a01d44e8960300c1d901c06d4490711080c0a000596089d4020080780d031111003a180b803081218500400c511303200a0320300c80386010385560f1045036511024070301d81d0301010480704c1a55100005000c04c541e2410081d00800441c4016030100307000c20403 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 457723956 1250 457722706 457722721
    0x6063114120c120a05030304061d0c010c140c0604031115030c0f360418170d09140c01030c090e0f0411060d0501050a0f08031803011d0a0605 62
    0x31003200119608000c10100424108100f003100c904010262280500d054840100c0d80600044d44201d01034100442c03240303150581105200306000d40e241482e00800d6406d8402d0781e00c401c00360b40f499004181c500200b0b100841f00790525981d054040e5201c0400113000081084510940c003c80100721480c80141c000744460752030900c401c0720300c99185d078410094030300d080b401e02010b0003000b4402032100d04411030042c2007160426040b900c0c0410640d500d500802c039071a03e40580d8420040c081c030b0100b0b000703240380d84111840341d101440f00d407074100209201c918100940d12500100703810070705018182d040340d5503880d100d44204140500082c01c02c2442111a402001840201c628090071102c04c0c0d036a000b0140c2880c00d018104589480c0494045001c0365204000740c0340c1c40816000c0080c441d4540420044d446060381d1010003c1c1c020303150308009242c00803080d5034201c6800c02084444011100c0028010500700040008084802c8000c0c0c0540f0300c0000c0c40040c082c402c03201003029845021 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 457725206 1250 457723956 457723969
    0xf140f01090302071502060115110c04050708190204060e1212040b030106080f1003020910051509031005070207031b0504050a021225031d07030503030f0a0501030b06063114 76
    0x20127030580c25088076850400e105e060000101c4640ba0199400c0c4030b403560020f8280d0f2001c0d900c140001d21190140000c1aa1305121580400038140046292510f0000003929401ea0b00b00c08c140710310039048211a82c85001d004c00320340c4a0028151680d0340c2c3d291040e0700e04642007801400c0000303e0380000a906044104500d9000d0884060702c100300f5861a801c10040903802801082c00010516002510313844003000c00070b40451201a851312004440d09040c078101144003031700005424841404805600481c41c0b100b0381e80c00c0032124841d60704070001d070b540c1e03807000d80d2105401628103020851382c1c4005030f002d0304d079200b00700c421903040b5180c038030b030a9640515400400d0b05440300040d102e0080c2d4020340c48081c456030002d01c1d60f46445c02180341d0a0420080342d0007524140c00c0001004501c1009201c0d5542c040001d03d8200325550564460041856004005a00400340021000c0344841e0340851602c441c4040c403104001130903400600b00707042e480b40c4524160803001485000040c030b000d4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 457726456 1250 457725206 457725209
    0x41e0807030308040212030c0601080f010c0203030f0f070507050303090a03080f04022206050a0801060510170f0403140d06030524190603020d1a060a030f140f010903020715020601 79
    0x655802016465580070441183e01001b107a068134030003000008080b4100740141402009144060160301020340303d064203643c1811014000c41d0420010003609061000485801c0107444800141a960305038069401e4880c20601038610f03c40441003008009000031020a0541303e80c0e2030070081d03214041c600220340000c0d14003c2d07011103030013103000c1c07540d0005990060380d010302c0034003240d21956003000c10969a070680082120b651074103030501140c100124900c0c480c003032524100214802c1c0c1107051f07241c42406880000d100f50100d0104e41498030440d082d4080e5041034461703940e9049201422402040365200440c0c0782c0c00b0f408004100e11000d0b80c04111956107d0440802c1d03540d03020700808094110040c2040c045035034403004800745c0c5480700b607070184d24031900720305040740c044001801445c840207120500c030303800072034042c00021200c69030a85800d134000440c803051486214124141000386000200301c1d07182c042c011b41810384c001156001c6a0990440800008048000301e07101e44d000d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 457727706 1250 457726456 457726463
    0x706090e0a240b0315090105060d0207020f040609050a06140307050d150e060901181709041113210314130806070e0f0108011401050d06050303041e080703 68
    0x2480081e5032250036800c0034104403035409221840110081840e400110103801031801580080100410056900318560400740202e40e10b80e840d601d81000562035110b001e00031285203402007000800c5446032080390803901c20080050100a8641c8404002010300700d600d8000c0c541040000100415410108820884050701030400e060411041c08401129054216030b1386103500030360342050315244103c0d80b0b004400d002502c882c1c184082e0941c00d4038080241076160110440100e000204520b2000c55900320600c4941d07100c82407071001400a1519040d1a0006540080e47d18250700c00962010f0a40c1c00549560700441d100c010042014201840001c0201e9100c40e4940c580b000b42c8005000c42c40d090900c0400e1098a4049540c1010001d442d1840452000c005643c001d107064080003c040a0030310706140e9a40c035100c41481580400c002c0390b070500a0000380780094400907040440a02005800c0b03030342c0e5541d140124180210011101004c0c000380d44c1012402c46004505003040720340 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 457728956 1250 457727706 457727729
    0xf0603020a17070503030c0a0309080606090a0b03030c0709050a060f0f060309020d140a030e2205060a12081213080405041802040e160b1204140a05030f040503070609 73
    0x40074158000810003201d003220a22940f80b0001d41680d0400c010484400c0b09800303401d1044c264500500b1003000386e00a54260707000501008281d4035440d240951155041c0782c0410200e00c0711011038154481c0d6180050203006100c404104030185030002401000b0f080c10400c0758a030b0300c02c40307140494624099651a00323002d59082210074071035000401010300051900b150b4500a603514801040b4030021143c043d00902403410a25030440c075401c0340484241c441009142881a420402801c00341c68610916650300104d640f90329800290320240c00006a078941c1d80c192400c102219400c541441c0485542000020304c248607400c3c0c07040c401e903520018440c1810f040504200142001102910318200c040c501c14016a0300c0b806001950032104c2c0c05020550000c502c00e400303844107900042003d803c2081021700782c03c0b9090f011540a50400f02c0011042c0c2d8240c482400d0407858000034000c2d01c004104034540c0107c8000400c1154811012148580e0350392105903880aaa4030488141c82c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 457730206 1250 457728956 457728959
    0xc010c020d17190905091302040c1110020c100e03070b0406091a041b081b04090803010807060314010b040b030402030705101205221401020d0c0e0102010f0603020a 72
    0x3016800d031490107124000d0300614a00034214408103400c08103401c03030b401000070850301c0d070f05030001003000150400b80c40d03180283c03078a124105038550b20144000d01895440e0719210720030b4407a10000b0110001e803020707640c1c034114034598240607401106500030f9500803040d004c412a5054440c0d06900c81200c400340d42448000c1d108d1500c000b00c02403080c1d855a45568003000001c0041070b21444010311440c04500d9400c1c5414600d45c85062090301d402d0250341101e09011400b0001010406c401c0802800c54480701003602184c040e026040d401041081c02000101e2402004600402a00e03103a81c1c0c01c001c604a00749400f00c01c5042031107120203104003013000744640246070b4000c5034002c2c0080e0854812a0341c3d40701203a80b26000380d0303078207000030000c3d0f03440070b8040654060503070804124903401350302e00502841a4140542c02e14001c1580c0111405107181c01c81c02e4054500340301c0312442c1000505407408003d4034254602030454019480d151001590401c14812442601c0e005002450901e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 457731456 1250 457730206 457730209
    0x140703060e0d200d0f120f02042903130311010204080f24130f0b010b03180a020303041e08010c12050c03100302060904060902041e06020a05151003020303030403020a0c0501020c010c02 81
    0x3601c4240c17030b103000c02c1030007000e00031003600902400d100b6240d050801a55640b03441098004602003602115228404402000107c141d0509032a0806145544c8100080c0c003407400340d410401110350395006500204002030700503000301c0e425071161000c03010780f13106c442240302250071000848115020424404d0101d00e00034009441400014402c0c14003222926180d240e221070f0b40c50903400500300440000c00c0014a50810f400c002003404a800245015a03940c1e001a4507400b4901801603017400901e0f100d00b40404031a1468024044803000304401006040001d20348044489060445401c1c100070804d002c2800c01240d100d01010b440c0360f003c2030704641c00c2241582c042154164025280c581c04204420640700400041c8080381c514124005500c00b900060940c0b0750107242950401c00160740400ca02007040340c40c0782c0b109a1403056958400640c4070400c90141c0010f905840040700304810980c0000d10f00c2c10940c0181e0040200c7c07543c8400490341c070940b1841c2c02d40010f881000700e1005 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 457732706 1250 457731456 457731467
    0x10503100e13080706150b1602060315150703020d0c0201020d1116080a0507080c0918030403061a090906070c0605040c08061009110301030f140703060e0d200d 70
    0x202c4880700c0080000551601d07904166000b0f183d040d240340d59981c20200780d1428001030030b401440003443c5581401a0302510002c2c6001501c0040c0c065000000001d0005e8407440d01082a40b0f802040e00350688000c0008040325005240b0440161103004020f40100340205460071411380d05a00a003a0910b445108580c00d00409800c600c6610400f42240301d001c0003e14080c01400840e030041c20a00ba180c1041484c000190b44155841c0e00241c680002686803001d1456004085421103804060003032035191543c401d0b1351003e00018988030307242c69032140e041841030301e82c1e000300c03400c00007034507160340240c1c80d11016036480c0d0101e43c404188000042480d0011a80207005030360140c030103580d400d400307824440700b11f0b030420785007115850a0002400b940310380c038003222100b40003504542c110b1b0f60754019011543e00103402e50141150010100c1c00030000340c03019540c403900900c0000b001203081e998580041800340c01050940441040e0341c81214184200d903001e000007031480d11013903071082d0b81 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 457733812 1106 457732706 457732711
    0x1c020102071d1609030203060a0605130c0f030c030b0405010b030f07020106210809220b010318020f03070305031c0b010305130303050702011806050411010503100e 72
    0x1400241040264000055294040401d070b407440305130360301c02c002e0b0f10082d0304d807060908202c8850081d4002000b01d42d01070383c0c0350050020005400e029214400340c183c000501c080d0300e02c06084d102c0c0d04001103009141c00c000904100c41000b00f01555000d07000010300c00400003e02200464058034507078000000e2008000032410881031100c42982e0500480c131a036055400d40d414484608219150680000c081c480e00740d07445651002004030004075104c1c0c00d0320703185000f485075000b801882d0320080c803511880c241210340e0303003000039541e09400710310b030548105d81020000460070070090240c0f001c5505c22240d405001e03100c03103080e111083c5155041509100921204030421040355a0b1030382d05080100c0c0b1a610444201d0062418840484600641a0849041c4402c6a110301d00a034007400c03043c82c0b00c0d0580723001501c5038401036070a5401c2c034a5a00040103d03603050700c600754 = true := by decide +kernel

theorem cover : BRFrame.Cov 457553956 457733812 := by
  have h0 := BRFrame.cov_init 457553956
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457553956 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 457553956 ≤ n) (h2 : n < 457733812) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
