-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3120
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:43:24.313874+00:00
-- url     : https://prove2.me/submissions/9a1f70b6-6a86-4ba5-a1f1-84032aadc52b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 560971223 ≤ n < 561151079 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 560972473 1250 560971223 560971231
    0x3050c0303120142030509010b010917030f03012706030309051e0909010207170a0c2012030a17150d1a01060f2c100e0613051207030b07030203 63
    0x205900403200d040306a00c402d010140d042c01800003240314035101400340c20341c0c6c0300070020200740c2d2410031642e62030f80e003000a03c0c0a40d043d800c000319404d0055606245507108964013400d05000100c00090314180a8404085540c0054002e0105804004444041d0340749804002c0200d42c800c10140400d0810640b03581300031200b400c18040c02d5407010085607200d14203840400240c0d400050007800e12100d10020355080d01017039003880c901220351900801e01121800000d020380f142000c1281c06c0300c40d600000c0c1009500600c01405c1c80703121056160750342c2c4030300c0030400802c07200407485030020f4100d001b091040480c044900b801c04a410308000da07101401c00115444526000bc490940e081c40b401c00d800780025481310007180398031a001415040d810911410441102070188001000038045d07415100c10030390b44421407596a80c400d581e00110220665042000455081c40e41003801500b05d044a000b0741d52082f41480c8040346e103445400350700010b4900c4aa07a004202180d00c07a074015070740 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 560973723 1250 560972473 560972519
    0x2403021608160b190b100c0813030812150607030c0b043905120d03090203120f120105101b1502040e090f0f1908120f0103050c03031201 60
    0x41d41c8040d07910b600f0000c000342e62000302401a01e141c80301c1c0645510079680103403c100c0710740c0c41c01d180d00d5a0040031450304440041c41d1003c08600d2600e041d854060050183d40e010202c2c68031601401521080328070304503850441c0313918210000010342008800c071040180c155681041d000b03c152140e41c0c5c2d0803006401100d000724100c58541c201441131300a004400181350440c000390845580300b00390201d298100a1041440310a45288900c0000c3c890042c54010706011510242a00000c5e0501daa044614262003000050b107005042c03940e0f0007010141102640144d0690300c3d0000d1010041481100c40041079081505281d110150001c0c50f521603c20000d1045003004c940100c0d081e0f810540c00b0340b103000041800d00860300801d2000105c9104440014103a141c05400401e59600051041c4001c1c090b0750100e000904c601c0c007044681d0804200c0d501c05031400c110720088115042444280d610b80600e049280c6946004803c075411480c61840758560740e4200500800c45020095510309 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 560974973 1250 560973723 560973757
    0xa0b0a052d040510080c101b050c0603150306090604082b090609020f0114090f030f01060e090f01020403031d01051207080117030319090218012403021608 68
    0x3030b40c0e036801030900c00c42802014180c142d2070500b030f1500d0110307081c0c1c0c05803007420f0130000f103003d481d4011954059800c89403000880c054403820200d042440b585581ca030042000810484e4400b0702003504c103180d1a042e41120b809030366181a01e034941c40c01303540090400d80100f18a521600352204503400d03624078440b440c0180d807499000c42d0125078602000f04c8240780c540000006501e018640503008200030300703104030308800c0014000c60511480491501c94008c0c04107000440e20200844e03003e8007010340080041a840300c3e2a03131039001e0120b4000d1550711030700a182d100e40c00c0c10300a0790700710390b41506c40c03000080050915030355a5180504060401c5030501c41e07400f42241c1a420701d0300641070341d141c1c0b83c460350604500d802c004624100300e0405d54000c0092080064212410780c030a0b5005050008030b1503110b02c00074440760280080b000400480302c0021130036585000a01403017808003030000c58140b401c4441a01640581c80e03e61170044034038a490004650000000c0003401c40502081c4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 560976223 1250 560974973 560975059
    0x40507171018090221100e0c0a150f0f0c150e0c1203030406020904060b0403030302090306130b0403080403021606030b040c020f0304231003050a0b0a05 67
    0xe550301000c540d01e0040c002050420014500840302406084034203480038040b0301503603004280b03d111100340b03d4690904000590300d0880062043e40d1012407a83c0c014465140c0408645a84004001021b0700c80c5450f00400909845e0145010210b58144d8548422480c00e8200580310064001c0340078040c41a80e2000f44005a90740c440303141e0007101c0030030024940801c140d880f07141000d1030107410700665441d00c2d44c3c0d20464001003900c1d80940d000f6400344c2d6402484004c0f0300580910b40c80101c100c0800f141c0842095050b401810320f000d416402c070b48035542e5000c003000451030004400b40a250b0510081000b09104a280962241c028012601c8903c518080c0b030f00c400640754407460001e0b59a40003201c4916150064400d040202d00c0108401a01650342c2c03616841035110b0825102d81140300d22009040c000e410340c00c0704000500000c0c4c8404d000f41c1c040d0203081d0880348501910300e096074000c0e00385840c003132101c155074029200802d624856240050300302900c182c8504c00740145400c031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 560977473 1250 560976223 560976257
    0x70b070b01122d03090e010b070809030c0307031a250e1216050a0801020703050a0807110a08040e06030a05120c1e030a0908060c2b0914121206040507 66
    0x111061a0007a90110000f4010f06009150200c1600040070030003907100100045901042503039a01500490b07015a56150640060715002c114040b0075058002c2140000500c80c408070901c51108010307810801c61358800751100d68400414085c0c0082c640155556140b01d0300c00d0407000890070340984001000250004400d1520151071070311424440040760074089402c0851500c0000c0070900c000b90f00740452503030003408600030f040064040182e140c0005401c0c0d8807680e00c0440c0c2708000c0e01a1003005010b4100010907600500811600d032500307801207003040c10b001a02400281c0c01c64003900305c1e2903a4007500b00c02c0358811082d403409441202540c018501d421811068405c40c030fa0700446d070715000032a018140200652140200380c01c0031041141041c82a800c6030407548030140d203503144d070f03002d01842c070569240b0031480d0361070a10707060300181000000c200c0640b141170403404403216410703042180c414074440d1018101011039100c1c003044942c105900801d4020165007045080c0a00e45490 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 560978723 1250 560977473 560977523
    0x5011503050303062403010312051603180b130506030705070206040e160503040b040803040f0602030a0c030623040e0309101d010e01021507120e070503070b070b0112 73
    0x2003a90309410000611110f49011900785101d0314550801c408032045c115000c091a0005200207092888200524480e50740b0980c1120000a03460b20394103281c111500300200500312500c40503085900005010030b0b11500f40040c1c41d00c0300c032402013880950b400c1c041440031541024150006012042c401000180e9a07800900041c2080e22880c0d841345c9065582c04065582e03248060007441400c00a010226206415156102c0d0708030b502240c2d2034940385480180d81e41540400b9101a01c00300c10706c074680025820403080d15000e0341d024055a42c45030f95280342a0742c064010900182c0c41c804901681c00c20703420680310000002c0c1501e041003000008134030118a0344902c500001c0588042c00b003a00a500d8103544480707828a41511703200c02150010b0f5407403000c01d40c18405203100c0c40000d00c00c00d1085882c00c80b1400c07901814402c0c9920940c4103541c9030498001c035840303409107501c00714002039a44140c0c3c48098100e0400b0045928040903c0202c2a80d0103080d074166202c019110507403001041 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 560979973 1250 560978723 560978729
    0x14011212180f0306021c02040b030f0408070f030c020f031209040b0a03080a0f0822060e0a05070b071505060d02060a0309080a0c060c03050606032202030f070609080a1e050115 77
    0x4d0701607510907060080d140303c10311809502e01c0e41071040c40240614130b00a0706480c3c3c040348083d0b520710302c2e845074203001c5418044c0c45801031003201c0c6602a842019482a02041d40d41d10030344005040b0040c9004164807841000c8041110500511000016207800d03000034000440180481603a5038403a10790002c0c40c0d008000440c04034209a0301003003e03550050450b82d11078024004880030800181038050708100300080504000d440d603c402c0748010003071001941d0b55520504070740d455680c0d030f40c026880350480c500544108403018081395141869002d80d0748111001024042e07028460303420050309821580c500307005c06591b2454400011aa803005029505051301e90801c0850715180182c00e44039002d00d00c4e010541480e05202c401c0d241d05c815a90032400030b1480074000c10340345682d0354814800e48000b070340c10710032640d100f9080a004a0303204180d88895507218200e54644070301c1981c0700c004440c0100602482c0100c61038029092003125a003500c00c40021074040b2441c17104541420080d0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 560981223 1250 560979973 560979983
    0x9020c0606011101200f0d0504060618020c07030b0702070e01140406090219050d0b0301020d020a090806090706080c0f0a020d1b0c170c1314011212180f03 68
    0x2090041c1980c12540c0040c0a007010002488070100d038031000341c48074003d0040c01c0c84600e0041048000a84110306883c4c0007401400b0810061401d410101e000d00400d2140860b0540b043d180f10600078028000c480c2c8402442e0000c02c4c0152540e5120004403000410b071600314040d082020843c5848242000c7c003c100c05100302030040041c00402c0107d8502c0d5100211311403040002c9521024061440a503176100c5081203600c0c1c841c003580034405409000e40c500d80c1544005000510003040758050104408550344070000341c2c1d11008907581e50841a0750381c0c0880c2d440b86608020151151400e2988440f2460070b160422100607600505500101c1824025802142800d001141c0c86190303c1046488543c81b030402c1580d03a241c4002004050040c0c1034110360800303028119000401c4201070105016001c041c0902c0804100001082c441190803400d035000c4000081071028050096015900118054024100b07008240c907001c00400c21000c0d0a00c5e10500002e1010701e8940ca13100440c01a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 560982473 1250 560981223 560981233
    0x303020720030715020c130f06091a090105030604110f120a050d050310090908040f0e010906050a150c020111121c051b0c030f031023030319050409020c 67
    0x31000b01400c21a403500a021010780303840c5020b450990009640401103001d440d8400e95000500c0941d0182c0550406084102c2c1495800503100e0303001d45c8004201020030765510280d5402d0000c200c0021820702c603069141d03000001141c0450344443c14131030b00e040c0003081800301200700303000f18034010010780321902c494010348400b5003482801c1c060700505001d985055403952520b8a03400001d0300700340c01010038040e590600c6404206940d0115006000400c1e03440c030395940e4484444600803000d000e2414070b1401c0400c009024100070380502c0030740d58950f00c11483c50042c940c0031140100070392802e904111030028050804c41003803200341c002011000c100c030740d00d2480b100003180c0100b1402e10510300e20700c0c003810404500c0c103604003010131100c40f0344101e544813800201c03180745d03000700b00645c1b00348800042403081c45026841c08034111780100c03801801003d0341d8021900d46c540d45c4000e140d0940c1003006034969059030141e0801034804203080460030681c0752110281260402e8140d40e0749030f408 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 560983723 1250 560982473 560982533
    0x201020606030106050a18060317090a09090b070c050c0901090506100221031b2106010c020a03020405070302040305100b011e051c0912080f06060f1603030207 70
    0x1050124907800344003a0003d1045034941800f00300005c030148104020201e01c1008003400e642d1507000b400c000c581000d0106107280d101c2d005040527900541c50345120394030010001540300706034010314100c107800c2681e8030b60301c0c3d845030801d0f81c0e041116201110b1900600c80c01c0c945555444203102e001e06164600025180740c410180300a0908503081c800c03d541c0040d04000c40f00045200f06203062200b5440c0548030344481401d4200f0101c00d070404401041b0114071603c86d90004250380d149000ca214244a1a03242c400055403042c0100e5406908920403603800d00141c10f0507040190420034500d401841d05a49840c1d880c1017260000010724901d490310b451400720b40e402844181d1200d0b90344c025800c10342480c0b9001e41244102e9942c403c0c2c42000c2c002c5500403c07869030046241700e41000c410120b1182403100109000c0046030710204559001000c942142031040a03540e8035075107148900d142c070f4041e040d00310450030124022010141c0030010040000c0c1c4484602034200d03900c00c017455100d80 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 560984973 1250 560983723 560983727
    0x10150e0709030c090207020a0911040515070b01210204090305190c0b0a0509100c0315060809010c080705040605090f180708010501030228090e15030c0a15050a05071b030201 76
    0x180341e400481d40c640144081b001607920412624101c480501000a000940c40c2d4014094011a4005507110207100c0704c80d8402c004590060030540c3c4125000700755a82c03120b031403602058030311040450ac0c400424040005082991041d08054080d0800b02d0404a00003035140048003006040d070006004030781c08004200c40080d8040d007000b1814400e00c014900340381615a2034a0051500503180e40b621003401044c0e0107035010342c00c82c81215150502468a40c0e0002e808128184c0c0c4000440d803074080c0c030410403403060009a004115940c0e03032030314080c6850000c4030503400041e40a6032110405400c00000d03562404080504088007000c44094504690003800080d4140c1c0990305060041200c2d0340c0d120309046003e9456241b4016032290012034210445455149401103036410110800f440101c9212482c15502c0c210101c088036403940210043c070410100c1ea12450350101c0100882d194000d003d10301400c40719840b45041410811661202c6994030944030407518402c00015007030003075503 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 560986223 1250 560984973 560984993
    0xe010e070302150a05030f0c0906030c0c0f0d05160312020d092006070816140303150109030203030d0c0c06020a08010e012304180c141c030210150e070903 68
    0x1d01c00c042e200c2c2070101c0c12102a00f1444001d100420030040c80340065001380e25123042d1014410003415060301c03403130120744440a07644800e01e122528490800050603080c40068039000020a99544908003015641410002000014220280000e014921000300114400f80501d1080c411002c11031010a0620400080e005000303100300d580ca01982417410b8403500700702d5811951100c3d200f0b41d1203595a001d400b28500b000e400030441500d400914200e910b00102540c0107041c50300340300311f00301c0c2010015600c2e4102880000d4041e0010700c80812414010761013a070500301a0306110f1840000c03a40c03018100e0b40904410f601240d130640050003606141c46e502405000042c201c0c4021401c0c0c0107661240d09104e024041c03040743c503150460001129140700300c0c0303050341c0441c0c2e80400303d40b101990500f50304d043d11001d0059521350412048440706800c105071250701a0080c12000c4110404103000d0f20800e5840210509079441c005003500c070303000d1100c1c840c2d0619900c81c1651421807a1280c1c60b0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 560987473 1250 560986223 560986249
    0x1023007020d0e0d0f1209050f0d11041a12010912110a0f050c041409010b18130503071202030307030f0c0504061b0c0303020a120c0c05090a0e010e070302 68
    0x1903110860048419030048690302c1480003ca403240e21135159441c211207091403149009000401a00066100c1e40e002080c00c81652411200418800c060078184080403208201c081d1100489020400e92030074554021500707640d607511605942101c4d080800c604401036100d07010702c0d84d50b61140c00c0c2441500e07400b03084007005070f18001d450341ca5412001e070b41d01c18a1a00c00b9202c400000411410480100321400c4c855001500c00d2003004003812a1205110044a02c40110350801d24022910318010b032072045003500d030384940c0340591103402120003000a040c4044034144000c0142501289585922902200440d0b0003190780745400388009068424116404130f0272070901502410860b0800c0c02da4069031888d20705046084484000d203011000c0c806000790a140045801100b40342d030104040c80075601600c0e07800d2040b00e034903500721341a40080380c000d02150b10700e1400b4003107458805013068211a039418007060016080d41d0300350071140080c400d40079640c401c03e01042113041c209150504 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 560988723 1250 560987473 560987477
    0xf051203011e0f0315021809070302070605060904031e111005010501031518020a0201020f0c21040503030d0903020a0510150801111608070821060306072001023007 72
    0x82c510315581c00100c410807600b15206250041600c2a201c150080e1494207100010550304827070400e4040a0000d600030001a41c80c2400c282c00a00c96091884035580660b9243d540e0341d01040c4841184004007115a000c00b00300031034455400304c80e000801580c81340d001e0301107000809514181c000b4080300c40711145c0c03c01404070003008205851440c5413041e06070002400259580030001403c0b8024442e0010540c82c50101096159920301d0000741c018170000340610800b121405000301200502032840342561540c010030442039261003541244107141e03ca80121207503048103a0394a42002001101d100c115555010003100b0038040c00c03040c80062038400000c00001d02c410520300c46600ca031b007210b01401041c07040010304200c0c864044928181d00b080c0c4d050303142c07000d600c1d44004d42606640b00304c80107245000031805030703d4040b03980c5000700090b8489582504002c8000c0c484820340300c00b04e8401d55030038443c8807066801c004442466a403181203480721a00400141c0700c0c0b0030806444001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 560989973 1250 560988723 560988749
    0xa0303030b0d1712010503210c0a0c03081911100f06050909060f01140a0e040302150f062103070f02012601090c0503010510050319020a0809010c1b0f051203011e 71
    0x52234604164407420401c5110840350780d0b0905501440c900b41c00520300401c0240202400000c0c00401e8001c4c1c0034030941d058001d20108080003046680c13103281d040d841040e400c59001100b03481c1256100441040d1082400704080c2d540e80001001c681040318007031020740040080050652a002069000d8842101111614801500410644e1226000303011545c54100082401e00d4020405004010300100b05090185040b400441072508241d40701070089103292032401c2c811000c89940b11504100720010b50503c209a21234500500070440281d06001404030400d0803980d0003808096001c890024a0005502d020845000c1b035040000034000c000f030a1005012076a20080743c4bc0e508002843c0c80c945980360304000300008100300300b060f041d1500c00900c284100f80c04c01303026441a0000070003001442c40003003003603c4541c0809013442200310f05415180000d183c40fa18491072a01810031903103650444040039805610a03005091460100c00045400d1580014100060190100084 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 560991223 1250 560989973 560989993
    0x150f0303040f29031f08060f0a0b130f02040e1e0408070809040603060501060806122d01090c210807030302090303070c060807020d0e0a0303030b0d1712010503 70
    0x581c401243d0140d1030b450207103800c2026142c10307150b81203444106aa022141d030b80c00c0107060ba1850284003981080d113100701c11400503170400045900c0c1e01c9503600c1a510b003400e64039581e51300024080e004c6850b03441796400a03d800c18025500c80c00d40a0540c001380160ba82c0c0c03d11240d4882c0d080000c2044113801c00c031741d01e810035101010000d290461390000a064554400f840c0284040c019450300315082842d200d000000d00400790040c41c100ca1a64a030301c8540d0f22040c042c440b555004000c054440e9200014100d2030780084c81120888403192140044050f232580526800c1da8410b1000396200f00c0c165806020242c03034110005242100540c26860104859594292034080c04601405055001c22560500d031000c4c02116841d03680440007a9501e52900d40151402c072080c3c0310b9500601c1503008541c1002d0080c1a5041c80480007444240c005182d69130840182c004004100d80041041564400142c000c0d04401c0380500e081030342ca070300d82c000a1240701c00100140c0c4168425402a5441 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 560992473 1250 560991223 560991239
    0xf160b09060f0319021810050a0c241b0806030a031b030504030b070809061f05090601020a0b090f0d140d05090f0a03021f09030215041a150f030304 65
    0x19441c15aa0402d015200e640e01c06502d104015443c1c030700280240006030f04411082d0450302c0c00d01c5140304881c44014903c07110030889a901640c1c0e040004030713a0005881c0e002c142042c0c100d81c99030a41c00c40b000601d000c6a262041a00c8200616401546135038220548280c1c02203c4194040400e41c000c200504860701c00610a0070a8480703141003c4005415005141c40b40048802030358005100c021a404d00440040100d102102c4280140c0200c1d000301d1266000b09480c0b2602c021909410850301d414101004451600075203041d06521543e0120340009402c03208040c0b1618007940680080080c845429050221090410040080b41a9680905885841614007038400301500080a0751428801d900e8400f4198550009101c0e440d03a000030113030700184402076001200410405004415400c5080e07925100c0001d015801000b605d1290052811001c1e91090186031000c1441c2180e140780341050348251524212401c101421503068141041e03488440502078006625040c902085 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 560993723 1250 560992473 560992477
    0x30c0f090106050c070306091b06110c12011d160605130e0901061710060b18091009050103030f020d090821041509050319080f1b0f160b0906 62
    0x142d0400c2c400007180a040c103600400410000d940e2290b4200201989410800760710700500304c50801b5200f08142c0801d6207840751242c01c088844c004003e084520030b98040100340003003154491469903071407100344458906082c1d4041d0364007030701e00940032041d5001c460103144142908a14140a410003401e4064403c1c0c0d403a6408940e02070b5107418040d156000d040340500466405200070660810071a0a800c0b80031601e450006100c4004111b0565601c0803103195006000784a007070500d5540802c040ca080c4400c1d400e0b44121410081c288140c0c550031482d080b51002c1c1c0065000070320498200c03007038540411065246050b03030700300009003926101c110741e80e0728050f400745a2420280100281e01c0c0b41c143c42034030090558414080e604d8030020074001d10151140c0f254912900c80d000440c0b4040060300d0003010015000100039182907901000355801d40e12010203290f4212180201502c1000c082c040c2601d44090f050241412003031781d40d9406c2e0101040c2e0003003403c0b14020030418a1070303642c13081 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 560994973 1250 560993723 560993729
    0x60603070e01020f011401140102070b1603090f0b04050f010512150d1e020a2918040e01090201120e19110d0501090b16080a05190c0806030c0f0901 65
    0x2401c10a0041c803540101d0501d1901d44030100309600f88421100d141e24141c00712410b88020030b003100c011501d00780049a480c010382c81a4190b441f4101b040011900c01451060640341c0a404c0100503203584070a4440011340c16400100d0824010506201521381950074400138102407a10078280324442d803005601e440040c00809204041c0ea10000d800d8a0b81c0d859402c103290043c000a44400c030031504c0b80203286109108034415588910301280042e4000540b500d00c146800591001c10f45140b84601c00394065050f40f00c26006d000c08418041c0d0b1070f8083e44a014007501d0002c210030901d0300c005001c0392540e40c90b000106050a5040c1201d6a0000390341141f03124203a240080718805081c098104440e00b015107070010b8055108000f8480150050020709200e80c107400002d81e900303c60304d0039075029844a04001001c2201103600c0c82040d421807a08504401605410004546900d2048941d844a4400803d1a000401644e8034050081381d1071180d040e1803031068041c4030710000789200c0f4140 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 560996223 1250 560994973 560994977
    0x52d06010f032408060907080318010306050a030f0c08030906070312090506090f0d020606060304060e011103130506010803030103020d0b1e13060b04060b040902070f081902060a0506060307 83
    0x820341908961180d000443e8005000f80018254a82d516607030881080138010302a1078842c24010480a0340002208022500b14902031800c20038840901c224020000c00304504054440078042100d0b500d01514a008511840d01c60504440f28640303480c00d0380c13466100f40e44940043c0040c228a855120480322910360620340720005021125500c0c000704008000504644101000c200441ea400203d5022104200e01210411500c000003244d13984800c5800c50380068003407011034001522900200c01c924400380c0042020030b1050345203041c2d608110f8000681030752401d03981082c400c040c05854050204500950318540c11500030610120700108000d080858080c0040c01d800284454000c03c1d00440038000014148401910007555083c0400e42c0c400e4501800c428092400c1d2050780c0442d0b11101140d03080c1460950894000e410100c03090b149031a2002e02c8900061003500208690942c1e561200200f140c9007500038504030004043e81720451170b0000b070105543e14241603d90045540c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 560997473 1250 560996223 560996237
    0x6010b0d0204031403032715090307051501050f0306042d08030c0310050d020d12021629120105061305041e0b0616060218060c01052d0601 61
    0x80c15000002e1050b40c1c005015100000d450300b884540c04030096000703134500d1401c0e169140e20b2030b115455034021361030501426485140c0c003121a104004c5419800141813060300d0900310030303865550419180e80186510f0001400050001d454914080d81410078241d0007000d02c2d01d0603690300416849050201d03070341e40185002d403840d41d13222200c0350f055140c0c4c13040c002501c0341060340354003605400030f0303900580e01e00720307402c0c00308040c01c100784081281c5400420051601c101625052480c4010360742c0302046009062500e40f2000050310b101c030041c005d1104e10700305001003003a206126440e0307900700d10100b8810010743c48108000000d890658a044400ba0b0741c40010400e00b40100310b29074440c0341c00505010149c03c0079052a040c00302c003501642400d209840d5807408100c081e11070407007203152042030031108501003a01c61380603000d2401d0014040e80795200010004c0c0082d00511444051a0344500401c1155034020026410507102c110104c03d042e41204004100780c200104514104260 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 560998723 1250 560997473 560997487
    0x7060c03140a0c320c0a031b0f110604120305030a06060801080a0809012606030f0c22091a0403030e030901090909020a050a1202121c1805040f060602060703090506010b 74
    0x282c3d810900103444e0b044107031640d07109010f02458603210a003c0c1603020402e900d01511608428101d56130715a075000800c03141034a40340c1d8aa0700302145903150300e03410060510000c01c0780030a520700540c00070f01035225291030749052110f03441602e2068015800300300145004111007480000c2005200b54803203900c94a036201d0000403202c061503e02104440160055402201034080c400b06010341d0f015400c3d200d040f0a038550b45613a0f8500d000049401244140d9501c0e0f46c01a1685082850882005c1c041412030040e203d641848200081c880c40c41540e040030311040540600c202420340030b0f180055802d0660760b8001034451002c0b0700c07503e8501a142c610100856039001d202e00c024100c02489008641d0701c0d154003541540070510103c0c014440c0ea21610751340d00d0f000910031144001141030407400700c0308501c02c03220068814140c68000b418900086400c3c0e03558081c02a1425503850f00042c4149080070013441c114018010009152604001001280c1c020602340e054803030305810140e81d991 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 560999973 1250 560998723 560998787
    0xd0506030d230d1e0e210c070510051914091302120c0a0e03030301050a0909030c05010c0f030b060a2307021804020102060c120a09030507060c03140a0c 67
    0x105801c1003554141c80c0c40811644201c56605501c4c10540c408010494100c508402c0c0340d50306003c00e1184210807001064200d24548040144030340c500110650303104658680104616240075030030032010031008a14030102004508000f845009240350421764071b07c8150132080c080c81080050741c0a003519240e5401c0c80c81c8141c048070300d0200c0008103040306203840350004010383c1110202030000381821616440c00d20740041628140c8000908a03c42c0c140350407002c0780280a03c280480c107010f5400c80c9600400c00030312031040d1114075503e0302c80c0c0c503a45070080182101d009003a41442804240300c0703400740c10707070203c08070340d900b02c40d00106102d00c3e10901e0180028055010000d40c44560498091441921410760074000ca00c00e8003260900e1b1901814489a400340f014154489540c5400096103901640c008080d454060300f003551400d41e564a0b200d0980f0031060b2410b000c00e442c1c1d140340140e401003036001a4400c2c8440703420020000a0103004021890225104240c0b043c018028441d0030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 561001223 1250 560999973 560999977
    0xc06020703260601181a0915120a1104120b09070f0b070c05030604120f03060b030a15150509220e1c030207030c03050d09050f030d0506030d23 63
    0x15560b003801c0441d00c080c01c4202102464211810b90002c1c042001407000303c800381a000e42652002d101c840c159442c141ca804409402425042c1e40c8201c0e1084041d1030030000f03200030b029a509000501780c43c4c0c50000803d000741e81c4078003494003024a08000410040c0c0c000e040780e40e01c00d40c0c003e4101c1d40030380b0313000c891a10740503243c3c0100e034592041c62030004640001d000100303003042c480c0c1c14441c60140d03190304240c0c90780012100a41005540305125813114030615038074914031618100041c02503200c0040c217030140c00494641c50f11642d0340c0b074800031225612004000a00c042d07100c40b642d0a051480040090143c0a0502d014103c42d200e81042e04104005001d4050031a18041003140c60b141080d580d2101520040607022496a01406070144280216032055405484114109502d03030350032281503101301ca031340324019510304188001034070603c040c2909000e0301d40195180c1c12805003240850b50064800e074845c1d8000c5006204007a000f1034584115000d410419000f417012400e010228 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 561002473 1250 561001223 561001247
    0x406060e0c0c0606030606060f1b0d120b151e040e0a0207030f09030206041401030b03150912031b1605010905071d04030905060309100216061b0c06020703 68
    0x2104084204000200800080d24280e0b40103801c45038540c0b180030915844003015220b8540284080000d4503280c501c403030003405034038810301c48001038a90302d240f400d080401c203d00710b000203050440b25240c0790000d4040c1070543c00b0120342c481c1c9510b9000d0301c5003c551180c241000021111548404c08804268050b074005080c141b08000051802d0903c00d0002d521013501240820100c0044501e41486907403e4000e0f80d0340030b0011480d090420302c0807529824682400b038109525031540e00d2440e01c040c0045000705814007200b80711400c1c04118181010300c2d01e248001142d40900800070780c140c40503004000c94501040c950750740c00c45100032104100700d03940040e100f5800c140d0a00c042040c0013a9020880c1d40d9440d01040407852251b030a40b03840e1054802030000ba001d10303c01c0c002d51400400841c1c0007a000c0007150b0325a5104242c5070266044229110400c40443e081075007801414000c11a9510f070034040c0041e12842d001c8042c241c2c00c10103901420306580401e0403820140074042d24464 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 561003723 1250 561002473 561002489
    0x90311011107030b060a060f0c06051008101b0201020901020c0409080f13140103020c0c100905120c130b06030106051602060c1b121908040b120405191a040606 70
    0x20b0140c0700d0a1103800d071881541e0140c0203082070200003410500c900c900ea070718425242c0e82e1040705003503911640040e25028084e54809843c603400050345407800c0114205800c3c89103008501407803980581040300340c4503c4e050040da40100040501c036a030124a91b1101da10464000035680c1071820440264042c4084021280707400242c400c24646645e0700150454005402c42c0c51f01088410044060f4050040540f20941c045000a201d620340039450100d0001107242c201d404540d92000110940c1110000c00226005042503894030300b011f400d00c0e42080c98840091205176600303030210b5041d200501c90001000000314142040d95441d10141407000c0d0001c00507610340e05400440d94441c3c884803510114044003081c13407401ca050451500070704400303000c09048030503008a00c110740c5401d090021110750b4820400031503c20b00300c101501e00e07038184205145541ca4549040c1d0301c0c291208082e00ca00a400c0d0005200085520061405c0c5000300311813502c0640329850300c000502280d8001d055 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 561004973 1250 561003723 561003733
    0xf1804050f0d050d150303090b071a0c07020f06040503030307141c020c060a0e102003100609061d12010e0a05011a0f130b030319021507020d0903110111 67
    0xb1010740c00b0010b0500d5402c3e184040142100d8a01c11262242d07083c4001404959000c00401c43e050321710b0007401c0000d014104c0000d40e00750030180007084000898001c03030a008041040c80560400380716500004109560031442c160a003400039035280401000d0031301700420501005c0a640e10002030703612800c1200d107511004401460350001940041c804001984074190001c0c2403801e2500540359403155113030117080c0d40502c410b0401c000d01310703820510382489002050300d444042403000071440b5600c03c486600e15203042c10300c01400301516512000030407031006902940583c07480700c1c80c030b0560022209040808080c0300c0c62805400b50b030341c8842d2a405007068007424418190003413032070104209020302810044400308880c2400f811a11a040940000c154041100310ba0141607803600080807030382808034044200c280000c2d952070240042e00701c00400c28040e22300d25081134010800740050320054003000340080c520006444090006400f01ea21821247d000c1ca50035070016503000180d071 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 561006223 1250 561004973 561004993
    0x606050403111207240e0d1214091f140a1b0c030206180a0503030f031504090210051e0702031507030225110a1a0702040b0a060807020106050f1804050f 67
    0x360000c00a8140140450b42944c0303500000e07e04030800c03802c043c1c3e0081c162198840507650494500d2110070400d1031241c7c0c10031580407030b41d60302c122f00000c80408001c01100d45801c010010204282c0b0030340641200801e005c40100184c00861010708130324600b0072006250700b1418200880d90f502c2d80041d402c10b10000e640710907407446075000c1e03240c02c4080d150020115500c20074140c1e40e100d5000801424001030010550000380d10080001c1c803800240003040c5100c00e07400048100480442d04030214038001807210314984142c0b0844000006558810300b800d00c1070b008651a4209070100d83c01802c140c10020b9001c41c081e60680d4502c140030140810b0700880c00f00e000c081480e8424065a0315102112a0b041c0c5141c010407103015a40d20b5690130b1103030704800c0e540075101c2d04480c01c102d900c240c40b40c000c0a45034440b00845070040c0b00701d56480005043c000d5010782100c2294014034000e10b00941903146a8403034444418101c004a80545050303034036820403034103000384405140303024000c90b8100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 561007473 1250 561006223 561006269
    0x304030201020a03060b03070c032003040b0a03060915053007050109050a030503090904060906050c07060b030a11010f05040e0c031006050a0905220c120606050403111207 75
    0x82c2c1600001c41c1c4081040b103481300d501b001c040c04100c1d00703000004c1c0e200222200091260900c0e81c403c0328045088940d100d0750300d0186003136030859000700c0d60105020801d03040c0c0701d9041c0118001070180000410003881c459003008980c031000d005482c003031482d651101001810031203c0c40c1030f04444c440a001031480c038100703194840a40d0702c1040e00194a02c800451107240071381031141160340c00001517140c5036103c0148083c50000a005548e11030359580d607200400c40c2c0b030080c2c41c1304400d0710384400d50701c900c1361618504588410507414000d5110109520000c0c5044d044204104024241003d224441520407a803e11035504080c9490742910140048100340d40081c40c0a10680e1041c10301407511140201d5090207070700c80100004415032400c11443c06c2042d0000c0601c20030000c500003440544000b18165514110308100083c00d4555107001d502d89807103010003a000701c0c6055480c0600d5600c1d000d868800d00742d8494030a01d072142c1540d43d40785003040b06034014030b603801034407680320203000c05 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 561008723 1250 561007473 561007477
    0x3172502031b061e0c070201110712080a0906031e2c030a0323150a0b0318010e0102180f03160303020105040c0e01050d0303050a0b030f010608070e0f131502030403020102 75
    0x5441c144c0e840134454400e0384258009100d1044941548150420780d8035001150048a80d0004c00ea2901406002140010f0a98464040c85000712400c0b50b60706071802c3c00410b01840743d80310720708252401c0007190520303010000000801c040201c000c91204440d422140c0c050f03041071a1b0003807a8801d900500c03213048012004d808805030a0f281042164940c03200050100c00250055000100207800a02205080e0908000081000c1c146414058450500705d03440e920a031000d82c0040301c0b18079285040d0400340515803401528074000c0d41025000c254076070501000110140c45940e1204c0d1405550700c1c10041240c205400c5080d003000141d881c04d0181c024581070b102590070020a00340801d40c00240f00d8094121880a044001c00510603142240181800340900210545400c00074507140c6c3e0820244048500360000007d6052800040615185807a130103004000107070810401282030090b0240c0d13015620141c00c0e18058028900010902e445001244942e0b10201c1440b00b890760540c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 561009973 1250 561008723 561008731
    0x70b04081018050a0b0a1107050a0c081b0103050405011b0c060b0402091806181e010806060303030610020106080d09150c2003010e120703172502031b06 67
    0xc00300000001c1840101030000b548030042c0c00b6511808511001802110001e984601016800209030555904101041e030100380c040d150366004500c0202030080c42407411000f40a528000d064221a404000d42c40300c949400303071818140d95400003014808203400400000e8240124298603c2e9514005410030340e469000f620030524002007030030b650915108840c1403407070040c4800759034070b2003140d0051280030003088160441ca444d40545003a082800c00350f401000d45420610303c5a00da0081e01c2d01912059200800640c06827007401510307107011080300d400440989a5014002d201e0a040c0c0c00351480c0c2d4400c072058415081d0800d500c079072041d141c00c165000315100c16028220600200d5449040000c050004030a49109006419051454035402c203005400805c0d10a030400825040c0400390f014080c190000007075003003c0691180010340c1050010010541ba81000504110b800c013130b020f501ca0522141c807181302c7c0360a0080050b620000c0d2030003500854081212086500c442c0309079 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 561011223 1250 561009973 561010003
    0x120e030712150f06150e0f04020f13080102030105040c0905151308030c0c010f0e18130804140102010b0d260408031602030d091215060b0d0c0e150a030c02070b0408 72
    0x845c5085091113480c40d803840d10741c0141658040d10036802000004d520003d860f109481342000348030310f28041c4a100400030000341f4001a169890101030006590f4402c03031850030844d01c0e80050080d9a030780101c02c0d4000101900f810340f6000d442d200547c01c0c0455401c9038050340700200c0c1ca10b00c21100000d040800300c0d030a070b0b6a10084a854202540d801a00c41714083c1d0020400c1c003450124004401d0095200507203074001d401d03a4802c1d840e9072200e0380c060b03002004594070f000d186425658090080303c00c401c405a0380e0942c424642d8031601c10359a005240c10100c030a81a05018448183c3d10503074000c1d04440c000e0b01e41d908050007206910b1803418008a0082c001d5040c3c20515900500f0a1b004440c0740003800300c1d5445169503a1a43d6110004806008030350704c44010500010030006800c41e20715440002511540c084e0024185400c45100e01c0d04c02e107a00c904440003800407100350b40347e2075560b04000c03642c03409a50301a42055903580210200507030210b0b000514100010310b888802e1140 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 561012473 1250 561011223 561011249
    0x141305120307020d0e01030b0406030609021e06030a020d0605120c030f2d030409110c0f0102180103090606051c1e0804030b0a091b03120e030712150f06 67
    0x1500003403030036000440d0004096081540f1908045028600c991394034901454000303000340001c00014100c036015002540c00f030380d80315810011402c03d1103e110005c80761001c7c4001d28030b0103000181036840000d1400f251640c003c0740302c090402c2d131900800e0182038010040306140c2da8103151103036908402c00e5070600ca8401c0c80074643c940d400110342c42051100d07103001004070310400f40520080e504500e076400943c0c4420000012031440e548255008030100c1b1076031030307030341d504c1e0140c00c2d854a0720540309a2079a9204120340400c1642c400c400b444241401e00380410f4a01e4181041d000400c0950300464004401d9180d810300e5603c00300031030035003d2064014442c00060740c64602e00c04040c0c01c01c01000d403c000c200c113001150b11403145540c4100c0d01d05010480f91910742c0c0f0661000d10100c0203655042040070184100f18441200010380526413400748102d82e00f10b030004e030351044244141191039498520010030300c00300c140500742c80b40700c94806000c00d5040001610050205204100360010300c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 561013723 1250 561012473 561012493
    0x6160f06060b040e1e0702071203021f0204031a10030b04020d050d0509040617071e090e0102040e06031519063218071b050115030201021608070b0c01141305 69
    0x845c0703015a00455050f40140081401e10f84c1142c0789284004041c2d00b54400c030b0311035007101410034850982d08016903202585072491454a4202019048188034860408504204003a5020788101049036040034592101c0c0e01c4d01c3c00880c2c01400120000b41241c00b0b10810748100c950840d00900e03810005a40c00c20880c0d0351400003a41c1c030725081c25808071307680040c402000040c6150480240c440306801c85901d40070f0341c0318440340803500100141030090750045010080d4800e1a00c400b40e01c10320603070140100d80b0f0480307031744048400020708010340240c0550101c08801460341c0701c000038010904040c0f42260315142500c008080b048850411890001002d0416041081c69005054078034031400c840c0391075180049e0348412a000100800850030542d100108100b4020b40c02c400c10b0a0351103807045421400020b0422102c0031100725244c10140003001240c00000340b40040f00c84a40030030b0b850b402c0c541e007030602415161120315480400e410034004002e03403507a0303104001d91098044910000e0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 561014973 1250 561013723 561013771
    0x30503180a140a0515210a050109050f0712020405061c05070302041a03070c02181009060b0d05130b01030506150d08030601110a05070803120606160f06060b040e 71
    0x40c0380c2c80c002c0e8100c0d240c1c14040169050060011220640680d046810010054852800707410f0304a1501e0300b9070900d00900078a10110b106140c09029902d60900c0640f81c0085450318008025001d00304009a140e6a01803020303150f81900c028080c01043c20b80d50300701039134100301100156400c9182d490301d0500807840c50b601138402c071011141d8012885010019041001450380c0004110034203101030303806da010050340c502400d00703180745042540c10607908200d44100c2c0034a1040d00800300213031600406000b0380047c207050710600b08003e01c012800c0e541e1034000c0c00f43d24054040091000d60490008400c0000100b02c0380d1040840d1107110700000010030800500b400030200207080d002c0104003003401d9500c580980d180108801c800c4512203040d96440b0361801440354000b82c0c03160170101c0c3c0110440107021019070004001ca031700508140607039400960351a100c0300014400c0544a42001c20464030783c0142c802403ca6004854840f66a40a180009501110110503688a94030740f81c0c0c02030303 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 561016223 1250 561014973 561014999
    0x4140d050c010f0516120e03072307030507050607080d050a0b030f0109081602010507050d05030709050604030507140d12090303030b010c120806030c0a030c06080106210c0306030503180a 82
    0x6001c0ca0342d001411200300300203840c040041c000846c8515100d400120014400f0401003c040744a0100c075006c003560581c0317850607210000913007465600090000c0000c50030000d2000c098440444a070f40e52404180350030b50366485a05501c612040c108420031800c0700d83c84e400702d8203d100560995143d01e10050000e800caa9420748010110300b01805a4042000b12038402001c19106040031840c220786522014680087c010f11080080c000000b081400b0768040030620090000f9502c46003464215a11941c03581e0030341c042c880c1c0041203511004e2150351149d40b0001c1c9590000f00204c41c0e00b000800c0140881c2440c0426004282464900d0712a541314001028040742c0225140e9104c3e402c2d02001c0f0740d0084007404080d8984141020021984d4032614184001c0d4410f0356045015807400d440641700b920140d10003c10300121260b100598550000390305003a48407407000291403501c503081900213103419003010707005100100f0391014000b460011800c0d02c481c02c45c5e041c400c0660f1944480148 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 561017473 1250 561016223 561016231
    0x2070e0705030408070213021315030605130e0106050a060306080105010f120303050907181e02070506150d080307110106140307030f0822090c180b0304140d050c010f05 74
    0x1401c20800903020809010140c2052172004041d2200c02c0a913620324010ba8100161081c400076907145d0400503048540003440000c07289003403d1111901d08400030780700407550703244c580625444144548281400b0b501c840041e0100504804007640ca41000800920840c011000150318000010400d1810317a00504219810102c0c91204c000c0c1503a0110f000d4103000d01011840e11502c0c40100d08914140310740609000107160010300c0029410810302c0711115030b0600000a4070400c0031201081000c02c003954410002c50800c40145003c0000c00c0407045601301c040c00c12203000c0107200034254015403049050032481e0091007003503121030046c000c40458206080d072551002c9001c000060580c24a40c0c20310740601d20446c28801138541c4aa8a062000c0d035144140c103c41c4030a1045803114820201c111000d03107840e540140b03114980340e0554000340502941c0e0701300480018108109a50b22940022215040e500d00130074604000c1e010b50000031001010754203000032444034241512a507445 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 561018723 1250 561017473 561017477
    0xb0d0e01020f031e092d16060507020306010e0c03040803280f051023120304030b1e090307030c0f02180912030c091014070c0603060b1911070905150102070e07 70
    0x203000000e40145200c05400c2c46110302071301801e104000c1d42082200000024000c627140d240d1b69514601c10581042c1741604804a41d410507000d00607860141c0007a40d03071082d48102038607503d4990081c040c0b11107040e100b88504000d0340742d00011807800642c00c0314183c405030820500594484001c01d40140142c0d01032003000303001d8017545a140d208540c0d0f1501440001900180203180104040e500303503840f80e0130644607a401d03002800001080d81da10401090b0384034011800d43c5c10480361481c2c50340700b00c000c06000c20031700364042c406100c001e80d607040d04554020030209a042501c0b0100641c0001203910040300c1c06488103602a14214508403441480e140040300e2030b1814130406c00c004c0000401c01c00c01002500c0078105d1008120900400f031090103144070410b020300e032140040a035006174101c95030f540801d014144030088520740b120707002085800c000d1646221401d0b103a01d4140f159002130550741c10042408051301111000d810703149000c0c0e007941c100b0398641c150448103520550311040 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 561019973 1250 561018723 561018763
    0x1020a080a0203130209040b07090b160206070201030f0f05040201090605161709150c0c0409030c03031d0a0605060f100207030b0403300f060b0d0e01020f031e09 71
    0x10003403141e5070045610400c2900440d403080c00a401240302d01400311400c690764001c070002e0008607900100e000006141c0da0108901c0c06810020011605600c0d6100078001c0310003055980071a030003900320a02e100a0841e0400c103950115550302c010f80401c0e1000c0c0e000c50040003000c03649601c030300d00301c0354840311a6880a0f0a000030703070f440110000b42500d2610007080c05004002c2282d07900040780e0480380700012801e4490318481280c1303040c141a00000e81c801d91505029000090300050100704550309030400051604c181e5102c3c01d580d186064440c100c07805803003419420081550711171030103003005450342540070250310144140300740300240010160340312140410019004c02c00c01a80319100b8038041a0b1005510950f0001080b20445100c40003440c071100a01884c552041b54440000e564051001c2860240b903003000d40300c0e280040c0e503d65298001190712031025012100c2010311070a181e9540d21340314036155280c2c5050a10030b13856001c4400400c84004000950754841c0c08034443e494 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 561021223 1250 561019973 561019981
    0x1503061a0d2430080d0c020309090c0306130615080609130f030e0a1502100c1d01020f060c03040b0903090603070503060d0f12090b0f0a0e06040f09090b0901020a08 72
    0x16880c1c4043c6810828905526a072035103410010983ca007580b51055200c2a15501800880c10665808440c000219801400b9400141e5a40420207400c0907011207584e66903250b02001c1640c03c66071545024005041410000f41c640b440320480030070210f6541c0341040c0391541010085056026241f81c1219480e8185010220f82c0c1282c04805141c880d081c01e031a02c0d5112400f16a10310030682c400000602d03031402030b00708140c05000a00c80e0102100b020054590b5a21026020710705980c04820581c0940c170010406900800c03c0c614602049011220f43e45044621085281d1080718100c446a80c41c0c13002c241c5200001043e288207079801480a03066545a00c400c8442c2d41008010a9210080c104080301040c66401d4003040b050040c210550320040500014081c4d45850f444102c11510400850003801c403c0c070f040d14100f4141d440c040c5585018140001c0d40c0c0d0203030b5000b8400401e048880018008501e500064045115205520b0300d60f4600200c5400c03401560326540202c0c031804001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 561022473 1250 561021223 561021239
    0x1518070f030b06270d0605190b0f10030b0d0b0907080f0703080a1202210405160e061306080f16060801050609092d0604060f08071503061a0d24 63
    0x902c9130b1071405000d14030100296280d142c203a42d41500c004e03884801e000c0020350162101e000b640420801030310041828650b0300040390801020240300010556110343c072601545d5a51004004140c001c0c5045001c2c1c05e10a035038036282c0100344a81c41d1948510301c86002610000f207050000c0b41d0b04442d1035414005c0317045041c0c1e2840c1d048554194025401c000d05142840c0002da800b041c14000d055501d1107103010300c1c01e00d2800c02c41304c0704d149441c4980b020400c42c081c1c030b4542d603e510601c155803000c00303521903001c0d0b1005070009030031a14050046030004401490700290305820059035000740d00c60b0f585e9904007500d801c4002e00400e508090200480038584c00c202c010550044900c41d1b041d0302c2000c016119001800003842060000191401400f40500d402d0095070040e0080924882000b4a45940560740b0403ca10070905c0140c621003801c5600741c00fa510400080100130343c071542410b64401e8031100381c0d10900c000b17145685030044d0309000011440d40701103500b9030b014030f04900328140f0f080 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 561023723 1250 561022473 561022537
    0x20c221a011e0e060703180b0f0423040939230a08010b12030a02071503090b1501022104050d0501060f060309021002010c02061518070f030b06 63
    0x1100c00e00030951040f80e1141c890030b0040010030f0103551060614505e1061520b010040c50380002004201402624003100c0f004040710b0442d5407404184110158141080c24040441c0865650003854188002c05101c11b401a2842c1110302c1025072940789450080b83c20b4000030000201d81000b610042405000c6c070b0110f00d031081151a03803172038aa0025070380c001225035030710340c10122050751114600d00c187c0c2440079002d40f45e5041a8091410400002c0f1300070b5441102e0720030710701c0041510000085a13030080c0d22442c0c089800c09009855445e10300811204600090060380c010b11a10401881c01440c070b4500d1002003070481d40140c6400d140c403042102d0302c048400140d43c1035684240c009084c030000440e5000800d032507100031540d40101d004104c07803055504890819a41415800100c595001c00c0032640126040d482441816a820101c0d028194820030700c00045420428021001e800403000d2022041d15036061084507000018001140240d58110700d854131101c426024040c4045e007 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 561024973 1250 561023723 561023777
    0x9051f15051c0501110d0b010c05060f0705120403020a021806030a02130609060e06010311130b0d02070210030e0f070806270616022119020c221a01 65
    0xd502c070603410040e19142d0858180d11520014180300080b0182d90100a002d1429119024280503d201c40c081e01c8207526079400a0103000c0444c0c15200268810f0300400c02d4420390001608a406640b6042c9000703580e9a10014080c0d101c0c0f030002d500803c41592010801d0300c10a0050b029103441c103a6a400e001100c41030399514003420786c0b511008281c485543c071941004001c41d440401180c100600007400301c0350b0020039154030301710400000510203c140ca420302211200e03400c8aa8910005080e04021b000e4208001d51080a010000b10300692680107030800c160a2320a0358644000b184100c1d0b641c4400303219402d0150406000103100b0b40c80f140220b6906161b00030541c242004e0400900d00300702d000c592080846c1c070b260150451540d41040340001e0241d03144128a040b5040b52010902030080c00151040c0f54030303030b0360141c505030320a0104040c0e035800a003004181002d0312407a0120920741203100c2040518296540c14650082c01c0c046103207003c182c48590b0b90a16401344032204140100b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 561026223 1250 561024973 561025009
    0x3060f05180c100e100e0f030102040312110705040906020a08241203040909051f0b010516030903060c0e09060402090904350d05090f0c0613030609051f1505 69
    0x20360180c0c8a80c403850786aa4134045c0503916581d441c0030030b20412460521541e4014040d0780705102c18000a0500d42c280e00c4a60402e042c10440040880710843c507044094100e01d0b045810301c41820304010700c03500502049405034980030b40b15901c180c6101d9900e405074010120440c4a0004c09015080000802885c07400c1142603034502911303185840300b40d4480ba50203c40a902c6080b400f4554a0340c103110064141e40c000081c031150249400081040c060090307056291103004144500305401001c1040045501c040148920b000c1400c1c050855000050800d00890f50600054040e1410b4400c4a0050714000c1c11400a920317691112070035035038001c1d03445440c2642104d00700b40716100e071340c0b00c140380d000196486565900700318182c101351034000d0314040450307205001c072082d500c0c00803c070481030600650b05581c49014070ec440313000c0d8110703c0e0300140c031035483c24407403e00303200c40403500c58071000c90030400030300214010192004807590114501038032080c80d08140418070306580c14803262005c1c2 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 561027473 1250 561026223 561026237
    0x501030b180403020a051005070c1106190305100803030603061f0b030c090f091506030c0405130c02010510030b190f020d0b010e0a03030804081e0403060f05180c10 72
    0x444118407520300282c909030050b0340021450420801c0811aa101e07801003500c0520090510410242080d460140c00800c0350482403206841900d404c0c2c02e2b618420321007a0026644494081c001d8000d080c1a9180d4040402c0c40750702068809002080340c1c00f6980c040e00822440c3c2d503403280f0f0300315030301010070b1412441c01c12113001440b0749c1100041d500440d250340b1541d0f602e59000080001000720f4922060198074146d08210b00a910140c1c5610303549819150301c1d9490b0b80300d00f40765050f8130135030b0031151340901101224509030650f83c2c4802c00950322038008006540b10819806900282c034800240b00004d204006000e40708105481031119010800c04100c0340c02c8a04d980050760491502c811180c0c5c1d68109240496078030820340d06540c0d8040d01c1072450b041c11520000c10b0003c0c0240042d144080000303694084804190f540d500301a01002d0107070700d4945928001000e40020440301c40e1050600001c203020306410080b0000002c003882c0144080000a0240080c44034081c26038000d101031 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 561028723 1250 561027473 561027499
    0x40c06270e040201020a0b010e1e061c020111010c080a0c05030f0c070f120c0203100506010203091c020a120606060905130e010b1c0c1a121302210f15010501030b 71
    0xd03144e00da23020700380031540c0c0eaa040c90660092210843c00711080c030400481e45042c40b4041d21205428255610010000b80f218070160006039003100414201c2c050942c40c01020041c1d4503445114580518110107044c4440c113489401100d00b400300b03480846854901001240703140c115440200840c61040c0000c0d0180001621800c0418030303d03401e5070300800c0e4890304500461400744100710807400202c00070010382c104000000d580c0e01900800703901030000c0d01c0050482045807240201c50940c0140f0f5204c0d1191120b040311011411000c0c201e400d04c0c20005c012600e68050380c1c80c1001c0e1600603000000908070000300002511000250310620755803418a0a60780d00d07011000c1c4001d50403450b03011200441071800703070a5447d80f80c3c41800c01c0328441c100c070240c043c0c84108031a5420241e00002d01c0c161100c00381c509503550751381b200941c070071440500103801210310508a084001001c050303c965038091060103071148512003841440f558030100511a56000e580800341405000c0c1000001c2c010b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 561029973 1250 561028723 561028733
    0x50903030127060b0a09090b0924131a03301c091103070506090d020405100b030f0412080601090b160503040b030f01050618010302070f0b040c06270e040201020a 71
    0x170101e81104001100128148520b40729402807103401c4a09940c94030700c510342030024a030700201c08580c0c002e9140e9804461841075640074250140ca812850041000402502c0303002215045c81c5946c074002c2c0240f8200c250f1921325020032249030400c03546c0300d1000d01c0c1042c000030307030700d9208140750201300c00c03030402211901401d489000b02ca54424001d911030700300c0e003000700f5107132480b651b21080c41400100080205621140c40382c05980d58165404141c9403100d01520041084e590454a44000003104111003004042d90603805140540c0f1008408803044004480000c0101d1305940400d10004041102c005104003d0041256201345d00071526516a1a541503500981c00410124408014003440700d060360781d0a401047c040714002d103000014608800f0b0300e0010750a8905240c0e01040120500c400e84005850007540700300b00d00c0072031070f05281501010800c3d01500000880644c28003a00340d95061480d1400e1240340050140b851802022140451008004a046004a10000c000031b5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 561031223 1250 561029973 561029977
    0xe010e01050103180b131b0807030f0f080f0909010b09100c0201031b021606020a0201020a0b070e1309050616092303010204060203180d0312180b01061101050903030127060b 76
    0x142c01c41c0b40502e00c10556081192060400b00d10800d01f81c58040e108000400700001c00c1401c4030b80c009038103014951542000d000d50345220001410810700044d50042c101101c07001071901c54011160b00319940d0700d4010303140c0d6500905112540012012020041c2940100300180d07040d40f0515001c500ea03080480e03405603010000b110040560b0140c0c5480161070300d0002c030600a00103600c024158820b480d00000c0d903488d800720f0041d010b120030700042440350780f04441c3c1e000b10000142c40150501032400610000f80a0144241c62030300034040412511068141d26410805040d07403820070182c10480e00c81312901d4081e0f4024044007074a401c08140d500d0070300103400186129009591210f02411045003040742041d003d40c45003428148500000c1c1c2c00c040240340c121000c800c005400003a8101e00d80288007600310140203000404000941c13103900602581804440030000d0001d03484007440f0315503900082c01018024500d4040c2070016280e80a00c1807400d2990728408180c059039070090850341e03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 561032473 1250 561031223 561031231
    0x8041b050a140a08010903080609190c05190c0201080619031a0414070b040e0a15080d02010b01030b060901080c1606060f08030a0e0f030a0b010807030c0e010e01050103180b 76
    0x454070202e0030310414600488075400914000c4000c0c86001020b03a001049200020300213449180359401141200c40c41072840015550121810080001e103003802a03c603812090041002c80d1024500c000b81c03601c2041000440759060b1241c4115450f00002c0050500d07085400f405400608000040440d030010a80945403001801c00882d03401c003420b100140c6040c40a43d180213512a02c400c2110b00300f8501103508458000c0c2165245407901a61100640605822080708104c24036000c00c045102281d49401c1c891560020030580e18110010340c2500d00c00c00c042a0f0210081c0701903492540204e04465004c0f5846101038a005030b072250319107a4201c0c00d01c2c20765840740e4903c0300744485040312507048054420000218140004200001c04801e44005a90b028500c116a1150fa075181000591001c6601039071900040d80c5410701159030322403074402502c210002c581c1c0003950384103018005060b19072400d50b461007a030800c401940035040e180140c030050719002c1c40c9000404c5000c2526405 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 561033723 1250 561032473 561032489
    0x60a11130b030405240a090618030809010b220b1c260313020d081603020303150109030309090216080703030c0e040b10140408030a120609020301030308041b050a 71
    0x101c3c102418000d2501080c4002c000034001c55009980041407401d07007960784100e0707454001c6100320940ca0908040c010307000c900411014000c030050200343d009250f40744922841d1000300b0004040b035007000030b25030f0130310302d030300c82c0350001c061250350500341504229080c034000380800c45da1202d8400815211205034005a80e608010070000e405c2d0007c458201d411103100200d03481c21070402d01005038840441d850028816a0300c0c0c010001003103903603415107650301c01044412801400c42d08002c1e4995004649140a00c91503007031300010307980101001015250160350b4868118104907000000354403140181c2030308010410f0a00010300c7c00c200802e4014400d035804071f101c0451000242444014444041c4210f003000762102150303ca114000800e03121600d002c845401c044a1402031b0351107036420044807400b000810803041e0f42c000514800c8114942800c00101c0ea6440343c4400700d00003804010b0003c0c06450104010641c0b54485810407007207114004403069594000030030913150b5a200440f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 561034973 1250 561033723 561033727
    0x3102150f19020105070e090a0c17070f18030b040b3103021501150e04020903061302030f01150603020a0e0901062a020a0b0c070e0c030a0e0f060a11130b 67
    0x607950a0083c2138200301d070350410f5880039032070f40300060b001c00d002810404519510080500d1540c45042402c0300d0448502d918083d07404c03c0e08006040590182002c00480e41c01380c2c55070150822a400d140c110707a04403003240e5058441c0d50b01c0c000700ca90080c1151040140300c60f8285000c9601d00348051f0441901c60b0180d020b040540b0b40070b41421132080c01e801490100000400c11030b0801c564008000e8050314108103010100700018009008125050f42c043c4584010051342e05000c0002c650300a00840c120351081584800aa090303899903160094101c4c4130540400c0300c1d81c000e40203450703555094180303000400648d201103480010260700190018484d180030404004155041104a00045146c0000070f40c0b5078000c5483d4a640e88602c1501d900005031502c9405024008080500704450240110313091280700c5a51a0b00b041d40d0341040302d0f1030321064000a50000681e490341c40c020134050851595441517940007004842d0100c03504030740410805c20b040e003000340d03008040e15030030144507 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 561036223 1250 561034973 561035017
    0x60f07050c0706050d110c01020a030e03070804051c02030f150121020910050d0302060105010f0504081f020415091707081506180f3102150f 62
    0x4015005815181440010001c41d441c1c808041006429100c090802d0380e80e8800d80081c0c44000c0c00e10b4807440c10344100101c1d002c5e5088006400908243c40315540a019240e0a14843c039140d1060110049c0f0215040008110504140c0010045800c501440114248840c0c0119050980904400000f504010801f0025000c0e4500060140030f1700b4440c841080401c60740200c000e0410100070748540a22000030305035100c0520720001400000c0c100340c00100d694600030b9036800080c0141804901610340c50021a0f01c90350544044070460340040c107628226003c03105003100040c42d01c1c003a00340c00b040085212901c000d407800da0340442d555001400da2424003024002102c07001c0b12295074000341c02c2041020000204148116141c407840038181c0c0b5200c001a0090070075544d4240c80800110030401101e99440000e44100b10100b1050310100680c4c0c130504226221140d003000c01082c0781034401c0542400d0146c00b00b494031280041d45050091540240c403a00010f000c0c1c000d1040c0070b000d075 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 561037473 1250 561036223 561036241
    0x203010f0f051f08101d070e040c0504050c04090f0f0e070806010e0f27070b04061707050a11030d05011203120608030403020f190303031a12030a0e1503010806 70
    0x80c2e9001003003c1900282e95041c1402240c44103122081d9942c0c0f2501c81070203500c4126240000038000e4102d0781201da40070750b1036000e04201c4000315816a00c01d005440001541c1c18180541403080310220f407024a06400c0025100c0100800d64450404598506521001d180c07184502c900e200c002e08024020075107400f040c2803404105170400b141c0c18035044240070303250000329440e641003110b44100303445c1e1341405d0050103941f00c3e6508034510284940000010700d114000c0042c0140d500c0b0f55508072200c2018800c154000e03405845000006100300046c4203040d114500c0c00d4207120b00039040e40d107004090400802a10403c0c0c100245003500189140d00301134010120040f599501c55081c062240b4192140f40c0302e006d1448080e0050a07a003500100c941d4400800950b082030b42500010444d03101d040040c0140a4184103054045103e081000149044400103100726a500021442c05010801c1100c400600003031141e00714221411502404190300083c602801c41741005007024a03002400c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 561038723 1250 561037473 561037501
    0xd0f0509101802061b031219060b0a1d0607080c0102120f041709010507140d14090307030809150301031b060e031c09050402070807060e03130e040203010f0f05 70
    0x800010845940e00c80141c40c4ca0050707800312031070110011061000000c03018210302ca08240e01e824200c079802040301642100f0750a10840811000810440c0c0c0c2321604e0f035005104080d0304101041300312000d00180c0d188064510520340c00034000604004095940300b0540e0000c03040d011569402181c104c02010701c4c520078590016071a0030b00034007402c080e02c80c80136628210142e851602e0001401211070390103401143d80e80e6600c0714101409801d0212015200c50243c842e4a000a001c00c1640c500c00c40c4130b90560307050b51402405040745074a161740d0042d2aa0000341003e170401c0304012140108082070300914002c6005502c2920140c042440c18090012a40c03c0001030040540424100c1e0300c000804924a40b040b40d100007080c600000c5c04e45900b01b02d548000d6100e800052200204100c03480940400b901c82c94091000a1040c10a40d450b4069012a411005610b0300100914201000405d070024005000001c070400260140d5041d642c0c0503600745140398840d002d20a0140501a03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 561039973 1250 561038723 561038741
    0x12020123010326040e0901091208090709021c020d060b040b03010f09050708070e040b03010507020d17151e03030f09130b010f1d030a0302061b0304080702060d0f050910 74
    0x1a82024240f031404007186180183c1c0613009840145000060302c0400940c49150748640004035071100101000c2e008050040459021300d90b03000f0750400003108060750080da0721300c0031000c25640c07200354485e040b24000e4101054440525440d03220000381d401541c0010704c05420200d907050703035960505003046192245070340303d81d40a5103080c00300948158401c0e11107070050700600e46042d810351180300203005450360800701136065203400c0034840500d400181c062180c8031141c03580d4610080e0307001c510010144c00c440302c056401c4801d00400c83e5280a90003a84440c0001e00309940841c490b0011074074641251446500b103443c0010a05d043d0300d00900901c0080007030010a004007230710540000d0910060761070150501105a00c1e6030020400600713000c05005014040301c00300c8520b414001e64071103066070303900c14144d10b501f20081020011811a4859900a15000e16203c203603403d208881d030109410381041ca6550300b01c005625541d02800b8082d620400042c0550910035030141c04443d4106 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 561041223 1250 561039973 561040013
    0x1e19020a08120403031d060601020c19060503071707050405130c0c1403070f150b090c030103030507030509120705010305070309110607080708070f1b050d120201230103 74
    0x89403000010140c504480340b07011140d03a18100c40d2a60300e0150041c200c96100482550640782050040400c0065018410700c2e00764202c564036204a4140701c60792050740b40034801d01b001c81c5410300c8114040d000440d00314200c2d1510800e0400c074503c00104200050388c0c40c01c0000c0c2d0000301000a45400c2204828540c41c401007004030703507a082400f1b810720551100050603c1c4c69103616907000307002401a03440c115008400034038100f03c2868600e20900b003401d0036180f19031800c800c0007068104070040f14400c503080d901103440c40c1d0a58030305850360342162a04070104001000340300e6851b00c03014002c03403401070648018a0b12609140000d07090700c400810b0720b000c142c904082c00740490701c0e0f500b40c01415001034824035910b100505254140d48114440508a2940090076804206484c03100714a403602034842c0f08070003201c20104400390302c1148a1554000500c1c0398038000300e406d40c0b40d4001c6885140c000003640540c1540030687c85051203d6500460501d20010010301c80c620440c0c024020400d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 561042473 1250 561041223 561041233
    0xe010f050907080f04050316051006090e070306020d2a1d0307030311100914190b06010e0103060e070203042321072301020d080c0306010c0302031e1902 67
    0x2e070310001e200b0103004103080d4455400f1004502805002d10848485000d00c01c10b680c258401404c0066486003007031000c2590901c0c1010000703440d2164418150040010005850030600d55111100a03400c03a07441d6052582d900d5100940e04034601702d18400307803045034915000e20b1490200180000c42090381464001e030b40e030f206441850f40c007c05c1250660303a042c20003400d60700e4480215882c1c8034082101c8101ca031b1801c2400303c140203000201100d400c02c41c401f1101da2072000082c54141d0a02e10200525503a40070020800d198011240b4110001c010700d000138a65039a01c1c401d00840205842c4407001d80c00006051003800750b0b0040c540c185003d0340301011340d6070b0f20b201c011807203010f40d960000c81c040d52100c1404800d104148104002040d041a00d1000004164290607580040120b1240544180308070819814014147c1c40c4c403aa1100100908541c1d481c001510918084034046045000800103048a048504518600b0400048185403170b03c100521505009408000c0c0906542c00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 561043723 1250 561042473 561042481
    0x60604090b060111160b091903030203030406090f0b0a1a0d080d051f060f03050702010c0816030b03030d09050105180601091a031c03230615070c0e010f0509 69
    0x80c0e0718089412080070b1910380140c401002c003141c14000e80e04040c1d4000d1201010000381aa20000646200d0504a0740480c00d28400165520f0882407440001d000d604144001000f240b925400510010b02900302e051040905a840c0f007481c020844450031a2643c8030f0003c1000098582d00d0075640b041556801c000c60b016855a000c14064804185043ca456000090408154004803484001940002c0c00155122040034002581c0640e8400000c1d01e08800103510310700c14002c007110410107441d00205900c0e000e250020491110380100141030300c0da80c06808075202003008209103030b402c002c0000d0407442d40c6000340c00d448025000074000604503428101c11503003c1129411240012800034170360341c00442c000b000d00d9141000355850300030740151652800000c3c4049400241d250340800845640c1071140180702d03aa60080400c92066070000341c02e904081d00ea60060211140003030341001d0165880940c8c820140e0080e242c80c1180f040104200d41540e000c4401a0908a5129500b803038 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 561044973 1250 561043723 561043733
    0xc09060b12060f03010207050a0c030501270f030e1314010512100b0117040302010e060a05160c02040b04020c0a0b011a090910090f0b0f0d02011704060221040506060409 74
    0x1e000d050701d80b003000c88601d01e1040f650254100c0d80402c0e404000e44182c4070140c14116480a0180b2041d5169400c0c00a00741c41a0200d4107030140a08100c1e94410840000d519020181d100c000e400720180a03410b00c060030b0607692802c0f9205007480480010074414020314590754000303010b900c581e001e00038190a0340072a02001c00d0488034140303a103500060398106c0c0b80041301c03420b02000c0da40c44021400014001410703419040000401e1403101160302644403000c0302001c440089070103841502d4a007220300580f0703200b50400c52039503000900100e540c6403090002812031b400700310101c180d54046403520040180c0341c1c840c2c5006100511079202e1040c5c220200a0480c403070a074001c0e2181400200098003650030580c0c070b2002e0811240e04100034009403800d80002d08a150725035105041c005080701346031030f01c040d5954003658103039586c0c003420000020340140d44e0710182c01190029000d010780014154501c9111001c1212000c00250b64141824960b040c0034010b085a0b005606001007400422 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 561046223 1250 561044973 561045007
    0x1e0b04060b1209070f120b090a0206030c0c01060f0b040f0605090f0607060905100f110c1c110d020a021302030f040201081803070c0602060f101203030b030a0c09060b 73
    0x202c440b44905110360ba409600f0703041008981003421482c0041c0350205402d1880d80b14001c501b031003424005150349070345a40c03d071380b01c0d55550000e601000410000b07900704200c0c3e001c0e0090185010005c5205070300da02050052051a410145108070082810496050003c409000070310550400e585440040c9022036044c607800c9025501614001416408024061380031030300a81e042010307240c89010207a4188007070840030f05035081d030500301000c401103186540d04840b40025001e000300b8103420003012120148400707070795000c24810310007080e10060400340a0a0989260380c0e015040d1806284108400380d01e08040e031054152040c020408118036900ca0550450b409003030034806a6102c41d40d00185c0e680c0b0070b010160343d01001c41c28900f0490126140010741da2540c003500d81c10783c3c5201e025841c00e03000301c1e00c080040c51841c2d0204a07a181c441e1041603c2d81c003a14000c00c00c421408040792504104250031035030003400c400d08001200151007020041c02c40304502a1401e022401840c0f050 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 561047473 1250 561046223 561046237
    0x12110609030712050c0604291f0614031602010e030c0102030103150612020409080f040902040510081003140a0c1403210702010806040b0a060c060e010c0c08070311011e0b04060b 78
    0x610b071154000d041100d0503074423802041c00031580002c1240780447c019101949504202c142e40154880b002c1111070007000c40d6070501085104d410b041d540c82c100846206406c076420f681c1076550710080078100d941c0900007800038480513000940d07254035524041c1c8130780b40c07441003268440c0d20b4041d042c4015440c1448403289a5012500426001d44d40c1c2001c040034807509214400f0f00d030f0300040000e00c08029030090811030703e04440300034403440f00700010341d2601401c40304540c400e001080c0074000030354038904991803181241d040f03079012a05581d9a40c082a90b54006410101600d40c0d15846480d040080308a040404031548035840a01c5003245200d026001c3c0007410b00c4035080005105499583c443c0c01400c2c0010b200c0d400c9030b6034842c0c0152a440704030105840003810100c441d100d581050054085001e13040d65000c9203444141c13600c84854011900890401082d030041060303000f000d0054440d0281e8019100452019a40d031036022a42403800b114050b0303042c5281040a848000705a80f28 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 561048723 1250 561047473 561047483
    0x5030c01082a0c070603200403120212030f06120d12200d0c1404050f0d0305131401091a030f040201050403060c03020306130212010312110609030712050c0604 70
    0xb8a020800e01e45842c0600790454490b0060125840e6554140051603030700311001d685003044410070a00017010818403000300018560341c204010030000305101107103000e0b10518816619504107090424121740d20540e801c001e610000d41c1032009516140202507041601d42008061282040c00302400361001402400106039594240d112450020f0f62841400b260035915103540d14881c120001c0144442c280f080001160000301a21810b00c1104031000da800c010440c0b1103814400c020854840c1c1591000c508102c400d03c203003080e80c00304425100c0071f0040b01c604440c000c18000300044c02d6241550202c0c3c0740c1752091000c1c45a0700c0703000c0d00701e170f4109032140c0840c4890b03030701ca00051301d0f41d208aa0008152034600b1908840e2141e06a0180d401070b02c00300e0b000000ca07031444081d08141d000e0500102014416440100700080308005584202c00786810441d20290613011101d08004040382c080740283c00004090301080380c118441c0c000c00d070743da0400da400d003070b04480d4113941c4003802800180 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 561049973 1250 561048723 561048751
    0x7211e0209160908120403030f090605091309021c051b0906120c150d05160807121b021c020a0c030f05010207080c010b030c040506030a020415050a06050a0905030c0108 74
    0x1038100d03c01e0009001600c111811a03045d20100052400326503c54402540003030941120200a240b113103503400210f50360760b5551410205000c0811400d06040c110019a0301d5445c0c4103c00142c0314074140340405c241c1104480300b804154208541414102c0c2203400c28200309800c502002c1d50761b03c0006420500c01ea891000b1020074503480e52a1450000c101540324048009510810b450040200800c080c40c0206000700d032900b642000600c003030507030300c000411004000910040d00c580040482a880c001e000326a041650321a020341500503e811801078014002e411605041c0031480c41850800e84028162500b2a4959014200603400014104140c606800302030000c2501552001d58101c00c00c16a241a10b540c0fa0740200815800c603402802241e84815851a103842800e12070803015014040b84010b42d030800004100a0040c60a07228450502041f251200301c10034010b40480d40707540c0e685030305040015040b80d50301d0744881c1c4a81d010440344000c40c0d9100540c1604980300150640c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 561051223 1250 561049973 561050011
    0x150d050903071a1621022d0c0712081c0e0d0c030e09010e0a0e1501080a021801030f0809040e1f06060206060604150207211e0209 57
    0x7411881a040c0240494400c60180350303601c0703c4010701c076014005803a01e190000c9282142616940d2100710034010040840c1c1030242d100c00c1c3c81e001401c401a04511184105040c0d0500082d44803000180082c0120003240745880e4203000c1210380084c000c501440031141d009652841342c5841900301c04c50200000d0b200d440441c10361508802c80e4402030f0010380d10750a16800c0010010250384400768002504000d00e4095410700d801a02d068400c080340381342041d59242c2c200000350a007001b0300601c500c5403048150703016244070f1000d400b800d420b4001c1c0200c0b243c00e004018032100002e00c9004041e00c0c90004000044144000580b01071703100c14110f440305802c074000b030000c150314107203180c80e070040604110318070480d83c124000d01c03e90300e0b0b4100040c0b0345840d800c80e640c070000c0395015040413081009100003841110a400e03401c0080c0f0484401c0d03510341d20500070131000c010a1039440c442180350319003000203040b929031030114282255072000a0640010341410000f400d104c800703076a0702031a0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 561052473 1250 561051223 561051241
    0x30301060215090322090f15061e140903100b0a0617010509040212100608010509011a090c040f0605030702010b0d03081b0f0708090a05040501050a0e090102040f060e040506150d05 79
    0x41780051074682d04c10000c8500044414014100c000114403030040c019101180046c00ba0060120448100b450b0b070507408201e03082568003074900508280c042d2014481200b241ea4100700d0f00007010320580011071124145c0060228040080e0070500038854004103c5007540205020641101c1c0200c072540c042c2d44a41c00400c0c0c08182c510329040d05070082042090707126203640c000c3c1d0211031424000700641e5a400e0150b5080300d0309902014602002461850454a06152004c1d040a8000401460240e88000c2a58800021b0b40440007042d1702004100e1601e40a00c81e5420540c8156041b1221031600d0360000e21118000f44043c05046100d4015202100303020103030341c00029913a01683d611803090411500c160000111030340b1810104401048070b041a018050480300003800380070f542e60900c9208418020f004000c919a99401e00000600d00703000c82c440c50003032a043d210107509000500900060320001480c082c0104d803040f8012200c0381c098000c03a001d00d42c5101d0300003030f56201d406103 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 561053723 1250 561052473 561052537
    0xd08070e0a03050a05070f0b0f1b06070c1e030909021606020a020c1201090b0c0309160e011d0f0a090303090501050705041e0e31050303010602150903 66
    0x31030740c100e0845900801002400030304600b26900507000c03240d4403a035418940402240c1409090781008c1c0520140d906c036400d803005401c550040c629070b0301160f03401034581407920707000311241c200055079403643c48244404400c42c0200d0014116030390242c14030648014000310030728451140d80e25800503822000c1c03c2e81c0100e44000e10341c0800199603034040210000e64610039140441c1c800e1849070740140301d41205124641c03011b0307440002003550342d881418079600e0390001042c1e1302c928060940f030700e000c0510903040280070b800c3d10301800311a5410400c031800d1501031203400300b2888101c0c605204090500011207540700400381e80203c2d040415207000c80145c885060f00902030741c01c244c18800c4850708000a001560320b110400854062888015103030035610307108070346d030120542c004a141c02e81200035000740700c1d078050100144a62200b0356610030104140083ea0240c20200c011f01400380d040c8440c501d003481c800c2c5800c6e100d042c134a10f420384a20440e86010424110b0200c4c82d1110a601d00ca = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 561054973 1250 561053723 561053747
    0x309140f1c051606030b062106010c1406070e030109020d0b0a0915020414010c0305040513140f15010c0203030d0e010b120a0219030b241302040e01170d0807 69
    0x76503c10030750b00c0f640e80e032940740381e13002e050040ba0424102c3c14660400b80103658450f041842411142c0d54210800007020001910041c10042a801085e01083e0080d44403450060000000c11492030510380c000c04a2001034581440f90341048a00b074056610039072500e039125001440200d544d00c841600e040240205c800c0203210007000c1031400444103566000c0d2084902100c1f0b5144440d411070011100302407044002030118000740001e00540c11700740000180391013040c01c0003d00d468031101e04441c05002315095000402e0150070090fa10001342c458446401c0c007030924441e0200c581d4006a00da01401e49501300c115950004c1060f026000d4110400023031014040c1461400c48010381a01c0c0c0c2203c01c0d0503406885d414000c3c5099508100b81c4500300e82c0c216000c6543d40c1c0351010a0b40d00d000c0710100c0c441e480300b01000c0910b415500c66445003650145988016501e601e07000e94140e000784140e2000c039960b54680741c400700e8000c0101c0c540740c520345107180c0301c9400d0352a02030a03618451120 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 561056223 1250 561054973 561054983
    0x30f020c010c0201060f0602120406052203060902150f0a03050901090c0e0f0702030f0901030905070b0d0207020f0a06021e1f0f1a1c030201020d05130309140f1c 71
    0x14030402d8440e0194081c00a494030f80705104202900d805040e81d80c0c000d0b40c2410200070008010402c140e6100b0b10140500c1100720340034481014660f0700c40050880d031904251401d5983d40040ca003180b9204181030a01c180c540c521030f00700892140501260700441701d06409050b201c00000d01e20031405e510203440954003421001c400e41c0c866440d015900c00480d0352038080c400010208130910700001c2911041800e41904510300704c0c80500450141c003800b2700440302c910802d000400c0c0888030802801d001c2495039001a1590308500400a6854142000741d0040700084001e02c8040d07404649551410601481d02401551161145150004000d83d00341e9414007409540000c610301c1d00300d1000d8158142d01440300003050a00c001039840055003003540444c034a0684890794078031800121241c1e000f4000141081c1400c1c400308251001200c000c10300544601e05002019045004d0368090030a0040301345a004030400803401a020b1010643d1143c40c480820035075141d1003a00c0703004115402 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 561057473 1250 561056223 561056231
    0x9051009030b0c0319090b070e0d06060612060902030105091b040b07051c111c03151d091212190f06030b13030903060f200a09090912030f020c01 64
    0x85852291103030000c1c1c40300760445017201101c04a51049000713061400307421428140d41d90f255100700703403000b40400b80481d4001c08107010340380c080382081c403d07400100701c607442c2c2034041034880c0b0f4502c0849100d60095481d44c0d20600040c81561591000107038020703d0460395503011040c690301440540190b500085001c000001c040e800c2042c0820f400c801c61000c1c02d0030496007909000700b41c0302c80e00041d0800e90729a00c40c0b034074224030300504400c50303000750040d0034009400c0840d00805003000f00c042d04000040e518a0b8103000d000740000381481c0e4007180d210301406a00d010312928200501c141c5000c0c1d0b5807100e003070000c60001100c400914455001c00141001079410300d00d920070140c41103100c281c0d42c0c2102d00380040c00501040300285a4994143d945403502819681c482004100c11005000e907541e42e006012500401d820078481c2c000040420f042d00c40c03a5645000f400c141e01034024031007150914807060001680b140f103100c180030710790030040b49004503800144024090f0701da0000711903080c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 561058723 1250 561057473 561057481
    0x120718020c030f0d140114010e0a0f060206040b10080d0c080909040605041a060d080c01140712050702030414011112030c0c0c03060c0307110a05030d0509010b0a0609051009030b 78
    0x4003c00400c1820007800003070100120041065000703210910466030b210102e081869201d62141c1c1803000d0007040100074500b066281d452003001d50900380c10000240e80704001348420700601800165001c0410203000720f08600300407101c1d0f16011311000c90f805100400902c0d904020740e40069410906010700301c0c8080f4603040c01c141e00a4203003a2020360380c40d941800c80c60030850b003005d6070503c10b03480603112a044400c1960b840382c40f42d20000584005541c0c034107800b00894600030f4618010340d802d54441e10040c148110360b00450b80c024092000755481000200881e50074881c181c01600000d003410320342c4407400d00526040c001c7c416100b40744030380c0010810540000c000702a145101e540011211141515402e042c2e80704001c2d203007074005d00e500b480021b001c54070990070240c200340c0300c8069402d80c52885da2030710326680011081d180882e403190200b1140e5070302481030340c80c0746c0000c903403a02c90f40745880005892100f950007524021240d045207240301c1030198410500071a4001e890000034a8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 561059973 1250 561058723 561058747
    0xa290d0218150405190e090102190c021305070203090406060513050307050a090902031207051005150123090d0803060a0501050715091406040c05030606120718020c03 73
    0x200c40700c000710707800302603904500c280c0c1040d000b41d1040c1c4100d048010300c1c140c00c0808000340c0c401550304186030705143c0000810740301c0c00111424020300b035100026888505a60700300c1c424641240d44031040049110311034006da6156032403400607007010440010319840e1804200e007541b15501c03080381c1060900000141541d488402055058818081c150f000354554080644916142c4a000d500140808090100740d04075440001c1d40f074401030850788a000c029160649a802c4410282c4403a044454848540c07803ca000d0340da481220020342e0203005440c0c40000e0120540f16000d2481440c0c0d41d000d401403012160f0403141c1ea03140c01407441c04c41c011649441120303540b00b00d5609005031008907000440c3c0d40507a00b9503201e560301080440e08200110602c200400600703101b50b5900c521240b180c8058501030040c0790090f4002e9446064142c200014180740c000c014081030302803004407442129140000c0b401c40155082d60045000001204131214080d0150400104e00b41c00009840a0907903 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 561061223 1250 561059973 561059977
    0x4020d0e0a0605010918080c010e0d0908070e090d0e01090f0e04061406030a060207020a050901031214030709051e090c0c24070c030c150f14060a290d02 67
    0x610540c1c2c24405680c071180840282c80385881800d913000c0c1042000310003d40140c0203000c20701040d000004424034103413441e914016038200070340d000c5800c0a4040c400c0601c10302900300a0306180b40101e07003506141d21316550b5440030645000c00c0011160030700405a02c04d0705084003e201c4a0700300000c40d5103402d0310f40040314069800311111032a18140008107013002e00340d640b003810004c0c007414410409445842c060b43c4a0802240c1c40a03440300301140ca680c54030704890285005841e410038480c0320590161084000702100caa00710402d100300601d0070f0340090000b091390010342c2c0102c9800d101d80c0c687c04040c010600403980c085072203002c005800c9604405490070b4034902048039a034012180d0703440f205520000d03040a2001080b40003508481c0110002c0021906c83e18000b90700d02500c0e210000c812510741c031800075487d11440c400300104d0003400744003510680001c00150301c0c2045400125150400e01c9418600700d09503952040590f10321814000b414000f40b8603d5983d01185070500080d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 561062473 1250 561061223 561061243
    0x30e0c010e041401121b140f032a041404030c0f05031c0f2009060a0207030614061005070803070e011e0207062606121002030a06030c1e090f091b0e0f0412030b04020d0e 74
    0x22f1881c016040700e08030421303520140140c0e05602e030840414840d0302c03800c0808405010507502ea2008000c9002c0c840621254040601c1c602100050205120740b182c1c4141c8000f8446442800c4c50001c00140030a256000c0b2503040318203e072881c0d0341d02d807080300c1a400c001e4a58006080f4a10385101c12013000350000711640310303400480d4907110300310f036024056800e4015190003810482007440083c3d0500e0051888200c02c0300141840070071100c14000e00c8482c440503010311401600070b00000c02c8581d82104102d020b40c1004019040d0000281107030074080440106218814001c2c40d81c1c012281d1000d0100c00d0030700c40080da055560789041d40c08007020700005d22086900303416a107400290841c084a000e0740b01700b0184060984207107070002d5030703000d815410155000c0700d80d00c02d0031400140501c64406a4107005944002d40146490700805250b9001080c520030040e551080000240c0c2a1000300007401c170300e040000d4420111000700e0024001e450079030100034034002000108400002d03501c450 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 561063723 1250 561062473 561062479
    0x308030a06050102030a0804150b0603240a05010c0f020f061303050d03140424020705070509070306050d0b0703060302090a090b07030e0c010e041401121b140f032a 72
    0x4542d864004a9581c42140d18840000d014440400c00007003510098403c000201800032403034406100014007a5402611801280043c02440050840201041c01815807040f5032440004e86080c0008c0c2003074040f4903004141e402c50150b14000c5607140ca985440103600507101d10f40b200c410980c902d00d4810a40015101c501c07079031003108503041c801e019910783c00c1c180310151085501c5554554a6581081106003118084402e0003110701c1550b102030070029001c0c00c01081394503c2e1030203202010310042d000f9400c16080071781c140665140d8540c0d03501c126920401200341035490101c2100244800d400c000d41c0f001840003400158406031300710751065400395100b01c1194581074002d804648880f601482d0756080b038856203c181d030141454080180010344081440340c44c00d507500c05091000d801440011030748801031801d0050011503219006042402001c406013000d0001d0f8070b0004c000d462034030502c20440a012076440501c88043c4807102c03402ca0a00da0309010300f0140700c41400310034a42c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 561064973 1250 561063723 561063731
    0x1f0b09060c010e1c0809070609032003061e060a2907021008010806130b06213c0601050904021c06061e0b091507320c010e10180308030a 60
    0x46c04038000b04003c4106d80058a50041140c55581c65118228022030949081c010400f034099583d24180000e61181c200d52501c05207402003000440001d05002c1c042c40e000c0c0042182c20300407280d1800e1000342d080c24400643c401d41e0300505075a03000744502c0300007e4100b00d42180c400041ca400c540100c0c180c03550401529604d680306150b0320103440302018054224805500401c1d09824128102c0b801e03511010070465446c041f40c800d1510705000780401c04104504a800c0314a4a00c4d001c1405e00d6000c001ca8003040c0d4180620750041e903071441070203440c1c45104410045011542c80c442d808496603c0d0a04d80d05103c0441e0820380010412440b90030b42c90100e0004900403048942f000d64151818421142c5c10441030314180003c1a0340203c42110780d95040000c8408035250001015524800081001d40c01e18035803c14040c3e0103441924503095480041e2201c096a00070041c004004001d0300c41524058484c681221501d8425801003105a411200841405001c0c0011441204c003008288 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 561066223 1250 561064973 561064981
    0x5010f0506090f06030c2b1410090515030a050609070f0308030109020f0403150c0f2d2105090c01230f0f0a081f0b09060c010e1c08 58
    0x410248562400b480e440806000d40106503d0020080c40e0044600102c803804c001294120700c4040a1115400d580c1e00e005c40000c4030407105a00460000f40080b40d8021140d0a00380d041da03806148038000c812800d903c1e000020b00455040507100b101d044010115201400c950030b02c01d4440005440040c45405201c0c0c004c19180c1200d04100200d0350711111562a603842c01500600a40103444504c1000404003c0000422007600d030f2130401c0d803410300c03000590310b00168005c0e00500ea1201c04405001500c2c965103501c40702c1001d0812641120100c4402d4010600e90132200007a50481c8046445810310010010707800720b41c0030f64400e813030100440750074111b488019a0903078011f6100c1c503c1002e03c0d046400c1403220358400340c102600241000c0e4140003004414080c60f0300021400300c0026500f504211602480d48018a4504090b1407007240190130f082c6009410711804a00f03a000d441c0005541c00305a1095018118604982d4169052214480c03881407107400c0340c0000d0000541000049 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 561067473 1250 561066223 561066229
    0x325081b0408100e0307022d0109050f0d020427030e0603040519060b03030f0a1d09070c08070203120a1d061b1c1806030e03030606250605010f05 64
    0x1038041d02d0b800030003040b0000c2a0102d200c00341a0304070380601c190100340107040050700c0320b00c1140030040303100d02c2d075484801814081507004000500054104070100e0820000ca032192495414001c0c400c0d903490a020216001040c045c010b0203080c4882d881c038100c003100800d080341d00c0d1180300521944d20207515485040402c64680800c1c0c5024120b074001d151481100b0b0072440b11004000e211f850701090711000c020000c2d00f9a004103040d0b0205c0b09d40040c50002c07540c0c0c448401c2507800251010008914501404202e50030401408042400301001c03c410078000d11005403500994010111282c44141043c4a807440e002070b007140000c110000da8004548564815504030380c4400340203603003080000250901207082d400d540d405c007806840700300401c11a181110051003505178070f601e21441100f072000300c0b501d42d06a01003001c140c07602d0b030712403600382c0c001c000c4070f81240b4101c40d215100c01d00101c1c7d52490114941d0103031002101a44000100f04c902c2c0c01160480b0358076404032055581c0c2e1414 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 561068723 1250 561067473 561067477
    0x91101080604021c1a01020c280e0a050f330f030a050a02030114240a03211404060206010b0309070f0e04060614010203030a091506030516060507170325081b 69
    0x20b425404403040c1c084842040c0074009c6c001159010000c0d8207001d50385d916005142d04025501c190085440c2d0041141c0d50032516085900654110340c0a4410900044c0ba010747c130b2294100c204000075201e016131601ea441000c1c9044040004003a6030070403020346001c3e56118003250040740a035003007100e00403059012108951050704000318400d030350301c402d1214070302c59504010055444500140040302190a07e0b551805000840a014041c0d5042420140904201002030301c0b0000007080180b040542c04664503046039032007403001e41c4070f803101841c85082040c00c2c5c01c4008800c0307684100042c0008540380e05401385000783c50070407000c1d884070948030344140300012090150b0310403c0842d42c6450b0a5001600080c0111a50904c5021180c0080141c030030700e600c00e0342c080c0c0c80300040700450016590130344002d290904083d858007846580d000b070302c6442d00403290300c1e448c0c0100009007010480c16005568280310300c05680d164215800240c401001501c1a55650703a14641000c02241c1e0501 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 561069973 1250 561068723 561068743
    0x3100504150c0c08040306091103030406090b0c030c0a080409060b0306010801031217090d080c030601080118090606062105010e0a15080a030305070f03091101080604021c1a0102 78
    0x5a4125101411804001070720b0159000380401c00e22030000c0010401c000701800c0914840c0d1404942c1e1040e074241880b00236001d6580a03ca0b0700204420130480d50415070f0b0000b21b40c1c1c030300c010703070f0f01c4e1154404500c1c158041d40d805080c050061180380301c1005009801041500c2c40000100049500c0d10140c8480340000c07140240030460354070040c40800e210060900d40aa0309280074204821140300300b042c1c1c07100c01c0e50703183c405070302c040303501001c00344c1020445038001107448a450461030308000003071010506202d0200221023032410549911141d41080d1022a0459018411181d843c00c0040c4440705480d0b81d40301030804000795580c2c00c3e0490042d18100ea43c1500c00b101c1544034281250010400d0032250510b80c4060b80300040c80c118140056030b8001c0c044c4c0c8001a80b4940030b04050001c00308506190101071400c01c0030400522901d825018040081c64800c2c12660751038081030007881030304480c41640f03070741d0f0020a040b0f4200d0b810090f89070101c1b0700b43d418050304001c016692100091 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 561071223 1250 561069973 561069983
    0x2042103021f0e0d0906031d0c0603100b03131406040c030204020c16081b1002030a0f17091c03060b0f0f04120c090b060f180f130b03100504 62
    0xc1011904100c079002071106a55400001000315011180074034101801c1300d081c0109424000070021140c242c0b03d2640320044010080c0890032500c00c0e450707200d0300b010141d58480c04001c80031130400584080c024001c1d05041265694904020f80e864041c0d001d4080100c564030030240718000192000320320540541c3e8015030810038141160308100107500400b8145045100706102415014125040300c00104001c03c0a00340c141e0001c0c419075240f004041e5003500034480040746020300c590010450348518182e00c1d0078401980c2c4c0120844248264602005000e41b04905100c80c440010801c9005080040ba880c00340d00c01010007038044c0c1c1c81c4c52007a000c0c100d005200013507060350385000801c091504411003501c0c09446000b58150450f0805003901c101904100502c0303001018803800344141c03800c442080c1011082407602c41136100d041d204074082100c00040c0c40c01c5072101c201880e080e0800510700c001c7e000d07501c022000104030314203107280300348202c10914940103101c3c1304a90080343c01c6 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 561072473 1250 561071223 561071233
    0x9050c0a08030307030e01020d18020f12070b0f07200a08070b091309020402070f11010c0b07030207020103060521070906060906260a020307121103060d020a0e01090204210302 77
    0x140006a00420000100b101b042d5002c12000401a055114807040d41e20ba4200c0d00e110181c0c0f900502808000b01c0d54040c1c05202c42e110408030b07143d000640f81080f2100c0301314070750351a00d040b03081420700d000b200c40c000c280402100c0400c081c0e40c0704000e1240400c40540702e07400d01c190380d8001103681c0d20461084100b01d52003001b2130542e0f42000381110300502c40d840408200b80140e0350102d0200ea104076015100d06a10840d2a01000408518450088000d10348441034028989951130644005800365083c141d0024103c000c59000350031540040400909906001304800170059820104410821144c010f4002c082a19401403182c1d5058515aa0f141d40400d130800c030f0242d500188030020410700406041d2010002c02464040c6403050141140150300c1e0f0a00c86006031079003aa1a21140701a800c040400014603174a0701500c2d401841121140e03141089400424007103500c5400045104004000100d48200c840d0000d20032a002d107100440000ea24401c21040580071010081c01a000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 561073723 1250 561072473 561072481
    0xb06031606050a0306031e030f020318010c060b2e110a03031d01050103050309090708072c1302090909160e151e0109090e060c0304030516030309050c0a080303 70
    0x4148098000f1400900700050b0960b1a0780b1a1403000d581910514580d644404c6400b0405600881e116000610303400194109070081c6440ba0320300c40490000d90400c1100c1c081007060000c650010400450041e192401c2c00c000040f0401c1e40480d0352101040031000900c292039003d2256004d065440320f02e0001d001c0c0e26a0b140e4048024100e00001e00c1c02e5070252001d400b02004080c81042e0085115800071075032080450140403600100802c190280f0031418100240300e80c01c000760601258285100f801c040707000741c0402642c050f00c0205140c1220740c4409c0c07010503440c0c650080c007040c0b4040301c0d51100c82c3d50390704081c0d035142c0314454005516030b02100204003a540c45242d0503003085070031507200540030010303010032100d644808214134440252007940545503001942c0101811440c44c041c0040e04000c00095a0f41d000a031002081000010004041c584204141d6110640d03034001c0590f41111400c000700038010b41c540a4440d4050501030b41241e19160404408a56042020b141035541d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 561074973 1250 561073723 561073727
    0x40b090a02010801051c020a080609100501051c03050c12030906011203050a0c241401050402130515041a0c0705010c0c0302210607030e0c030a050616051204060204030b06031606 78
    0x4041c2c021b14010030102954a006035580300424000c1c08841000700250b28105101c3c0e0b00d040b010500b41c0f88402e00d004010b02403900c0d100b0788020300c0a2400042c103030800840c90122014428140041030a0044282c804107200f40e540c0210300911080003140c0e005c0c1d80300d034254007a00e50642c0c8002c011500810445901c1d40c01680b1144101e07004420800354030380700d440344980c0e050200103c160b03556500c50070b0541404520b070b8031601501c42540e007141032190540d076012494840f8040e1500c651fa24182164408880008650181440071280034081d0811641850650020040700760103000d140e4000c01d040d449008204162a0000c50410801340f07550240111118682c00b184004e4060328212041031004002c0719014950f6581c0004103002c210150078188034084001a2090f0003901e000d001040d40083d110303400500041c0364104940b5581000e6517103209a00342003518010300d00c04c200034404c0a501400803280911503005280e500d54040503100d0100710100700002144031402d0000038 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 561076223 1250 561074973 561074989
    0xa0206071b05010908070209070e060d240305010204051023090607052506080c03011401050c010606021b0609030a06050603010e03071214030c09010804031214040b090a0201080105 79
    0x31286075070140140586860b02400d540031001e05490b9800000b403070000b14104100815808151450300202d01003d0400182e12803080d0000080e140c1c1e16071072a0081c0c050060812107008240c1401d950040c1e0396850020301039080380c41074900c9a800070903602d03041d41c082e6074041d1100b40d91940e103803d4120b490b0ba01805941000e66503503000032040c024680042d404206900f0702151104000740000a0400049080e030780c1d5030800301c10042a1010300c607198540304140ca0665108051400c5c82c190790b40c00480391030080600c110800d41c24900c0004080307402043e2417104503d69600042d042c8805010321a041c4a10080503815905c07031040103010510aa210b2504914000d001043c3e5038003805502e49550031104040d42c24048010140514942100c415910440500b180a05518041510324010302400c58424141300308800010209881005503084c0c0c200c80842c100002c2d8503041628005113412141100d221020700d0224010442c000340d545031aa605a46100b010ba0030141801020 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 561077473 1250 561076223 561076247
    0xc02070b0441090115081302181006140c1c02030d1a09060409050d0c0201052809060e0d030311160b19020304031d031204080109020f060a020607 64
    0x3620052140d00518200440c02e00201120300c042608540d2161040009102c4103030f100c8009400c0c07601d0508906a000040c19030f100c0d00c034031f4615465081d14008507000302c3c003503030318000d500c406a41000740c800740a02c0000b080e55990741d82c21088007001c100c41c0c005031081640006603503102251124018a0f031080a001c1c4c00614030541381400000d900d02400c1d9100e0002102c0d0300c01c1c01400707264250801400b02c2d9440101201c0c1401107807060303191240c40b580200316070410031892480e072409690003503089522940d500202107140d42c000392001c1c8684048490240002211410001900d502c00c0f240200801d00007004204111082e6a00b9002400e540803c40043c0d04140030380c41d0681c81000c00354110900480303d00130140740070b94180f5604113407180407082844c410f10070300020071750205400c0081c180307048024200482100010385080c840b101080e5080c07000003000308424006411210201c2d00c21b4641d6042040fa102c20000c0e24001c401032440183e02039800200024843d0b1400d043c1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 561078723 1250 561077473 561077519
    0x140115090b03130201260f1302061303020f010206042f15030603100603170a1b11190b0306040207080c030d0c08010b130e0702030c0a0b040201030c02070b04 69
    0x19a03a9030303201e507015400880d482d0080404180d40f040035944c00c800c3c0c0910181d4a261440c8044104905c640c0715a007000d050b202175200018005409503040c66152050113400401c1c4c00e4507403103011080c0030740d428640012405120b107400c0f4030b4400e50000800c1c0b40115800341800100304603a2100242804c81524840c1100c8100414180607803946504030320001101180709541e450b0441c2850320b0550800303006869a071070044100081082c101900040004c8021b1103035a0f01c9200e0300880300c000201105208103006100c45100300000503e0041a1001c15104400140c00c0f051f144240c084041c80f400481000800001740f076490140d0080407400c0c07103101400c0c10081284070032465034008034061021190b82c0c40e4101070307040d0030240c05801000e0001d400c901d001600171130b0005840580c07040c0c8a600c0b4103074003c210124000e02c16504151781c080101c0e0041740f46400d09418580301914181d0200b490180d540280600c0800c1c3d05c1d0a80c0c80c082000c61600d031400b06096a00329035440d100d81 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 561079973 1250 561078723 561078737
    0x614190507030b0a08030322030f033b0c01020102070209010e04020d080a030b011d100e04020c0f1b010206040b07080a14070e040b0f18040606050a06050a0210140115 73
    0x20f035a075218120302016001c1742c4011030b200d01d800c4c491500d0362010320071103001900303030740100600003540f0100d4101d0103c1e9034580410381d05054005a8501d21800b5804410010030209103081000b1250b2130b00c000044100481c2d52801014005a00301d204542000e900417400a006003d0b070146601c04c0c0c1c0d000341c4046c003840311b100c1090300c3e08807d58000381c10701000643c5500000c140b07580d0100744412520b000c00081615002c1c0d00c00003c120301d985103110401d2104408540c442030f40d403641502c1e01204040c041e038032034890b0020040c0e1180a0704100c40402c040050310410254400a241d0b8030861b40241d02c03250a031070721401a14045001009000042d0b201c80303005500003094030f0359a000c0c0102d6101d0802e070780075507401c000540f07002c00105400740b0750070828107005640c0d0580c0494000301001040300a503d071070400c0b03c040c0500780c00003908444000341c00140142d0000041400c041185d080c1c4051405410102c0c084c3d03401302c410710f2410780300f9000501c0000c0360861f00369121180e07401d00103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 561081223 1250 561079973 561079991
    0x801020307020a05060c090d140106091a03070b040e0c0c120d0603050607140a0e010e0607030503010e09060103020a031425080f150705090d08030109020304061419050703 75
    0x142aa4821100000140c0011010104100007040529040314503d50960300780f824103c0072903002220300c07130701420380c54540e80c9401c80d101082d400031016220205050016251034094a2201e4800500042c002c0c42a00780028541500200795020b5410a000f070032010b03101c42c0c0da141d025070403500400b5154020f290103006050092401414100c41190b80443c9051450500a003403c100829000910105010742c49800d040007040340c00d420141d0400b00d20301041c0b0401216890005480301c0d400080000d90401419003180185048035038040e01c03110903079987c0c0b811a854031000c0c03200942080900b0428000202401c1030181601a006c044414034644c81800000008203450340da158a54401c40600002d2424442040c4c5d00102034000c100250030b100d2100350252001b4a92403c0180103e43c841950b541d12940a03051900709000540705e50712840e090000b540156012142c00349405800000d4a4810b01d005200300201140c41641030211101c800c05010000c120300200f654910001d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 561082473 1250 561081223 561081239
    0x2809080f030603160e0115030212220203060f061f0507021e060d06030516061e0201020f030106110d09210602090d150605030705130c090b0f0a0e100e040b0604 70
    0x8000104142035101c85c16503d01b0358403844543d41c410500d400c0600400040080341011140c503508180e401c150f0209a49041e0800b000c111170340d0b0402945805818180800314007414000381c0108800c60388001c01280081d200c1da4070840c81c1c0c0e140c034041041400b4500241c42d1000410a81c00060109110701c40350040009010794404403c03440300958586052041c2315040200d180d165500081c8440321504000002d003100d0084010120358808071462204a24400c0d01955400146843d0707503606c03940c580001900c10060040400e449229500e4249220b61040020100f200d20501ca0f009900300301098410360030703003450030655a6030f400300455005500d40070244001e0900604002000b10015810340090324540d0380601d100740d1040d1f009101c50b98031104041e000341d006003400035030100104401c0c1c400c40300c0703984512022140820700c4030f8004401c4004000151880c0d0791120b0351443c000401440c1d50007030070410001120704152081d2030070558080c0c044100007c0c621030520340d40307800c0e03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 561083723 1250 561082473 561082513
    0x3010906180b15181f03140c01050310330504031b050307060c0f210809010c140c0f03070c0f06030e03030f06040e062809080f030603 59
    0x444241d0318014108014803000b2400d003900101d400c490010f000b200c210006004041c2d1080398a142d801c0350003c07540040200c0e80c0300c01031342c24080148031165641d05003504c00c0600f0001820b07103409070045c000c0482d8841c5044900c1030181c0113800034450708080b454041c0760740001d0200d403d6032038034081010920425221081420160755040d0f511411468845d0f24a40310414425040702c20f0340c4140480d903008034545056030b0745445e1451034503200b0706064141180005000d000c0c4c20680d4052000c0398511000d81700380000381c0e11040d043c3c0d04c503051100e08a80017005480c00041708001c144c111003104c1401000c100000d2011103840c0580700c1c500f142558030110b4202e8807402c502c0b80400c0710046c00d04141c1e00410b0141020072a010b4449180382d140e01c07000301034400044410000605c079543e5030707001c0c0c204900c22408a403403914060144e5a94480e1580700440a04c0318480c01e04400741c0d5501a03100a9984030b80d117070707082020b030a2080655401c00341245a060051800204452041c040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 561084973 1250 561083723 561083741
    0x2120f01020a09060201062d0929063a02031306060803040e15210a050c0d02060915040e04030513090b060912010e0a0f0b06030a02090a020903010906 66
    0x8001695509515009005000144d0010040d6410301744204428152140b0340303003012844c4203850780c5d11100320000c01038089454100200c400c1c503040d010108004040d88400446401c1004050040010010407080d0b0040c007207003c08502490000200d410f00808a1001c1c41900c6880105035001e20303034000b02681c20455a803e0b04005000240e010722109010342c40007050080061803420341462040d2000c2400202032101c050060640482c850301c4410300300c03140010510f0081c00c4492804001038071003005910551b454450308040c5141c0740b41c185558280a45c0c01400503280c07424920902080203803000d290480f21806000000c0c144640441c942d200d50300c0b0342d0340e440d0b071030b00540b181c0c4a140c02076800c002140c2d0b16058420300702d47c07280012605401d4003103401814001d040d0b100c0601502154031800b01c80e0080c5a00074040200c4010301d0007031184581110005580d440050540e1240c1e46000079500109403408184000c0705980100001c240c050000f00707809003203454038001d40c1c01100c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 561086223 1250 561084973 561085003
    0x912054302040b030d080411150a1103040909060b091f0e18010e1c021b04020711060d02040f230603100302150a080f010513020a030f0908090108150303040306090212 73
    0x54104001c0043c0c280044440610803100500d0b09101105101d0442c000d82c1c0b00c00d03050100d2f1100c15140c0c40010002c0d81c000740001e003403c0c06408040c0c500305c40034180c59410940a03032402000704024080d1040c2d0640da17950340c00390390758a50b40b40c24040c41035440090140075030b02c840806030341c511410038020501280327400c400924080b03441450000c03000160200010440d0444044128100c0150f00440c0750f90408aa0242e114003242c00c1007036880d0640961710b03034803140004641e0300385c070034a402501c102c540700245030100036526203521501e07805544410521517410b0f00c09007940c0c5002c01c080c580194205500521007a100d5011901d03194400400164100780425004003c55220f03080540c000c02d441000a030552406010580000308082c004032000e40115109815510070b07401071030701b407008880910806440d414610700c0c42c0d01040406000494403400a980d082e1802c00b48100e801c0d0103001107240034a0342d11141e00400100740100c1e805070b0400d6450680c2981007189419a80100d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 561087473 1250 561086223 561086237
    0x281e0e03030d0b090c0a0f050d0e060106030e01150e06010336020f1801030206180901090f05070203031306050a06150807020f0708060f0a0912054302040b030d 70
    0x601304060380b0002011181e20480c01c118103c41c159018115480c07500709414a151503010002d242c80150400348115000340c481e950001410303650640141c40c55112a100802c4401301007100d80c8a20031b09401010754000704500490550f5200e075120b10514a004041840c0803030955031220b2680414075035111a810342c1d6a980d0301903141c04001100080c01c1110300c00710700080348251a5111005100180c426000400e0469801c2500c4a8442c00c50ba0010030328000d40da11070340c400005000800d004041186440c0019400c1c42c000402c0b00e008146088010151808958464014010051241114917100d8000181081483c0038441b0003400c99200d5505a01e000b4400924001c0e00b050a43d5480d88607840030040c413000418400c0d000070100500030715590303031030025401408510100a0142085401100c40d041e8040f015100c555611404191354100c405003100100d0f80c0040006543d0000b02004032a14001490032220346202600c04180e010300740300024100500c100c0c01e14086481 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 561088723 1250 561087473 561087491
    0xf01020a21110a0f0b010509041e0516062102040b030a0b030118030320180d1a0115020607090f060507030216080a03020123010510090306090602281e0e03030d 70
    0x340456041c00751a041e240c080766272410b611441648550f1284811400340d1141c138030340601c0b9081c8400c41000090817039181d0030075900d00000788000d681c1c1110000c1d40c02460061942600b8a000b201d044441c01003219040d40c882e03408240051081e024600e07403640d6075031443c002d010741c005003c20440d80a40c030001840407249164a0010050700c8504130460070810183c0f181c10000040c03112a03010a465490200c00685000911001582a501c0003080c806000140e48150845514801e0819038243c880e9030325421015264001d09014202c0700030440c0005100b070510940c0509500d41c0607204940114210940b81c01ea81141508601002c1d08210040300900d0380902605030812480001d0f0505130100f00410b448859045c01114824110440701850242c800d0f00311102075600002f04000840d072610f0500000d40c81410941d50141c0141c07014120402c40d1482d40c40d1100d60ba4071070420013112071403e6049907414003035480511422540f102c03055217080018116041040100180602c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 561089973 1250 561088723 561088733
    0x62214030d0c0510020906040503010203093301090903050904050a060503010614150c1005090303060906060a140f04170322082a03030a020601050f01020a21110a0f 72
    0x30005581ca8240202584800c0015600207021406103162001c01a210a03e03100050420300c1264270640d415030001c010700c09a21008104410724070020300c101442e480007004a441d2651602c1c907000341000d404070040000074066040060058800d1070560710706010900054211070042e0390058585984460501990400344100c001034a500b218465881c0f00d40300004003c011b81e01e0f86806955004a40c03002c8500003000b030171b822180d5187c0144407034600404600d0b501e8100300c41442c03088460700d001c42c0081c20141d08450355203c0e00d58482e42c20b28004a0384030f100e0f40c000b06a00002650400c800504c5414101504d158103904a0265554080b201d00c61040381c41866030348485819420400c00c40d203400062b0604040c403204141e8906240074194403120b0010041b80c1390307010b0000280081c1065404190241615000c582d555825892040120394811403e0401494903407040c03120444005030100200b0400d50750b141842041c9000d40c0c3c100d061540080d0119940038404104900b001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 561091223 1250 561089973 561089983
    0x6040204110c0640111206012405071a2503020d0609060b070b04020f120a0204050109270f0c06050d0c0c17031b040803070203120a0207030206221403 66
    0x341c078030700030000c1007002d007508803c04c045801001303001c14150315040e20280c4800d80c0c80e16285000348140c40d20b0b5030f900d1499411f80800c0821031805152002400302c1e4070f9000340c0c251032603280c0200000c12184004600054502c0d4060174100b041c100c004041d502050102070504509030165502503100c0304810469405d4400a8103c2000d00781082c200340150411401500d42e5030b6005020900c035510744c2e0000c00c000c1003e4210032030b080030758030000d98002c0400049804402e032080d0740411480c0e030303554840e204440c103c1d0070410302c01884d50b41d5203e02c46040c03000a54128020150710001e81110703940d901c3d0f082201d512842c04204003148c7c0c142e40094620030880d51042d01c0c1802d2103044202d07900c0503082c19102708003070586500070011640341d10a000e901164082100c118941e50b07501d4102059480d0001081284640300d0100546c101084600541d08005c07203503001403070403a00356400c101a5800400607201382c0c40900e07250208603880c0c010210b001f041b2111a41c42c01c4005c41c002e140c01c003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 561092473 1250 561091223 561091291
    0x30916150e030d08131a0a09140c2202040b0a020f06010b0408070e0901021c0204090b0d020603010611100c0c030e0316150c0506091501080a030206040204110c06 71
    0x290864800c4900b01d0740c02843e891781c440d0722400240358082039071600d40140d0b035040141c02e400c440b905080040325411580400074103809170f0b884031081680c2d54001999400300a401c103800407695011151003600040c80034204d2000100007500f0140c445403501c41e0360b0412000000181e00404d90303082448403d0101d203014118610712503140a042800301d5607a140e580c8548050920940c0006481810a40c181c40010591044031981c50104200410103504540600d1800b540b500820081350f02d01031040c000c085901805542c29686400000d40c4c60081d510703c8240d0034003030305401c1e001c20162403040b89416003083c1c40700d03240807081d0f04006240415548149000b9445940c0300314410404407065000c40d03000c0301c0003010501c404002240c1140c0d606d10000c100384141d40030702041400103d21000040c82081d95454242e1384c1c0d0394615a0b03840481c2d409000b5800c56004140542091307081000b00301c1010341601c0c50050740b030112600e070500880d20443c1090082c102c180459000040449030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 561093723 1250 561092473 561092479
    0x2130306110f03150d0f030807021c120b04090b090a05060105010806010c02150c030a020609060907050a1202010315090f24120606090518010b09010308030c030916150e 74
    0x1401d02c40c95000e0700d1407202501d0525a4040d41e4454022541c41164201c20254812241500c101c55450098010942503d02e0030160050309152a42c5100b02c0c1d078144c88013083e594502141465100c002c2e001441280100307a0416118120b000c04038600081d401d0185182c580203082404003818810300300281038000361b04104c1140d0a1000c560f90112005030000e07011220b038049030002190501c1d00d48a9004130309280d020100c2c04510164022403414411350102d420b9405036580d80e84001e40310196809181d5011041c010b040c00101c508000c0740309010b03c1818000b4580e401003000e00c0e0840030340c0e4480d8007450340310070250008400c0c0303002d00500c003441c0842800e48089210303100c56449805010300100000310020034000d00020b5080341c0001d01401104010600f40f0f58021078105501e11080c81056007007208210b003d0421601e81d9040740e82280f4405e007180c6800c410f6241c0350740058442240c911a0034014000300000903c0341340103084148120000e4004100042d2241c180e100d05144 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 561094973 1250 561093723 561093727
    0x80f04230f010905060c010e0d030209011413360203151e0d0611030103050f070b03040b06060705010917130801060f060e01180312120c0906051c0213030611 69
    0x20290360410160000c0e02c104480740b0351154810403134980140b00e00103500078980300e43e5000c61000c52b00b5500614001c0402e0b80d031860034116070440e405003403195002c81c0c25010b000360020042c1c0380b040b00ca0203080c54560010401410316004100c1c90307219100c2c00100b0515400020f0181c0703001e1241c842080000192903501c2410802d220354040100710303040d058000c0300081494420000994004440c01c1d004110030364403540c4a040c00f60b580d058014404100340306002022601800307107030540b44100d90080303418131507030364110500c9070350b4101d1001111381d5921901c00500140d00d0158103650100c150a01684032162004a5107102546600161540c1d15107170003800713142103a0002e4801c0e110142880c6802c126020700480d01c1030880303200d002d444200118040100110100300d103080761819a07a003104010701180d040b0440c2c3d031040c01310020608481042201e1030080c0054440543d44242110000104054404c140da00c4400250700760340d0b103210b05100b045110701c40e007107688100025080c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 561096223 1250 561094973 561094999
    0x6010e0a0b030a02011205070c1703090d02030c100c0e03060406050f0604020903060a1a0a09051b04050915060c0313180618090206040f030f03020105071404060804080f0423 76
    0x40c00210032070780b1b10030312075490b54001080c80c2e0061501014a40d80503002080091000640c1c125031f8000342e401400d1801140314001c1682e10000c1070b80d10001010010703145480380200c0510041c880b4031040d40a002c0364455004d21a50144095489103003d14404101c40c41d0051510301030810040c0301a115920501c9408200e40b400203036035500c010007180024a4040d040000103000c60b0400151b90700c81941c90000c955440c1603000342d40240e44420b100c1c2500d11542e481d04809000320b0142980049010300010120f00400e14981038840c1d01402040c41e1507503e2000c2400d550118154040c80a05207404200c202c00116400d401c0c0802141d0800c03a56051030b0140c240405000c25000403a03441d11052025503442c10110b5000b80800443c9560041d540e2030b101c0d210740895081540503501c1c190000740614059130f466000c040442100507c2c0030304009080d80e007608041c105580e2480d060004250a104520040c0b000e4680c02d207130300492000300801216103030540d0880c9070140e44a078440c1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 561097473 1250 561096223 561096227
    0x150c080402031507020d18150207030501110702090c0a18060e330a0306180f140412030c270513150303050a02161707090e0c041d06010e0a0b030a0201 66
    0xd41d050380c585007d41c0b840b44c41155005507018640c004541101e000b0302c3c44030382036800103204401c41340304400074030440b200b040303140110740112400030790056003410000b0b51a10240c0020829000c4a0601200c0600e44034080e2107200f05a411042c0443c054040b0340c4603501d0001d41907020003100c1c6208440e400d10082034544407982c4041022102c00000c1403a0784142c1c042d4112f031000d42104118806c101d22107203522409811201005210b80c1c2c60400c9184d03c46e0007030742d216881250809002d0b220f0300c4044400320700a00195107020301704415070f010314214006041c0242c4110781300441c41c084450504041107030049d000d015820086191a00307940341800c0751000310003101c0c0c050814648030080081c045e81003480d0b803000c113107180c551110041071403401021542c000c074150340200c640c225244c0c410b68003110b402c00c11002030380d031040359981c4152410390490b8402c0d003110042c00c80a508000d242905e0008280c012401c8040440d04000050120b8031034201000c80440092122039415000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 561098723 1250 561097473 561097483
    0x1240f05031f0e030f21060111060708060a0905101403060709050906040204170715020706020a0b0604090203100c12050403121a100915140f07150c08040203150702 72
    0xd0060b4003a168080c42802d02001d0040d9000007a0503841240e0315408002c1c10002030b4900302041280000b00700105449510030280c403248242c184004040a484030101601c04020007822554080c0348600c001c1020510b074000c003070244216071454120382d03007443e40d050100c6e601c090149020f9400341d01000311003548641d40608070782042c1c6d1080401e458072804a0b02a105a4000e280038a0205070080c100000000342c2000303c07820000101500d00e18180c0c202c1c3c54120504c200c0005038416034001022940380808550880002000002c24143c0f40c0d0209050031002c0031070050013662106580380050b0441c501c0b07000903a401034200181d241a0f6000340c031140400b04940035403959220400304841080d0401d80b1101e1000f844402c428484000050a240c4140180d0000008440d0100082030040e01250f50b821b02c2d450025080182a0022003101d030800b1009494522131110340e91400e000510400c07070306140c03582c1d50448502c2d05005151500407d801e22450a50b030800400c40d1850340840c5c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 561099973 1250 561098723 561098773
    0x14040308030a0209090f181c120e07030503070c080715030c02150108070f0b0c06132103020c061b0315010e1906110615040c0201240f0503 61
    0x2400d0780301e8076801c410000038040c00d441590400080b04c1840b09008461030790620404070084800d555040c00b2000a440300b05080090414007507010190700c0480c000d401c0207803a8000c1072030009100240c488502e15110b01f903401600c0d0f60304001500e00c00d001d080d06405001d0001c1d4030040c0344040c5050a114003000c0600442401c040e561118030780c41794401e0100207101d001d03004582080f540c4605034151076042c14030400078030400308400000d801341210181e4a8050740b04000d011030750f0743c80c410060741c3c200b0314000300d8030b00880748403e008a1440101c543c003030304116980142c44062488462707140290140c0681a003000c1018000350621061003201d5100d1725840d02300010040740401a5620201115503950045100600c5925089107a050340b048030956520b40c484606440500c9444031401d0390410240e2403959404c0d0500d040c26080940b07080c2c0c06100020b103330722400038848a4100410070b40c100400500e00704001c10301c018030089018010131000b410780b614030002c0811070f9482c828 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 561101223 1250 561099973 561099983
    0x1082203080726180703050c09040c0b0c0601060909090c0303050906070b04060c02160b120403120216020901090c1b05010209030a051005070507020d110a0f0b0712140403 75
    0x100000708040e1146020307001c02c02918001640c51425030449641c0354004441d64080c0d8002500702c4c1440352000500315084942140c042c00d44054240c0c18080701550090080d00c000d0790492002405003645002051018203007005490716505100000300800503660003140d01c9800c00c03242102046c030a440000803240d2505003140c0da52142c0c0c0219410703004a002c042c2604000b40104011b010131504101c001281c0d9500341c400b0940100d440b4a0140064000c01118a400348001044a98420b82d256005070003070820032000c654041d84070b01664400380011111901d0002c0346011420a00081405030440c481c0a02c12421407083c010902c0c00c2480c9178403024420072101000f4801c00b0360441740c503c1c1e40601620849021400c00a540f0720300c000901180d40c1c0381100080d9036038400c4050700d111310760003483d4081100e040d443d03501c0c0c4002c802040a9003c00e5030400020030b10761603800e11b4014400b52580f245c407034100341060f0710000d000e0302c201c0f81840040e0b450080e443c1d480c02d007140c05680e400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 561102473 1250 561101223 561101237
    0x3050c0d050c040207080d060510170703020403021c021e01020a080915040617070804021003020a02070807120b060909070b1c021b010b101b021f08010501082203 71
    0x350030454501080852829046840001d50a00f03011004d00208400300e25131030148072203035560707091144030494907803020b00190311800000942c07810074104582141c2c0034540035041030313102d400050400c10403000da83c03458001011040300b1411303e11204620442d900e26507410b885100c1002030344403851200001c003030301c0b4001100203040e074450200e007402da04041819070f11140c403202c0180017451619400c1c0c501c0e03c054800580d04501c165480c074030031a809850180d0000c00c084064000e03402052140c0154080d1040103d9082020083c1c00010003240c050705101303c8007410032002c2200d000d03013914010701962040217001c880020341c680483c0d81c01e24085664a40042e909680196990b8104080c5400000c100d0140c1c0002e01601484c00c08043c020825030014008000c00d084100c15440c01080c400021501030300c080107a4003c0440c000f8002c07418144200c1c3d10001b118116003000c5c804138034039a0050085583c090f0791640e0042c04140100c01e070344500b0018020040501000400b00881 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 561103723 1250 561102473 561102499
    0x509070c0c090c05031e01050609040225080901120b03071a04090e100501091406042c0307120801060203030c0d020c150109150509040210050909090d0e0a03050c 71
    0x50216210081910907000c00555140c11002004c6900c2582d840800c007019901818445001542c0c0b04d040310001080980751030100400d00c4065048a801d9805a0801e40c8004824000f2241c507500031f103201d050425a20031040b00050261500f00101084030381c5003000d001040d0700d000802c0c1d401e590b5540904002d1402402c0080d80354407494101002d03035820729803010f03103204001a460b00c0a801181d806c1c0303d140c0c0c9a03210350341120740190f452800d5070000004201d050038503521400c00d00548820701c07210030804840c8651240314207140c0d05070552000900383e05101101040700e0040c1e8451a155240d9450100000d40c0c900002d00783c1c038101c03400000e20b00720102040c1d044506a4074450255680020b29102c0c4450f0902c003445100741d40f80c00c00103100e484010f0f1546510580d4001400c54140c0e4440b5000d00046201c070845103400c3c49400c125400c065624031344454030070010030380282300e4600d090301d000345103d1b91501d84502801d0307046018030000310040340c0410020010389000180d205 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 561104973 1250 561103723 561103733
    0x40e0c07110d081e03190921080f090d0503040b06030a0209090105100f060504140a17061504110a031e020a03020903070b04080607050d0b0604140108100509070c 71
    0x509070348015480540c0e0803180301008480340241c4004d04010303950a00e54078603440c0e070b50000c1c40b0855226a0703101d2041c008181c2c00445030300095040c1d014480d400245d241c04144003c1e12a1140c142e01c000c5418007042004114400e9520b59001209402400f1403106035980a81680809400101400c01e28800501c9540b02041b940305a50f070005d28140d0746007000ba124600a0905440d882c2e122603003008003060300c901008078031044031800d41e11a4505403608601c087c2e160408100741c0d9000311083d00005440c1c420303590300d2b0851794003031028200504001e081e120364a46480c50481c0190304107541c4010201c04102902c0c844406c1d428041a02806e03090300c1804032451030740b110210361020400c2100150b0603809003400b540c00750200c90106441c1e0a07000c0e46802030784035041a030351207900024035042c03180003e400722803000c0c440032a64211140c0014441e4109801040502c0200015003d00d5a4410303065070300300e11100b41c3c0d0080e2605200104a01d0b500041c00e0a00788400b495040341004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 561106223 1250 561104973 561104993
    0xb040e071407020405180105060111030d0c0905030102031602061012140309030d0306060e09040f1205130902090109060e0f0108190203090f0706081603110706021809010803040e0c07 80
    0x168024402c001500e446d41840410745d0304c4400c020203940c82c10300010142d500a80f0300002020a04000b1820115815902e001501049a441081181044c0c00040755242400514018044640041031020034031100a150640007014187d40342e580100400c903600b120184c0c2800d154215500905014840c40424518400c2c0e4000e56054418004c0d40d01049034982d00820030f451160361031210b955115400c0200b1400c00f0748000d407030628075060240004903074007080d0013125100d00300715040a00001d80b100040d12580d114038200e50b00085d01e62025031f40301d9451406005113040908034200307241c0110f2980444a586541031080260210308042070900c0301402c0910a00d03810740d603901d80340d0001500c86046540d440c02c0c9100d0002c0100d80c1030300070104c0d24030482c641d020788080b80d41c5450040300501096402c000710640c08000e00800700d815400104400345144048041b400004014010aa44144d0081000b07070800c0c84184a408080d5041c550031210035107030b1a45901d10340c02e180d1400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 561107473 1250 561106223 561106237
    0x306070503010605033705090f030a1704020319120207090606020307020d03052b060503060601081308040b280302091507020613150e0f0904021306030605090a05070b040e0714 77
    0x4070b4049406d10003450040e0b0842c0c0d1240f10404203039441603480a5801d07030340307006100e103136001714104450706101b2516941300707075910500003012200d00d2400c0510f114040c001da5402179501500034800e43c1285501001910300800c25404100810b91a00e80001d4480c011140000e1150b41c0c004c0311401031601c510242c40112041d50000c4410700000e4454070f05008000d01310510307590601c4000100c81c50041291882044180c492910941e40c250000b00380c00c0070800101d405007018040030070a505404090918550a6861000d8060101d40c907100c6940c10fa82c801810507004221221194079030f2241c0d5003203000290111500e9402d1440003446c2c0e40500d1041e5004902402d40008102000c044070b441c0b82032081e01ca84120308110000e022151809a18640e0803454200200d001410280c038401d512180151000980c280c881c1d541340d00b662010348075010f4561004414005000050180b04000c0c21030306032891400b8680319029402d090024043c206200040e18004403410080c8103c07103403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 561108723 1250 561107473 561107551
    0x6030a110f040e0901020403170a11030a121b23251e05060402060904021306200708070b130f09051008011e020c070f03050a02030607050301060503 65
    0x4403103200d040e0201c42e030000d12541d40c10b5070303100f404100119410301c01c40c5d0680e600882c2002640700402c2030401c3e113038421080c4108102c283d040361101c00e041400682648001c681d513441e4418001c403041011703102254210041c002d6084d0131006c10035000300c50f041d4003000090b8402d07a640441d0081030240e00610075103188540101b19002d004002003003007100c1c1144210f5817a560000c1e000403485808516520041040d4031940220780075240000143c180d40500030b201514224174019050704601c01544040d02148a800d50341000076000303100a2100c50700b40d001003c0540c50309140b261740b50070910441a0144000a004000003080c0b08040090701e45500c82c0d4055030342d00d1081000502c0200d600954101200701c01144060041c0142146290301c00214100c1d003100351480d1009600100d00902d440c814208005160040c1350741c608000c60141002d0700750010140103141c10400c0081c000c2c1d0400c00100018410f16402c48140c982005d085024920701aa0345640b0000c107a00750030b03407100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 561109973 1250 561108723 561108727
    0x1b021c0e130e0111030705040306090804120b0a0c020a02090103021005040803031807090c05070632010806070e0a060e0a03061a01030b041a090a15030b071d0f06030a11 74
    0x85900311a4000002da40390320300080200c0c9601d42850f451500080e6010300005804000810204105801c05085180203408071740c1f907d66111224001480d11100c216402c0f00030201300101d50702240f00301807800c800c50010748820400799001408842c0e0500000388900200c07580552507610a00a03130300504042c0d42125603070300700440c02c1c085c0c0d82d11030118410240324000c008201c4940c4d5001d011485d41140d2910b41c1091135a80d501c5018049412104081400c50403a0851000024a0240c005070b4500350703002195040020090030203900428190911030b40000303c44e0185c40d158180c00442c0c08500e03109000815050001e89601a10780c00a03102c82e04200d0460305010906400c3c14115009032002c100210100042c4001d481c0241340303580038003c2075410701d182c5007040c6e03108550000040200080400c220000c0300101f10a5030400e65100e6814400c0040704c83e0005c41d8800e04103064200d0b9910007030f064000841c4a0b0288030110300543c00440030170601049a0001c00114441c042015 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 561111223 1250 561109973 561109999
    0x307061403130f05071a190e121f050109060302150d0b0d03030506030607020f0709021308160303170903030601050c030712211107140a05030f0306041b021c0e 70
    0x1d0f03517402190141d01c100c001442095100503003154101c03400703484001e401e03540700c41401400b0740d0910034201d2960381003413004c0500710354a00107104901c03074000100c1c450407040608408980484005030000c5070700390301d82482480960fa034055280d1019a440c60f0344da650b40c0107000c5e84400b07041903401c41c0303800108040450041641641145208410941c01c544d060354030b1880499403404040c000103802c0d0400d040c02c0c441c1c90481d030000d2401044243e020480c032551207035003034941900e4041c625411b1f0031030b4209000f055031000561403003100306907240301d85080c040a020345900c00a000107050010004003050001e80902c1540d400390381105c4c1c05410389a11001c05413041600180701142400c403094180000f52861091703210402c554145a41082d2950346c0d111502990181c40b22004d12461229100240742000140705c030150300078000c0d03100d0401c44240301c141c0d100005040b11041400c4d02d2840d0f003d074005441003d03100740c00414100c010603588181e070225101c4142a03000f11034a40c0c10 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 561112473 1250 561111223 561111233
    0x30a060b180a0902040e0604030804170903031804060b0f2508070b010303023a0207030c0801020c010c030605010f08150a060203030910060e0f07031803020a0b060307061403130f 78
    0x507241030007641d0071b201c40f0b0441c01030a91181c03801ca9005000c9091040401e011505540f03065415a405401d05c42c54000030a0000f40f03940c00c5100c0710400b040145040701d02a08003402000014060145181e0601640d401328000c1c500603881c040602c1d003442c1c0d1100380790403920074010382c0080c0c01c41d0226540315a03e0a05121141c02400b0940162161145a10140d10140c1000704004030460343c000d80544070480c510030036081d515006085119030080413011400ca001c041c002000108001a940c10702c501e001804d44003450240030034945080020031140c0d030011400d6541c40100e103405d4032182d5a507206403000781c050003a11a0003140e81c4a000c14070680020003940904194000c0315241d40c038041c40c2c0302c2034030880d0180011440ca1000816a000500c0c102203030032119134200801c060003038000080905125640540c01603106141c00810321a072108a10380001050f405403540da8144407000c0c20fa416000d01000c100c920010004ec0c5445115081c0541940c0c04440c00350000b102e8140 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 561113723 1250 561112473 561112481
    0xa0e070f031a07110307080c0a020406120312020310050f030a060e030d1a030705010c2f040c0206010602060c07020303070219050901080f060f0915250c02030a060b180a 74
    0x21502909403078082820f03240226080480444050700a51038620b0302d40e226161a00300c0d14008100d413058080f082c0c01130f40e0354003800020b0945e200140c5032000caa8203006180c8040d0030042c80000741b04000740040610220003110603100c0c00d55071000010b181a01283c0351844407400600418a8000084407040d40800180b01045083d00144029200d260b500e01e560f2034111145540340c1e0042c0340400655004159400c01c560080c60301854041031203070603043e51100045034000c48941c80d2221011403809100d9514849101c0c4010000380d0f041440296a420014005519002c0013207681e07030440da8100111034000354068481c402d2580d6141e010f0008035071901840b4481d01a010010034200720020b0f040d516050008010052925641c5c0030500f004006480585280102001e440503e040307581118015102c05140b81b5403c04c2c0e0900380741c64160314440c83c1007006180306408000da5000118130311400c0e000310001921040c0100011201c02c25100700810700a001820801140c1c41584 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 561114973 1250 561113723 561113753
    0x411031902030c042c1f0b0a12080f0406030506040c0507020a0501050f0418020c0f06161b0b070215010501030e06270f0703050c010c2a0b070b041101020a0b0a0e070f03 74
    0x2015141110242d1b07000039030360b40d4028590070103e01c2000700f10644408500c0707034541e07004000703c51801ca26004650b1207a40190003400100382c8035003e00400d030406109011015034180707012400c0041660008040e2403107881707094100308000c50101c203a181c0e050100c800902d1204800c520160010f01050040d4009110729803440c01001c0520000c200040784452150142e0203401882800b00b07070f82500c021a08600300414a03c0c5510000c002521000e14140110210b030020602c242e01e03d0a02c040c0404140c00180c105420031440110708040020780c00e80100b400440207025103c18400064441e5101303841c0c01051040c44e0382000c2a0300041103010903a40604103484442c20200015501300300054001409a00850b411421a911120517107000f4858100c0d040d204541e501c03100c0386990000b0605440c40d2450b007050004000c54201122010142800a089800190b0302c400c0382080f8001c01410440703855039402080c1f000244030a0300603100c0c03801c030b003004d42d0380b44c0c00c01c0060250856 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 561116223 1250 561114973 561115003
    0x904020409050907150f0c150c0e0a080d02070e041a0115020601090c0f0f0e03100e0c040513080a0e18150a0b0417030d050411031902030c042c 63
    0x28011a5400307140b031001d65000846e444034160b2094188048402000194050720f52615080c404080840c0b5070040c1d134aa600d403581c03500d4004c200042040f203d0704540c0e104c040e0395400481c9000046802180031411103071018407201090f0303584c0c01d100418a07401d10291321b103402c43e040041288404d01081220f044d4142e03080b910182c1c1c0b00c1580f9011218082074903c04214903000c0084814030403030042610041500d40031600031504800f103850018074403860010a5111400c0d40c200007802c0150280300a01103e050100b41840003111000441c91000035100800004906100034040e10301038103241800381c20007110810018000c400c40809035004074034160540011201881c0400d48113080c5c07402030042d1450030b49040d07000384c0f60035062031038403c441c04180003000d0702007000c2c072a030741c410703030241d541c0c5107170f062004007014100b8081d1028400409590018200541c9001500807514581510005011220302c14844090400d8501c0820f03064001400c40700002c401088203c03c07035002d5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 561117473 1250 561116223 561116233
    0x402040e01061106071b030201091407051e06030408090a0803120a05010504140f090f0a0809012703020609040b03030a09030203010c0e1f0c0807030e0310090f0f020102010209040204090509 83
    0x45800252124401c0d10403100080045120300c46d4034040d0443c0101c41482400000703840c80700e41c0d4550342c0e00c04064103030480b10340100c1c0042003142083c000c0a40c480c1c0d0300c100c940d08540701c41d4000481c02e00000d840684001c0d0049113910182d00d44054000140030202c00b120380b80e124003111800e403040121968060b107801c02000050b43d00301401682082045120010300d07652313038141c14601c401c0008005175594422100880c1e6401000e0065130425400b42802d60b649640e80800500103d1501140700b60300000705454013034000b80c4640304400e5990454205685862543c0041c0180403059010765050100060b82c072001a00540d8000071a44280d0082c0f080948848040d214070095400c3e4981206440c000a900d805280301e1001880c40641010042d808803520703185034981003600102c02040402107082c000c1d00d01001482541041c0345014041c04805642d08000c112180c44010701c0c044440c0e64203011603000790141c0e40c3e100800b510454070b883e03541403081c1c00381109544e1a080c90040f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 561118723 1250 561117473 561117497
    0x20d0b04030e040209091f090e06162a05010603020402181815090628091512080c07052d040506180c0d060b04170a030905040f06050402040e0106 64
    0x7402919480013000341001c0851360303000307040c0c03c0700b030840310f80a07107451f42c03441010031a05040c0c8626024103021000034a614900882084400e84007401c00744148464416051109010f4200104041211980a034003800c03451402074058a200d0b08001e60042c00450410508070b0401c130340106404c0e08407280000740b8000d441b00c1c0b074414000d403400300700301d10510302c07a0308181030040420307800800103800301d203c401c54104000c0c076000f0520701861141c818a40100600300d00ae002d1400c13458502032102d00a54a010380f0200700d01d84802e00284a814080b405032100c1d81c081c000345005003409466441c125401c5c07981c186100703c000b40038800d00c91a41e01076074941c0c201403062511030803010707020300c081c06a10145c01c0f414100007014554604810402484500302500902000384054000d291302d480c18514105403404528200082980c080000e801c04a075100b8110000c85100762400101c492103170f42c120010f4000b0b0f403c0315420500011300001c0d081008a92035040340c0c1c01d95900700500301c2c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 561119973 1250 561118723 561118729
    0x61e160b070e0319050c0409021c061506020c0f211c020d080103150b2413050f01080109020d1d032a21070b090a030e01090f09020f0403020d0b04030e 66
    0x1384010140c070580c01610210000d08040d0311802c2414001400307190300300e2818070030920568a529045501903126041284c980c5a1092620701900fa1800035154645208002c1020000b03a03000300c522801555011400640302c5910040c030405002c4291500840841c40c40304180070040e40c440c0042c410750881c03030422441540d03114140c0b0340c0518207030100081460040701500c40c00c4902940500340c05d2420490903011012a03450203030041c0c413140c4500e0b255150b1182c040490380002d025034040300c0e544000340e0b0300102090644012050050300d40314940b08a41c01064088001010340c0e42045e000c0166940000141141410341e03442c86020b807880e0151200040020030709038546502441c4050301801ca004542c1050b01c450b01c0c125070521249848a00a004c0255104a640d402c0075449105040d40650b4811551b80d0a007403002e0f41c24070745900401c4210581c403407078014680c041b400d9110042c00340c2c100c40c000e64004052245144460034a0380c0220300940c1c0031808144081d0065003541 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 561121223 1250 561119973 561120013
    0x1407021c020601050d06060b070b0105031903020c122103010e0a270303020f03011710020306030709091e050d020f01060f090b01030608030307020102090906061e160b070e03 76
    0x8280d07074003501c1141d10b440c05000300704141c02e208441c1c140d11688089508080600603007000707805204c1002803545807609040c1410048040311980040161034070011a400180c0b202040d00151004c030301c0ba071032950303c0d41e040c8040002060000d00055410301c02e24006800030f9030680740340c00410501ca03220351f00050116103c0400c000e12402c580d80000310b5488080880e0044107000b0704015140c580e40016006095000740c00c0521790404000b040c045103241001035120a0414400440ca0350510000003984c0b42141c1c4035510301e6030b8888003103508200c185c00014505070050021203c6080eaa80342964507001214200700c01032049599071004880140503803012600c004d10300b0007019042c80c0510010340192074880741456202c0d90009500002000114400c054a600050b02c0704d0703170901040030904001d0b001611481092250f04990340d62031444440d20200d4007000380d504e030311000b0b15541012140388040d081d10629001c00001d140c10650b40c01900c0b1084056840780386600103e0b40c901 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 561122473 1250 561121223 561121273
    0x1e01020903240f0a0f0219030e01111902030f0a09170a080403060b1f110c010309020307090c0c0c0e010e011e0b0c0a060906021b190b19140702 63
    0x960b840804585000310071a02507800408815000c1350520380c0e8040c00080c0c0e4091146003100881ca940701c0c0ca01c480e4103100b58031001c540c170b03c020700400c02c692140120300c2c0100c040840c4001c016070700440d03495008004454030707021064451b41d155204808042e0800c405071240030401e14110840251041b4045514901594429011410141145ca17698010405001400e8100d0140c04400c0034161821b00c1e115050941c6503200407481800348074442c10708221001c464145801c1a400c1c1d00169404142d0106071040088006078022502108940c41c0000c100050064000040c4c040f52500010008a0581ea0403030004c0c4860703681c039121341c6102001d021500d580310032040d4040c440700011070300810341d440d455400c032100c00e0080d41341c1c0340032624511012155035900003012107042400c41c00409100480101800c1c103004040202a00d014101398004c04020027800044c003900341200b42c2c1d24013100b410004002f849191881c42041c008107442c4040075100380c6045c00f4003140010107520301 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 561123723 1250 561122473 561122533
    0x10207080d180e04120207060c1e060908040e100e0601020d180503010c0e030c0307051c0f14031e0901210e0d0f03060501170103030507051e01020903 66
    0x8414000d140c115484404004000100c000d00480012002e011411050240d0f001724600300e900380740004068030b04006a0310803011321503400182800320b47d00d070400310150a000300c203440300503045182c050000c0a000c500280041c40200e0042904144050428450b40da840b81c0c1e10039032500e65030002d118050854400303005a01c1041c8c02900e00384030708084002c20702268004440c4523200c50000f4259104d00a080c0b0004444594450403031408106c03480040310194044c107042410100400c0034440071941030003490405085c10720800501152144c0390310b03045034444199003102c0e411030342c4075888071982c865442c2c0c007800ca10907003049000465800b004161650704104403041c80704144074441d58030b0b0048a5a039910b5041450b1021b02c107240840c2a04e545507103c10301ca914001c2d04a50098104604024181c14000c1e02c2c0342412aa0f207042d2901818070719218526450441c0ca8103415075500c00290408001540000105402424019004a0a40d0598528401015500c089100040e80 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 561124973 1250 561123723 561123733
    0x120306032112020d0209010905120d11070302030106060503010501171603090305091c0209100305031c020d060608271b0109090c020304030c0617041101121e0b01020708 74
    0x4440210045a500a041c40c00c01421111411107100100e800c4400303203a25654000407054000e60340201d0540107003100310381105110700020201ca5030340761304000c49010b01075600001154070000304410f400856004000b8000c4e1516110b00800d0364000f840307901d000c01d40131490f101000d03ca04100328402c4448296200d4420b554030006c401030020118107030144041040000840c1d12038000382503911004442c00161400035105011a408004100404580c494141030000070404412501d00000c0000102c042015003c04034000b441074480d8240602c1c949032000904680020031039110301e40c084200d1042800c00000360001400901101c1c2c41d40d00010442201c080d400003809a504030185400709407036459003110012901c0d6a6040809030380b01103000c1041001c03801703455024040c6880e00400441209202d00322801015100410400384142e514030b007a44220380a032007a4040d420180002e000c00c203600c00c660303010a121000e6603410040d9820807075000080310350454180000410b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 561126223 1250 561124973 561125003
    0x15050301091115090901030b0421090e06130507030516141c02210f064f0b0315070203040e090a150510152007080307080712030603 58
    0x1907003101c0c50b804014980c609004d42c2c1c010b41c81706800c0a010b10b08c140c25000160500b82030031064028030200b060401e11414104000c00c40e8408140d50441c0c19003000c0d00c1c810303220b0303500049a0280c4d000c50b00e10b6242c81d040422440e554150080c0d4012240e0207401c0c890401e5040084903200c2903d081d4140058041100504461810100c0070000c0400640141404281e202d0017822040fa08144200e00031004103110042000045054000408499a040d89481c1f41e4544c1c3c50144607a0f102c8003d6540d00405000200c5c4082da0350264602000407a52284440c0c56030038010121044654080c0c420650350701400c0e5060100d85002c0c41c4130380c0007581028900402d400009034010844039450145e011359600154000d0a07100200300e030000c2c0030031545000d4006d0340700c4040580c00304d6600885002d0b07002c3d00c66044501100d12407440c009081c2a00b811604640c0382120741c0e803002d401440002015020701c250407010f8011035204001c0c40b0941c8074041821010784055000140c50504003100326 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 561127473 1250 561126223 561126229
    0xc2906060906041a07170c1b090f180303100f08010c1b050c09161205060a090903030212040506041b0503060a020903011b1805042003060d0f0501150503010911 70
    0x4c1140706070102d000500c2e110180da10746e210602622000d401903100491020595107003840644e040d44d0001850312400e008030302c0058404540641056120022400440e0000c020740c6d0158070328a000b00e08803a900e08040703052451010041c403401000312003085001c01c005c0c1040c06003055003613007940c42c01d00c0403440e0b0961490300302003503c007243e9900c107200001034075889034070500c0d2045000d0381486906040442000e410716400d24010001d0918000802540f80d4440c0c100e101a1410108005491a5945400d4000340301c1d4601050110010108000c208072000a04a100724800c51510440b0004809100044002d90080343c0e803640005d00054070401003903001e015442c1c00200003003649495602e0601c41ca43c0d120007440e0000f8090300d22000f800d0041002c0b8401040160303010450520b0320341044401d18004d09450704542800008203078507030348034580c00c1e48840d00901400c40005643c0b425900820314050740f46060144e60034001414a018816a00c10703507000b00700301e80101821020 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 561128723 1250 561127473 561127499
    0x110a0507030b19050106170108010e1b060918010306110c070b1c020a020a03030c0f0215040c0f0902030402010315030b0a0f020d0f0617070f150c290606090604 70
    0x24903403d103020a00300050385825004050082800d5119020a05045c000c4051103180c145c004902e42e078105030107540c00031400a41c1504001e1011644002401c841c000a42d4500c5908070160b8054602c841070304400c03400c11079180c101d0303200b0503003081300b540d01e0500481c00d4040c0d52045c14107504812400c205c42e421460041103200300528010000b4134601c50541c00b2a002440681d0041c0e01896000707040503018410581d800f03500b400d22003110144000d0003981e40c81c5001c1f8481c459003a09010a080040d810662805081410310700ba40954075003031880c2c001e420845040e4006420132881008500f0000c0218040e45e4110300b02042c1642c3e00c5901c080940000c10021013541d900700b15484000390248100b034a180071000f000715049161841903202180d914204446980003030404000d1b22401081000c00c81e81c480d078080551082c029400d40300d000c410780019004da035602180488060181030369124180001750079522070340b40c40701400001c3c00b5640c4001e40060080005010700f14041071 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 561129973 1250 561128723 561128731
    0xe0301020702120d0807050408030412020307081c170c0403060504021305150109080d0504061101062105060708010b090d021504170d030b060708030402040b0d12110a0507030b 77
    0x589414520b60101c0ca0250b05080c5820550700071100c0760b454580d01541c002d4102d0060301c0e085041505283c0050b4aa02c614401c50718854060780141d01191000d005030f1b4000c00810b0180e800c21404c590400014600c1c0c1c515480006088003031141110254048180c010400c92420b54141420b5690340d400505000c0c0081c1d81c00848078000600d4402c00e8017907244035801200d482e10a41410078005081c610843e0840c07941500840c080da000c00da802015141102c0041c50b03d203246d40340c0c01ca1603500410b02e64021160700800402d268400401010000415611401c2100e00741d03030302e02c0c0f0308461040c000c0c081c000003100c0401006185107000b4194841d2031380014100072407078030345022046896010750f000161742e00c00a9215800b07090148588603114450b8202804040080000280981304289009140300e0001c40442c1c2551143c1d40030302d1195602030081307040071081c0d0800103242107480b480d080002e41d403041d40b54100c100c007051840d0400d51110080c039129055644090605034010 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 561131223 1250 561129973 561129979
    0x305031b070501050403020d030f020301050f150d020a0c020f030303131407170a030e0d11010302181c0501060504090312200a03020703080117062e09060503060121030e 74
    0x1004101c0415420f1059074000c034030907002004003691221014080e12034a0fa0408201403040c4010040c80d02d540300e03014000c26003100c0004240301c4c03d5001d0603c07806000e085012444c404940010062b40108415502c5070003100c00841d8241d20004042d0790b4401104d00200f9804c8113801d07000011242500d01840c0b000500c00d60f8041902c03603400852050444c6200410307540850301c2c1006040d00100c00e07016264058560100800054807006c075102c282120050405900045684400c403014030781c0000c0b004014508a41c407540001000003284880f48d09076110751030404001428503241c803510302529030549401605010101c4150010650b001ca41c00d0756005070a880d90800d83c450008000344c00070341d20010b0301c030001818010304504051b085010103021080d81e0690311040054040d81c4191081000380c04034100c24a108200c03491444403100c034040b141004186101c0c0e5411600036200f0079008c40d40c450f0f0380d580300c0540f0b40320018203828074499260031801c0404c5c441d1440500c440d1003e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 561132473 1250 561131223 561131227
    0xd080a030e07080109050106090f0c0c031d041107020109080c010c08090406080d050403060f05010501080c1806160302060c04153c0e0306070806100c050610061206030305031b 77
    0x72003243e4250b5502d0042158644d40da210103001050951003064061040c804080101c0081d80a0103004000d11000c080d0510080c0281140107c0400c034400030000d0015109201481080301003816541141e00d040b40801c900d4500823514590019005003100e1050b515100500308a03195000c2e25407003180f1541d0031a484100100301d1030f0040043d49480c01c0941ea91b1396480385182000341c12184d4882c1c00308407103030070200104040da9110b2411074200d251108041d941e450313858071007141c03800c0d1b00f805140c010fa004501000b00d80307a00003810321020b0098080d502e541d0740d4408828103521560061010a518030031000d223030b2500c0791642c000703e24031108000c2d04200b04000d00f00c040c84004105410040d502d203003400036043c1d100d0072426120744194001c210904200d5000f900d085001804e00740680002c8448110580c850040001d41c550403d00f55002401d0004c1400c1c2240c01501504010503104a00201c01c5041403091a044030340640d507250458544040c1e41c007130500511100c0d1b00c000c41c1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 561133723 1250 561132473 561132479
    0x26061303110114100b0301030201080402090c0c0a03080604060623070c080604241505061303170301050301050c07260415030c0e041e02030603010216030305040507050d080a030e07 79
    0xb4400c41c03029078107203d60380800e4a0400d40c10704910030b050300204c5a110b0700b4001000181d0700122a00c0c1c009a046030f040000d941c80142c8005580641070750b01c280d51003560400010306810090640c0507080580d001c0c00120303240c0200f50745200791000e0030a40f10416030421144040c10401400c650340c4079030002c1c86195601d000e080d1418400351004c0e42d24403545480b1070041c0c4140f480c5d10300d00c00c0485505116040005c000711420001078400c0c540500c00c00079005000d5800c00c1a85009107511680d0041c1c241002000400d09400c24015140258a03200201e00e050100f4407c0e146103507401003540040e82a81e200a40c01442e8003152020100b8042c000403919140c082c01401d0710400e07550740013410034441a4003d00003100ca42c1c0c400d000c0e43c6048880d001035100c0038802042c8080c041d20150390f07a15040042402441882d2106149941e80b000101c10960305401082c02180940c1c100c8a600b6158070410101c8041c21000a215900411004001a001e90000240032040340140c0b103c1c03582e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 561134973 1250 561133723 561133757
    0x102040f03201008100e010510030e07080307030804020a0603050c2d0c03120a050112060b1504031505010b12040311100f0b1e010f081b120126061303 66
    0x207140484004103401303004018110000d030351800020074041045210f25403414002ca071340030040070300040405071070f00e42e0905406030400c03110b802880003004030ba507145070605000304162070a541c12071143c0000000002c056100c0d004142c01080010492860701c01c0f184a941c1008010f000c00f0068010880b866203030089e1344502030400e051050303001d540c0d03a511041e0403101c0e000000305000040c0d03240c4001400a151540c01540b20581c0c0028002000940c5000207880d00840d10b1811540e00c10025003c420040c00812181191030311400034442643ca07224143e05074024280300301c070800007070340020380820300c610308002d046004041681ca6580e40c00462006848100e070b0100f214540f02c14106036035043c16030000011084091962490340c100000081c240c1085a011a0400c1141e0010038040401078010004800d0000c554607950b00d4040d43c1c10380c00c180f092103002c005114080c0d2903501d000c006e060036500044a180a44420799480001060561a2081c19402c00a4107603110310140 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 561136223 1250 561134973 561134989
    0xf1a21040b090d031b0f2007060f0206060117150d1416180510080a0506041a040b07050a030b0d231209010c170711010e030102040f0320 60
    0x150080d00041c00e203103401e910b8286001c0e620b651107410586414011240544450324804588410f460301c01244098204100c82200e0000728500a821810b00d94000010002803140115101d40c1c0302c40803684240c51080c0d0320340c0c8048030b0080c08a2498807030030302c000c2e650641d102d44c0300760440000e0300a02e88100109520400c83d11013160040802d0351043d42120041060b040381562150a040400e41005d1544a203150244000e06059846102183c201182890342078003801903401140d41401c0103051003a5242c4042da03062310203401202c0840c0301ca01d01002028891a04140c3c581e1590321a02c00403192980610700c640e0030160790300102d00155442c000780340c504601450900003400e40319416001c03107104825840c003c03035010080c1003004401c1041507401c25002401e101c4d0707404540703042a601584c421400c00d540c0b04d83c002061410031071502d46102d145042070f42d03403182e200c8000d42454202d20031801b41c0004080c1c605400c00028007940120040419200d2016103c100c1c000f020810071 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 561137473 1250 561136223 561136231
    0x2071401030c260a110901120b0f0d03080f010b0306011d1512010e010504090f110a051002030c06060a050102070b030a06090516020c0d120e031516090f1a21 69
    0x7402040c01482613407082e0f4051800e0304151600c3c1c507440c0114100c00a0400d0300500012142a900c0e005030480603603801603d41410000940f615404c164a482d00410390320045a9103582d2004d03070000414000b10043c2500e03c1444103840300182601340001e212010004000f01070b0780a440c00c5d030400d05290700000641010420740c109039005506041c003908a401d016001280a503141071400404103845414202203181c102228100e0241c00a003c80e8080740590403e6820180f14200a1021980000141700741803c1006880180d00e0b89003c0190a800b648101c1e4016440070070103000d04401c02e03005507000801640e00080c00d940d9402c90030181c48089405140001c0340c00c110f4040f040e014131030030310302c000103c0e11241c0c412081e9580c03e07090340381500c4540400c039560b0400142d50700c04000c3d14200014503030b03c0303003010302d400c00c1d21820340044110294002405444005410400001d64a0a90300004050030300b081c40101001034941084040c02940140540d40c0100c45044850320b50003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 561138723 1250 561137473 561137537
    0x1e0601080a0b060d020d0b060708040b0f04031b08010b150a141603090806010605030124050705010f0e210d11130909170304030215090a05060c1902071401030c 70
    0x1502d55800d106c4080700e11110109004450800c0312a0010b65418211002e03960388100319500d600000c42408428025604010400c0700e4112141d48205d00c00c0c94200c08481d039040081c82454804d4040c0880003180c22114007000310300780254243c1c2809540c034401c88a2000010300c3c1014440c0c13000101d41c1460b0318003940444c1c0308031814011500203001050142a43e4141a85103500d0442c01592100800c400c0103002103026243c502090304c1441241c0c10150010000e00100d50f503010070744010503668030b59074074501c034055502114004c4080c80600c000301948110b42401e04900c015000b91101801f603005400c010800101070201c50110700c2c000d4a92060002030780e6a403882c001001c142003145089503ca414820040002d50000e0410908171540942007115102d21000b24079101d0b201e18020900c1c026581049618018203000d48621080c0640c6090610300310481603031102804d00400084400045100314194040d4201c4c540701d86d15440e10003041c804039416170703000e1043c90f024200 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 561139973 1250 561138723 561138727
    0xb0711030f040806090f0a0b0403200c0306070c021804050a020909060703150312120f020a020a0b06011115040f0605011707050303210a0b0909151e0601080a0b060d02 73
    0x1d408801c01c01c081c0d2245c4000c0080034621400e544c0c3c1c42d42c80100304001045a1009000982010700c1110032800301d4503803c540e050a004074024403900c1e1400282c100d4080c0c400e11000902051103050018100b80e00a03220610403902000d061003007140c020415121032054141c04801600c0d0144800e1203086460058140303810300e850700a040c0e640035250480c0b283c40101007270010911100807038250070120f05000c041c854503c3c1d0030602900018040d16049480450343d40d0382203402045070256544940108c0410390b84031401500c8801a003040c0354215400500c6a03885980f01c0d0b14901c5e0428000d054400d0b228403181c3e01d02060b0341c0301343c109552981c16048600040c1600300141e0740980780c110b02440c10039042d401c1031100c5454002c0c62100c50907565000c40d8150101c3d40c4801c1d001800684800e469140c00852166224600850003085c2036858001a55103c4a00d81c1e08164100c84032941845071034002c01151750a10140511708256074456029005540e20380c001c2110b080c03100c802507 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 561141223 1250 561139973 561139979
    0xa061a040303031506140307020708010219140304050601051c0203012309010603120c0201050d0f06030224042607080c030f01020c030a05070507090513021f08040b0711030f04 77
    0x8041c1d60248402040b50004d042040c07005580100491020f0201044081e4a0b0b964075a0100c1c50602c456209007000e500c00110110820943c0203011800c4c0460340300c0005500c0c20928501d041c1c807085030b0160068001400522152400150046000c0c0714040e609100c060183c0010f403c540b0080310b80416034211241c01a42044217807000c5901004000003040b070389141d51074402c038011041c031408081280c000030403400c45e030240090321080b040040c0b0800002030103c040200030712890000b0ba00c5551a0400b110b010341034043c030200d05c00300004031182014070780742c01c10240d068450019218440c0d40000080c031400200700040c001c000503002450901400d00500d0b0600207004044180c1c1d07401040107542031003000080301c100b92242e2502079682c15090a240d4100f01068106100c3c0780d062100340092a58a00100038440c0d000b110a10300b150f2506522100c034010401199003c2541d96000078086680440901d40c0480c007401e01c0c1414045210010b42103a01410100052640200e828 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 561142473 1250 561141223 561141227
    0x1e100308211303020a030e0307030b0a0b120703050a08130b16060e0a210306080d09300615050604080f21070f030215010602010b0f0907170a061a040303 67
    0x2042d04108101c0341e06400304015200203450b080503100240500c14801441d0350561810002e40d8021130f00200e83c00d941e805e00c031100601501e00442c525108500c00c0030000150000415200103c2e9403200051101a005507185e628070703002541c0a91011008a200041a1104200424020203489001e058212082c54840120740050881c111182d001d29100c00c00154048030f49528111448144101420b00040485c00b030f06458010043d140145141c103101d40c0c0d000b030380000c26219403980484010b042602030550012401c2d42045000d2140d07003a00004c1340140d030281e40c000c0b5503204c0d0340702c6050f2180042156035210b98444800359000300036071083e2140c188200d102251031084084030088450b00c00740484d010b4404003400c0d01c401d030082182014001c11105a2200d040410890a036075640e0020f030080000495007030113104000d0304441316140c19025203100c1d1009403600c060ba6403802c03010401b0808000d00441d010f41c1d441d1000705030ba00c0b000340500075800030a152240da80c3d08520780 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 561143723 1250 561142473 561142537
    0x4020f190e030c0609031e0604031e08060f040902060307021b06090102030306131808280504061d04050103060b190617040f0c0e090d081e100308 64
    0x9500100020650765a001c0d070b8010480201c0c46a0894036141c0315106a000241013900c0c0010044510b100a0360350313024404003250540c0b0032402503d0791010904544541c8801c0d54140c0701c410001420000055820316200c3ca0f0b600704501e010304002007210455000c950f10ba802074650801581c00b9004018111040384500c1070b811009850141c00c20031f20b000040d60341d001c0502800e00c9000c403103440385001405940302c65003009070340300f641540f48034505000041e54400c045110038119016080300107505001c8007049801225a2403500c1d0038600002250400030254002d8040074601825541c159190701400e4069405204001401075042d010849000d90342e072854401e604052074100020b6400c0500791644d1201410418119511886c1a00742001d108a00521000076000c02085140c21140103d00c80c0c080d001c112031420359102c80554450f442143c1001c071421000d940120358a01c40c6500e581c110068160f03200001c0d48a54070b00c0c0701074120540c03a45000f0230480d5441e14807180d04403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 561144973 1250 561143723 561143767
    0x90e2a1e06030c0702120d050d0c0c1a06012304050414090613141e0c030a0b0c070c0b0703020a0309061b020904020109082d0609100b0f04020f 63
    0x518601a0400e58042051400002c02c0040d0a0001003808015504d80340c41030395944c020001940c6601d03800e41400b600c1c54024071120f0500c940340400c0340139058060744000310b40a070010002c1ea01c4411200c452010710000414450400c1a411155980440e840080a04517080c4204132030700e0302c0c241428803040352080d80e4003030704c040c0a101c140030318210f0100381242c01070100e540b842c914103070f01e00707000f401c42840700303d40e40385440344540e11150294440b5151656800307040603101c408401c3e008140d664860311802a02e480141008610714150b40d03070041418a105102c0f052500740e070380d0000d03416034115600540c0503030040c000440415074400000405000300b4102a00d00500e190000d40004850000090041040030081815a0b004004c0b45004004d000100d0b0301c86990000203d44450450f6010710104080741445904180c02140b42072068080c400201100800491944060701c2c0d0022401c2c3c02403030000074040380b500d03240001c0c01000c0c070701d0900301d60323400e4200784044039124030399 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 561146223 1250 561144973 561145009
    0x60d0e1f14010e0a0603020a080a020a08030a02030d0e0a0f0c090e1c0e0307050301021c14070c0b07030e1006032015130e1305060c03060a090e2a 64
    0x104192410007010400c50305540d81d5030340401865944401210050134a40c20281d0b000d14070020009880c140010501c01c501d10941c1d40d45c030005d603102e0040f982ca000b04203100d40035030418844c0e1120580d092b40028001d0f0142c0b4111000e0941c0750721120704116080d2000c0e00d1064000e4030a100700c0c0c0e128022100e50b4a005002070404542541c40c040c20070310702c11400010008031000700c000c4d90703804202c4207000c1d2200900865460202c01e500c0a500c1100c0b1b00341c3c03089103042a003503101e0001c3c40000107100e5582515042100c0e20b07540e49221041c4c070004c01c21014180e585a014103111810001030010318004440094210308506011401810314011400071400701d140d8600c0944560a04c01c214604603414540c60342c18050858a404811340c0040b0a9007410500304440680010506160140101c064885030b4407003600340c0401348001c881c00380e04603100c0001000f240c0306a5001d03107500008242514280001c0794442c2400040301c132942e6038081c0100850354028589506484555450a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 561147473 1250 561146223 561146231
    0x509090702030304030807050702130c08060a06020a020f011b0602040617060f0a030308090f330c0301290d0507080c0403020a1503111c050709050f090402060d0e1f 72
    0x45d0b035000f00201002441c1d03d04100c4003081400441d00c0b0082900424244030209008551078000300404031042203c002d4802d5005210024016001007105a00680c0141c191030103200490010b440b020602c007c800d101041c4584044003046203880900301500d41c42c0c1c1c0d02e1645003000d0110046c500000750040b44106606403010203e50f460180510449074141400e908a944a00b2000c0c1009401500c2a03005e0180194030686013508a291101300c804034041041700102d03843d0f261101400454101c1504001040144201140c6226a00c40c010007a40f000000d11059190000c0c65000440c403651225191001e0214168200002d9130340850028aa18100b501e590009490b4400c0c80c45003c00456070300004100c0c1c0da1098100c0f4010b403070290312003591100c80c9070b058080b44840050340500b092404011501c0303148900301c10400ca49000341120441d14102040008418028100b240c0c0030300d082000848400e441d00514103107065078005028011040401e11035050340f0700c22a030001e40e1078 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 561148723 1250 561147473 561147481
    0x10503150604020c2407030b03030706020f040b0708070c090c020a03031a06070305120c03070e0f0d06050115090b0a08040b13050307080d0c03090c1e051005090907020303 75
    0x5620344451003a00c904120545405002c14001e00c00c50352600080c0c000c0e0712510742004000810100c0016080c40408810b035a096811022103464908182d8560401c210407804a16681c0203095110300742a020303031500e95503501c0310b02c45a00c00301040700e42540104200c41444220243c01d401003450703030028031000f440b81200030748130300b03101d00010181590b031201c0d04c04070818a2800c0031404400b6101650713424007400c3c09403590304888082151601c042002503091608031040c0ca02840d5180c9440204001c19401c01080300740b01001143c001c012000d803140415400d0207860700a01400503412a620b5203110020703d118a0358208640a5004001c8104910f5000c480994003640104106030591590a0702d1507080307484a1014005100110b08a0240304d203400040c102c4544c07c000c10016110008020b070b050700c4507260003400c0b920050744200a40401156070221900304034014400c00c1c2d840741c002400c1d04045e05030540004402042181341401e041c1245500501e0600045046181c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 561149973 1250 561148723 561148729
    0x1a010309030e22020a03050910091203020c010b031f0c020a0b130507080f0d0e010f08180f030d0e1213060e0409201003021c020a020717071d0105 64
    0x181c21080c6000d80c9125541040c9020181c04080e03c2e0001079406640e5160b9034640203000c1c00c01529502014010f4400c2600780c20391511411500b40e43c030090f0005a8070616500360005d4002c803c250b5155520780c60500802d5409012252a40c418207007100c071945c110804000c211840c401c1800c00f07561100701d2046c040340700b402999034000301103512045d143c095842c020f410001c0f00e610600882c856842401a0b6407008184c242030b0356107036664030080d400c058004480d094410120a4045202030001c641c091040c24100c042160f4520219904190300d0b1a066146503ca0542d5440d0701c0c0e034480e040b06ca89170f400d201c120300d1500f14120144c204a944100301a80607001d110310b1061050702001c0c40c00d0368036960800d0400c0c1d03800c5000807400c2c840400c4100502c0181410261081d00741d4100004518068800d444144c00d0343c040d05826503e07143e00302ca00951120480806520981c040050006e000c420302031101010f0f80094442d8a02d04441c481d210b29100104a0000c00ea02c40140180d403 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 561151079 1106 561149973 561149987
    0x9021f1404182f07050c04090f1412160c080706020d050c01060308070b060a05091905090a0501021b010501050409080706050403090306060f1706100e0a140a1a01030903 74
    0x62030086c1000308590304030000400c5120303040c8684c0b01003100280110744c201d030303220304982d200d09030320007210070b02d400c80ba160703a50114542ca003200400c03003004480d100420410300201030f05820f04501030f450302c42184000d410420b0100b0325202c0703507409400c56801540c01c0190b00381d4540d55403e00720721032102203560a000e91422040040c850812490484c03003810600d0090189140d404d019201034140a030052040703100c1c030744440001c101c080c4010981c2021a5211036100001401d006003500e005a04c0103208a160024200c08101c00c0740842e5101c4ce448800014580d07107a10b01640c964130760350000b61450349042c0c800f1882c19001180da009685010080c010102e0300c0c0c0000c140e4070b2000700e4510bd03031040202000c00c0400d4041c01e0041c1c001100c244040b8047d6002c0c0f28503100c508040318000840740d21040442242c2c00300c203078010724046c002e290074480e950180c0c42c058586 = true := by decide +kernel

theorem cover : BRFrame.Cov 560971223 561151079 := by
  have h0 := BRFrame.cov_init 560971223
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560971223 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 560971223 ≤ n) (h2 : n < 561151079) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
