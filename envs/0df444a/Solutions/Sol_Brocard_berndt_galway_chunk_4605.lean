-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4605
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:09:20.406661+00:00
-- url     : https://prove2.me/submissions/ef0988a8-3606-4f57-be5f-24cfeeaeb8fa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 828057553 ≤ n < 828237410 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 828058803 1250 828057553 828057577
    0xc0504080a05030403030f021f05180a030e0315040f080f0f2706180f0406031b031b27021b07030c0603140c0c070b04030c05040f0902062d 61
    0x613545186401460408040c24441c115084040e10740c510f503c0c0181c50030408011a100400c141c0c0e60f10282d00c1d91200c40900c503241500c80e9180400c10b243d001191100300d02e00507410744070180d800c0d1880e8070030818199401003c03440c2d54201d17900416448400340c8101e82c0f4a400b518501400c006a01050b904501501c501504410f01c00d100c18880e1070801401c205001d91b071041c10209000904070300d5540204059000d12200041c04401d40d80750f034880009507900052012641d2400540c500c054035840c08101d415148d484489800e40c11b03201e410a003182c003101d041c030382d01e40684515480007143c0c0450640d211750f001c2c4005400e90b1038a0559440941c0d240c030003429500d1450902c0b0510300802c2c1e100ae81858a40b525403000c018040b42c0443e0b12801078801c2650361040d5200c0145461200c0d405227030002c0c1c022a0100030032010112034011624101d03400c3c4450340d03568141d5411540c0c600c030002e52102d07040140300c0c0e1090300e80c5421030030341c1440c1000100103c1500841035442d0311a0001100c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 828060053 1250 828058803 828058807
    0x1b0302070e2d0402031c020f010f0e010b0103140115095603090f06010f031506060912110603090c0a080a050601121401060306060303300c0504080a0503 67
    0x240c0034209681ca021400d056080d00070340c5043c00d4003c40e49131074040720b0780c42440e183e644076010000c1c000c22852060b100c0c000000c205290081850500401d41e5410140555080504414140d0700c00e010380325002e0903017402290103920302441816aa9544c04851b0284400c2c02c20002d1161020b881002e10380d08900c003070b1109000d100240e8008400181d140107001c00025130420480d03482c1c3d03443c2c0212000590495a56500e50010f01031074031401881d80d001c207215420002c5a05041c8040707800031240320344954010607441d0303031810042d16101d009440010751561010084030052001a0200c1400f491460724400c0385a004a6030b96801140c0c0c0c50701d150b116126100e5030381040e07a11900100009070280c03102c0740b211b039209601c1d00700621643c012140c011400c02d0074024480c01035006024110003c0140e15500d00e0b20402a0041d444150702280c088945182d400124003e8058450544400e4020030b02e0050700c02401002e0300d22003c01044403e010101e4246d03420041103800724000c0300116 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 828061303 1250 828060053 828060091
    0x2b0602120108150c030c0c15010603090b01122111060702010b120604051507110a0c0e010e0603060a0e0a0b010902181e0402070f21020d0504061b0302070e 68
    0x191038800c4405000180b0500340c2c0400c0034140d030718416241c002c02c00b800565a90031281f864149000c60000300e600ca6401182c000044864250f4495a81c0034030540b9100d90981e61030f0340321107450031901406024440c1e0503038005000a40502030101d01c0140f402c1030a0712612402c403041c58036200322a0500540e5542c0d00780440c0340341c1a80d400c40e0107801a00103080c9443d04d503840c0303500c0e080e284400303039107126071003000c14100c0c0e005503c4000290311440460b1310580c024280307000c96840610680c040d21041c0c100101e91911948982481503802078014030040d1100104400184429141c900300d40c051a90a5400038483c2d0705054000d018002d400760b2160590105001e103403100c40d624034402c10304200100712045ca90f12103036000030300803280141c903058141841026003c102c50001c16800c81201e0308200084440b40b09840c03807c0313075400c9030032900b06144150b541e8402c0380122404200300004485d109080c0d5003103c5141e40c400e2050710245ca035107102d0340d40c502a0175101c810003402540400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 828062553 1250 828061303 828061319
    0x1081320040e0d170a0b0d0501020a0806010816180f0f14060c0618030918040c0807270219020d0e0d020f04151503091a01052b06021201 60
    0x1001c1d0390403900d0240c25100d61041c4003501c6441c0c000705600f00540444c002031018100c0b0381c006009210007400d41c81c4032500c240303486030003980710007106404503050302c0c080b411035440780b24203912840c1006040c00074503104060585035004035444451410b0181c01c1c003c5505c140c3c2075a030034003c190102080c42100c1c01d0190300031240812400d801e0081c0da05205211101c0000110590850070250301009454104034406007184a8511003c1d0040c01b20300700580411104400c16120b503020300c424401c0b15031a10340080d00c9814512400c2c0c442c04480d90004500103295010700740c02840007000501e011842d43d9610303000c0b585102c4043c0035030401c00e82d1803112038000d80202004003045a440c00e41500960008419810b403030000c500850b910140b208d007480c40e03080c441c4090300c200e0404060f10f0308102c900038040c2c000c0d08011a40a4440c1e1180150050751440c01816548004d102d40704440301880280c500308080b007410200000000032a6020549520007000c0880e400b4001105940c140b10072 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 828063803 1250 828062553 828062561
    0xd110a090c170411090c04150c0201030e010902031b010c060e0f060a060f060f030e070e0a0f0203061822150c0507030905040c140301080102040e0105010f0e0108132004 74
    0x1100480894500f0000092059003c90b4440d8000326444c00307a60716105d039032140310300441d00403070a1918110300925100b03801410544d0f8842c400d903002e201c4840c01c40c40c21800e880c4425802034166000000c0c1d8202c0d040700c194000440c0e00c06141c04452070b0103a444a10546400034003002340c54000c9502c011141030300344a842d5100303144d03500a00215103040310100d0800c0440c0300340c9080020000b83d1003813540c0320390020201d040d007800840301055250080b0980380c40d17095540361412490b10160910b5104240282d038031810004042d81070b410072180714200c11400051180714503507000c0c1603401410307030341c010046402c41c040c113203455042141a007900103e8032401480018041c00f800001c00280e40204a5002c5c0d500c203580c0071034503440111302076400c0b111044516070544c03c04000810352000550140c402c41d030385040400810790b6140011b4845103074940e000400a82c011001e083c1c40d50150714281d401400e161a09004540b01d074a4140780002003480e40311440c17604a8501d80c04e4038041c01 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 828065053 1250 828063803 828063827
    0x80313081b1c09030b0a020408010c20011505130e060103120305060906031009060b0303041e140901090c17250504061d03010e0f0a0b011406090d110a090c 68
    0x4212641d0040031020f04810101e12001300070608a6001920814154040d1002444508020300000c200705101402240501684000c00c10040803007141c8000c05018820030300c40d10600500792b250500301400070030348129418552043d1100710007211235100b040310b0390085016000c1d0ba80300300c454031300040a0351409084140b0884040b4180011b80c0c0e00400d003000580180b80c400140d04100b4500300c4064240c403083c00d40d0600000c500004d020134807010b14011407100402ca4500c0e0b980f1100e000388003810700341115800500c0c0e40014841c48140d41c2c04010f480c0e2007401d01052103090001034080800c42240c1e40c0c40f807420008a00b0413840c0b03041c0000c83c289121400e18505003814032a000b813507035118001c00b95480d54251203181150b00e0030360081c1806107000040d1756405190805899965038044030449a02c40850000988881b1015040492000040c140c030319103440c0c0c0003088003d5141c00c00684500036058500440d036641c5603000b0f030081100050100d0104e1840c80c010f4091a0084 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 828066303 1250 828065053 828065083
    0x1020405180117060f0a0f0f0c0504031401020421050f16150f05271002010203041a09030403020108092a030706140306190e01330804080313081b 64
    0x710a2280f04416805c2040d4400d440300c5000551510300c8640d400a48800320703240c8c1c1c0740c45c60480d004490303070791020052003664001d4900c038141064600e0054207d1149124010350382820403883e032080900c0b241c00305140c80c0181e0403540c1e552107a50005042456040d916442c07100b10600c208820503000c1803c051524a909142d0441420088080c20342e10402c01441c01020760440348400002056010080016000c0e2803283d4541d9804000ba0003980155030075900080d240d400d03003200c0700002e41c2081c800c143d03010103117007010f01d103030700541e00c05a014244500310b000e0001a5904610300c0e11842c119900c400ca080c13404242880141802c0500d076811990400001e410b00007007080103401107075000b000503180c6070580008041103c42d01c004035048480308808a000000e10300d080e860800e5281c0c079180d80000c188002c158400b100400407481824046041480080d020502c80301c0515400030503040c854141d030903103640e0b81c44258042d6001f43c8104000441d4155480784c20040c00030104c02e00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 828067553 1250 828066303 828066313
    0x9010f030902240705070b03041e03050901210203100603060602120319060b030709080115121209120c08060a090c180b1008090c0613050d020301020405180117 70
    0x790081201c503e144100022031480e200c11408451140d00d0488400b0b0383c102c4242c4020540ba4514542c4940c01502d090725550141d020200460140a01c0d05d951070b5819101d0340d1a05110000664203509030100c1f81c40c160004503001c0e03007500410300095114032109200c101800d0300305103028086420b190000011503000800c07040104c40c200003281c0c1c100400303a000d120b441506840300805002ca90300300d01d180c0100401888505500400584103540c0100c0013841807000710383c0c002e51805100c7c4140140e188118240d8408588400d415880200e01460140c0c142ca480e8005010300d11850a000c842c01c00d0040030030810300d40140a8150043d203000c0c42804140c2142d250444107040c14000c1407440d026800c0c0b84040c2c00442d61044e9010704015142daa80000203080203485524115114100c50050740410b0100b841c1c00811135200a4401804911041c105028411145034001080b601594200004109647d4500c460911401040c950300c0d915030502d8100c01c010205403510851507400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 828068803 1250 828067553 828067571
    0x608091608210412140606011d0103020306370e061005210a0b130e07140a03060212011802040518130c03111825121109010f03 56
    0x46540c040001d0340b4a0a120300380d01082c4184400d1040798401500400d01c0300e5a83d0030403c01503404212108540b0030341e42c1c0c1e69102c1c801074030481c00151903600c003003c2500342d103803040d0f020b54003135500800044e208102c1641040700c883c40310841d4808400345100c035480c007450b001703c2c03212000001e40040b5071040d02c141070a0300460303c140c031288016018800c02182c44804240031603064a1071003000040004282801400b2030010442110030500030744401890310400307805030003143e1548030804003c10846291400e10b15008000f2042d25900c88c0e001c020000106070700e400134162070300c0304c8045603417a9458441f51040140e01d005403040070300e00510081110365681e02700366140d840001400c00d51070f82c500f68001d00c0e101e00098001c008004800c0d0100500101c0c822804001c5800e9030440950f54071448074401c40e5804440c0c418001382034401e105880c0310a16031100e0142246e05102034442e14a800e00000e882c4824014417500300c011603110010340c2d010703880d06008405410101f0601e24 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 828070053 1250 828068803 828068819
    0x62c0d090510111501090605010305060f1f020a02060f04050102010b03070f0308030a09050d02100c0c0f06022a15060d05030928030b011e051e010c0c06080916 70
    0x290a0703140900882c0d8440c840c560b2024000aa000d844d4808120715540c1c4910b104802410707075008190000c1e10f4600010154113003280e078072204810007052654428444200002030311211085441140174030341ca0800180c480030080c11180c184461407584540c1048002070031a1544c208103072180e40042000c121840301032007101d0607290003804a0355070380d41c0c540180d4081c140c9414001c20500c03403e04007100441e07010449042d0903c8404003840f070050944421181d082e80000086c0142003a005180c00061b080c0d802030222820070a2156a00d600c803e180d420141103204041e50290406261048401440c0080f241c0c00b800c11204d0041c80d9640b03450391070340c0e40240b0103454090b031451200c6003180c255000511a4140000d40d08403410760310382c54018599030080c03244540340414208160a030311740e002d20311030940d0070243c418004203c000d4451404030041b034030490306010001a8400100d690005075401070106522a400e0600300103508500d0880c0d005804800e800301c00d00d00303100d814 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 828071303 1250 828070053 828070069
    0x151a1206160e010201110c010f05090d020d0e13050f01090501080d0c0210090806091f0207081603030905060a0b09070e0a14031c02061009090803070c062c0d0905 71
    0x550340c600442500e44982c0141e004015501041441242c00308454984a1054114072650a0545400e00441d00c80159240c0eaa402c00119030008da0404940c0700a8030748503c0c907010448400600000c074401c000c208400403194281c6034100120080f000500500b8280c0c02800c0c014a5490000d0051450710340c0018802240c1d032400171701c0b80c8501e000f0360724068401c8400074054000301d4156101804c0003110269524400c1c1542807482c20700d2010702c50f14071038034425039050542061201c7d240101030b500034204c9940c9540100e080c0760380c4400500110703908004e4107104840088c0c2c001800120360b0704205620500920180400004001903501c50711000b9001c0105d81c7d0b44010b9500c40e40200000134240005540d500f4070345000f6403006400d0560000300355004600400760032003c1500d8007050015110307a050050700c0280300b0404940c0d00c511800f00c4008090161030000f4010070348020741c050005c00700c1070741070080d083d01c108031292410500a58601c0059420010756652038140410304031 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 828072553 1250 828071303 828071341
    0xb070c1e031502210f060a0609050a06080702120705060a050109050610050a0201091407060809340b07110f030d0e06030601030213030f06060e0919151a1206 69
    0x325070041943d0b00b00f40c460301c62000902084d124255802c0c5800d40c011301d00240202c800512079035000300c002032110f024000316030a840700a8441c0062504028082d140d200340500305801f103100f154900c04104548102404100348100c01030142810003c1860080c0e03103060b00003141041c034150901c0091703591100a10008207040c185113490701c410f070b102a801480300351030103000704802c0307031800c0301e500b0300428007805680c501e8944c00740e56159840a10303512845542c01e2030b01185411100480c1c001501c1511110142072031141113010744400204003245c100103401c441e400104140308280349014941403440000590040100005040c001400b0301d4180c83e445000e040004045051a4820340485840c0c040300752009010f2940c80ca0130202d18140360034117403076140c074107200862108105603030035020f940700500a0030103102076002102589451001110300c1100490201c1c401d0a160041060f5507011060812029549409001d00c1e4991040d00e122150020b004004142c24034a003003c0e50 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 828073803 1250 828072553 828072593
    0xc050313120207180204080105070503090a03080c040510050c0106240503060409061b180f0e0a091b080717030f0f07060f0903030b010801030c05011103040b070c1e03 73
    0x2502032515070a81c14280550460642c0f5960901005600602170300248200c4294200800080e43d907040100d071540416581c02f6107941002d0980b00c0882e2107852466041800c00700410301d459903c00c0002c6a1000f40180d460104402140340112240300f8030807000140600040562140403a4151000c0340e080b128a1340c05014010000c64810b81b6283d0000b04000d920080030003840208820501c80803411241b050000b640810310808a5600c42d0411422660b243c800b480f01142084003124480340d000341210340441d551543d0700c1c0441c80102183e014080f000f40803908035410001c40c81d041440c2600704c2a0414800402c1c5980040e0000845060000d2440c1e01912032078007504010340c030b1040c3c0e0005041d4ad070900c41505680a02c0303601c2001040d00c00e45081080e001948019150382c08248005045001900d100b0071003540103e0404201041e07034000c0e20301e465203401005070b840e00028810713160042c00140c00e00c02e10241c3c540216150700041c0503c40703518a50b54602d064818580040d02c9 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 828075053 1250 828073803 828073823
    0x20102120a0306080a0302070302030607030e03030601050306041e0b28090b011e02010f06090b090103060b1212040303170c04140a0302090a0b13062103020c060304050a060c050313 79
    0x1c4a9100e82c0c0802c0c09088901d09030703605040c02c1e041c001d41d1b9443e00c3c0030070380c40390043e81c011584050003032290500401038407000e582180d48030340040d180ba400090141d03800684031100b0001400c071440d51810138100c00040054010800024041050a080b0124502800081d4030300202000c042091040700c0c414a4085440a03040004882e0603100c11201c2c2c0c0c0c140407002650190035010741100411160000003000340c02e54401d144401d840740c011038550032401050060012442c2900855402a0f014103072070022a01c00902030724000e400001c40c03c0d0740b40003180138810903030702903020400c22103008580781085c140000111000d100d0780c41030704000030108001810a4451280840c010364004145003054030b05a42000040c0c020b40000c1403282d940c45040c045000c0081c0b203404180c1e8508075150361080c403000650010341110301002d0b01944554068452280d45503001540300d20720500203060355044d035140030015a4a00d0f8080424808280100500c2e2080307018040e44864004501c3c007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 828076303 1250 828075053 828075067
    0x81b0102060a092a060e180402191211030c0409020a150c0c0801020d060603020c0d080c090301051609060c021c0c05090717100b2d16020102010c080402010212 70
    0x41200300a00d0313851080c040c51106911050035055440004680068035a00c5030081c201042103500c48008401c01c3c240c079442c40100780507007031480c00c028002c1c00c88010035480685802c4001c401d440d03c410b0031540e0128000da4031410381001d11124038128003d1700c06203c070304c400d40c0c000340c4190414001c80d03084003501d101d40d003080d9108840e40040550001d19248031140c5581080e07010f5445510500f030080c0c14000d001810904c00e100300ca25003080d03a40a8804110782410440c0c08850281020740f45590030f2140b004d10b40d42c2845140e0080e6000380c000820049004000740c18031119501007800c0c401e02d03080e0500503803228490501300fa130104450241601c8145854299081d00303030402600810114104040290001c0081410221700d22841c009580e40342400c940b075070403d000b1003001d6202804060440c95410001c0c41c602e146c0d9815003400c2e800300c808921002d400c288c2004030107101c071150300000d6503028410490075a2140c541b842161900d500003031366419820358620840c501c0041e4134 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 828077553 1250 828076303 828076313
    0x9011215090c3003020c04020f1215011101110f091306290306030c010f05071e060e010506010824030a05011d0d1211070b0907081b0102060a09 63
    0x5a01c15444a4200d414035210401040700c1c2003c15403c40000d040c403d2000204500c010602c034049030b1650040110541c1007041c440a0b42080c454803071014002e20800720000103400680d40f08800f00120784403030074503040005220b90104409001c2d541d24200d445d030380d0007400301c0440354410103510b4526a01c0d032032a00440c201c1e007804092440d0886ca404030101d40e2a44017008102266003201904680007450500c5007018402521119456030101302c0c5452076500a8440c40c0c0c00701590f04245042001c144c5038038803078442c19000d01108003e0601745208212a81c4544058142800c0c002c212601d403010002e00140307400f0781003603450030090707021a1903070031b441000400610300a400c0d03618000c01c502e01507000c0c0921440794412444441500780c484400040c80190841c203e564820084407251500c1e001442c0d40010000e113000304005040c0441e040b094868011610b9900030506d185c5807070310181c2051800302c2d00d40b0000100c0c01904015030b03400070313603a504809a80d20024529001e4508 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 828078803 1250 828077553 828077561
    0x30a0c0f02060f0c0d0f0615020c1c03050705120717070b04140f15040c060c050304090f020415050c070905060d0b1e040b15090103020607061802030f030706060509011215 75
    0xc1600000c0c100002c003200d059458010701f0844e404059a1140960a0803060740c640401c60701403078002c04042c2c2c0d00704212600420711440a4024100503151607080d803191802d00b51142d07002c4621000001746c0c4001c00550300720451000054020b40f07414045980d0b510b5802c442c0c054405800062120301e1180c0c04c075818400c030300b120500c0c17508031100040e40210b40904079404490944001c1748041c4d001450a00034203800d5101944078000d076103804d0800c01c9441c01810020507249425500703210114040c60f205000310014102515004c0e10791012101c01441c0a5039a04820341241c14842440490b0321200201c21000b680481c0441d03103036607850f80740e40402b00304ca01c02c00c20168034801404180114413152500480d0f0900725050803105507818062040c07001c1c40001d4019400f00440c2d00130500c9644803c142d030340d2100d0300300c034090002e40000c0d107050040e03020700381e150704000340d01c1e020042d19214403801448140c601500079858540c00f5030408100d002c010b4000070401c0031a220f20103050340 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 828080053 1250 828078803 828078817
    0x804021201050108101b08010302221d0615031b030a0804031a0f040201020a0809011704060501090b0f031b1c050d0f02010203150121020f030a0c0f02060f0c 69
    0x1000b0011981d45030480d03540c410546150803240d42c0b40030b200c400721004d841d4038243c4008680c5c4940d40f07240d1030340d400c1c0024240040d02400e42e01603a0004140305150314041e41c01410b0780040c54064070f0041e200350074203214028040040180300b03004100015100421039545012a000000f40e041040c0d4000c02c0c10500450b00c020050800060080f007088548021140300b058001c800c444d080d078551140090b0407005940190150388804131311000141480c00500720f150041c906014941a1016040310601c002c0d20112100c50300c4600601c510205407203285180f56003290450488a421000300ba12202c0711040d00c05038905004810102d0348902c441d4244800b0300c00d01c0400ba0a0083c1000c03a16400c540d0090310014a440d91000a25441402a42e011741c255000d0f51003490345140040d600b40a000c1035207007201c07030343d110038002400841c40900501105000c0d82d0342d80e85014a22174023120003406005092004484070152a00ea001030f000d0b50017a00d1a9a81c0a1501d58000e07290041c003440d4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 828081303 1250 828080053 828080089
    0x12030e0a1b0f240504080604080912060a0b031c09150908031602030c0d030e041e090303020304110910140102010b060a0201020a030f0203060612060d14060114010807050a080402 78
    0x10000d181c10098841071810f076040100c2041008451000722218800c074842c4003c0d642c8110046004140150014400018010005401c040708400c04c45d05001c4112500f10005a5a032208203160606022070f400d0390140e030040d84c908003a01e81c1d0150060400340108510550543c0d083c1079800d005800c004040d1245400f2031f900e4800c200407a411000200c20101c0c02402030048421081c14490305404800740d0586600703540381020b000b03200c020801581020700c114a0018803e126010302d203c0c04040c20b0180d500580e407450300e8241103000300002040c00740113480c0a0104000d1000c0c00e407072401034807129080036411003403000040f800b402c9848210340e80203c00040125071160150300919006c0000c5d1018030140340c1d155451301c100d0000721407558001e1002c0100040c0307940c11034041584500010101e00311034165486618840c41c0340b00341610704c0e601800040c041100304075810110315030b0900c0d10700c016142540d00201030307000e5501e9038000d00440b00c000c01c00310b5450300d0304108a800d00f0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 828082553 1250 828081303 828081329
    0x180b1f05010f1124090106090203011a070614131e03082d010f060807030b13090618080a1b050703061a130c030e0f060105010c03091805010312030e0a1b 67
    0x260010061120045d9940611986042000a2401c0c0e42d4002d0324103e41812461465424051300c1c03c2402d64800c10f400c035a4203a8400c08403804107003901c025809881000e88180707045c10286040c1c501c0d01902c284c540a034441e000104030010360f10940d581d130303c40c0b410008007040b40d148030461440d5002d0707600315540e16080c0000103d464000c0d02c0c81801101c4850751828016260f00e41e0940c2210074808110fa00064043d109402d643c443c2c0d0890028a4843c01000440d03103419000010b4a0340f0021044408190014403080b003242c0c4600900e002282076101500703e20840d035190303561241c3d284801418203031150708140c86403058203c46001038001910b242c005144100303141000780409180400400d2070140d07140c40d01e00340020450030351414400100001d909107001518038074440c01c8100c0401c001c07400c0125100e02045010302c0002d901000c049040d5056280c21600e6454150070082050301d4154008212500011000c0f0000d41120070307642094588800d800ca0f400c410307007108138a0001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 828083803 1250 828082553 828082603
    0x1605030c180103021c05010f320105100908010527150f131407030209100b040b090604080f03031905040f0f1e050c090c0708030f0901180b1f05010f11 66
    0x12600a2500d403844c0c0355441d807504800e440c1c00300c0c0b00350242d144000b901527280c00511040c18480030701c0541c0c505605140740710f5940c801d03001c0d094441c21240117801010001030168090b5403840420903c01b880005003421440700b26400001640041055021400840c04281c1c4400001d442c412665003040051441c20381c60948550360380c2040c80200d00800e20b440010f034038540103404403401d80e08100a142e1800e0310340b0904800320b82104805035031141d01000700107400f0310200b000c51401107801d40559120320f001d410400201ca00d8007070000c01030341004200310005000861aa46569210403501c00c0324080c0e040c01c00a108101da1007406095419031071000344600014070240e007541c200ca848060780e5602100030100e0080300350090040906201045043c40c05d0710445034003d2903000001703210b0074a4058020115080c002c02d070780d42038070107041c40045061a040f81d4900b0582600414801d8070307090008002c501c2c065018020407066407940c610310201408070151041d244040850543e80f = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 828085053 1250 828083803 828083831
    0xf0a0f03060e04030309050708190209060a050909150a020a0f0305090717010929042003060c040602010b01090602071521020919080a02010f02010e1605030c180103021c0501 76
    0x1048003075895103e154170008803249c002601c540842038503009541d6a031581c0d07003030005294010f446260705c580103c102141e1516104591841604150001e00b0a580a008260781c0b14401401c200c0d01c0c1c80c01000910443e0341c1001580c8144d0b6100c0c0b400080c1e907900c4444c014148040c6d50409000d561514400456102054100402980c007510b4149400b24010404d40310509050910603403006100c8000b8005c150b03080c1181d5920000004080c000c028441c000034104101240c0b0030001c2040410306100c8550b0910a0104061003130802544840c00c000b0043c2d0340304031600c40c44c1000004000e480c40c10038400ca08180c0d643d502428065100c50008100303070041d4001c02c0503203016150003412009450380405d40c000480b41d50038040e01c9419810303001110200140b030345e1b81013559240c1e442610442000c0003e0440c0c5003076040808201d41c2007104140c10031040b100483c0c800c1803a030010700c01041030005558116030703040f079505c403184066400c242d0003584a8803002c2d0040d444c03c50400d4501d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 828086303 1250 828085053 828085061
    0x1509040606080d0c0b010506250602070b0105010e010c060b06070807060605010e0a0315021803030c0604020a05120c040b0d05030d0c0806100203030402121c051c020f0a0f03060e040303 81
    0x9800b01e41929000a0300d440102c41c00d04a40e08042c0217140ca02004101c7c41c180300008190003000846000c0003114001a01c2044244403038049070040c0e80018035100744860004200e000d441c091030031184c0c407100000000c00050b0400c402a1840380d480d210306240e0340d5a8021a40c90b164001e5806845d2911414414001c1805108407404580d4062880e10146050301c81c200c00e599200c034110205000701c070f210b41d00940010403003900d0503400031040203803a0340400c054080b000c050710007048245000c0c81032240d01c80007580601d004030381041e028100044086910707114004150360024a4080e880d0009007594200c0070007078014040000c080c540b641254010314a034010580740c03040992240814406125000c401c0007005030018070200f00180f400505001c3c204140004071400c0002c0744903250041141c2e8003001010840000d1103012640f012840f800c0488008a4118100002e405e802c24480c0301d507118080401001d0080c07038076514065802503000d480142d00340706c2246403d2502030020 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 828087553 1250 828086303 828086309
    0xf120705060c190305100f180f050c0912100914010b15040b0706110307120f09030e06030709030b0a0605120d0e01030209030a0b04050a0b010e01050105030f1509040606 74
    0x140640c00c00120b016070070008880e2108070030140743c1d442a0000008800924014002441d11a00300c480001e0f4000b00c1c520400c06004207001010040e100c01402604841c00060500c001508100030041e200c42c0f1201075690300001581c20403060140600307207506003070b03100749403500d160b251113514814401d081060381c0b001814900200000c44090040025a84d0046818030700491f0800041c0800315980001c1d1484c9485600d020465100304541e0700e08507003040f9850b000080307040150341580001409400000820110b0400880302c00d0b4500a010041c80500d150203600e001000c01ea0580c4100d50f080300840e0801031800c1c4500345840004054060781c840c851003403080d40f14038140d008001c500ca004051107601c840f000c0b01d4801e4010350294200180c0a070740340c05003240d22408a00e840720017620851050b0701502e141c8a081c50726a28242c0e060300820349160f103490040c051640c10108a9070403c1204410082540d180460a0640e00110200e00d410460b107001380000c020320b5410600039 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 828088803 1250 828087553 828087563
    0x10b1216270b0c07080d1e0f050706090302030a1803051c0c0813170105090717071e0e010e13030810030609030e0901090b0d02040e0c030307030806090709060c0605090f1207 76
    0x1401650080480340b0a52284020307c00c504801c400600c00c0e03000e00c00d80006410641465400c0a6141d03c8020842c1c2e0609001e9016800004010300c980e41c2c031440c1c19803038415615a1a05203800c58840c80d685002c030148a02100b0406645045c1082c02140822440caa001d030206070307141608800704041200301d105528000c201281284854041800795500c982540002841b003985400d425400b80c0580f880544042d0043c81c002140d90900c6140c01c280d90215070303920080c1c56240407038000120005a01083d0100102c105000c0421b20107a14422100d07010301d420340141c1c45218107104200e41a03440104018980310541c010580c000c0e500c000c12910484041c0781682c0e0311303182c00b400c0c0c64a11803403a038041d070b030300808bc3e0040c5483d62003d4504204039080b15148011040420301e1a400220140c0214100b2810490245030a030085644031036a483c00c0ca202500d05440030305030fa01214802007078161034400081c4100c0c6c04100002c110744207801200c43d90190b882000381241e203d0401500c5d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 828090053 1250 828088803 828088813
    0x909060c08150103050c0c0f07150306030308070507030e0a0603050609060303030105030a150f020c1006150509011101141603050a06030b071d0306010b1216270b0c0708 74
    0x110140684150303445900282d510b0714a503122180110000c110080070044140c07428800450f01e004100f00400152000d14001d001c414100300e110304030081840c0c102000c060a219090000030350007906960414413a090940c3c580041d840d055500c43e0180f05c4254000c045904005a82ea0b410b0304014085c2c4415100e131451074072a0014141c0700d10090060702d42550001e112040050583d8090034183c0030401c100160340c0c03d282c0190030030780c0e00c103907080e011642c80182c0e100480d042901c62540140621b9003074584404804a000d041030041043c281c2c14000700162450310000290804000303820180c01c1c2c84039901d440f01d80340018002c130030940d100013494a0700103448005144030b08001d42780c009102074011b9981c6242296285c19800c1c1010403619030201181e5a51070401049010b803804c0c4086c80d440d409110070f00d010b20300c1d004000a840c014008414a03a89030844801e18494221f00ca00000300c00034252002000506648000c20b945070000e0101c105900201e01c000c140c03110101031350 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 828091303 1250 828090053 828090071
    0x71e090905101a090303130305010b1f1b02040e0f0718050f01120f05010603050a170a0e15090d0b0402040b0105040b0f1b0a050604030206011e050613050901090906 72
    0x90000300c058040d07543c8034100b01102141800410303001d0066468000c080368601200c0c2048031843c81220740c403c44d51a91074041072182c916100b01424003004c0400c94031440000c00413002054841d501015072000034241c51030400f5900c3e07682009a40710f1071a001c43c0c10b02c8070041591955100180704000310001100701050010200b40182c6006040e108200003081e401d180325986003094a20b401c41f10010b01c8803043d0300007034003070255000840c092406803100c3c0409040c01085111416100060b4460404c810501960808289280c0c15002d0303600401c07142181001060342e10549844540c4030038804128403c02c455651000d106910945081c0038442d409001542d1500513170190400c011800d000c05101e0305100d1003d060400070110000c448030302440001c9042005100055899030800705c204018187c041244500400341201040f01050041e000486404158080e0502c10b0b0f000240c00c5948541c107012100140070010074124980d60761b02142001040c0e180c000f2100706007004056 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 828092553 1250 828091303 828091321
    0x309031403190b010f12021303121e0525021314010801140906130c03140c0103050114180903090a17010b190e040f1506090605030604120503071e090905 67
    0x1e02020105d500c03a00c091074840c1468002940159417482e8002200802c0000814070800c1c4881c55440a900d0f1003040341944843c1201c1c000c07101d4400400c0c460100f02c1c0b540c0400003200324440005080120120441252000520514010980030074003410100d5a1021041d0740e1b50081c101c9103414000c11482c600c10300008440c290484030003880707400000004034541c41060810028901c54054030031107580b29500c24800c4d11200c0051a059400405c0b4a4800d5030141324890240c0f0040109580501002c0006511422000d0f604182e00e10642c0c080355034100c08201f500c0514400900405070346440e0070040c41c8240101030b0000896081c90040001030170b1654038084001034602c810340701c60342004070b001042e481c0907200300c0706c2080c25072600011a0740c1034969442c2001c081e001089891070041200241c1d040341e0032442c804c2c1c12900a1000048d4080e0a102140d0081d040c8540c50b42d0f0b440d42c0507603007801c0305454450b610b183c030b0b21548d1b6029444400b4105881c2754034403c1105403241c0000c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 828093803 1250 828092553 828092567
    0x1080a06061407140a06060905100b16110a0b03091612120c0b0a1e0515091e040507240f140d180b06090c09010309031403190b01 57
    0x100c00100b42a02d00140280d80c1c44001803901902035400b403204140b08480d0140340a501540c2620f000795203100c14418820b160281c66002040c18002c40c41c22401c00306001540d03c600c103c504c00306002041c110b000c000000c402410301c800e00402182056950302c0000503540e204880341c071164083c1c0301e050080e1540524010301600e2902c405030710302c1c10241c2e58503000103540d2107005003402001038000c8009507103912071510a1550f000c000c2043c03006100100c8182000003900c0c00f0b010304000410891880840300c070f058515040703540442580b101040011504a07118101a40548440401052100000740c81c1d048403800647c409074101c0d00721007100303070700114282c41c40002e4058000703900d4144100700211058086904551a04001002440803110741c3d00d604020140e000d403242e402d110003a810b00340d01c00307429a00c42d016860005682056842108401410315686261080a061007a1100b42c40080c84100a5580b4145001c1005220012100400481d8280820a011548690b031 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 828095053 1250 828093803 828093809
    0xe030307031707110105070f0f05071a0606090d12090f030305030f04060e011a040f11040e270615030c0a031e211404050a032303031501080a06 63
    0x500c902c40740040d20039440300d12402424070820032280f42ca410050384000e2189600031441c6840b04514132401500c00303048000d00400c00400c1c01018051500403038085014440d1160483c00e0101d040c1c0d4a18001a5583c0900c03c0d155401c10000e1b201c220400035105c0d503400038a551512201200c55031015014074500b00b50100500003042800803500c081551208540c003c0d10410703011400c19501c690960031250100f12102242c82061026006410240304803006110600004d0161220a07080d0003482e1044c0d20804451140300300009440c0c4006610804204c00d0142c06085944008903800d03035034032410741e07031200001701200f03901500780b0b400034000744026000707480d0b5450301e8a95114082c0c442502406907500048003102a40022249551424003030011100140c03000c1ca20078000701007207041c5103043d5817048100014000341d900c6400d4941120b030320000c0100302900441d203140c000000440503a40e58440071041c4a80d0f000400c41d04081c4010170b0340c2c0c45420356102010203094444030300c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 828096303 1250 828095053 828095057
    0xf080a0323070303050a06031709040510050d0201050f070611121e0a2d05010f060801050a090203090a021f030b180a05130c060306050901080a15020d0608070e01060e03030703 77
    0xc82d000c0064083d0300566400321800343c000410356607a84031103508092454144181d8000051480703500e281500c21140c011186852500c412400d000204201603582d0001a05018002c07038400100480f6404071940740b98010b0003440545011200c0c03040c10b411142c51100c0340d6500100251054142e4240740c03102166100c1042c0c81902da90900304000c001c03124030301e241d06610b19041060f0f964191071489484221820016041d890400800301c074601c6500940204108100100916901d440a24003554001c0c2c0d801640d07515403c400920f40350309684000e420034080ca844803056460101d9011170309200c2d8500740305010401d02004032501c1040e02641e01102020b0104034a120345034001d9a20900001d24030b5003415480d01d07820740c07111840c2d2041c000241c59160070300080c2032041c0d510b8014500c9400920b9a4001a507410314401e4280303c103980920740c04102c0d20300c114001d4000000501c100c000303640a06807901415030700b40c0b4090140c400460715181e203078200c40c1400000c4910f880d40507 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 828097553 1250 828096303 828096307
    0x207020f010e180f0708130305030a050a0209040c180b040605190309080f13060f0c1b05060c06160e220f0509061005060a020c04020c01060f080a0323 66
    0x140019150145203207101a002120001004900300d012010300e4002c4012501d040d00320720308100c0086c10070500511aa054031411504a070000f038001c82542e801414200020805586a001360402805002c200640c03250414000c60082078100d04046a0509020740c2c0941282c1c4444154202d48558420440022820030810140000d030514136041c4091500c2c02241c50f0f921070702d80c148940c02868030003c3d0383c60005840480040340b04c407660024000350900c0414007490510180a4400030f29004d841e2090820000c1003a00f05c0c1e556117005020010201901c0306031403003c40fa5148011148901fa07844c510501450503406031501802039040141b00e01c1d04184440c54a007006030b02410f8212a15031510003082004286006a910800c01c01008041c00e14100754010a001c0042d030000b8065402007107221881d9034040380748152010207480250307803103000000b52401801103620040e5118111744000c1201000403c54216543c001d6031100d4610340f514080701501510810117000d10201 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 828098803 1250 828097553 828097579
    0x220501090b010527030a1a010f0311060c010b03060106020a2a0510030b04061d1f1a0c0a0501060e0c16121211030105010f050c060403351603020702 65
    0xf44c800d00310510b80f090000118103c910011034504031514400300c4406c148070016010040700e0744a420300400482071088952451600d600f813451170811503c500801c0000780c0032121000941003484124006412665190b075071b410003e44810f80c04a088034600a00c41d0200705005860300780304074003880715000e40d11443c50700d4200040d01119840c02d4040c5601c4101c2d8141640d99880b4504c0103000c804500703040140300400c24040e03480b0043c8004100c00303a840c500c0c0c0315440030014410643d0010b03031650210311002001e14810f8001c3c010b14010902c00c0c16915810404107400a03c120b40d110305c0004070342e49503001c00306614080c100251500c42c44602e8a030009c964042e05200d078444060412000048d5080d0424050b2140b0660286207400000010899540e205040048030310181c5841401c18040507109911000f01610160800c900d140344d4003601c1c4080502042500500c2d0452a071820b84145403032a080300c111041081020b0400703503004114024000c80ea145907000b40040d1001c0b903 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 828100053 1250 828098803 828098827
    0x160e0a06111905160b1c020c0f0307080405040e0607080a020f0409020d06061b020d141203040c0608010b18190f290a0c0807020f220501090b0105 64
    0x492071008a40510600881200e010341d014a400401c5000d038000d0010020700ba2520101d00000d82d000c01c2001104006c0004000c2c0d4001913220314072011400981d030368140e520550300d081d948500b00d41c0715020004402d400c00851000410484406850501c2a01c2516a80700e0700d91070101c0d03c4802243d110400500760300f8481c1c0c010803000d01c200070481e081980322070b4031200302e030030840c1540c42c0c0654482040c440b1b103030403c1070789a01000300000900c1044443e03002c908011610080141100e00896001d07181201c10f2042c4030070303041c1c04541640c5a00c0c0904046400202d140309142c0452724000012070100040310880b803403005030f003898001c41004202480519640e0b052000c4c4208021080480e410752280311060041005240403c08082e881100d0388040c19401a28002d1a900300407410b0b4154106c81e8825010703811100d45500e0b1200c40c0081200480b500c2000e903400081841c03410817880b80110000d400b1341040d0000c02c4947e0700d8404610171215058985408124248001c503c004 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 828101303 1250 828100053 828100067
    0x1050c0d05040c0f15030501050a0f06120609050903120702191b03060c0e03011d0705010f1202031e070c0b180106090c3203010b2a06160e0a06 63
    0x15100d02454401c03265503030001400b04030140c100056504054220b501e045d40e00d401291302400b421503040302e01703038a0701405000b101d03014400c50041c40310340360006c44071401d5176103c98010b141e03d1714140b1243c0381c01c6100070b88030386c00b110029003600c10360400300e2009071001624201e051071902090700c400e80d2a4540a01203001c64071400840310000e40007000080850207000007640150715510f010074811010507007511002094410b102d40841035200c20000009094000c841083c00c5c083d920304ca925030304564813006003c0c0c81c5045400001480040c03061211181c06100329040c1d4a1134a03122420f003290a444510000340c1001e81080c00302d0383c01011240100001024480006190380ea02e800c003200340e546107041140820250480218851740308070808001130b845400d812641055071089221500060045005041020400740d4180c0f441d115048003880d50906400d1403040c801c890903a41e107800b1105d4503c0702c6683c0d0444043c880c0211990582c9410040c500000a41010f0b82103c0c45 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 828102553 1250 828101303 828101311
    0xc03051212010e0a0b030d0e0a0b070206070308091011270a0303030b0f120c0a05060c0d030504080c0609060a110f030412020109020a03081e030123030708120d0c0201050c0d05 77
    0x15603981701c00040341c0c0d081055100e00e038a02d890b1744801e60558010001c0e080c009a020f00e41489081280a005995440440b200160700d03050085007a00c030228540c5c0381280c0701c0d08400e001458602c41c64501881c040c05081c1d0f000c402d0030307040040610310a11081411060036482c1d00802030b0a414000a4020f4200540043d4050901c6103020441c00006a032282681c040c240d0710340000900400300d00b82485040003501c420348103d443c05e0050b134205961210300300c040404269550b030200e800c100e2907030100d130340e000703d80d03c100c2d4a14100008180d45814082d200452010318010b245d002c140201420f46000110140c1c0203400c41e51640c5400d8140041d9045a5046558035080000142d40300b4111201560081c0b074055150007040c01701c01458075141003a54030b480303014001040a00b800f405044080d10303903018842c00284000700800d250908680006c5080e000703c10021002c07005010142210000a600170b0044800450041e401c0742c409407410072072841c0c100012080c10019410907608 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 828103803 1250 828102553 828102571
    0x130c0b071e20040b0a0f2103090905090c1e0405090712060b1908060a0e01050f0411010306090204081f0b060403020d08040503060a0b011206051c051006030c03051212010e 75
    0x95003d03d50300055170510550003001c026245840c0500002141c00c400c40c01036007003001c803505496901d0b10301a0507005036216511080d5180e00000304458414010141c4441e0050074034080242140c001f5080c440701c00310000d00032860040024249480020604e0440d01e50740c07101030391027a5944a01000d0240442a160003041a80d688858001c4c040708081c0100843c2d000781209003411584041030780e00c118810b4246038100014085501e04d10790005070050742c404e0380d0a4040200800580180000740d0080c03500601c04100003900c0c0c0004a00b01c4042111700c00f052003214a80715180f02120301803e004e50700000280b1003400141011800c14010314001c6400d14201542c580000c1c1c90100100c8800c00f0075511a5060712040d41c11000148a11341b8500003071101a050401282140600807000300b00d14020121120903c0300c14044401e4440c207452051050f607884e400c1c001e040c5201840f041b5000c0c4180e011807452404c02d8001e80d400c14982005102d03d0340d280c1011040d0200300541002c003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 828105053 1250 828103803 828103811
    0x619061b02030a0303020301080d230c19050714010903050c19150315121a1e0c131a030604020a030e160806130f0b130c0b071e2004 58
    0x9a03400300000303c6418429a000345c1c3e20340c149803040742001c030760000c10800d006490b103070b03003070111503074090703070415403806401c01d40c649215414441c0f925110140600080b44200d14801c1031103801315020f4240c403501e0032140400c5441350011103c11856100c00b4080d0340296001503c1c0345050140072600c036205d8103000300c400b516a50b0052980920000d00008a55541c0210b2540c00300b00c030101000f80300c40c0450024902d21a101c808070903c0c0c1246004032078481c0000070303007080c940d5200440416140c4c000d04101c0c0c6424021003c96a010203000d09810390740710800118200800e140d09264404a035030076007540c84070f40612003c0c6d00114209005d00d034851045141c83c0d80c0400005070010802e8480800c95454100024100f9401070100b03003032040100120408500d800e898115460f41c05491031400d40e68030038049210004090307000700341c001d83d00b03000030b05e1030380f00c074003800056001c1c003288880b01c0280110700c010320910384001400c104040080404600780c2d21a240c04c5842c0180c404a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 828106303 1250 828105053 828105107
    0xc01091a0306090c04170102090a050406120f02041b0e041a0a210b0f04020f1c08030912030f040506010807050918010e0f010e0132070201020f070614061906 69
    0x11700039031503d081010303623502250321a9180b510b103006000410701900c040000505118000c000318621007000760412001c0241c900031501e450744908403680500d00702d12100004c1d104003c000c40b02900c02180b2403403e02c00c070070b14403090041031842c1c00700c001080300801514100b4544100910700c8014581240708001c000045400c0040580c071544010148044600e0244100714024401c01600c502410101c100c20040c021210302ca1960213400144540d201d80d146804140340500780003d21040640c0407041c000c0e01071110380e0507401240703d042607542e0b1f40e8031007801642d5100140726003a4090031a50200d800c0400c3c0c52190740f0114140c10002c01c189042c08045484c08400c070b0a901050b070356440e6407110a54080c858510a03002240d144007843c01504a40320b01a040890440700c0e0384070303035008a000c580c000d5048407010001c014099442e501c181c20224000e01007051600481122000058100e01c3d240046910340701c0315065400d0b0701070400404940d50003195a40280c070740e40084982d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 828107553 1250 828106303 828106319
    0x309070e0a090209150306070228020604050a0621050603030316020c030105090d030c030e030315060c0a0f14011b0e0a050603100305010c090b041206090609050c01091a0306090c04 79
    0x140c2c4260b01c2e013410209409141070074940340100048c890411900300c003c0d050404075804454080c071445048a140e8000a14000070b4171520991740102d900803100a00084c40c40c1e045000070345030220304282d10300038601c028070706800d072042162401c0c1e064108100080380d0802c103680c0030703505e94080d00c100c0300494410404282100d809a50052081d8800900045501d03030600071158080d240f80740510408100103c21503030f0380400f60440ca22250002c3c02681c3d503445039810341b840810b03080e0886144000500340f030440500c0403102600c42d40315001400080440c14003a41d2440b06580c503600c1c10343c0e08100c108841727182d0342c02e00d03c640c0100c004800081561300d00c00a14014a902c00300c400d4141e24500e0a1821200d49007041020301c0064101000481c0d42501900c0441c2c030001481d01c0c900d441858001d0060007001c030b000b080945002e99000a00200145c070245021082c0c0300d0603801c035180c00004010070302541c5134030701d1202c0400c0043c540e42025441207030444000e100701d5041c0760b01c070000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 828108803 1250 828107553 828107569
    0x4060927020d060e06120712020105190c060c0c0b04032d030e0f0c090f100b070812070315050d02030f030c0307060501062c010e030706091a0309070e0a0902 69
    0x75102c0c0603114041404a803003e0451142c010700200c9040d0301403000c0c414469140c1a451096440c5080ca00c038210003564050821030b040700d544101028072070034107650050004031500074291511454200000d041c14040d40f20310803d036811050244c51951140c0d0f0403030319001442c500c440300c1c28030204410f4010a40400000391415071392404284e8502d040b075041d2a001c10590180a664010b03522440691503d8500d1070700014030000303500495407100d44800480341141d2003001d4140d800218841800000000381c42c82c0f4590001040e01515840000c41c241c40c1c00800e40000c84210030300401c8240350a180c8200083d1001d006e441ca00303204149841c1c1980c2044402c11159000042e400d8204a1a44511409420303503007080d11386602c9010701c051103040800385402006010034001400c80e070003406481c00c190401022140c41c0398603200010b044001c0d52040c00e03030141488206080d08c003641810346c1d00c203c038000002c0864501d020b12154041c4409007040a01a5403070707501c54003503200d00c0a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 828110053 1250 828108803 828108817
    0x601032012030a17100b070201080a14010f06031b02060a0e12030106030501030c080a120c050c030639120402011812020f060a0828060e09120406092702 67
    0x307400c2d4400720041c56084c00401d00418000381c1428850051050070f07207800940d083c03140c0a28003442c1d5a92242e2000c8010036402c1031380080e0f44c8a5400001e915254500014140c444580d8240311218030140b2933684a03200592010141c1c0021000444080c0250701003003844420701d084a00c03110140510a50035407080c0c0050380000c0c3c4490040c0288082e5040b014024003904004055818172600d40c00070001000b10b4201c10015020ba500702440303810823100c1a081c1d801000c4d10031030300307203042e0b0015001c13610ba480754030019014400400c5d100c296002e1701b510700c1003800344900e014000c0703c16001005000340124148014600c04202100b099901c0c48064041c08030980784034030141c01002030382c1c00311012031803148d002005140207851f40025800d4102041401d202070101e00c15800d10000c10030b0321100d403000c0341b03000700000b03d07101d01d00000b501480100043c0c4003818030004526000388501c1c0100004503807242c10400c41c4200c4224682d25582c141403100840c0c0d10990022400d99000321 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 828111303 1250 828110053 828110057
    0xa0801290c240403050f0d0f0c020d021c020709050a02040b040603062318040c08010e0a0c0503070501020d081504140402181302040b0f040221090601032012030a 71
    0x11051502e03a403680d81c1012a9a404040c2e1180c55207007907600101107200f10010035103540703c0440d0224038511f0b150404603c50518034014041c48000f850300a507035907601d81200740188240042c00740400892079507080002c40580c00b03402120308002150021301000fa1011843c29801c100c000340d0807000b82c010b030024054950700400c007985080001580b21039140a0b004116030441035400103980c4422090446034801d00180f001035541d0309024207604242c1d03003c00740319401c2c11250110031002081d12100700d84540c1c1540e20312600c840600d40d031340c4403500070103016038069842710315460f0140c2c09050340855400d04002d00c40c002540400e05464000381006d50444202c81440110702e40003400103200e1800c40c42c0b0450506d020206800c0c2c4c104402c0340a03015550751849203542d40c80b0252003e0b04490f003c4d000359622188220010000c2065140c1c00701e00c10000008143c03000c2001c0303521812a80c00800c0110942d0060660448580e149030380715134400080560704142031811300181066940320b07 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 828112553 1250 828111303 828111313
    0x51501030b0f0907120318031e1a0106020309011107030f060c0206181009050a060e0a0b011502070e091f0b030d032f211b0a0801290c 59
    0x129403450710100380500324030160380002009200c00c40c140041c900c88213030580340c1181f01080a400030100d0402e00d0f00040d1164003000203074442c00341d03407062000d000380c407441100c03614103c6e580d0b2111151030203000c0d0400503002080344810640c4190040341030240d146040e5030000d0b41c1c9035140f5848955641044030b8a9494910032000a6014043c03a50b10800855043c90788074001c4040d6a02c070f4048408075001546d44040103818040100815050554003040400041e81000f80c506e5030303211290001c0b5020a102000803c5003020500c80c0340015115030000c10a160074880c00201d808001000c1e981c0c00c0c840c1020f5405824000c61540034105052180001c1303a5091405150601c1000700c914401c1c0345c1800510040e6181c0d800c1c80325980301d41d0707440458116601405802140c03003554a000b400c00c87c00c000c8650543e0900d50b246015041c9802e94010904424001114500402e00c4040205002c840100898001800c00c083c4045840c0c09010501d0510606075950fa0001d103170400c0e035540a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 828113803 1250 828112553 828112561
    0x9310501180605040924020c10020408070614040b0703050706020a031d0c0d060e1614030c0d0807020d020609060d1a0909030f0a120e01090636051501030b 68
    0x828450003016010a490174042c862050f19003542456891402e01d10211604014024014041c0c0c1560b82010b0751000303071035109407032280200107074009020300794043c011000700080090003989401c0c1d14507042180d00f424540f41405800007078000038000d40c1484010082d08001403003500c000d29442401c0d881c002500f2080c4100a480048031021128042c0d010442c0c024850fa210602012655403107500810300d04400b10040d402c01040c414200007101d092080455402499803450a480409608480c0002000400c2040c00040c03004090031300c43c006c2003000054140040442d90440c0058511440c119800c0c000c903019902006040d420681d841601448018250b07880d403241207004c46a10f16503040a410301c0d904e0b84181e028001c220080020344203000c50242d80c024200090101081001c070218140b0503019226140c41111003c1c5041c820a000080350410b00806241c8190400c410300da442010342c074030700320070b2105072007621035890605e59444090700d581c1d01a6109000030a12810 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 828115053 1250 828113803 828113849
    0xd022104050d080912130509071e02070f0e0411120d020105130525030213020d0c02120d0216050d0504030b0907080a02150c0f0c1509310501 62
    0x6001d00310304100300c9240140300b440d10000400c0e00b40f01c101d05c00305030354a0742c0300d0041403001c20b1254451070300f0000e2402044082d58102d20703d00c0300224510442c111154560504980b100c12500500f1011403c51205014001d5a02c3c0b507164044d1090254080c116900000100c6250411074084035940c48818061056642801980e800c014681d41c0c1c0c000700031f500d545e96520342d1055001205c1008030044042540741008100100650300503045d4081c40a00d4070414010f58007162402002e1414110401030301403001600c407100e2100e0051080c108a02d0600c50340c003a40c0b0440e40300080038540c820702404a003003031040c1801441c182d00c0d841d81d502c0c558948180c0c2e8580c000c04900300c64024800c2009990408111401025412140346904a50881881d4614040c603030001c20315110f0040b50180340b20300001c803d0b4000074216001a54418101d000320014480c51030720036009214511601d16100408070742d0906000c0200c640c1d145540e00d007a440c0304a8009a1212641042c1a2080740b0804 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 828116303 1250 828115053 828115063
    0x51b01140a0516050c0411160b07140c0d03060e07080103030809100212011e2312011a0112020703140306030a021f18050904230f030306190510050d02210405 69
    0x104000200c1d80c207040c1c0310b248d00075690440503400f81c250f1410300d0010f82000d1144184040c240c3c09005120380362085008202d940300340c005285800310340f60800114402d074000c01090f01c14800d940d14050141c3c2035030f1b400c9a00200180c800d4004d4464000c0134141b81d006800070b0510350b0305d9114100d03c1580740c0341350325007522503001150504207000f1100f44004001c001100d00c182d0500352014a00381800c9010925100b0340e0549a5083d520f02080c0c40b4039400258020a40580c090340c40d00018107005050314100d00c10303413100034040b58130703018482c0403d6044405540d000e80000e066420f4542c0e6074001c20f05400e4031001c40081d500d020901512410740012145d01d140800e0b81c18010030032b0600c1c000c0343c0d8000001d480074040a03805070350b0144400f014035260302c541cec1040066a0300e008d41901d004d5525001550740e1403050501c2000480c0c0d030381e1020420800c0324001008100c140d184203005851a6110741d0300805880c3c1c08002000e184422a0071001d100c2064808261f00c80c5030034207001e8201 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 828117553 1250 828116303 828116321
    0x240403051f0b0d030c020d0204060806040302101802150f0a081801090f110d0c14090606031006121113140301050402011d04020712030504051b01140a0516050c04 71
    0x42450500e45100755143d0820000245515050201c1c2c85061400000e43e61601030768000c0d03019040c00d074003090414021695a0140e8420380850310740c8216203420fa17040d2001140482c0c001d034042c0055202502e88a10030180ea1085500b84a1802c2510910402c0030b900441308070011272140e00074004415112614580304019040003000504582c3d5034039008180501c1000c2c00e80096481e116010ba47c0703c0a0b9000303070039849207110b1207195403040192240000e04000d00e01c140003020000d0064102030003200e200d004800818131002d400c14038159183c0c01c9200e00c0717041c5999250024105170303001400a01c0d00703419180410781030a10300020f0b480e800d404000b40d40d0080e4103060074000180d03005010040c000c2d80400040c81854003030030204009008d00c050180c18100c02c101104061034060340a18000c078051010780304000c45000c0c1a114003012002042e00241fa5504181e00c40641c400184c8070105442c82d00d1840c1c04c10002e2451048864541d003500c803034208220400d403614062151940b1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 828118803 1250 828117553 828117613
    0x602060907061d0a0320040204140402071415060a06020a11060d0f1406010e03030406020307060203040f2406090b010e0d14031c1d060624040305 64
    0x480c5001980151100c00301e220740e000307000d25800038100e40007100341c5102c580c41d8094118000b16035203060192541e25000d103460080701c82002e00d4900c81c00c0c02e00846055810103109803c28034002c40c2400000c0d44802c0c1c0c1a14002c007031204030306d0b03071640500c101402e100155880181c1414a14108081070342103511050079548115403007070000d0158100070f00303030010440c0c0045d1100610344004003d01182016503202d01d1500c1c0c0e200c052040d040740c0003030080e0000c0c2d85100c2e1400000702856640d100f01c0c0140c80c0035901c03e010800014509800842d4000c1c4507450401c9103503000d542e506100b4010003149001e6100c002d41c101c5410800c1d01c1664000d01c9508014004406030320006412115400240e90260051380c2620042c0240c10074414141482441100d0f51b0311160301d114070748541c18200310307480e06090504d8404599000004001d03d500c900c40030344101d881e9241041007005001010600001c7c0c506507c032852100c1802420041d0f000e08082c01282c01452100c10304402000b0030844 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 828120053 1250 828118803 828118813
    0x1060b0d0516110a030f14040f09050705040e010b07020118030303050910060609030f020a0b1209010e0a031d1306151107060807120f09030c051c14091f020d090602 72
    0x2c020328002131403100303c580500300b14071404010f03001102c02451950707440c20320200004000407603545048981c01181e55042e01000305840b1642d0171611481144103030040e12070658014061000c100e4002c0c4040d510505001441c6d00780e07040c10254008056000740c0110b40c2d11020460f40e47c00034820414208000300c0200f00383ca080020140c405038150002800d6078821404500464480c0000407000c0e21200706e0941c0c40701e030489180031308550201c0d00c2440c0e5500746828481b04070000101140c045a068450000800c0c2145c0c000c405e5462041c1040d5001003228040c8003480950301c00e080150a52140c0030220412419019203007003d1800c000495503c140010070689a0206607607402621b10300d401600303040c40020202c090a818030300c0404140c580700c000400c050b08200011012486003081c1c41d00d9422070010030038200c400d08400008216140d00109091100760014034100360024410700da01819240d107061820074441c020000b503480712200b8100140c100c0b03840d4008142601c0145 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 828121303 1250 828120053 828120077
    0x50301031b031205090301090c0306050118020307090b090301020d0c0521060307150903241109030d0e220608060108030406050a0f1103030a1b030e030f030901060b0d0516 75
    0x685034103c01000c01c4008901c1080c0da540079080740408030b821001908031a41c0300d0402400a000038861010700001c00e4020342050189030007640e1113135000e503c88082ca90b150800b1b4255035444050990b40c155400c00c14500503403554030408030700403960b03502d1a8880d410304484618422441c20915405256141088142e5500046601c05d8500c1551444c040d00203045c0d09551001d91504000c00100100710709280703211034400c41c0e000300510080d081c4020341c0740030f088900c0c80c402d5802c200d8054010060701a20b941c0076140c01040c0000191186440749200800300155950030b442c61301d01c480c0c4480d400c200150042082c240075046180245240c6443c2603c040c0080c40f940c040001403040841a085060340501107000404c420942503940c0d80c034000d01c3c0000144550010403c040a154000c100400e200f4400c003c50036425030000c500e007000100301a5400d07080204602d40301c0d9201c0d10040f440c0c0c0000300240054502c140b001003254180320010f904950020700311182009480c030251 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 828122553 1250 828121303 828121313
    0x9010609060501230d02041d1e0402011b080f0a020714061c0e01090602070501020d0c110a26270105160f030c0b0c0403021e091b0c0d050301031b03 65
    0x1100249107106916912a181c178040c0e0040e008a600c042ea018541c01c0e02070400b00c41542d40207100b0300380f00d206088a00310400311001184400e50300a800507008510840c501207054941801d031300d000e40d096600304641c00442507565480082ca000058204110800c00050b84803c0c0600341003040341d401d8240642000c0901311506080070361451280c403240b0405680e0303004c0d40081c542d40d801007000c0d552089541006800307584540054000180342100c0f504460b44a0f042c180d0060414002038030440241e40c40758141040140c50504040c00306c2c0e120b04114900400050035130107000c0a0701140064104442042101c0035514241400420482d24014008102c200721040c3c0d4040300c00118864903040444165620a800900d01e001035020302014000310005001203034821511081994000c0458401c1c284140c0001504880d907107022030003020341019a520496a14100346003042600d024a03850809400b14210120f40008018001d0000b0404202010416a0705a888103440d40e611 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 828123803 1250 828122553 828122597
    0x504020307210207050714130e07050f0111061e07020303070c17090306180705030a120c170d0204030606120f030e06071502030702010e0a0312090804030b09010609060501 75
    0x200d52030341d03801025031040a400e030381c1030362a070076001703030846144030b40b00c4002000700a55000c03014480e64084c4400440540ca90084045008202029006091400d82840041c42c0d10308102e605000c2080e48070303410300c00f0412410344103071559404003c2840c1c80301525040c0b810098215030464000700708102c08142c10820103141c5c15408150a040c140c04041481c085001c2c0601d05640340c00383e10f00b406624000d02c1900c0d070940e50389030181c0c0c042658541c1010b6407081c2449006080c0601e2003002c00100d4001e14007518a2401100c4c1040c201102d0000c1c0403150f031043d4102c80d100c0c1e40c003203020701c1440300ca0b101e41130107000c541071406000b0075030b600c403c82c0c0d00480c048001d0810511345240790080d12404c060742c21143d48400300024008001d03c035040a50000c540c140c00661038a00b040700141c078002090401c440e0180c850100c403071301028004025144d010070660b501e007010040040010034060071140b14440320000010143e01301009075013910507a6018a04001e00744101041c0f200103020 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 828125053 1250 828123803 828123827
    0x304050607030c050a210f05070810050303040311120718050403030506040e06042012010e12040506070f02030321041101050c030a11010603020409030f020c180c1b03030117070504020307 82
    0x6408200454084540007074004d0300c02e101f0601d070620060041158100c407a19025500c001c400401468a54052540d82e000d948005030680158a4803d00a400c1c10700801005454000503160456212030740c008a07603031002a806401e81d507680411003031545c1840303a190020030880742449080da40d0710380c80350384190103007018041e4038426825003880f041490b43e1403030425003e41648226103c400311240244804141600c3c507010708400000396061800c116425604020949400c0c41d08649400112a650f000102d0b014802004800854801003003040c0c001c07013911112000138a800e28241d00e5922554042ea41406414001500c1c44003012003038504403040c901d0043d80c00c83d0100c0f60280580656400650000d113000126410305500c030402080e01a4607030212510385240344180b165024a124a400c01103d82c0b4011503040c1d9802c50003041d404513050100c100090b502c0052600710b0303000303078030101101d100d80301e180800034400c0c004da4006203c12034007107056282022028006401c216 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 828126303 1250 828125053 828125087
    0xc0b1e06061c060f05120f030a12021204061a0904030806040b010e0901060206040b0718150e0a0e0106090806102d0617060d210905060304050607030c050a 68
    0x30402c00c2c039000698042d410002e00102d000e002c00c55850100182d1403025000b858092030000a160140c5100014030b45400c040c2c1c00c0045241030401c031000c032009440c07070414240e0f554003007003840640d00411040398010b80c051880041c1e00400741607015504001504107038000d14051b010031010075004103006a0200c02941c0100c2c5070703011303680100d0f001040c500c0c940740c3c018002e10001c507040340d0006a15114900c83c1e0001040ca440b1441c040d55890b420761614802a858141d05200d89000300d410001e070f1000c9402c155261020420005000c3da4103600326035a225400c01c010071425a204806e04020500c03c4082c01007170034006d00034559810103004c0c200307030002880600e5000c0080000001ea2a5005030910a0b801e034580c14014178910055080c2d003000540d04000ca2100c0c5001030114507055070200728440030900702d800d174120301403039462000140424000001055264140158031961040000d400c031498403090150803688403c1100c1c041040030300c02042d800342c1140c04510344001c00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 828127553 1250 828126303 828126307
    0x60709060809011503140601081f09080d02030414060c0715360209010b0c1b120106060806091e0c03040204090c0905070905150d230103030c0b1e0606 66
    0x111140501514040708504e41c3d003c00b400004d020a10410500d000700020541c0c0b000c1e640d4110079951000f1407110a4040b02071030800c0540e00d041a8001107000c0d10804460341041c038202081c07001c98200300d4041ea11040c43d0111035030918001d01030f07c2e40c4071406698450924105440300401d41101d220f0f40700314107994403a10f000d1440240030000707447c00d030708001c0c000c54110100340814034420040124050742d0183c001040680c2d4103001d03916070f84203810007008140650011905562400750950390403c25049844c1403040003030048001401441e1516803490400d0030500c00c2854004005240c0103c10700c0209443c540e51001040d005600c184142c0c2e12519a03000113802003945040081602d2600300d400103280420750800e5100340825103c111070300d681c0703400384641e07800d20005003000c1c0f80d0100802404000c0355441500450216000c866110fa00c503900e2549000c8280c1040c1c01203036aa0360201e0812241806160b404070201c800b803d09190a400d0113600d0040c003500c494894000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 828128803 1250 828127553 828127561
    0xe0304180f180c090b040209100c0314190206101401080901020906070b041110050a0f020c2110020901020c010813050a0c05040c11060c1b0d0207090606020607090608 73
    0x1640080070311000303844542c001010380f03103032041a04106105414415080c14480481841c151003610940000600110024584042e08503003601000c00100c042c814800007c0c0130303c6600001401911003810405034070007051040180c80d1030300080c441c1010110300c58051100b6174107010900701a0000782051601d80d00c41ca904207002e4041e06d41e00c0d64002e20081403d005100303100070b1082c0100c4c050003140724200d82c07860500104100900c030400214000300520100b141c41101e2842282d2030394410354511a0081001030200c800c00c0300212841000070740c2804c07401c0d0f01841408070f0030701c1c4d404046140c0800e020000c0e494801c1008142d050040007000182e0b00c117105442d060405520605032401062645083d00c4201d4050251600952400140110341e82c010344601e1400c228a00003000148e031545590300c80d69120412203014000d0080341000050741c03c00c4180d0021000d500500015400c02a10341c044504540c014011948030a080c04189034000b061002030f14001d14100001d070766 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 828130053 1250 828128803 828128831
    0x11a0910081c030b0105090109180212040c0330080c0f13080c010e0a090c0c02090f090d031109090a1d03091c08041701090f030c02040e030418 63
    0x180581c0400750902622212652622641d02c031616010810385080008061000044034640180c060850201c1c0d01e5640174815140281040402c1e01d10340e01e009458480024469648484d0559040b900900c007080c050040284e00c00f00c0806144441c10381400c1c1401c801c0500804071081814030060290325000300e00c201034000304542040c091804a6641d40b003420b0b4031800701210320300c40c00c1b03454000c510041415601c1040387c1c005e003510091110104030b04258469005115100200c0180405400b00000580f04d80c81114400d44041703402661a152101666090500c0150300c4001c0618103403d1003904071860041d5080002c0c1a034034102a5030350740c43c00000504c0c075034280f072007104000704074608180d00000c01012410b030240d4440d00f0702021a07080010079501144002c000c9179062201b440440c20000300308108201b0040040b903281e2050702d0750070b100c03a400d10382a8009520b8860b04804d60030706000340c5a000c00008006d41c505450300c0400c84040150341c0034600c405450b0311114544403 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 828131303 1250 828130053 828130081
    0x20901090b0a11010b09070903031103040f0f030b060d02010801030f0c0906090e0712081606140c04060e030d0206011a0d05150316030b010608090319030e0c03011a09 73
    0x100d044031aa40d42c0e03107140026102081c4032910b99269828200c03148034604020007194001c0c450741e20340d60816030841da8192143c03601814121107e22050000054260710b10246400400300424103c2c2a80d0840c02c0c0a564000000c046d2406078591580000050b40d01c018034504480c0c00810400c60804c09140020105071240c2c03240c0701c42404c048010860900c1644013a0303602052204031000c013551a0560070326000d4040e40940249028443da401c07111641d0401c40840e8420680050740c0d614050902d20524011b40310020040700100301406480d0f00800e502c1c0300b43c0001c4005201412030120020355601050003640016071101e03524600021038282982e00070030b0154018056444c04100010241c8454400c80d8481d1041e40c80300f0188111092107802942d4000e038010800c1c1c1e0800e1400d450008010340100b100e880100b0002d980048043c0113808404019a000305002c282c00d05254039000280c0c1e903d610a91410b40d1603410302a0022460748004420f4079039800326980c56030403c0c462 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 828132553 1250 828131303 828131309
    0xe090415090b090d23090d120503040201140315131d0d1b120e0a122a0f05040c1107080d031a030a0f1103011104090605010311030a02090109 62
    0xc50600c141042040700b00480c003485410395808640302e0440d0100c0c116400549440260620040e988644408500250040100c0500036102c1d2070301d040c00e40d030b40d031605a081e8100d4000148001c000d2000319a80b001041c0049020200701078158100410115143e90304607140c5842403c0c91178241035240c0300d81c0c0054001c3da001007510540601c40e204001c0d1510031110012000503000b51000c250410944041c0101980200c403610f107682c480320701580c081007040700f404e074030000d120400204418032490345120144190104030a444080701c200e40d001c2c44208661002400307c080130300003c40f44003e541e080b075400321804a19140304d00402d0381c10240406020001d070080e0300010904443c00145000c1d80b51150b5820070804807a444040c0341640d08a201c907915400c070340c0401005c281c001290480d1180205c4016895040840000382141c1c00c2031000d5482140c00300d01003000401611401c17004100a090500c240c001c0100b00e4041440700808840090394042111b07041c591041c0010009 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 828133803 1250 828132553 828132593
    0x2d120b041401030606050108090312090705090115021b0f040b0604090e06070f02011404020f1801060306080f0d0504120c030602040303050c10090206040623030a0e1b010e0904 77
    0x1400c0c00e0701c035152800d55090100b640ca060801000050f294483c841c0a4818100e0001075400c103000d01b00299840040a020792001e8854140046415a1060509402400010303210805549181806424802a002140d04076652001881e18a458000c01400034240807900015000c00c0d15001504900958008440d2140380c48000d40d50745000040e114055003054070744400386400c0640807403d07038011002c01c24440e001c0ba4040303030060420980c00c10403154001d015602c40b40d848640000c0c1803400740c3c4800c0000f606c40302d0402604a040c4074181d070040218002d00044120100040c205104500c02c0340d01a85113400e0740c0d014003020b03904c040055a8004015952581d885c10010055000102003075818000c2214842c070385191445008400c650140605050900d4070406856960800b9459038080300c40f9540461520380780c10085220389a40076000451a8038100102e240c0703281012024038180c207c0c400000c203a0380007940e0b15241001124000f41c2513030355161603d424034461010f848 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 828135053 1250 828133803 828133811
    0xe03010612050606091b0405011b20120f060711070e040606050f1806060f1204140d18150e0d0605041202150f061908010c2d120b04 58
    0x4100000030590138003540007202e000703c45407a904469810007200e82080601c0d0b0300c04000800c0b803075001d9410a0b441601c090341d062607045107a00c4000141c0c40d256003030020110391050404d42494420007607880c4400000090030842c1541038500c1c2d6a0304040d107108123000f6802110040003104100901c05440c5250402c40fa40c01d05107019006041c00313005851080c450007942c1301071801d20503c03401490160000900041c0c4400b424454564041e42402c0f0386da8034208883c111061582c025a80958842c858101c1d0200c0440300395410f01e80060100070420403116000c4020304074144200003603500c40e0280948081540009465054280c0f40a9400400b8547c29005210030b950145101d14040e216851200d0920081280c40c0d0311410020007810f0007241c0803818107070800724400d51080c0098030079983c80041c070400c07184003002580045102e80d110800300710029070180d40d40c0318080200140c0ca03100b06030440500701100d90740c800c010400c280b02d4110b40482c9002e40000301031800c0940104 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 828136303 1250 828135053 828135089
    0x50c0613020303040f0801020901031a010f0f2f060c030f0c0f04030b13050d181205101416020615010c06290406080705060301170a02031218030610060e030106 70
    0x1802303900202e003401d021916000504102c010014503c0e18501016942c0c0b185e10340a59506445481c0170034442d60801000810000f80b078483c0044008420707290346801503000c00144041840d1a20050810362004018424040c481c00418650340d0401c08204400d611140b8150304000035014542c005400f00d0f035440103002e24103e002501d905850f00810540707207100b05d40d40058038000051404101a400e10020400c4040d0b0350072034a044444c410b01c141c3e21042c00c400c1d407100a440c00c0740c01100024041c030090050361b50b054450001c00c1c1410b800a8800340c5801c0070311840c2000e410ba404e5040c4a0602c60f900d0420501d0761103910540f90403c10b10005070380c0300c103044001580c41040140261306d04000421218800100c0b081201c9004205601c1e503801c06424140f8040c407280c00743c4003445890365040041e80c040c04510f5101907034200040e00c501c10f034101c00ca00c09100e2a03519010f90442c80500071460782000310101940e5560500c0c6403115010300200c0d0042c41560300c4044803000001c054 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 828137553 1250 828136303 828136319
    0x4030b010e1510270f05010c03020f03120709090921020c121f0e0303040311070906030305130b070510150e010e0906100f05220216060606050c0613020303040f 70
    0x2035103d107030f00c04078450b41100d004c10b15200c0c18032203402030120780e07010358100300b1040d84624040b01000703201c3d20640b4089006403000c6842c1d9008264a02099560348041001d155072000d0504002c000895041c0214181a1103044000e10002c0740c0a4088601200c0c00d02d54034003c0101d5140185c000e0400d101ca1840b0084203622043c050702403d02008081c01170300040a0300d4000d0800300d002110241d884d40d00d0350b0b642a02e00740604030500340d42c0d005030840080d01101a100b140e00440c06612069030f14801b04002021805544c0c002c11290a01413200401080000894800344c140d0518002000405041e511520062940c000d1503c6c000400001c00d0540b001c0520900600310102107820b2038a4450a10102d45000d0003861901442c3c96820450dc2c078202c507070b0710005030b00312075000340081021a010060ba41b002191394041f84440104000b0460948201c1004102a04d0020b05000c10300304181d8440703001401c0d4405001e1704038403070029964140304a030b006251048101c0c1150b941c940d81 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 828138803 1250 828137553 828137567
    0x90117090d020615010801180915050901061a120603010b1512060f0105070f060b090915010b03060d02120102043506060d24020d0207021504030b010e1510 68
    0x41c1d030018060800881c0f0340319100e902005074010705848603400f42c0c3c01c0c440d4a01d0b2200c05940300c1c004990b15601c0740d02c040f0303034910940d00d2881480200410039142180a09082d101c1d035600c00308a0300100c03450300010221400035600f4049010101c00034070307118080068094551804c14940c0b0501400c0e0010405450030000c18411449541400d01070384c4000403c0001d0b48002ca0590100b0000c108050001d8591010003070054825003000a030080a6030114080c40d80449004000c0c0d03018a4540696803143c000840c01400c03410340c258518175000d0301081661050780d500a0045240c035003e04241c11080d0140c0d405401c41000a0041d000b00c11490b01c42010071180000042d102585000501da002050092060744050700f1154059178503500c00c2a00c1ca01c4d500210008001251440d130071007428001803000b44010322015840b601d0f031740104030701c1c3c032048429158004820801080084c10990310541100c40c2c141341c2e45507c2e968140e640d9410a00800b01980c030032416040d04400701e4005407 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 828140053 1250 828138803 828138823
    0x270106050a050d030e100c0b010b0909150a050d1425080604020d0f1e1218050a09090c0f03080d0e010e061506040f0306020a0e030a0f060209011709 65
    0x79048454036540d07420b001d045504070802500040d801c0c03030780038290f06040040302c1c402c10743e9240c2034000440c5c50f1196a5103080a810184403c0c0001038654598500180720341d07009011441500300400d802c40028210b03901c24400d960042c81009018018085540c0b03003070071070700124400d072085c2901c41814414440b50180040c140d20300b00050105a500000603030b07512880e03006c1c0840451a40f0f82d02c3e49406a100d501d0200c645001c20007004c882c1035668043d401d04540300c1c1510030354198400c1c502030310f0a80014081c002000001c0e400700b0843c1e442c050b56070304541402a0010b40d0400c01c0c00d010b440246140c103c100c990305440c10020412000900800c00050045400c20014502050030790a2381c001a0040e6299442003001c1440300b00d42d1782d990002200000c05261411341d880002c1c11006c665507000303440250740420820032480d00503007801caa81c0802c0300070300708a900b5607507101c4910565103c0134240940c007080004131a4003c815485503041c030603280842c2031803d400440e580d191111 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 828141303 1250 828140053 828140059
    0x70302090703150b0729040807080f0c010c022406060f04050a230105070f060b010207120c08010e0c10050d020f040305061f0f0603050a240609080607050301090527010605 75
    0x2c0d80791841c6c101d007092040c41000144018204940b140c1e1a01c1c01160800c00c07060310383c80340800808203401d400c5401807150101700800821104020000a41404a140968407901c1c00038183c00d001780d0b010701031681d0310a404640554840304003124a07038640c01540c00c6580c0009400401052241600e4050304050307012840084d03048042d0f4004484a00840d0303801004102c407144c044000500c10b4214035600101841220520707a580e003c05010003429440650300021000300030300c03030f000080c026203280900c280000c280780044400850001088180034108100001c02c40c00d9545116070119002e4040380310380700751120703101c0c10a030b80c0b076080a85134102000071404c07030340c4a414605003c00c001c985482c2650300c2103d00d4440103a000d02310060041c031300503a44100c3d0404060340c680c9441441c0c00a01340481d006424094003410800341604201c50541c070070020007540542c170804403070540312140004940e50322840c0e10300f495002c48183c600c5003d001000c51074884c1105501c00c20440c2c03030407 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 828142553 1250 828141303 828141323
    0x30b0406050c1c0b010201140a0f140c03271501060e091b130e04060605010908160311030a1202010c1b021c0f0b1014040e070302090703150b07 63
    0x6016800c040d12408500c81c0040040704040c03003c1d2000380d80500f1101c003043c000840d00242401000c140d81108503080d1070b05990f01c0a05403c2020544207101c03855007103000000c4a410403c40c0314100e070100806400864507a1921403c03541600034240f4110041e020447c2c0c000084c020400744a08000d014910018a074130840c01803a1403c103801502610102640780b280d0441e82000c0030183d4000c0d00701095545580c0d0b8009258250312125611485c024600080c3d407505200004000c3e900380e84c440c0321207910141d101e20045080d800390104032640200c1d00c40002d001600801c0c14100c0c500300103000c0c0c90301e50081525081e010342042c00c40c8411a516400b0050000070b0604151000b084c001e5007107000b0303520501c0d54802250361020605c1c028076075080c02c1d0043da0b9030031040b038a08a5030120b01c2e440c08a400c205000b5207491054442d0002c0314240666a603005806035145442e00c4041d1144a480010516041c00b90780240348910540c1008008140c0310306c0c510425902040040301c0c0c652203 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 828143803 1250 828142553 828142561
    0x91b04032009090c150a030b030a14250b1303050307030908070b07030512181e120403050c1e0d0302060126101a0d030f120203190e16030b040605 64
    0x1c0401c0c45082c400e8000c014085c1030002a052182c51b801192200040c141d95003552a0b85541c2000040012403145402c034a1082e4600c2c0a24102291600300c640a2030800900d1848501c0c100c0780181522501300c8074588a02040e1080c2650300b2207603102038000c1c040002c03414103250384001104207840500d8100c03016159113282c8880180318184000c0c0004d2070610044001e610040c40380780d000b4105281c1d24030b0910b001080c00c0e05086075404503004040d1800740f00b001007081071207103100080d12402c81a09052842d202e480c0c4940c01094014841c1103030001c0441c004000100c81c02d090080030740721030080d000328940a590380d0b0080c0180e08a0301809980d640d00600ca4091140c070302c00711070000e84001c90316284003401411030b200c91810441c5100400c0c4030b0540f40c4640624400380696030b6401d403a0b8420002500c0c040406125941c030034010020000c002d041ca501e40082045443c00c00142400c170018a00c1c14a40d09601488401c44402000024445070f64041c2d402140038a40410240d2a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 828145053 1250 828143803 828143821
    0x50a09020904110f0f0702240301031e020d080d09060204121106070f0f08090310051f030b1b1314010f0201020a0e0f180702030409060504020702091b04032009 70
    0x284560f20001684101304c45c41050344100c014103456803014065009015105108144503110007607441c01c4128080010400d00c00079145400300e0803048002c44900c4010b50300400c4078040c4c2076a020f0007040002600c1651701d01c065101e003083d1038200b0021500c480d180c440815609086844c283c94010701800426214030f0003400304c902d26a07006015034005401d6680c1c0180c0c8920031081070340c22060034001c0c0c14060310180f2021040c0400d8401c00601e40c5800310701040448a41c813101c41120300268410300c0050b40a50b500c90300070344030300c8030507103102e10801030900e440c800c07000d010380a0404590000703481070001081d80000e42098a4030b00c850080c90390202e00300e011700c4020a0000d19400c0e00030b2071501f001000903501070700181c40721503000c0d025005030b11030360703800d88105005900000d002c02030710003903114210141c0011038042d89072680640000354201e1028000e810051008581051410001001c50f001503500c1180300c034103d1030380643c4c3c000c61603288541c0d44c003030215800010307403560b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 828146303 1250 828145053 828145057
    0x5071101140f0411060c060f100b0903060c131e08010b010503040c05010f0507020319030809010614060a0c0c0311013504020a051905030708010e03190504050a0902090411 75
    0x46592501c0b4a20340e42c039180d40c80881c2603601000d41180c4100850100c0090500c040d521078100c6040c68001801c108038140d201c145103601c40b0720010310034003040d081641e000c109150004d800000c241d0311801ca06060001146407a030007174403008190304400303840b4941ca1900340226280703031008000a8400d40f0054440f4030040b113005211310000207080c8038541c0500c6c001840aa058036015040c00d415502280c54248d01a07012400c07040508400e00405d6070110030b0b1548489a20003e10140741390002c110890040d1104141c4280e07004681c420703c803841502c05260300703600714070311204480d92400c140d08440010229240062801002c0642e1207002c00c02c45880d501034070810b4200304640e0b5050f401320b04000750080380d000030041e0300003500d40d40d811850b09504105000001240b8078010801d0300c0d00090b81d22211b01d59041c103a00d1a100d81000c0306952900c1185c1d14048444580740208880901c5a60440b950000c1412030202d82042654058500300405803010400381c81822214040c038 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 828147553 1250 828146303 828146311
    0xf1921020a0303050309030f0f0702090106021f0b1201060b0c06010f03020109181103010f082a0d0f15050a0e0f070504230c03100603060b0a050a0509040507110114 72
    0x8892000750402c0000d201d0001140d001154070706903030900004400c1000380750700c120501112510085054010741c81d02101c41c5004112500041c103500088542c0f4060b82c04d10041c0c0400c109550707045c1e101e0140c48001150401400c000c00030004561280c0601c8643c1d0032050440340240f0640e400130400700c3d500b0303034044192038050312480100d601e40782c800480d00201c0c400200d400ca1701e4401034400000180060b5000c0d0002400f0070358024105841e89103003842c038181e1240c085082182c00c020400d0341000302503e02c581a9024105e0501c1400d00002401604000a00282d81d501c410310b181a00c07548502d00a070078440b0144000c0070350050040e13071446400e00c285559003209408100500d440d61090050a145c3d0801740603001191814200c146801c60f40e407484141c000007084070b90340c51a0b0411002e401c490404004142c1001030f02c250b103006242e03600c0107004000403031800c40c0d800b070015103603041001041030006140107400180801f50060014a1035801c1c10320003805400c501d50207502c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 828148803 1250 828147553 828147559
    0x3030403091518170a020315060f0d0c0306271a0c0a1719060906030303151206092f0a092a051201030b0412030b0f09060f192102 57
    0x10f010700780514201008103880540a6912658401c0c1006031024420861501c2c00c00c0000b480500e4003409212100c000c400000d407081003207003000000655062004401c0da034000d040040c0390601440200c09841c45090b41c0b12201c00b4104c221410402c4004540440c10b018a140e10003a07140d00201c02d0300350007606180310215030741c816002e8842014489a580c0715561503440388107015041a14000c80d2141d4000141d1540c03908400d009154140c01034100c092000c101c1c0c07102d00c078035012030241c40d04040f08004008640f41d10703140c01030009000300f419118640348019005e80900c1c1440480412406000d030740242480580016043c031a4440e261010f810b01c4010f4181141c01512004070044004510b82401400d10006220282e841c3d803581c0a0340c0305174880d4619003003500348a06003104011442e8101424502c1440701d84d02c1300f00310510300003000ea850700304540319940040c0c001c00d00002d6440c1c22940303140c0e4030300107112088180000c4450000002c06c0d209013182002511103004030000e50 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 828150053 1250 828148803 828148847
    0x2090108060103050c09100e09061206070e010302120108061506090d230d02030d150311041503151a03070b09150d02040b4f0503030304030915 63
    0x9260b5000360041540305078a4030328146004078100014403c10a1018408001a10742c0c05180807414440109600120112541e01a0300354030310305180da0314401020b100170000c0480340000c46034002e0701a42c50043c40c00900500c5582c4403c003d80d501c5808803007000e114200d6500b80a103c7c1000403c441e000c140103841c0074070450182d200ca07185202034162900226121402034546054203002020305560268051603541c029410034809880400a004000e1980c4000c03c0002031124110f0058a00054402107640c03550b522703007a00d20b003406600140c9030b182e00308030324000900c01d0360004207109801545070004000210a2640c1d691f612301403100d9008040110055920b040030351080003465904c0a10f01d455402c81c2641c1c140e0f0410340c0160340c0c0c0034004c144030101e126085d41c00c40c59101a4006a001040c03d9142c00d400e02685101034403444045031240340b81204161450070191002604990ba03034201450300804c0d1004921514035070100311f90303116000300d06c504900c4d17181c800240d840b00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 828151303 1250 828150053 828150061
    0x411090102191203090f0804080109051c0f2d0302030106110c130b2404180e0a020f0303041d1b0403080a0806120d0c0510020412110406120503090307060302090108 72
    0x80c0040c0700130704c0c040d200c07000146c1c00040090f82d104000c001a160ba58000f05840740503180040c03600e0341c007005042e140d00954042800055001000602c0a403c80c81d10201e044200b10080718940503035588003c10380d44064020560903095001141201c040d44d543c049022502e8100c25100e549401603554003040900c0d0740c1c002c0c021290422801034000504041d0301c1046800b0703041d0079400196034000547e1011404010103c0c420030039081e44000c840c0103012000c0c1c2c1044094a6401385640288140c0458040c4251030303d04006482c0a0440d02842d50b41d03405200c1002c0518140c1264422140d0403507001503514040f0203002d8802303c0390300184042c01c4c404c10003000c1d9240c2400400c0703260402100e0400b11080c030002c11000003e10019169803d41d6401e03030410a050455090502a100340100000c100b95200c1c400d4213240780750450400840c401c40301d80003601404042d440f40e211a900459003106209002c4000d0400707003421012101010b40c4c030801070f8160f000381c40c0940d001c121884001 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 828152553 1250 828151303 828151307
    0x303040b040206040e1003110105070f14102406020d140c010b040c031b0f02210f03070906020f0d050304060b03120f3001150e04110901021912 63
    0xd41d4101e44018a00b506198035000c01d80c48480d41111540950040502c00700103101e82069003654103482842d00515200311919050031468100314010504000d01e51400c0c0210018804407645c05443c00c1d09002d01c1a8220002014001d40000351104241c03168001810030300009858074050f03080d07254001031426650103000c482c0c0180d4484081c0d952200403017503070b5a880d881050361b174501075203001884200c00b4441040115070a00f070380381841400c1c030400c40800d0b00040e00d2403080320170071130b2008280306003044644e0900850300383c01c54820020090203038180d00b140d02ca8054807500c3c0d0032901024411300d100b9a44a414003c51004200c0800115001c281c5603003040f01c803141e000e012960103152120061190b5031190300505403e00c0c0100f0400620700410079046140181c05030484001844c12458a030785c4c03c070600c1441b1585062140b400d40f1203006000b50280801d0040c420000c11105100e41e880d10750110b20300e28014001c0f0045404200599102c0e4200b2a402c50b242117400e0448943c2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 828153803 1250 828152553 828152573
    0x17060d0309181104060903110906060306060703030207050a0503121e06040b0f090114040e0a0203030906090a0f0f0e090a0c030210030207080c03070606050105160b13060218090a0c02030304 83
    0x700986030744034408204041c40d400f00401c0101465668139540c01d00d541000403001d464861313841d11982500040c0140c6070303159000d0b20b030020300884007590740d0301e42072509a00034424024018520b000309000342c014824003001a10786100b80b010580c0803036070781208568650303107144507410103482c030b07000800c00c0350909501c400076407c409403202442200110014280d00001d07845181d42440f15840c04041d414203016200d02500030b0001405840040e9001035200e008050003203000d01c40108680c07031280c4c1c9262091009002e040c40c2e013102580c6454004868800d540500f11104c5104000700b20051000183c062019070400b181c43d000d83e0540c0c0c03c01401410f080300344000c00d41c0a0000c00701003801c02e0024032084209000841e55007066140071b20603100540d10050601005000350300f89001c40c0e012450440c2d0303001d40c40045542d520305210349480c80c032180240079140301080f00444240200c03c0101082c0085030281081d1340c80b206c0780703011307500c04845a600503001400407900040f90480 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 828155053 1250 828153803 828153839
    0x6061312150f050402040b06090303040e13140a05010515010519140f090f04060b030c031905040803040b010e0601090e0c0403051606171e0910020a17060d0309 70
    0x40c00141002450040344150382c40e46604020855440041c0011890244168801001c040d01c43ca42005894000682ca038008e620851124054081c00204e080d60035035454660746602000b201840500340c00d5403550303100f0b46101100d0640c07a081c04203a0054000c2c8524000d040c1c1650740a14080316050231002d24840303861038005202100b10f84500400141014002c01c1c0d80511a2580724841001082903851020301424011490044188041c8a074101200d601c03e60307010395241d99840d0054140c518200411501e03c0c2c4c180f411007030104002c80b010045000d64016010480c141e40c07901c0c00c81842101c103451090118510020412141c06000e21480d8032440480940e410681c1d25202c0b0390410881410940f103040f101241400300ca6049000070041581560b605a501c1c5000d05028841c002031498035681d02110400041074140100070100503081e00400664035001c1108015012655455001121801c0e03480054a5400c010401c1c103007480c2c042e615400481d02c1e00414903100d0040c0030f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 828156303 1250 828155053 828155063
    0x60e0d1803080307030b0a091d1605090c16020303030415050a0506030d1215060908070f0303020a151805010203010f12020a140112060e010501030e0312040803220503090906061312 79
    0x850005640705007440307800d54110840c004c1c00c44812742d4440403400c02824017294480d00b10442014800d40d00d4a01105a014409445907661203d25000381d580302c801c5854001e43c1484000704002c10443c00b0224078250031050641848140c40790a100b0f81952070868841d9055400010600080da2042e00410642da414140006104881d1000220304030380941040340803414155041100071400c0108100801d80c01c01d90610a5081d550000d454503112640600341d15114164107082034455841503111555558022510608030314095010350803d203d40707000d440401500181222511280e41a12079000304500300c0b29003030410200c04210b01e580b4160402c20a1681720220700d10502c142e401505001d80d00b10030342e40c03600c800101a101803101c400700542040c41034860041006104a40203680150025144d40e5440c400e0081d03044080034880440903501c030f8401c1888408001403c2c01c40c6d00b95285d1039030340c3e1040207001540c4504141c0860a0a2440c0204218142d091000072140e11032 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 828157553 1250 828156303 828156319
    0x10c030c1b2c041b08190c0e10050402030415330308090d1707031e0c051c12060906051918020d020d05240910050909010207060e0d1803080307030b 65
    0x94500145858400314a813904003c986d84c01c4403e000304001c540004052100039440c00380342000070251110582d20a10f03004075004030100301041080760146140034000d02c1c04010800394146444225000e40c1202c081c03854000c51300c0d00d000c0c040b280c107440940c0e401c001c42c1860b004082e4280a0020910502035400c0b0103500d003445240a201e030014045103000703940c0c0070949840c401101c0c80d0209640000418130511491902c0002c4000c60303d03105460f8001021141410042e000380c4071005c5080040580700c1c90014007160003107441e030150060710b00a40e5140c074041012081500c42e04d000d4000c40c440c0c0d40e603404880d004098640c0040100801c224009800c0025000d95002528001d50340720540b1078542c0d854518682d284000d0f2514503804451b03030b000500b086816401c4203805070040c02d01803031880c8009540340d0b809404070b51115074442e03400c12240310313080036658941e8440e0b214000010303c640134038409052408014826a5009000e6500e182c44254040d40103122910b1403982014a0b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 828158803 1250 828157553 828157559
    0x11407110a0b040905010608010e0f10080f030a021903021203130f0b0610020c21030c0703080a200606090a0f0c091404140402010c030c1b2c041b 64
    0x421106034014248040d0694540381803400721310036154160440d108000382040104881e4074060084c80e000420000b004409450b01d00c02140e85c2051504560380e94418010007401e030300e000100428043c1c055900783c0b58011503210380350314004a1900050300692004144401410b00d2200441e08104043e100c860b00f24240d65603160051080181074500801c0181003204900f41400d1052007140948060624071842400060440e0301c14400d68002c00c1400c000f05503030f404200100c5820b054408104c8000396500d213880c01d13070740d40b01010b214001986003000c500a14607003004644906042d4000d0a11a0f550b00c040c4a020701000f011104180d4841c091500a5500c82c46079034040315080d5a003540c128105a07240da14461107a10b40d0340100d2400f64005024004454801d822070340c24a00300c08408034500301115004200038000c0c0842c608a01c1008103080c00e0004441140c2440b0581444803131010301e1024104140710f0015110040d24000800160008900e000503480601c656060103407 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 828160053 1250 828158803 828158809
    0xa141509072109030e0103150e07051213020f0109060203031605070212060a1a09130f0b0f09060f250504091a150313030507050c120d140901140711 65
    0xc0c805001c1c0d42c002e940b01640028550700c8143e07020110310a08003400341040d012030782c02104d0b085218000c032688418010450f0144501c040320380b25445003c3c2a00182000c103114641c10f0702c0002c04a01c02d06050b441c054155016400c9042282d90a0300a1410340e51b866071500300c50301340c2007811010080d0400103000142d03a2004030ba8481c5910300021304061502c943d0030f00c11140008460254040042900a00d07540c0307074100301c0d5214249030120700e2248147d140112241d102d00740c0091283e5a084100308e4181c0411711881d21600303100084410913182d503c1400c201c244d00751402e00c1100000250216001200d14080e89500454039055242607030b5404c0b08000c40340080403222240031034200e40206480c0401e150040310b0701c0da409080c0340d410701031500300320400c0f00b80f401000d12001081c031506019044c0008001c21602a0642c24000040242c0e2526803030260b40d03240108265a03003050180a144041d9242904e040c0c40702e0348a40510882c80c1100d4005500403948065191402d8405072 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 828161303 1250 828160053 828160097
    0x40201030b1f030510080c060c010b0a17071509120c08010e0f0c03011a090c04030c0e01181b0509030a0c0902040303110c06071403070b0702060a14150907 68
    0x2801e584540445800c1042d0000c041e1840a0000c0403107400448003405030f40030100b400342503e0402c83d02c00380d80708019a038444c00b4241d801034855000e40c18440006900180d1840e184070f490302142aa02030700d4403585410b00c1c40071840603034400200072403001d010790300c4020f00c0d5a11280c040c4403222001039440d071001d4291820000803001a07080320090900171001002211b2004204038005e0010407840941d40c800641204196845900710501140c000b41a0100321740c080c5400c81c5c2c907041b8054030740400d603900050138452540d010381c2900440001c00000d114010160445501c8480383e844c0300c16045403a5003104071641d5050280f4400100081c008044580040c408048056126882c0d800c014001d2440d1441e550b42a40080d24982040e5554204450f03400c0e5202d84d440303104c101802c180b14130718001c090004040c50150014400d00d50340020b0000e01c6844d81440900c035a150a1010100d07104003a1340e10740c600d00000403c0081851b11400352030b070204843c54540034258071060880201 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 828162553 1250 828161303 828161329
    0x309050109080d060b0f2a010c020102180d0f0303020f0c07140111070e0109050a0b04020a090f12031d01050c061302010f0f0807110f0a03120b04050903070803040201030b 75
    0x103202e0014400709409468014600144000103440b41895600d4190054a11038150143c503200c0d205070b03d80c00301e5650001a91010460760000700200d4034482400b0b4001c2d8000b081c44104095620105400343c034105805015565011403001e0001003540d80941c040d4001c03078640f0b00030440074420813403845020040e03c8010940c3c81000c0c103610082070000b40c00030303201c02042c80302900250413310444c0c0d000c40352581143c08903100001c40742e881d070309030100500400043c2ca511a00001d03600829542c0280007000790395000320329800d05035642050010002c8400d000402107450031101002000401a46c5170031400181002458190107114035400c0031402c82c0c42c86000d072224401d801c207650f400b003800c81e545241410304c400442000341c0d0103029440f00400d203404102c00340d107a010b003046007440180100c001040880d030300a206884c1c05007034440c00304000d00101e490039001e00a685014011a400b031500540a10314104894070386480e140d00080090341410743b0354280000980390400501c0003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 828163803 1250 828162553 828162563
    0x201031e0e070306050c0c19050c060a05031504020c070b0708070804060903031d09010e040c1701060305010b0306070c021201061a0c010c02120406051b0102221e14010309050109 78
    0x8043c3c11890507070304581020340400c101c11428080000d25100005801460032a50490b8090300c10461030028644071207c0315075900981d01141d81180b40d500040654001c40c91442207008500c404410f00089000b0796030048401e13440fa4104000a404090040120a00a030003c41c83c02700309444d4042691301c11303071103600040c09c0a1410814581e1115612080c0c084800b100b041c8104240c001500307889060007100362520040703011508100041840500070119900c068170b240d01c09181e000d008004510090b1801e500b00f1075a0807692401041461041e40c1588900c141c0401907000c0c48110303014626a42d00544d81c030407010811340041d121100c402200c0700d51231036498014a44a50a4035a003550f40820b40d448643d144c07207900013000a0318251015484d00a0300c1d2860304007007160004c15881034410030351000618040001818258503150941108050031003a541c404071403840c20342604240b0f2403403150710140071010711140365500c0d042d030515003c522035001d42c0b1a1801c5851903202210 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 828165053 1250 828163803 828163813
    0x14060c310605041d01080606090702010b04091b0609081c02101b110a030c021005090a0b03010f080f0c211504142d0a1407140a0605070201031e0e 64
    0x40c4c1d1014448400d0940c0c290628000e155152405680e80c0e548060f0010384108131000010355038178401d50200152900007041031141c0f00d560704044648502040f4004814180a1404582c3c580195012001c54258400411a1960325020ba82e4407405100c1003d0441c05001c000e0098400580182200310080f2503031100102e03240c10000e4001400d0501e5035400ba001540d05e01c01080c0c014032150b070300c1a010340d1940807007106104100c0e064841c0c00905580041910b9012aa019500c030245043e100b400c0f904c44405629022229614441241803100d00da02030341000016041515141e01c41078001e04a20408000d6040c1d02c030306100c094000c015400e00c00707070100130902001442c403d03228085c079005000260b0500100c3c1950345400c2007800900c0050b20030b000359038401008803840240c6c00c040b510000001c00403000d81c40315014811906c0303034154800e0824032444c00c020014200e4500e600c9040c0380612035401036020303191b509100600e1040c171070000f82c400c052500600000e001c003c40901 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 828166303 1250 828165053 828165059
    0x90f27070810061d04050601210204170730080d0e01060e01060e09041a160806030c0a030b0405010b090a0603020111150c0c0708030a090314060c31060504 68
    0xb0004206540080f040290211040d40200000c4102c011407002c103540205440d41ca1100503104d1158558011400e0720183d0100926030007940d0140c4140d5800d001040310020070045c0c62a0759904501482c400300b040003045590500603d00014415000c40300c7d8120415501e0301c84103455000444084101c50703d880140c03440510a01c9202e003c1c0035130503c40d001d25410b02c0c000802c8034030700320001d500030b0381a80c0100381070095049150500300305039200c20650740f8000005610044003015124007142403040498524034011520b40c2900341c3c05841181910300e1929180c07118800900705580a560721803011015484508809102e0300d001e40c0c01140461840c400140103940000a82032540c0146d2a240799420b5295440c1e50416000b010403038441e1035004074135041a0382a030013180188400601141420b400c005400212030040071986c6c2c00c501c8076038000b5101d0408807146242310204000b202003500b14100c50300141c400320040c1c80018100b08200e0408a074494000c040401c034049820 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 828167553 1250 828166303 828166321
    0xc0703020f100c0e04151809020a1514040e040b070509120c01112b14030a2a210e0304030516080f0d0e1c0c09050705090f270708 57
    0x2500700354200385c03010004139852007012200791400380503217401d1151140000120749040d40040d00402d4004040c0c0f4039079643c540c42c808584021082c05408242059a00c0000d07400d80810317a000c80350780c20301020303980e46c40f542c07204a0108000d1841d000d0200900425203103850b505e048046548405005144600320207001400240007645100e0303981d4050001910210011444840346400c4858100c0c00110081c2098403071482058400c1d03401640481000b101e031242d9007140004502245001401c2516001201518203100c030900340450384842c0c03050550103c0c0701c208403ca44008000299105512580c1c40c01d55005030310a070307106c2c0d01c003a00c12601908032901820040410710000e012140d41e4002207915001401c03104800c0c000d95140048844c1c81d60000e060720741075180c940300c80c00d41c9a407401101c0c02405001d003051092602e4006000c43e4018011501c100d01c005280341681140041000018400307006004a4681c1d11484122901c02c04c0c10600d000700c00d181c4070351000e80781440803 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 828168803 1250 828167553 828167567
    0x70b0f010302030f0a21110d02071d06010f080603010b040c26010807270501030503130929040902040e06070f170a02031305030a0e180108060c0703020f100c 69
    0xf10945400202c8800000b8101d448090505c89001001100c4e01101d11b9081c0c0e442103171b0145134005401202407600d0b1a81d0302040907008e80e40d0064080000e126010b444030107049007103803000d000c124001c0c0c40c403c0c0036020b414003503841040213001107041c0130364001017401c1d214403c50040c04910100036010342540801581034065010300d8081c030701c40d0700d008003950f55011a4410610307801c0300080c4107908502c48050300ca890011000c401d0000756503e29207545c1d07030341c0644094040031710b20784000300b8109500d01032080200b08616148208424803129000c402c1154004503a01c190386001c1100142c41d10b000b07900d2410001d102508081c40c1c0081d002d07084111800b00c642c01c02940520140040c50100c2c542a0464510b020041e200c2d1364080100300000c409101c003414034800822135042c139a038000700980c0440025503600000c404440c0e003542d9094000e0103100c80e95089074000038107a5001c0e00152003c28040d2046802c010301c50143c3c1400e1146682d01d0110180d1036030102600b075070700004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 828170053 1250 828168803 828168823
    0x412180b0a0f080a200705073c0f050111030d0f0b09010803090904030302070609170a0210051b03040c17010b09090c030604060b0f0405011d060604121502070b0f01030203 75
    0x900914202c0303d0005090700b00b140703101500d6100494090207100d03040051601800c0e03070003a80c00030302e0b5032608140aa042e000b1036581c0c5240c5040343d50398041089c80100d400f103400020640942c00d04101c0150b9103c4020329022445d03100c01d01c11401000340c03d0040703901c9007420314000202d0603651014001c031004142c0003103800d50700c10040301e04d203915510b004a0b405501440e00503110141858200090074513000050540310409800862403204200100000b0756542c01f01d07504d2154001400007552422030f055502e2240c41001c10010020810040d6449849901951a26502c5090985c011015007a4241c61a0354030703d000c10150424003001070b00040f92400400d5601301c0000080d50702c03c40104000d20103a00d0301030490700ad8444205101201d24004c200f48829a110f0403d4054415405840b01000382d01002213480d50628004490a0b42d250040c0e090b000c07100390705d45030483c04480c914407000c554204410b0f0045060010214000c0022120907040c07549540100762034180c41007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 828171303 1250 828170053 828170071
    0x110907030e2b1b0602070206210a0b030a020306061509091008150c1c1b0503100605030c03070e0a09020c010f0614180402060c0f0a050607080412180b0a0f08 69
    0x10a6040d000d0544003c2e0420b0384d80050301581da4516803020030281e01a410b1803800500c50848039805007501c1d94940c500c00c40403c4420492030b010b4404041e55540001006034150700160007040700c0342001011a5141e104100049103000d18120115460b060100c40381101407103003000500c60140c1c01d1117030f1003400c07203803152410950500b080300600c244100b5450415081080100f156802120303005032440002031005c04010720300e1104013804a5000700d03000c0e810000c200c000031520740c1c02001075034020303030360340000b1801c40d81c42c42800d540300f5504801256001820080001c0d23012104d0008100b40343c039036030000c1208003120340300740240c41c4540c02c8180188001d45660324191180d58900300419104502d0204989550021038818414540710841d180901c00c517600b24008001000c820052003071003200c4040e51800f00450f02d825040d1002002d0b8004003950024141c400c00c0001c40d14007202450105680e620704c40c100103584404c901501103180800003441071038111600035407000d402 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 828172553 1250 828171303 828171317
    0x7051b250602010c020d080c0a03060902030a0e06010807120f0c030b0a0624020d1d1201050601020d0309080304030f020f0d0206060a06090b030a05040f14071809110907030e2b 77
    0xc25401f4240700001086000340030360109446640c04e101b604140000c0000810855a0b800e060101c04054409000c980b04140b20391000051400c900103040011a4448403100001780038941d1110460904540c081e6030803001c46501002090b024855a4007401000b500058501d03c0e0007040440714500050710241090550003080859402090500b0480d406180c07400140240850031040f11074134002803900903403906404405003c2c158000380c09010240c080302c15010000c4802c4049d00c0f400f02c030040c041d07a818008540064029203050351640b001d4010745a0010301c5404061419541405803030040c0d101d6003d114080c2001d5403054041c1c84540b0340800c615091803c034001510000e020414003541d01d00c001030500c08008102e004040d8007103540b601303440307810900d039941e408140211000038084034013070a0803100324410401129440342111440305100020405034400081803c0181915601414607955091151005480d0b02e00000a171640e5441300e0021543e00410701d0500340210 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 828173803 1250 828172553 828172573
    0xb091b011701060809010e0a1101031103100308030a0605190611160b030a09020a06020a020108151f030209040e010e0c0d08030114030a06050a09060506060307051b250602010c02 78
    0x71810505480490030051300325200c01e2580c0740103040c599985030741400742d440b480040103050740880403040800d80c0c040c4901008080f184a1611060b200121003401c200c10030400196181d01a552003002803c0015105540e0004580c01000d4509080c00303041c0302c08000d000c4586c0001ca4050303480034000c003c05800d07a0b1001b841c0d0540d840c5000f60401e2202c04000207034018125040020100e0740030b0500c006071070703943d08080d5803040210800c0f03010076070090014108503035000001e00c079484020300c942d44048a50004134904040110b5160400d42c0821041c107103070300c90380230703a044400542d000018241d0000020702d0500110010303a034800c1400c808080d010488030415030f41035034103951103610b900c4621030000e89419050040184080d041108101381001c0070b40c40071408500940c01840140c4d42c40d0100b05c042e1104a8490011030070911031400300390007104114401c032410404440da2010036820f03084040703800c0140740141182082040c0440c59080c042d03400f580255000070202105 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 828175053 1250 828173803 828173837
    0x702070b0414311d2508120304062d1e06120b0a0207050a021512101404090201052704111b01200703021c030606090b13030b090a0b091b01 61
    0x403100c1144a0b184000403204815000081e6600010680c2e0012504c907100303074015847c00d40d0800c03501940c582e46494101003074010440c603840104201100e4180f45d090040720741c03a004020003008064078241c0520641034041a07445010f000e0b00d00600d440320340f04001e18090001c0741d4020010000d043c01409003034005070001403040451a0304669130320a840300d036107806c80341d40a071008001c4101201414084045038103c4003906660314507110010328074030034060106545a000000b800190108035040c01d40030581c280500e40c02078040d00d000e4050300100020b09603440281104490003000072000d120201c1807074035440781e0380903400a1155000400b8212054884120860f035842000141c01e42094420300c4082414005190a007a80c404403080050051840340100c034080380b44000040340204000083c0d4030328140007403811186504555402004a00143c6080703580d1042c107035060005000c0c0c6503c1841807000f24010030110307400c50b001540d40301d816001030707051219131624070796820 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 828176303 1250 828175053 828175063
    0xe0c0a0e01030212120a09032d0b072102090913150209040e06040525030b06040c03060512030a090f05010c14190312050702070b0414311d 61
    0x3a40441e40c2d02000c4038100b040302c0c1800000b10104485c0c040001d046040940c001c051802503c0c0181c0311350a00943c21505802e0a0104446141d0149144040007000640da216038a5100b58640360041030b03034101c1119644030b10801c901440b011a0003203000c0300c2d00d0800c041c1c41984406100364514184025403660124002c80d10600c82d10143c0020315817600d0380b51034200b9580008503a04849440c50141080e6441c1c980e03845090040d2107154200c922288a52601882941c1e08441401941d40700c0c0300401004002000d5244e05040e1103100002d41691444c0c100c0a60070829406036654540390f40e0010540721164100e04841c8030706807000d00069078814401240168080700c251356541d505207600f440c1840310b500395081e50700c481c44141e0405a10a0304141454006030b0b0a008034ac807282010398503100701e07000b1088003c0041c441084520b43c1140a140d486102034198402081031200b102c0000390034480d03403003e0218140d001da440c1e0045120304098540b400e41c070301d08603105458100c0d40721 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 828177553 1250 828176303 828176309
    0x3061104061b0303020708070f0203120c07330503010e010621020d0b06030705120c16230646110c03040305010506030d081e04050c0a03060e0c0a0e01 66
    0x202c10807040c0042018040d034100c445154006000c80c0c0c40301414940745041c0d0300090070881c0030740070700400215108141d4080d6892205444080d1000c14280300103025040340401d120200c040d020760001d601340c4180d1180c428180340e1780d91410364941c14007c6c540003009041c2e0041040001d5070304811280e0910300300007034100e0a030030350159890300c0c068408c070050700c140c082c4160311080010030f10020940020040000d03041c1d11015110560b20307214541041e000707100402d40e612000804540c00101d0101071400260141c9180003c14811070210f649007807022181d41107540450301da403103054500c01100b00d100c1169227281520b41440c925640390002c481d038042c0302c0d00b561215410700ca689240003d8812403200c81c001c4940700c3d036032410010f01030003040d11801d029010b29005880110300c40c4100c540700e40d14490002205260f9841174800282c4014801d40752401901e806504503580c00320000001c501542d804601c101da040220750030310740c04810030352240703041000403c80112400300b0350b411 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 828178803 1250 828177553 828177587
    0x3070c080328120c080a060902030c0f1b030c060f0603011e05060109030614041a1005010c0c030209070801082e1d1204031a0c1209011808040306110406 67
    0x510b0816507500c01003a030b42886603410920000b96441d0721803030040c85030710100c8040c8000c584e00c00c04442203200550310465101c0041007042c880f407806600401194500c001c0340300380c08002804040c01c5400c070080f00c0000360004018010750300340305202d04c1c2d040394045008100440368000120034640d9822111240c4ca42c90301c0004038240c0c040c5140740c0085070494010b002c40c5010300c643d032840c1c1e6003c807803c540502644481c5008003490111031445145d0b10b1011811943c20140103403055080e004040710045014a030203c016210201341034000c0040d030302c8015480d4141a0060700f800d0178055003205450f2030015081074501000c100d10141015007900040200178000c0300105c444103030000100c40e100d4042c075480345010200003402124011050750761a06ca919100d24031031101642d0031104540c00380401c0320002d400fa13240c40d801c032402d0000000c010158011501c44e030041c402d825140d44a000c1410400e010103400382c1c5610303458941c603082c5428106400038040d503109100c10f040c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 828180053 1250 828178803 828178867
    0x7090203160305180a030801051003060e010b090a090207030c0501050606130b130306020406050414010801030b0601120e0106090b030613050d05030907090f02090112200a0e090903070c0803 83
    0x15410444c01149015140c04000c0d40d2819459040180400c45e080c400e03240905500d4040101e030b00d1207403168000340c942c0000d010b10603900e05286a074442d04035003544ca51119020500158211030361008098081c4251900e045041d0b19090103400c548008040500440c0100001600b0b0b805a03c0a00b003510000140d80c0d480d03003a01075200410103c1d5800040030644005000f0912540081c0a0030032908100c2c4c0e503c034050180001110302050a106c0280b4480da00c1000c60a50341c064000e4a1262490100000d040c80742e1110329402d41700c0c141d00002050f80e640c151311095081c10b020751584082201826242c0e0b010315078400b5a16031a01222904002d004404200b4084040c07141d6001000d820200b0311500d800c0304100703c02503101e28043c07808103501400c6021182e500e80100c940030014080f042c0b4000011454a15055000c0540e00e0208419041411055590803941c24040d40202d0010b503201c6003c1d2514110701d000320381100c0c103940c1c0b041c400180c02000f154050f4010b1103408148607 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 828181303 1250 828180053 828180061
    0x1050310020a05070803010f17070b0d02030a2a0e03060906040201050304080d0903210e07151701030c0e0f400f03031104030812040309120c05010207090203160305 72
    0x8070f40303000310000100419400000002c4038402800018242c1d130301d00c82c1c030801c4115114442c0360303208068440d003180b545040c081c0150240e581d0f03018660103084407401094a204c581c15080c4414481ca52001081c55074a40d1191866404802c980b24400c059004202c03904110070000d642e2140100000e0401000000103410000d140e003d8420070161048140301c240d95900d40034049030184229024240d140c0120000540d405001300791840b072183d4090243e40307003440c44d8803a10b19810ba41d00010302c42840359001d0311940b81150b041c004c5000d002000c02039401d000c110540382c135011b4002a042d0300c1d04801d1203d40c10705040300d03074031551485a08802c110902014010104103840c00110312004000d608414082103540c0c0309942442030390100300302c0e07401c480300c21258003c0740000341141030705010082c190100c0c49100c98015020782000d45050b40e5406100000d05030391003088410707030290201000156010444e0801802c10b1400079419850104001250014018801410191144086 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 828182553 1250 828181303 828181307
    0x50f0f101127030703050105150f180403090807060c1502030105060d050a060e04080901080f010b090904170c2103150d212304270b0d030c061401050310020a 69
    0x41c07408400502a00c08440e80c5c0d081050082208540c006085d03520754038003010618180c485031690310001010000c000e94100769080380050000c0003282800120340002c1044070003040f19000528096030340c0080444a4034110b400031003d007488603800c600500040c0074954400040c0c608816420000080caa41e5802c50a0088c0030b4070744c4030200d07040104041c08103100c0d415000b05400c41d4282c9584005895a80429049810034800d18041400600204841d4506180c180390080e005003808000391302c15031011540e680c00100310b06065403003221140305003a812801d0b0f400e02600920750902310314004100c50400c0704a80300152256609a4400d4100040343c1f204480c481c450042d1121414207500340900f84c2103001c0c202615800b030034448080780e00d40d684221019680c0080002c1c81502e101190540d561000c14640d00e110f03611040e540c05180c0f81d404e800b00e1607900076070301d520a001e520f061420880700718041c0322090321040001844036480c00109100d140511141c0103a86410100003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 828183803 1250 828182553 828182617
    0x402190503130606030b0403031b08012102100206060909010216080c01140a0203010f08010e0a0825030f080a0b030a0210211a1903061503050f0f1011 66
    0x5251900c0c1c84c0c00803050254a07580039209520a427410444000d008102890005208810710f00042c0d0900c014001120301200542d14200c0e0204180c50341c80865000441c604001c500d0140140c1c400d000300322640c5056488140c01c01c3c1c60348000c5291640c1c00c003c1100b004c0030b0003c041c01d0100005000100d461007503120340d00e500d0815106c0380d40c50130143d2600c0c01a500178400c200e0700f190641c1c00421001070601c03d9072074003002c01e402048480c01c0b80d0b43e400ca841e0080f00700c1501012503c081e910001c0c1c065501d4242e110b110b80d484c0d980f0200c010001174504c10000c0c003529845490070392505441d48000615001050301107426901000440c00101c030482d800350010b078505003400c980005902240d0300104600382820394081c85240d280d20510020b02402d04801d80c2035001c4800800100328903601860003800c46e03034082e1840648030b465151030048485580403c503809800e0b8450400030500100743d0500c6023020900c01d404e0192007411713243c014842c5011250f10315404002c0c680542800e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 828185053 1250 828183803 828183841
    0x270b070c15090215160f0f050d0c0c0e27011503141513060207020109030f150b0303091005030c0d060303020a0516050a06050c0a08190e0402190503 65
    0x100c1001c40d0440010078802810040c2d000b01d0090002c00141441c6440c00740030398050104041020780403102c80c0c2c0b543c000c010a45081a1801c41344d1414200109200780304942d4603858645030022010880d190000c111842e40c0e04c0030703490707140ca2800e20007044428040301030b03140c5204100c03805039502c01100038010800700c0009110540a080000100181d1540880d00007000c00309544a010580300e604952001c100d564912964603515444002400c90340500761060040c076191007000e40343d5964502c1c0b01c0080c50107440b2074800d444400d106811380e00800790044002d070301450804040340f0208900302c1101c0035a005101c404800104e8102c0100156507400c4c0300c00c0c0742480f940d592030401035201d05441605a442d17004c0e41480c0c3c0c4030188848104401c952000d01048071141ca080c000701c81d250003840411601e07004074500000850881c201404000202d030500e02020b1003d807201814030b11703040d103a0340d005500500c01c00641260205a0a400e46260f0030441e589590703000c40c1c0d6640c410130320 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 828186303 1250 828185053 828185063
    0x1011070905070f110d0801051c122c03060a0906110301061e0504030305090112021b0c1c050c040903021906050f060103140412050903031c270b070c 65
    0xc0200000b259020f00c01c42c04203c0c06843d810224224800c0b21900c1d5103c1c80440d07408101100e004000c80c2c20035a94800429519181038004403281e82d80b040310341e40f064000800012502d2403002070f80e014640d0000284100c2d000d45003000e041c00b1011a842c2c80005000000c0942d45000c920300780845600a0840d04038106a119903c1d80c40340c5003c0c0040410040310258806e1201e02400c110b0b025004a13002c1d02c1c1c264036031a040410500044070745585105070b00000d00e800340903441c1d24011040c0c08101c280700042c00b42c884480c1c004103020411036010b080200080c08017920202088001c105c03101c00d40c0090340d020541c00003038141685861480340d10504441e07214010340e0b00b4042e050340007900035949032121018030b484440044098a00c6403c1c00d109182c0d8107000700700011009200c00c3c1e4106841d051580c10704080000007402d5801015000304030510008007007c11490f541300d0252030740c900070080074542d402180201e00c01d4007101c000400002c80c400101c3c15143c002c0c0c0c02110420303404 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 828187553 1250 828186303 828186311
    0x4020d0509060105030d0e04020a090902070c05030c010c08030109020c0a230c0a03033e0106050306180706050d1506031d0714150d020f04030b130210110709 69
    0x22801220042000312807009960140340700119462502040ca4500d5021960b00c456140c6058004c0100030b511030140403052044a100005400c03c160001c1d1400d203015030300185450f032508090508041c2042c00c204d0412502600340303400038280d601580c0c151240c0c102e00503141c600e800d00e4603244c5a090400500310960990039051503506600000320b201242d40242c4548540041c280724100c070580c0402404284c010400100020307400c46510070030040303800307050410545803085d80380514901d0000d42e9603944500c802d211a04080281680100d0074148034010100ca01880030b4840717285000301c4003048000600300b80020550b0304000700120f00142c0c1007165940d1910041c00600d04002c4150155051001c001003400c030106400e41141c43c200c040401250182040085295801a600c10b60510030b0060303071000396052015058241c400845983c1d600d0460a1040342080020034640d000d80c00000484010b071035444c400c040d000c0c0903040c80e8940320282441c5905112a64115559080c58 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 828188803 1250 828187553 828187567
    0xe0a0c0e271524030606060910030b060a020a03020c060408070312020307150c170c0a0c14070f0807140105180418080a0f08130b1f0803070201090e06030c09150402 72
    0x14041c01840345000e00f40040344a90074405058031003104455085d841034040c8902d05541c113211425420b074184070710340010034042c8a4001905038007ca5502401039110194200c10181c041100f8032a4220803110107041c10f2500318015640d81a60000030580c404801720503240328000c03c02c1d10b480951100c0c0034041341404c4001c0000800820300440b000503803041d03a1004003844a00c0041c001c581307100c015071400011200956210980303000485000ca1a100d10b80080c040c03d106050180c00100c01e0302c0c1d59a4a0141001c4c0341c400300360464105408806d90076880e503a0883c007211100407050491001c6207264100080042c440d207000b42d00c546040d10400c800300020b08000b0148540c0546a0f100070b040041c108a80b02982250004c3c50030410106260100d4020f042456008241352110707003e010305048041144d01103036000a40c55070010500c0801c66800152070006004090724800e0380d841c043e000295603400408400b40680c100e131000c40d0316604902c900c81c0c01c0c100d02502c00c1d9235a01c070b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 828190053 1250 828188803 828188821
    0x5010207020f0d1104051806100815010807360912110705061e0a08060117041a09030d1a18090d05090a05040e0a0c0e2715 54
    0x400100100c1c450840a070b100c900c6481e01d08410400280c10040c9121030080c0c1105100050030041c05036000101040d090b40d03240f42c0c0030003000744142e44100c00c1076400b5203840401131030301440c24080917003141790000511042e40001444c0c42150354155040055120340b04074881c0842402c0010001040c03007070003c0c181c00045030408070403548035403104004105042170440d206000343d100c004480d0000c010400003460704001410405012000c140108410a00d07001c2442d072000c41b010f00403802440c10480d056030004800c5034004ea00c0100d0f4a52440d05598800c8071b8052481c0e005595500312010689000080042d241c401403005000c000000402004021004421802034864180e489500700c074806d81c0f084190048040c2001402c00806502007071700d82d60498400960030580c0250700043d0740e5254040c1d41050f080c4038000e8a540e12050510b500b400c1256085140c42c44120824404c00b165a1440c01411100000b00e40280c1c440d20850035040901503100468040d04100c18003007642 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 828191303 1250 828190053 828190057
    0x11250219031a01050307062c0931030e0103201c1b170408120709080f010b15070204020f03090327060a03020c010e060c03191505010507170304050102 66
    0x102c5041440a580e41d8404245d91414980242400103502c03003000d02c5d45110380c0d01050f1707100301015039101340c1d46030700c5001c0f85ca521300072200b00d11069410000c41e80603110740c501d0305940355901c03140c0101c10366444e1006088060032a81940c10155210b194050101da0010079000c2c43c2d5241c1c03640c41d41c4203c01101180d20102e014201d818141ca4611280c04258844140700300c485010345030b0040181600f036484900007002042542c10074400c1150141e580e42000c8068072031000c0342c8848000600345420300b4640204401110440c0e8034002c404038455840c0100c40c40310728519004190b50b000140b001c64007a00401d0b545103a861008000c1c00302c0d224010024204001200e003056580b04180000c0d000c05000140d1156009203040081030003480c0310703070014501c110f004000460981c03203140321a45419800c8881c81c1c0c0c60700000c018030041c0803032212203c40d0010042d005211200c034032038200b80e070b0300003500c900c2e81403003400940c100411a080c000440c80c0c111088a03a901c0c3c0ca040d0404d03c1c007035 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 828192553 1250 828191303 828191333
    0x40212090d03180c03081606022101140a14120a060b030c030312060103020703140c0a1704050108010b030402042a0906080c1b010b060d020d1125021903 67
    0x46424040030180c01e0100b0381d4407581c5a50844420700031503142d511a03500540c00200100d070481040b40c80700020072100e000400c0399040000c070000300c40e482b030b03000b1117904c0d081a048034801c1c021750b04003041036548000210041d2150210349101320054400014220080075902c0d1100f03018181c0c0c0c04040c402c4562150808040c16030544d0903524228081544034400c440c0c0c80c08061061201051840d442540503220f00d51090801e00090411140c05503408e030090b200c07904056100c052540100100c50409105203104040b03124201070805001814108050140042c0c03108003000150035035956070444601410801a4500c5d0144000380d02659003518192920100310392100000342c0034800c9546511648251200600b00300c91500907081d4420803068181140d900c0e1300d0200307a10b075500001020350040343d00b80142c0c0e03030f1000e0000708141e031482000d800241d041400606440104030840828280c1802c43c203811180709803001890890b10701c11114400c40350f5180200c20810000c1d950745030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 828193803 1250 828192553 828192557
    0x3072a1403060601030e03180d0b0f061504050f0103050c070f0821011208030702010e1b0109090605090606160c030f030e100905060d0204120c0302090705030402060f09040212090d 79
    0xb950b01c400064094424403480700c210350348100040d841101000e074954034640d800074001c203c0610980c8454012560903a48001c9640795103040c0300c2140b903c007403203007281d103841c04890703003041d02e80740001d049000490052814507481c1e40008022099407021a41c4d60303a4096201c1032650383d107052400203600280e161203080c24203005007800080d07070620f402e070490340442e000d0201c5016644d0354071b403d03800c05400f14041d5900d404084156550030311074814000811100d00324441000b000041080f00b60340d000e03d1509203040024420ba031a0511103070703031040007a200b407a91484000405011103101d6040900003804400d004000c0045101d52070305080d001c0d03602c0b0344140c1c3e0a9001c100d50403081c400490040b0312803110800081c01c168014080407101001c0060800ea0340d0746a000d072001e4451011180c60300c062009004507c0c200d0031180e0080170924055080d0b203400d134003181c0b03070340b0800c00640d0000001142041c03060341c42d44c046405880b0800c240c5602804c28030109a40d8440c4032540b000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 828195053 1250 828193803 828193813
    0x1b0a08040602060f010302220212091c2d0507050a06050106090b030621010905070b0309160e0a090c180506120c01080402040b03010b09010816050f0303072a1403 71
    0x18055000304019816650020888c4507848491000002e15000010780c07000d49907000c0c001d8450b1147c802c040c16214000410107004000002d01860450900080f410300910140c3ea03002500c00e2128041c1c81d43c1c041112039140c0030040f910700c0640c1c150180d82402001031007041c42c040c04008150308072078103c40b001c1e29120f01158a42c0d034207030311b9400200c800d41d412050741000e40d40311010b104c2d50140050181000010010015120a4100940c40e00320b480c00e050000184a0440d1b02004080640401c070003226108c41d0804000700301216003d010f0006c141d44804104041c0501e030345002d40140301d0084c45e40111151242c000025110403a4001d20683c480ca00c552102a8013184c04100804141c0d108a055076640e82080300804803140d4041e003540d41c42905903125210220028060144040101690180350762592a80ba9581d000540a00340043c0c5c034403071a03100002562102540a5055420035006014086400101e01c0d1500c0d0310900818000a18603c64420003c0604c015001e4034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 828196303 1250 828195053 828195061
    0x903040905010f030305030a051005031002031906060f05132103020d090605120901020706020307020a060501060311070f03030e10021206090f0c0310080313210201020607051b0a0804060206 83
    0x1841070f4580c071015001c04c50400024990040e654411070380481420b103407254144d140c0010034a00303000340511046280c0c0c00024041041d9044800403014003100034144211410802c1c01080614030400c041d040c40b4005c600c03d03081c406001d4444000d85524507540c0024103807100320010b01c0203280000d0b001350003030b1004066910710916a10050b44c50940365185025642c401014030808010000b9100355820301001c0e00241442c001580912103650003042d0040450400c04103e41c41a805030040c11300d055003d00110888000340c2d01107a4201600761500c9005003420390140c1064048100280948555460440382550240c0200302200c845400d10b9a40c0b0020301102503400c4d038052589004a500080b84641c0c1c0701c4c01158405161030090400980c0c1d4610145141c110800c0900018503c0c041030101c408107030704001c1e00c03068409016403841c08940010707440344000b408a408114000420030f400325044000c180240b60003508598004485040200f003070380084c0264801402594086 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 828197553 1250 828196303 828196319
    0x5042001030e120c01020c030409021c060e010308030a140702072907080703050f040f1a0703170a180503030421120c0e040f06080d021b100512090304090501 69
    0x90040c881010b00038046010f07030380f480508940040741070070015902040301c841561410f1010300003c102e41c52002d604d03511440c0140c0c4901d144516610b103460300d000303c200034101030541d80c0340c1107039000243e00e03980e600c070120f040000c0c00d0741d204211800d41402c82401000c0754001036540c02c0301c4000c10300d2041c181c98010503190483c032a11000030154414816036010075441d500400499100b410220715203140c010044071940c1083c1e000104456203c5400c00c49914806a00007003070310040000351038100140e07006002c1d0811400100142c0094a002610314003003640101083e0100070030b802011107040c42c2c029641e0b80103c40486401003130300583c1d03e50303041c4c521954107100140d0722420300c0054042c0c032020003000400302460412031900d20b11000c984940c4a80c080700c0c1800300c03000c079200d424000c40c0751401b144040342d0700c11544010300206404800b565500d800c0c03c02115201e8800d003048008072114080c10340303541032600e02c0409205c958000000100304486c050b40d02030017261703606c0072a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 828198803 1250 828197553 828197561
    0x6020d020a0c030b06061c050103020a09050721060b0403050606040605011112031e0901020c0c0906010918061707080c0a0f0e0925030308060405040c17010f0504200103 74
    0x1800d0000110b42440022100140340703521000203403843d403c040c2d44c00081001c82030030040400349141d0710700c014400c0d0700b019170540c009449030b15003d0143d41000712008003580707090300712030004402d0008802e601c00103039000f120040c0250880680c5494480c10103d03150b170020f45a4521071446d100d40020b841d4014810035014968039800f815000c6040200010a60700c01001c0d0b4504862a611900010b113000000c24050050303a40016191149002c0b0103103031488903006980308980704420800c2c140c2e4448802800c1c2d9502c11034121092110070707444009005160007090391a00d0005444000d00000901c03801125100030441d400448101300b88810981c0703600810806500c00c0764240300010132410113070b400c0800ea4085034400250030344a1940508010322000303a515030640d0400074503a00c42c501503003018088804101508003681d50f000c502e41c4900c038549400b9108039690b410100290300401014528880500003881c00c4c3c90041500340d0108105243c40406074103415455209120b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 828200053 1250 828198803 828198823
    0x15050a06020705120a1a07031401050616020d05061f06051e1b0f160501050414010e0303120a020901030f0207120e0d0c0b0c010b03120d0f0204081606020d02 69
    0x103040d5150605050000c100318000140e1013a00c6100304410000d6041c007802c1c81c007074400e46c2c3e11207450308040d603004003a50104040c1c05496056100103015950f102001c48001182583d0107428000b414800700d600c1801201c1c0180c4940503d50801401059041841c6003a007041e0144004880d1101402d551074040c003500f0441004e170381180030401e0302c01d0714014135100910600c3c021b250701c4459030340362030481c03a1603207a82c19400c007101c00a031586003001180086d1109003007a90406044c1300981c4000026140386078104907800415a00e952030500451b41040a452265245880c101c4400c4c00030b94000a000c0c7d00003441c1411074120094140701380e403d035907880b80402244001c0b110003140c5080302052015030207040c40d1103441c00216041c01035001041208074242c0c5403032500a40c9c600b151100c0303440c20300980001a01d160310444501c00c50b1807040103000000f0b1002c0f03c0200d040c0090040349c01036040c40c0300c0c4098580c1c00f4202c0350590012603980d0b03800c40301a142105800c13078881d50000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 828201303 1250 828200053 828200057
    0x619030c050103021c18030806040e03030a020a030213080307120c081207030204090903020c0f0901031211070312080f070302180d3f020a0b0604051005031015050a06 73
    0xd40305001d075601c283c0003414003101e8030080c400c90703903482099075048a001417154040514020080020550405006540039508a408024003000c1c007501a4803440010581b80026034002a2001014001da040d100d4228040c0102440c66072904035440d03496200c03604c10380d02179080d03003807a014040c81120016242a4011016814000174030841c220f440c6019200c0018181c09010200d000800b0f0710506002501950003000e80d8010300003030005c0c2560900140d03005000090052010408451688000315913618005200540d00501c4070304145e4590001414421030011002d0100d900440a030f01802072820300700c1e030382c2c3c4400c4030680c200d11445014440640f008003620f000d915112408242503030060202410580b40b03840c007501074083d14203035000416030904059204401c604440080c41c0ca050009000f0108141c136201c8a50700000d00c0c1a00c01c50321580010040044c0c0c0000800404000d07040b103548040c00030503800503101040c685000c0141e03150340080d86280c1044030030101d82d00d0ba = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 828202553 1250 828201303 828201323
    0xc0204320f060a170a05100f0b0d1a04110904030507060c0c030e0f03100f1506051c0509031303050c1309020604050d03140c0c010e010201020a0f110f15061903 70
    0x182c0e15144d03240810030b41503c103004200304400030600900078400c580d01080c000041000c2e040700360508450780900501d000c0c81c0a40310311303400101c030303038043c44800c4244900a144aa40b107251807102e0038502e00d1401d42107502d0005100800d5000b6018000c42c920488013400000c40c0090121480c402100016000800942940c112030030820100d41d049138004c4c09480140c140002201d051b00c0942041c5501b456480f21003070001a40040480701130032084c60405c2c03800c0124061001d44280485000b10310550710004a42400400c01c22a50941c448060b070440302650f904203141c40e200c0800300c2501802c00442070f108a0700e4284182610b140c0c1c020304003401d02e8280030074441005441d0f04100c041c000000440400380942e04058480b030006c0c1c038014009800464001840001305140213030540e0b00500c00260a2508a02031400803220ba1810304007010707000545520b0200790309040000c500514141e24212070004a0041c4120b405440304141a440c03020b40d230340500b03103a05c0040c05d64a05 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 828203803 1250 828202553 828202559
    0x30801051806040c050409060807140901030c21020d030f0f05041a0d180c030204061703033c090f060c041217030a020304060e1c0c0204320f060a 64
    0x40741d44804c01c00125441e081c0c3c2404d89505101c0c007160342540182c443d80e40560b90030041003140300e040c484000b20540743c10314994510740d035518a0328554064461042d8001c8905504150307082000004140c00600c1c4441d00111410b01410381e09a41800c00000780543c05101d0501d40030358100c0b030485007404180f8013146489846680c035600700e40900c201c0251542848404c010060b094501c00038080c112801082d882c52042004683d1158840101c4600c80c00c01c002940d00003100b501e911604940d82c000e012043c0c101901c1907441c407010501c44900b00b100602c844001000d821500c90304003d01191845104240075a50301c1c0800c5400d102151304c200b200340400000000001c0e0020300ca1400381e207840c1407401e00000c680e04112500c0103000d42c0442040288032280c000d4000f8141400007800044181000140c0c01c031800d441c0d079030244000c0030041c4045480c0c0c0c0d07010704480e45c002c501250b59a05400788040c0142c0781e000340380701021500c0c3d0200d0400028040c440e8080c5100030003810010b46 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 828205053 1250 828203803 828203809
    0x311070605060a051f0e010c03210b120c040f0207080a0f0908071d1311060901050c060f16080708060d08071b06020f0318090621010504030801051806 66
    0x2100802c5150080041d040014880c0c81c0c0118081c5282955a00f0f846003403807440006040106691140703040200102108001c0780d0002c01c201c041d81c41c9000c480078800a84407800c00035100308880103400595040d0011a900f80200d02c00407a401e085409028840a0264500070380c040c810001e0320200301000104141c60050700e0300780040006041421419a032050788031b0410040f54000f41c0d1607242d030300d0341184420861150b6940006207010010540b141500c41041e81610641c1803802aa000281c0c804c050f8000c0058420700f10b000c50803100340d80f912400142141c0b2080d1240c012800f0420400d19203207004600c400e02c5151030b541d5550059980108006050f6000d0000b9595003400f013200b900401c2c50030581f4000c8480c0901150945460440002d152111105040c80d003034000340802c802c1115000c00c40000f50700c08542d200d5103600d82c000007904599071550310013620140910181200101900100e1165003c1d84034201c8507aa01c07410b004001842c211084842d0307410000060f014a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 828206303 1250 828205053 828205061
    0x31d0c12121206120f0d110d0c03110f0a060e0c0d110105070215070609050c060403081209010e0303130b060a14010c1b1d092a1318021003110706 64
    0x203c1c0007800e52035030040d0814180d0070800140d000c001160841000b103100301d03801000c820f42040c0f400c0005c1c94030411121006200800da200002c04000207804c49c5103014404108483e40703c03080c2d805655882d4041d16004000700760040140c002401800005080d500c4c081c40a0504190000441510001804011511070748540022684041440c3e039900b5034002c090050a00f0a04c1440001203d01c0d207411700c5481c0c250040682c0344101070801c001e00c0000c4548050b40e8105c0c115003e4184680c03516246680034005440c0c00d44e816201c04410041c2e1000d5034841c9880703641c000d421013056034491109101c403500141c040c0e03440d58850921030300180c0d41b084456149181c041d1111002044100a544844406a40c00304140f0000414071000c95030195900c00d8025100c0e030010451110b0340300f0800503803001c00c00b1980c0f1900807000250441e03150340c4030725100c10585403010480c22580c008100080642080268060b038810440d03403444502901c5448030070301c08116038a003071100659030312b0082c1c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 828207553 1250 828206303 828206311
    0xa11360705040f420206160c170c0d091406120c031807120605060d02030a031101060801140a0b0909191b06030c0f09050d02010f031d0c121212 63
    0xb5185130a0240554080009103000e41649a0340d900010030400007490032034058440c032560f42c0610301103080b4039000200c0f001000c0e44003407448145102542c03000900d0250032007807041402540c0c001407a46500280101c25140c491400d484988880011f0100078002e001c0b61484050610000c035a1030312240015581c031070710059070003403a01400e201c040c2c1455455484104c81c0d00c005440002001998050701c2d074807113010b41d6034648080581e00080d903151a9420b016062000050000344001800c7d0401c1016107402d5009204203000b0b1a04110148811100d201402d1300e01840c2414910741140b2450262034840000c08400c5c040e04124658040e0041c01128407480b5585020048860030014000030104e50f1070008030031201e208050007205400407140e0030825207400070705c101e640d0303440300c0c0549540a00c0d164801100200c4182c0c01018084c406070800f02c11540c0d000440c0c580010403814404c0c0030b80d40c1c21030022000c08059500e241d000c030ba20308425020302204041800f01c252071640 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 828208803 1250 828207553 828207599
    0x11a0a080a021c0605040c0c08090405070c0606030b0403110a0507060302030a140408130b0c0307030302030c160c05010f0207081c090308030f010f06110a11360705040f 74
    0x34110145031982d903821071424a01d01c441d5101c013420001d918007841aa00c002c3c44608181c1d03a90070840e500c020262169401c00ea02c25030303641c2c010032074641c841c1030103210030303984960104400c0780c0760300300351001d071808076000c90000b400800300c19800240401c0c0204650b42c001e0090186900304001980650001442000d58070781d00c2d01101446c501390000c00e40214018920f00e59110700740d9032411480303101ea800c5940d04050030040300c40c650b20b002040fa0308944d054070700141c80c4e450314503640182740b180d4032404052011880d0613000748014544800c0881e1001d0321902c00c2c1c100c042c002640c0310800d6100d441d005030040c03661804000c0c4c102d020321124400307900d4040e04458507903844040640081c1d0301c112325401804014010500c05132200000703441207090443c9518459a100780da070384103499009201102d249143d00c807030744420344556242ca00e80200c40401604601c40300c146200c80710b10010400081e00085803900c3c0c0030301c0440d000c1d100d0540700d5203000741c2071810410548984400700e050b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 828210053 1250 828208803 828208807
    0xc0f020f040c0e0a0602010e0d120605060c1015050a06110109050607021006140a06052107030906061a16111504051822020102120304060e06011a0a080a02 68
    0x1065503914480c04400d00302a858081c0c070f006540051107401100ca4000200350b80c585400c000d501c00c000506040c031a001498440340c80180089504040c1c08141d01090b0084008100b40480060100e00004040460603042280500054500700482e0203845a03a400260202c01030122074840c4c0e54160300000c603a4004600d850172a07498510f044c90842c2c5c00b00060f04107440080501e0f0207400303880700805961072400765034103a040000f0449100c504c1220203000700002e05d01c4d1000c28202c1c2d50220000310319200c2c0094944840003402804c40c0000441d0090314110000c680b030716014804803600c0a2600700c1606003406039a000c810403000e078000341e4140304540408003855462040b00503018521402164039149004c0c00d001e041c0c0e099511f040016001700c0c0410510101c01c00000b10a40e04040c40280f00365003030700050381440b0b00c01c0302e000000d10780001008140907954011054940c40c9404584150f80d0f01e00c000a498403c01490314000702c81044029001071058510365000480048014 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 828211303 1250 828210053 828210079
    0x14060f030f07060e0307060908030f180a0e06190e0a021b010501061206081516110a08040f150c020d030e03030304050105011401030b0307090905070302120a05120a0c0f02 75
    0x792a2954607844500000e1084804056030306080c00800003d0a040c100900200d060100e483e07160f010769030508a041401140b9080e03524005544801582d4000e02110b041c0da4072048111410242181c641d03015007005800d54bd0f402043c02800001c44040c20040c0d85aa15000400c6010b544800400c003048000e041c44084036610a2003054024550742e180d55404205054482080d50746980c0301152541100c14610110140084040d0307019100e0402001c0c8c1c80001e403000d840c83d8900e086501034030b100749070854040041c0c0e00020801d0b5041140b41c04112580d410700c0c1c440031841504000300003000064100d0050501c00310620255100e400c02e041f0042c02c0002113440c54100f00c81c10f442581d120401088580b810300f00b034440300d42c0c007840c00380715205065000c070b5901d03081d52142e0040560369103100020b004041c040780c00995401022020012600110242d0310001488152542d01544012545203a40e030030032504d034075005441d00d40000c8515110f000490308400c1044c1e0300406443d01c16 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 828212553 1250 828211303 828211333
    0x907020c0a0e0a1e0c080a090209060f01110d0504030c1205030d05150409060f0e060603070315110a0c030201061e0509060301060e070917240709030812150414060f03 73
    0x40c0c800c0a004c82da00003aa040503c2c0024400c0c0c0c0301178080710b941803404c0780351805038031101178440c0c0c030000544149a0304c0c900c010048988694203101101c05008004d040304030994400c0040048a020b08507281c20380ba183d40306074030342d00c407100c2d801402d980c01040321035075508064200c19070094803400d0742c8031401c0902c400314046d107500540844401380d1f14003060800805621800240342d101d0401407203e07140a602113551091203000160081c1900074510343d0342076150300304a141c80c40c422611034850807080c10280c504a40c136a0210055400d1000c045450300901d4030041200301041d103c000c6891811040c8040b07900c0291030385030035540750341c4007050701030a402c00c4034050107295807a0100d0902e8011a605950718003141e16031103070001901880b1421242e004803800ca681d80b503100355192200c10b0150340e01c00c0349500080103078001040e01d01c0c8026465066511a03075421011100e030700c80c03050400c004c550581d11701d8071103100303808041030860520511003030420b00d01904a8041d00c068060b0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 828213803 1250 828212553 828212591
    0x11e0206190b13020703030f05040506074506030e030702010c080c0d1d0402092115090d0e09070c060c09050d0c0314030a0c1209050d0308060907020c0a0e0a 69
    0x1a50003c43e4000410504040d454804c07610707040f9060302c0402103800c1658400da110789000e03104804002c031901041c00ba03032403200c42840402004802902c01c140d0b0041c8803145004184828200707100c119000020803900034000e0581100c8004055454805075134010340e011a00c50f070040d1000c0c07100f4407403007880c00810025120100703550b851301001a090b0910b20300121603104103140c0920f00601c129500c2c0e443e419921102c80b042c440d40c80c0004841c0480707140c03421203603900845110300d4020074400d00a501080c200c0c200641e41d6034201c0c00c10428014031031088030540f684000600030f0116100030540f558004040b0307c1d90b070b1414102d200d96402c001750300068807080a071200081007600300100898980800c0700300789020b010303506090601c04068012074070240040c0c20001640f00b40101d081c4585050703000b41400030000040200d40b030030020b1540c1c074100c400d80d00400c914008980c841c1d000048102c0015401400000041c0c1413200160b4030308006406a01c0d4591a140c07100320f21200401 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 828215053 1250 828213803 828213829
    0x23061b040b0c0703020406090209010c0809060f0403060f0f0902010c03120b0d0825150c170c180a0530070303050703030f0b10050333011e0206190b 65
    0x80100740c0c43d41140100300403102c50b540030b504010f10411121200c4d0340c210301110722807504403004540701c0d14800041541449100c9480c9024003000402104010a560000300500c44032142009000400015502124075800010340845d00503c6007000107886096460302c0031007280c0b0007088442000003c620aa140148115001c40c8081441ea1003034800506860480e0004c20040e4081d40342d503200c1da9035041101003801032a90329640c503c8003c0d801019090a00d80c401025031449203818142848160442e01008905084001e06000c80b441c14036028016550014410402d102a0504004048100e900e402c54090192120b1007103852082c41200004c43c082d403186c50b07480c69107103001400c40b1110b040c03c40d02c1503c0c20103103200715282c496120b0b5800c107990610503a03a8072490304400300c500d0480c10b000c444c0462200b1410001054031004100c0141c01c0e26001010900c003038000c1000c100d4031040c0801a4401000241f541e640c0074154141154054000280425504003141e8840500c0c8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 828216303 1250 828215053 828215077
    0x3020a0e04051e150f150d060209090c0301050f040b06220b0706141305030d020f0d050103080a1b0224040f080303060108061e010e06042123061b040b 66
    0x10300001c01a4a407040145e44503200400c030300d03401d2420354044084d00d1120b0740f2203409428008041d07010481c05a0440c0e0707030004020202c0c0c040e86451604821070b5442406014051048034003150201d0a0500440181d1400240413900b0091181182d910b26044030b825071001708848400010360203040070041c40b20703501503070300485c21641035282140c00e844040c0c8422241e06000000304041207000c030940322501074180001d40e80b80114001031103503014101d480c0200c0e9192600002c200030705040104440035141c0c50b54501c082061008001c1d2091340000030303421134240051a6140c1c8d2145064881008192158a00f0261650a9104030200c6504007010640c8000180300c425a000a185503000030119440da40016105800065065028400505200d22020390f66000d07510102640d001d0148144030854040c03a82c4100c40010440c640b042c0e450551998a11002a0515007400350307580c0e820b002440c01e504e901840a0440420341c0b09007180341024040810103001030380007000384003d00303 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 828217553 1250 828216303 828216313
    0x70b0f060f13051006020706090504110c06160801050103091a04020406170a1109010b1206011241010b030a0207120201050612030c07050405060a09050403230403020a0e04051e 77
    0x7051300e41c04541040e400400541d0300c0407900b04021644210004165101500c02103013218612498041070301503c804183e90740500c0302086604007030103508506200c2256110a0181d0740ca00040d412624000d0010340042001900040c02e00410a090358026102810009a05581e041e03911102100300c10300c1d0100350083c0c1c0d14907080c840c20340c0e1a6a03d800048a00240d154500b03050b202030762160740c40c0d0b0b00c4410301d03500004405a0040103001c61903c0c5140003071000c02d580224242d025011a458400d04095002c00880040100420081c0d003200960541b06c00e6400c1141b803100942005000e40c54941d000c005c5031000a0f045a907010001400f46c001040d681058002c101d800d140c440310301e40d42940140300502220800103800400c0707035001d0381c0c00035480c0ca801000c9103170042180c000c681840e0800080c482016807003420380ca14501c2e90b5003100010803a0f04c0300b00003944a50710000e0745c0240c2d104000c2c844848030520b09500f2a1181e0121004000c040040c00c1080e0036030301c1440210b03003103 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 828218803 1250 828217553 828217561
    0x403061509140f0105220c03060b0f13140a030212101406010815060313050f010903020309030d05040f0b0306010c050d032301081207080d0e0c1005070b0f060f1305 72
    0x20031150703001d0241121111b0550320707170440400000742d000401c2d1402644a130022404507009902800150078055032486c0d56038200003038041d80e5400903030340c14404080e03130300000340040a40f403441900794070050600d081d0341e1942e000c20440d0700c0039400c80034081c01060f0b50240703400941e105445200040b580b84001c42e1522100143c003401c0d0080c04070004a03a0a00c445503d07540e1081126404100c44151103d44a1141000c601d806d04200c0000c415601e406400d00906400001625031090214104d5800c0314045500701e480b80558415039481c80c00c01c030300601038001b4140180d5484031040c50b01103000d80751515070ba440c112585100a0120755100c003076072a10150180b941c15241000d106010301945840d03072071561480c156483c034180e03040201b2102d0800849508940881c508020300b030018912084c0c0468980030080741c11880b8100443c2e204407024003480c19641e4003074001244c415655241c04000340030180c01040d6035488844200e841d2a20380e181d0080c10220b2440311030014084ca0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 828220053 1250 828218803 828218821
    0x303030b040c0f0905210a050709150608010918060c080603010f0204051305090a1b0e010510021e031e0301090b041e020f07060e06040204110c03040306150914 70
    0xb20a4948400c00c20b032118241c2501d030708030354540b040f58019510609120b40c42d0000044800401c4054540f6010b6403101c1410702c08d000802c40c040e40e15448003000103447c10301040e01320383d00e0303881803c0c003150b03420b801000b00a081d54005002e0402079204040b51046540d00c1070210b030f40f5151481c022440035010300c00d95080c2441000880b01804a086160505110001e01c0844100c51340081440d196000545840c50520643c85070503400351007a10381d101800f151200c107865601424114039101c00000a992901c1c6060000300300c40341d0080c002c007442181001c0c060700c68044c510003d40c8802c00c0304001c1c0c0030701c0110315042c801103012415129410210600d040c1d0382861001485642464250085850040c00f20014032402c1c1c000141d036034050f0010030756180140d44001d0701191a101c00c0d11a091400b04003d44564401c580402807035001100c0140203000708508118a540103020a00c001003081e840702900c0901c00c1003022010f03a840600c0d505666842120003247d1100f40d0030300109030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 828221303 1250 828220053 828220061
    0x40c050105090f090a1103160f030506010509310608010506100f12110703091502010e1b0102011103090715030209030a08030c0c0a0335010b0a050408070303030b04 72
    0x18246403640c5004110030000f01c83d0255424624440c2013844041900e4101e581c1c004000d0001940580e6224648901c00b8591680d0180065001c42c1c00751007042160342c80381c800c2e5445407105071190f50501003000e007805250407400782c060782d0306095004a0980408a0650741060801160000c103070705040c03150180c00e481000c0c0ca10350007040f0359152407500c0c1d034101415080a680368a015808586841e2102c0064201410250740d0700ea000034000c0c00740b61b40001880195050702c06158140d4204510403800c8514585071401c403608a00381030b000046486012645000b01480003107040c08159000011aa1082d2204211544000c0d000c2201c031030440002c0324810070070300b4114104590100460749641554000070301490000002442c0003688500740c84500c9d2500c004c40c0c004100038500505140d2040705ea903d058000c80c4201e07900495040c4104550a18040c11004039034038018046059030042c10011051080520010510300020803980c070045000fa640450001d101c003042c40308039 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 828222553 1250 828221303 828221309
    0x10602010e1203040305090303130915050d0b060f0303070b010909020f06032a0f03040507050108130201020c0913050a110103050109020c0604020d03030e012409020301080d27030b040c 81
    0x198110300002c01440301210140eaa10036050705110b65200c110a0010f8214411503550300c44904807400081000c9046500c180c0d0410f0f602e4203d81c1c07600e9118010010208030f0088000c00c04003500300028024203195002c50000784003e42200e042080365940c294529034241c00421145640319040f10951500034054a1840f90030b0382c3da00c0c40c50801c590600d41c13448059401d403180d02110a01c14840b02261401c803950380c132a0700d07840c40e01d03030600386401e54031114180b20311400143c0f010701054a0502e003916404070349a058005118820900040c05044040182a44019180c2c99000e1000c0f039801d000c401111440359615002d40c06081001404031441a04009015841800204003004000604542050301101c08094516851408070007501103290b02410550900a0240066403003d00c0d00b00000002140801259282d00840d4201d0009200f207840704e5206101e10050703107001380c48000c0100e6605c0c52100c030003055148003070b85100c04c1e070f40304880d0041d5010802c01802104c5000344c0207 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 828223803 1250 828222553 828222581
    0xc0d0b2b0203071203050d0b012c040b0102071217090301020a021c0e0109030209090a0507090f0f0b0114030c04051005071b030308240a0308040503060f07120f02071a01060201 77
    0x480c0c02c0d1918006c1090180d0100e4504440ea18a1040e40c81d81c00f035141d5140e050400310070b0450500880340c8206030304400030b02a501071414002118400d40c008150300d41038420014a01841c1440c45d11001249100d8880051903854104580c40031910203000410382e064194008022000342c0c11f0561a515880ea07104800300a07101d4548001caa03400300981080380c1c2c048488408545608401e2810301c0c00c8584000c10074803d600c40080d031040242c0106154000d0200d00f0058103101c074001105650480c8030b1980010f0b4005540100845103001464024080c1d01c02141050b072948085100b4644e40c51801012800108244041000c45000040f004047c0000501468a035940141000401815000c0b02e215040c50690318a980c4030300130301408800800d00701c1c801d81d42c3c0c203210815a21a00880c0d002e4012407002498a90b04500f90754000c0210740e4549116200c0d00c0303885d50050000382d01c9144440d40801c031000200d11b401506412142040c0a0060b56500d00000607013151500b1586181d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 828225053 1250 828223803 828223829
    0x30c09050405151509010303081e0c030601050705030715020424020c010e041413060507050301060c151b03050a05070c0203120c15070302070c0e0c0d0b2b020307 71
    0x400184080b0703854003404110300c07003007403552502040000da264540400315080205c400000044c50380c0602d98a0085003c0104400c0102000d481d2124070441103a01d01e030952810004074000d940300300e00500c6a14010313400d40b400c5c140c0350b54404102002075418111440e4010030b081c8840d281c0c4e4074030300030032074503410041e0814031008601a44452000400a05024441603005601d4603140c000810800b03031903003400014a8a00305c08540b80b5440c100544640e450b0400180b601f6001341c04490582c1d1081d2994101d400040e5110480c3c0c410a01070030411a03103418030b00d15200c0384104400e0316510390340c801140528103070f101c0c1c4007194001044141080b071540a01d03c050789020030000b03070700a043c464040c2d817012500500b03460112146281c0c40450b000d4010050450780c50750151502c1840350340c0000300260b852030108a201c4054405039003d01c0208045032100059a00002034020080e040155a1f402c0b00290081c3c0050b40f442d44c2b011035941ca5107030007103103000d0042e04050400b14035181e03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 828226303 1250 828225053 828225061
    0x504060806090402130f05180a210201020d020c010506011101061a0309010b150705100903122004061815090312091a09030d0c021e010507021009030c0905 68
    0x4084000c090121801026424041015500e407401010300d55508000700b0301542c1e8104080c90f000380001c444100e840303c40541000e00024012a00c200c0943d00541c80d040d024140355540480142082001070956500304207031080f10710580094948051240000541d42c41c0c101e00141c001090070001082513407400405000c0b42c66098244019205000000c1c2d450351340f040807442c01420030b601400d502c43d44500d042008110381c54020149141700d2016030740d00d104c0b080d205e07800703031113240c03100070b021072903603da10303219030180354010100e06012030050b055586030742c255004294015081000050181c41604000003002c02c032800c001d2034082c85034000c0280ba808002d0095400703020041400a4085141d0b41c25842041c0c5400038044480c3d0041c041d1410147d08003881c3d0000e0a2140640200d00103612814000c500202c81140c000e04001015120300068174800081a0186411310005000034800740c0c81d0034246008000c003e8540141d81c038118240b5035040d040640c4840180c60400c0104 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 828227553 1250 828226303 828226307
    0x6030c15054b03150d020307091d010b010c120c0f0809040c080603030714030c030a080414031e092403040c120c030201050904240303030606031103010509090705030a0819050406 78
    0x403503024440800e00703070210f00b4a00001d01c0c0c01d85e2400020b58035205403440440c03507400d240c0c0410400a02c000340e0304004c0d5168000d05003a81d4a003d9001e0204010311921008102422201540d0704410701c3c110703d0740b099503581c030781e00d550034030601b52928140410a074400d4285441122000c544a0509c880d0310700d020000280d0728821100d0007000f540300c070001e10003820700c10025100c0f0b083c480340640340c6800d24035800030401c140c112002d6600305a00c081415103060044111a9005603103079a1100c0d8180714003c0e0030640e8007139481940c00c0346c988010203114069041101c03c4c1d09244044142c3d403810141001a449181038010001d0710b00081c00301070004900100401c100da5081c20440d441e1600080001c00400c4c00007504036100b40088045d5001a1030f943c184410f480c401e403001c0000c0c51302d83c14101c00b281d03440b01804008072020001400743c0e00d80b8400807503010702c0307a00466400760344400101e41030090002c400c482010006c25100010000d002e802001c069051a01da41020320744240 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 828228803 1250 828227553 828227557
    0x605160207140f121b041505030c1e040e0f0c030606060a0c030207090501090906050f13020418020303131a0a170613110d050a06030c15054b 62
    0x2071a21610072828551000c0d101c0104401000d81e01c0803da8160800d44a0020044005c88480300c2c0318a142442158940046107001410f8940180082003491020801d001806104290711a860640800c18040301e03595802582034000714640035145d01104240050b2600c0c1091800c1d6200f5041103042089948401c0705445124402e4900f801006000741003d81c1400301541084180e98140000071070859426000109601c1c1304120030032045e13a68a0000202d41e40650f0b0380800403a5810b550300162510b03400182c80310100c0c0622910010341680001e1940c0e129020460798101001010060f10b010459540304805420200c0d525080c00190001c2910b04020681d140181c840c6003c118961607008021003881c84140c41080480c000c80a160280d401210110035640c1c100710024166000302e0040c41300316139000512000300c84c1000451720305041c80b80106e00c01c0140a1220180c01102c4640c003900803003040303c0c9103030786e5188580c0c01c3c403545c0c004110000c0015500300d550320a422421003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 828230053 1250 828228803 828228839
    0xf020a09151b031206030b0103050607021507360e010902070b0a05071806051902010b03070504092d020411190f05070b15010305130302030a0c0c0905040605160207 72
    0x304088103194a80b40c10313150403400ca861070014900d801808400c12080c001701c40e0689001c0c000b16181c5130343d445800c9030385041e401c151800f40b01c40c3c0c4011500903401130030009605940c60a10516a0701c0c3c00e585121f01c441506ca020420025050003002401c030445e00c014090480b00350150314215481e11003951440f409003210008590784e40000350320500c03984001901400c500c0c0032910190341c0700030081480e041520340e140a80c0e002901000050700501c02d2180080300640038004891401080000034180c11005581c003c40a10701c0710781050111124000200403100160b04641c0b160060000710b54020101c0c003e4803004100c9000542c1c50407500c1003945203c0e140160311130100301c3d412a80307401254001820018680c040c085510103070f410414150307101380e038100941c0d540c65200c520103140390080503016070420007138000c0359803042d1140f5914500079040820345603a9007190f84202c1d03001310703801c3c1d5540c0d540354203100b0040b0480c030752200701070007600c000d00d440c9061041004101c2c0c0c03515 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 828231303 1250 828230053 828230087
    0x1020f09010e270a0204032102010c030605090a150f15020705040902011e03021e0405151303080d1b08040506070e100c050a0203011404140a0b010b0d0902040f020a0915 74
    0xc0f00080c07404401e601110007035680725505030b1900003002040380401d041801010059401d004c007101c80f0301d1003840f071201102d500a000031003503111000c10100400b03a40e01d036800480072483c0085080ca00380d1500703030005d00003503000410410a41d02c0c020304051660b040035204e9428081c040c03000d41e9204805518440040f01f808442000901c400d4009105510b121840e50500301e07420040305007010050002c9480603030300c10320300040003e240c1d075051040c034010140e000030032041440860705010180c03440c01c00782400040c3c0300c000c1642c0510380780f41c401080400281201c04010401405100301500f040302402e0143ca90400718001030200c80c030700c48140d010860b00c4c29031801403200802030116903540250080004c078413880031001e0361150484060f1000810308100350b0520b807001a0780d400e4a90001002608d603420040c82d8001030780403016a400711526000c048025a0303840c41a4400706200c80001030f5903032408040a00001d03040e900081d00030300313604d80318901b0941112222042440e54 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 828232553 1250 828231303 828231379
    0x423011107031805041a040b030c0306130f0503030a0609180c0611010b0a1e08031c0e0a02280b040e01050103180501020f030106080f09070317070501020f09010e 71
    0x40400b010f80e095014542c402d00f4001d41c0c5401c0d4140786488560b0403000e07102403010350310300002e0581c2c440c034400c0309035016888030000480780500c0500240040348186440c00d45100c00d40caa0301d1464005407001312209a955508103c84000c0d440740300c2211140a2204903012480c0c0c82e09008a5101d1080205101f203c0320600c114403c2035100c00a03c880040042c0c3e9215140c50300d10320070764000f482040224200313803000718010100005550181c41141d144090403850050500b0142801030060165440351500200043c0c2d03c070351041e1020404408042103907120341c00c5900443c4040c4c0e1203408440c008100a008810b4131404140c1910b0f000c2c2400b28001e01e89100b001c400700482c15001c0c4c032552021820b007401d00b48010081d8100c42c0c0550b140c0740b0517210180c0e0102220000c1c1c031600c0071940024000c2000441184601800141c161070300c505064454441d2400d9a11103201c1007601240003c1c10809580c10490440c181002501e003485042880800304603400e03800b85180d4902c0007d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 828233803 1250 828232553 828232577
    0x191227180e0102070c0501030507090b0421020d11040c090308040b031b0c01020403021009080a0312110a11060f09030f03060a151205060907090501050708070b042301110703 76
    0x40d03500001c060304507460003155543c92600700305201500b0390280c28002800d0601043c1e085214034107c4050300c0038030381000d207020303c1c1090842c03c040b1125100b64034020300c0301c00c0c200565180d10483c5092406240010718038143ca000b000210b0328480d0100302030241001e018000b2420401c1501d098910400550350340ba1600d031151240c020007444018040f040004000a4050042d0058422030384251107003502c00100813001e40d03000045004500a95000b5001c8101003441072400b4201028180000078441c00e05445410701c517400100007002040948044000c0010708001203035002d1120042043c0f541002441613849110310b072504030f074046012010035050380e5480103050040c06052039918008503c1000680070155145884412070320700000640c0d1800c1003c01c15116440c203607114480c09007003100560700b640200d00d00f030781c55203800d00484c40010503881c0e8860013035004900c10301250040e000841c10000041c41010384030f1341410590007a244502040d07548182e0b05050100b68000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 828235053 1250 828233803 828233849
    0x40b180d0803041208060405060f010c0323040302210a0b10050604030b07020f0d02031c0908030a0506030609010605153a0b030303060f0f03191227 65
    0x3410003000c0c1c00e5000c000244002c01c9000150218402030039110521150b40c1e920412007150000c4907030b2500990443c0c84900d0079840340381d02c4640d4910a007000c5080144410480f560314100880034003101d01c00040c14400c0d803400d00c000e0502d03d410441154507100520400c541c484000c120000c202c502e504012802164101e400403010f0b00c000340c882500c50b070307690800102c44401030b11390102501424251401003140480c82c2142d07842680c0045240c03441d17809503000c500d844d4600304c900d150350742c00c298000103c0041c02940944d119400105041c1000400c1508144014040591b960700d089400c0281d62039004170203022800095040b521540b0310629203101980301c50250701c04003002825410b240400218001c40e0141e071000801450300040c0038107a6900c07042c0c80a545c002425000203400789009800000c2500d40942a5480c139030400007a00c00d40c40c541c0d6003c40303504007222914441c80781d010b1a08403c06a00301c40c6034001c14601c00d152000c00050f8001c2c890300c03119106100344441 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 828236303 1250 828235053 828235069
    0x3080306010908060403020303011d06010c0b06190305010905121201051e10180b040e13030c05030a02150f0103020612060102160e0f010605310b0406030f11040b18 72
    0x5010402d413165481d0500c0e0003904da60090080c0b6a9410444c43d007424900a81da402d10f00c02c1006031210255450540c84290a80c2c3c4010206584000340d0004d02925001c03c802c01c8000714403c60011070103e10b1860041e0409c1604041e000c02c3c1c000c10700642e0417103001801e400c3c0c1102c03030641d086400c2c050303081e240c03001c00242070464a8001c4108405510003503881541c40076003262810307000d0507044d1690f005440911a0303103e05000d00c504403000c00c108054a1400f0b203a614824184020b5400381c580d01e4070f0940c3c01000320100541c024080e1850700410000c0b28550040c80c4910041d00c81d81075900281d00341c01000d00303003543c241d4150002040b43c0d008024045540d40c008010b45180c5644d00a85c070140b41f011108070700600c1c0034000008189002e0000c0d41ca02d42445a8440c4208856a105104440744810f0041040d409104001046c4600b100100003610503a07031b01240c400074a0041406840d0303012410200800100170403c84180302000b92042e200c00c9d03455412004800c1c50004410b1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 828237410 1107 828236303 828236309
    0x411090114041d07020d020102040b0403060c11100207150b012003070b0c0403050d090f0b1b0f031308010c050a2001060303020f0c0a0f030803060109 66
    0x80d6005120007071040040d407610382e0a00b5940c41640086500c01907900b0100110b07041031010b0360f43e040c401c40f045009035000035413505207005004142c0303114601c00641401d90301c3c284803201a114003084603802d0444000c44604008204000e0001e5105c04001c48044800d1207550aa07168280924154843c05841d21200302c4004c2c140c80d803504400d503251404d0783c0000c010701000640341d10719890141c090030210507119420362515500c3c0c41c81c0300c1d190f1000d0000c0380d4000c000018031029801c040d01c80080500b62135840504007804a5084800d040c2120b00412005004115001001e0300020000030059141e082e5518070050880d0f00a20000c00040d100700041c00c4401e00544502a120b040d400001c044c040e5640402402c444182e007003100160024044d42c0d00750503042188190413003040300c108503080d1400c0d05501405440744801040300d40c01000003906623009a60700401 = true := by decide +kernel

theorem cover : BRFrame.Cov 828057553 828237410 := by
  have h0 := BRFrame.cov_init 828057553
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828057553 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 828057553 ≤ n) (h2 : n < 828237410) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
